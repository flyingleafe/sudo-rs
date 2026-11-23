#![forbid(unsafe_code)]
#![cfg_attr(not(feature = "unstable-remote-sudoers"), allow(unused_imports))]

//! Code that checks (and in the future: lists) permissions in the sudoers file

mod ast;
mod ast_names;
mod basic_parser;
mod char_stream;
mod entry;
#[cfg(any(test, fuzzing))]
pub(crate) mod equiv;
#[cfg(any(test, fuzzing))]
mod legacy;
mod tokens;

use std::collections::HashSet;
use std::ffi::OsString;
use std::io;
use std::path::{Path, PathBuf};

use crate::common::resolve::{is_valid_executable, resolve_path};
use crate::common::{HARDENED_ENUM_VALUE_0, HARDENED_ENUM_VALUE_1, HARDENED_ENUM_VALUE_2};
use crate::defaults;
use crate::log::auth_warn;
use crate::system::interface::{GroupId, UnixGroup, UnixUser, UserId};
use crate::system::{self, audit};
use ast::*;
use tokens::*;

pub type Settings = defaults::Settings;
pub use basic_parser::Span;

/// How many nested include files do we allow?
const INCLUDE_LIMIT: u8 = 128;

/// Export some necessary symbols from modules
pub struct Error {
    pub source: Option<PathBuf>,
    pub location: Option<basic_parser::Span>,
    pub message: String,
}

/// A "Customiser" represents a "Defaults" setting that has 'late binding'; i.e.
/// cannot be determined simply by reading a sudoers configuration. This is used
/// for Defaults@host, Defaults:user, Defaults>runas and Defaults!cmd.
///
/// I.e. the Setting modifications in the second part of the tuple only apply for
/// items explicitly matched by the first part of the tuple.
type Customiser<Scope> = (Scope, Vec<defaults::SettingsModifier>);

#[derive(Default)]
pub struct Sudoers {
    rules: Vec<PermissionSpec>,
    aliases: AliasTable,
    settings: Settings,
    customisers: CustomiserTable,
}

/// A structure that represents what the user wants to do
pub struct Request<'a, User: UnixUser, Group: UnixGroup> {
    pub user: &'a User,
    pub group: &'a Group,
    pub command: &'a Path,
    pub arguments: &'a [OsString],
}

pub struct ListRequest<'a, User: UnixUser, Group: UnixGroup> {
    pub inspected_user: &'a User,
    pub target_user: &'a User,
    pub target_group: &'a Group,
}

#[derive(Default)]
#[cfg_attr(test, derive(Clone))]
pub struct Judgement {
    flags: Option<Tag>,
    settings: Settings,
}

mod policy;

pub use policy::{
    AuthenticatingUser, Authentication, AuthenticationScope, Authorization, DirChange, Logging,
    Restrictions,
};

pub use self::entry::Entry;

type MatchedCommand<'a> = (Option<&'a RunAs>, (Tag, &'a Spec<Command>));

/// This function takes a file argument for a sudoers file and processes it.
impl Sudoers {
    pub fn open(path: impl AsRef<Path>) -> Result<(Sudoers, Vec<Error>), io::Error> {
        let text = open_sudoers(path.as_ref())?;
        Ok(analyze_text(path.as_ref(), &text))
    }

    pub fn read<R: io::Read, P: AsRef<Path>>(
        reader: R,
        path: P,
    ) -> Result<(Sudoers, Vec<Error>), io::Error> {
        let text = read_sudoers(reader)?;
        Ok(analyze_text(path.as_ref(), &text))
    }

    /// Apply the `Defaults` with a host, user or runas scope (and the generic ones) that match:
    /// the modifiers of every matching line in file order. Each scope is matched by
    /// [find_item] with the aliases that the host, the user and the target user belong to.
    /// Afterwards these customisers are gone: a second call applies nothing.
    fn specify_host_user_runas<User: UnixUser + PartialEq<User>>(
        &mut self,
        hostname: &system::Hostname,
        requesting_user: &User,
        target_user: Option<&User>,
    ) {
        // `std::mem::take` has no Aeneas model; `replace` with an empty vector is the same
        #[allow(clippy::mem_replace_with_default)]
        let customisers = std::mem::replace(&mut self.customisers.non_cmnd, Vec::new());

        let host_matcher = &match_token(hostname);
        let host_aliases = get_aliases(&self.aliases.host, host_matcher);

        let user_matcher = &match_user(requesting_user);
        let user_aliases = get_aliases(&self.aliases.user, user_matcher);

        let runas_matcher_aliases = match target_user {
            Some(target_user) => {
                let runas_matcher = match_user(target_user);
                let runas_aliases = get_aliases(&self.aliases.runas, &runas_matcher);
                Some((runas_matcher, runas_aliases))
            }
            None => None,
        };

        let mut customisers = customisers.into_iter();
        let mut more = true;
        while more {
            match customisers.next() {
                Some((scope, modifiers)) => {
                    let matched = match &scope {
                        ConfigScope::Generic => true,
                        ConfigScope::Host(list) => find_item(list, host_matcher, &host_aliases),
                        ConfigScope::User(list) => find_item(list, user_matcher, &user_aliases),
                        ConfigScope::RunAs(list) => match &runas_matcher_aliases {
                            Some((runas_matcher, runas_aliases)) => {
                                find_item(list, runas_matcher, runas_aliases)
                            }
                            None => false,
                        },
                        ConfigScope::Command(_list) => {
                            unreachable!("command-specific defaults are filtered out")
                        }
                    };
                    if matched {
                        apply_settings(modifiers, &mut self.settings);
                    }
                }
                None => more = false,
            }
        }
    }

    /// Apply the `Defaults` with a command scope that match the command line, in file order (as
    /// [Sudoers::specify_host_user_runas]).
    fn specify_command(&mut self, command: &Path, arguments: &[OsString]) {
        #[allow(clippy::mem_replace_with_default)]
        let customisers = std::mem::replace(&mut self.customisers.cmnd, Vec::new());

        let cmnd_matcher = &match_command((command, arguments));
        let cmnd_aliases = get_aliases(&self.aliases.cmnd, cmnd_matcher);

        let mut customisers = customisers.into_iter();
        let mut more = true;
        while more {
            match customisers.next() {
                Some((scope, modifiers)) => {
                    if find_item(&scope, cmnd_matcher, &cmnd_aliases) {
                        apply_settings(modifiers, &mut self.settings);
                    }
                }
                None => more = false,
            }
        }
    }

    pub fn check<User: UnixUser + PartialEq<User>, Group: UnixGroup>(
        &mut self,
        am_user: &User,
        on_host: &system::Hostname,
        request: Request<User, Group>,
    ) -> Judgement {
        self.specify_host_user_runas(on_host, am_user, Some(request.user));
        self.specify_command(request.command, request.arguments);

        let flags = permission_flags(&self.rules, &self.aliases, am_user, on_host, request);

        Judgement {
            flags,
            settings: self.settings.clone(),
        }
    }

    pub fn check_list_permission<User: UnixUser + PartialEq<User>, Group: UnixGroup>(
        &mut self,
        invoking_user: &User,
        hostname: &system::Hostname,
        request: ListRequest<User, Group>,
    ) -> Authorization {
        if request.inspected_user != invoking_user {
            // the Defaults that `Sudoers::check` applies for the pseudo-command `list`
            self.specify_host_user_runas(hostname, invoking_user, Some(request.inspected_user));
            self.specify_command(Path::new("list"), &[]);
        }

        match list_flags(&self.rules, &self.aliases, invoking_user, hostname, request) {
            Some(tag) => Authorization::Allowed(self.settings.to_auth(&tag), ()),
            None => Authorization::Forbidden,
        }
    }

    pub fn check_validate_permission<User: UnixUser + PartialEq<User>>(
        &mut self,
        invoking_user: &User,
        hostname: &system::Hostname,
    ) -> Authorization {
        self.specify_host_user_runas(hostname, invoking_user, None);

        match validate_flags(&self.rules, &self.aliases, invoking_user, hostname) {
            Some(tag) => Authorization::Allowed(self.settings.to_auth(&tag), ()),
            None => Authorization::Forbidden,
        }
    }

    /// returns `User_Spec`s that match `invoking_user` and `hostname`
    ///
    /// it also distributes `Tag_Spec`s across the `Cmnd_Spec` list of each `User_Spec`
    ///
    /// the outer iterator are the `User_Spec`s; the inner iterator are the `Cmnd_Spec`s of
    /// said `User_Spec`s
    fn matching_user_specs<'a, User: UnixUser + PartialEq<User>>(
        &'a self,
        invoking_user: &'a User,
        hostname: &'a system::Hostname,
    ) -> impl Iterator<Item = impl Iterator<Item = MatchedCommand<'a>>> {
        let Self { rules, aliases, .. } = self;

        matching_permissions(rules, aliases, invoking_user, hostname)
            .into_iter()
            .map(|(rule, permission)| {
                let (_, runas_cmds) = &rules[rule].permissions[permission];
                distribute_tags(runas_cmds).into_iter().zip(runas_cmds).map(
                    |((last_runas, tag), (_, CommandSpec(_, cmd)))| {
                        let runas = last_runas.and_then(|i| runas_cmds[i].0.as_ref());
                        (runas, (tag, cmd))
                    },
                )
            })
    }

    pub fn matching_entries<'a, User: UnixUser + PartialEq<User>>(
        &'a self,
        invoking_user: &'a User,
        hostname: &'a system::Hostname,
    ) -> impl Iterator<Item = Entry<'a>> {
        let user_specs = self.matching_user_specs(invoking_user, hostname);

        user_specs.flat_map(|cmd_specs| group_cmd_specs_per_runas(cmd_specs, &self.aliases.cmnd))
    }

    pub(crate) fn visudo_editor_path<User: UnixUser + PartialEq<User>>(
        mut self,
        on_host: &system::Hostname,
        am_user: &User,
        target_user: &User,
    ) -> Option<(PathBuf, Vec<OsString>)> {
        self.specify_host_user_runas(on_host, am_user, Some(target_user));

        select_editor(&self.settings, self.settings.env_editor())
    }
}

/// Retrieve the chosen editor from a settings object, filtering based on whether the
/// environment is trusted (sudoedit) or maybe less so (visudo)
fn select_editor(settings: &Settings, trusted_env: bool) -> Option<(PathBuf, Vec<OsString>)> {
    let blessed_editors = settings.editor();

    let is_whitelisted = |path: &Path| -> bool {
        trusted_env || blessed_editors.split(':').any(|x| Path::new(x) == path)
    };

    // find editor in environment, if possible

    for key in ["SUDO_EDITOR", "VISUAL", "EDITOR"] {
        if let Ok(editor_env) = std::env::var(key) {
            let mut arguments = editor_env.split(' ');

            let Some(editor) = arguments.next().map(PathBuf::from) else {
                continue;
            };
            let arguments = arguments.map(OsString::from).collect();

            let editor = if is_valid_executable(&editor) {
                editor
            } else if let Some(editor) = resolve_path(
                &editor,
                &std::env::var("PATH").unwrap_or(crate::sudo::PATH_DEFAULT.to_string()),
            ) {
                editor
            } else {
                continue;
            };

            if is_whitelisted(&editor) {
                return Some((editor, arguments));
            }
        }
    }

    // no acceptable editor found in environment, fallback on config

    for editor in blessed_editors.split(':') {
        let editor = PathBuf::from(editor);
        if is_valid_executable(&editor) {
            return Some((editor, vec![]));
        }
    }

    None
}

// a `take_while` variant that does not consume the first non-matching item
fn peeking_take_while<'a, T>(
    iter: &'a mut std::iter::Peekable<impl Iterator<Item = T>>,
    pred: impl Fn(&T) -> bool + 'a,
) -> impl Iterator<Item = T> + 'a {
    std::iter::from_fn(move || iter.next_if(&pred))
}

fn group_cmd_specs_per_runas<'a>(
    cmnd_specs: impl Iterator<Item = (Option<&'a RunAs>, (Tag, &'a Spec<Command>))>,
    cmnd_aliases: &'a VecOrd<Def<Command>>,
) -> impl Iterator<Item = Entry<'a>> {
    // `distribute_tags` will have given every spec a reference to the "runas specification"
    // that applies to it. The output of sudo --list splits the CmndSpec list based on that:
    // every line only has a single "runas" specifier. So we need to combine them for that.
    //
    // But sudo --list also outputs lines that are from different lines in the sudoers file on
    // different lines in the output of sudo --list, so we cannot compare "by value". Luckily,
    // once a RunAs is parsed, it will have a unique identifier in the form of its address.
    let origin = |runas: Option<&RunAs>| runas.map(|r| r as *const _);

    let mut cmnd_specs = cmnd_specs.peekable();

    std::iter::from_fn(move || {
        if let Some(&(cur_runas, _)) = cmnd_specs.peek() {
            let specs = peeking_take_while(&mut cmnd_specs, |&(runas, _)| {
                origin(runas) == origin(cur_runas)
            });

            Some(Entry::new(
                cur_runas,
                specs.map(|x| x.1).collect(),
                cmnd_aliases,
            ))
        } else {
            None
        }
    })
}

/// The text of a sudoers file, as characters: the only effect of reading one after opening it.
fn read_sudoers<R: io::Read>(mut reader: R) -> io::Result<Vec<char>> {
    // it's a bit frustrating that BufReader.chars() does not exist
    let mut buffer = String::new();
    reader.read_to_string(&mut buffer)?;

    Ok(char_stream::chars_of(&buffer))
}

fn open_sudoers(path: &Path) -> io::Result<Vec<char>> {
    #[cfg(test)]
    if let Some(source) = test::analysis::open_fixture(path) {
        return read_sudoers(source?);
    }
    let source = audit::secure_open_sudoers(path)?;
    read_sudoers(source)
}

/// Parse the text of a sudoers file.
fn parse_sudoers(text: &[char]) -> Vec<basic_parser::Parsed<Sudo>> {
    basic_parser::parse_lines(&mut char_stream::CharStream::from_chars(text))
}

#[cfg(feature = "unstable-remote-sudoers")]
fn open_remote_sudoers(path: &Path, peer: &PeerSpec) -> io::Result<Vec<char>> {
    use system::{Group, User};

    fn check_validity<T, E>(
        obj: Result<Option<T>, E>,
        class: &str,
        ident: &Identifier,
    ) -> io::Result<T> {
        if let Ok(Some(inner)) = obj {
            Ok(inner)
        } else {
            Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("{class} '{ident}' not found"),
            ))
        }
    }

    let user = match &peer.user {
        Identifier::Name(name) => User::from_name(name.as_cstr()),
        Identifier::ID(id) => User::from_uid(UserId::new(*id)),
    };

    let group = peer.group.as_ref().map(|group| match group {
        Identifier::Name(name) => Group::from_name(name.as_cstr()),
        Identifier::ID(id) => Group::from_gid(GroupId::new(*id)),
    });

    let user = check_validity(user, "user", &peer.user)?;

    let group = group
        .map(|g| check_validity(g, "group", peer.group.as_ref().unwrap()))
        .transpose()?;

    let source = audit::secure_open_remote_sudoers(path, user.uid, group.map(|x| x.gid))?;
    read_sudoers(source)
}

// note: trying to DRY using GAT's is tempting but doesn't make the code any shorter

#[derive(Default)]
struct AliasTable {
    user: VecOrd<Def<UserSpecifier>>,
    host: VecOrd<Def<Hostname>>,
    cmnd: VecOrd<Def<Command>>,
    runas: VecOrd<Def<UserSpecifier>>,
}

#[derive(Default)]
struct CustomiserTable {
    non_cmnd: Vec<Customiser<ConfigScope>>,
    cmnd: Vec<Customiser<SpecList<Command>>>,
}

/// A vector with a list defining the order in which it needs to be processed
struct VecOrd<T>(Vec<usize>, Vec<T>);

impl<T> Default for VecOrd<T> {
    fn default() -> Self {
        VecOrd(Vec::default(), Vec::default())
    }
}

impl<T> VecOrd<T> {
    fn iter(&self) -> impl DoubleEndedIterator<Item = &T> + Clone {
        self.0.iter().map(|&i| &self.1[i])
    }
}

/// Like [check_permission], but taking into account the exception that if the user is root or does
/// not switch users, NOPASSWD is implied
fn permission_flags<User: UnixUser + PartialEq<User>, Group: UnixGroup>(
    rules: &[PermissionSpec],
    aliases: &AliasTable,
    am_user: &User,
    on_host: &system::Hostname,
    request: Request<User, Group>,
) -> Option<Tag> {
    let skip_passwd =
        am_user.is_root() || (request.user == am_user && in_group(am_user, request.group));

    let mut flags = check_permission(rules, aliases, am_user, on_host, request);
    if let Some(Tag { authenticate, .. }) = &mut flags {
        if skip_passwd {
            *authenticate = Authenticate::Nopasswd;
        }
    }

    flags
}

/// The flags of [Sudoers::check_list_permission] (`sudo -l`). Listing the permissions of another
/// user is the request to run the pseudo-command `list` as that user (which root may always do);
/// listing one's own permissions takes the tag of a matching command entry, preferring one that
/// does not need a password ([select_tag]). The password exceptions are those of [permission_flags].
fn list_flags<User: UnixUser + PartialEq<User>, Group: UnixGroup>(
    rules: &[PermissionSpec],
    aliases: &AliasTable,
    invoking_user: &User,
    hostname: &system::Hostname,
    request: ListRequest<User, Group>,
) -> Option<Tag> {
    let skip_passwd;
    let mut flags = if request.inspected_user != invoking_user {
        skip_passwd = invoking_user.is_root();

        let flags = permission_flags(
            rules,
            aliases,
            invoking_user,
            hostname,
            Request {
                user: request.inspected_user,
                group: &request.inspected_user.group(),
                command: Path::new("list"),
                arguments: &[],
            },
        );
        if flags.is_none() && invoking_user.is_root() {
            Some(Tag::default())
        } else {
            flags
        }
    } else {
        skip_passwd = invoking_user.is_root()
            || (request.target_user == invoking_user
                && in_group(invoking_user, request.target_group));

        select_tag(rules, aliases, invoking_user, hostname, false)
    };

    if let Some(Tag { authenticate, .. }) = &mut flags {
        if skip_passwd {
            *authenticate = Authenticate::Nopasswd;
        }
    }

    flags
}

/// The flags of [Sudoers::check_validate_permission] (`sudo -v`): the tag of a matching command
/// entry, preferring one that needs a password ([select_tag]); if the user is root, NOPASSWD is
/// implied.
fn validate_flags<User: UnixUser>(
    rules: &[PermissionSpec],
    aliases: &AliasTable,
    invoking_user: &User,
    hostname: &system::Hostname,
) -> Option<Tag> {
    let skip_passwd = invoking_user.is_root();

    let mut flags = select_tag(rules, aliases, invoking_user, hostname, true);
    if let Some(Tag { authenticate, .. }) = &mut flags {
        if skip_passwd {
            *authenticate = Authenticate::Nopasswd;
        }
    }

    flags
}

/// Of the tags of all command entries of the `User_Spec`s that match `invoking_user` and
/// `hostname` (in the order of [Sudoers::matching_user_specs]), the last one whose `needs_passwd`
/// equals `prefer_passwd`, or else the last one; i.e. `Iterator::max_by_key` with the key
/// `needs_passwd() == prefer_passwd`, which returns the last maximal element.
fn select_tag<User: UnixUser>(
    rules: &[PermissionSpec],
    aliases: &AliasTable,
    invoking_user: &User,
    hostname: &system::Hostname,
    prefer_passwd: bool,
) -> Option<Tag> {
    let user_matcher = &match_user(invoking_user);
    let host_matcher = &match_token(hostname);
    let user_aliases = get_aliases(&aliases.user, user_matcher);
    let host_aliases = get_aliases(&aliases.host, host_matcher);

    let mut result = None;
    let mut i = 0;
    while i < rules.len() {
        if find_item(&rules[i].users, user_matcher, &user_aliases) {
            let permissions = &rules[i].permissions;
            let mut j = 0;
            while j < permissions.len() {
                if find_item(&permissions[j].0, host_matcher, &host_aliases) {
                    result = select_commands(result, &permissions[j].1, prefer_passwd);
                }
                j += 1;
            }
        }
        i += 1;
    }

    result
}

/// Continue the search of [select_tag] (where `result` is the outcome so far) through a list of
/// RunAs + Command specifications
fn select_commands(
    mut result: Option<Tag>,
    runas_cmds: &[(Option<RunAs>, CommandSpec)],
    prefer_passwd: bool,
) -> Option<Tag> {
    let tags = distribute_tags(runas_cmds);

    let mut i = 0;
    while i < tags.len() {
        let (_, tag) = &tags[i];
        let keep = match &result {
            Some(best) => {
                best.needs_passwd() == prefer_passwd && tag.needs_passwd() != prefer_passwd
            }
            None => false,
        };
        if !keep {
            result = Some(tag.clone());
        }
        i += 1;
    }

    result
}

/// Check if the user `am_user` is allowed to run `cmdline` on machine `on_host` as the requested
/// user/group. Not that in the sudoers file, later permissions override earlier restrictions.
/// The `cmdline` argument should already be ready to essentially feed to an exec() call; or be
/// a special command like 'sudoedit'.
fn check_permission<User: UnixUser + PartialEq<User>, Group: UnixGroup>(
    rules: &[PermissionSpec],
    aliases: &AliasTable,
    am_user: &User,
    on_host: &system::Hostname,
    request: Request<User, Group>,
) -> Option<Tag> {
    let cmdline = (request.command, request.arguments);

    let cmnd_matcher = &match_command(cmdline);
    let cmnd_aliases = get_aliases(&aliases.cmnd, cmnd_matcher);
    let runas_user_aliases = get_aliases(&aliases.runas, &match_user(request.user));
    let runas_group_aliases = get_aliases(&aliases.runas, &match_group_alias(request.group));

    let verdict = |runas: Option<&RunAs>, cmd: &Spec<Command>| {
        let runas_allowed = match runas {
            Some(RunAs { users, groups }) => {
                let stays_in_group = in_group(request.user, request.group);
                if (request.user != am_user || (stays_in_group && !users.is_empty()))
                    && !find_item(users, &match_user(request.user), &runas_user_aliases)
                {
                    false
                } else {
                    stays_in_group
                        || find_item(groups, &match_group(request.group), &runas_group_aliases)
                }
            }
            None => request.user.is_root() && in_group(request.user, request.group),
        };

        if runas_allowed {
            item_verdict(cmd, cmnd_matcher, &cmnd_aliases)
        } else {
            None
        }
    };

    let user_matcher = &match_user(am_user);
    let host_matcher = &match_token(on_host);
    let user_aliases = get_aliases(&aliases.user, user_matcher);
    let host_aliases = get_aliases(&aliases.host, host_matcher);

    let mut result = None;
    let mut i = 0;
    while i < rules.len() {
        if find_item(&rules[i].users, user_matcher, &user_aliases) {
            let permissions = &rules[i].permissions;
            let mut j = 0;
            while j < permissions.len() {
                if find_item(&permissions[j].0, host_matcher, &host_aliases) {
                    result = check_commands(result, &permissions[j].1, &verdict);
                }
                j += 1;
            }
        }
        i += 1;
    }

    result
}

/// Continue the search of [check_permission] (where `result` is the outcome so far) through a list
/// of RunAs + Command specifications; `verdict` decides whether a command is allowed, forbidden or
/// not applicable.
fn check_commands<Verdict>(
    mut result: Option<Tag>,
    runas_cmds: &[(Option<RunAs>, CommandSpec)],
    verdict: &Verdict,
) -> Option<Tag>
where
    Verdict: Fn(Option<&RunAs>, &Spec<Command>) -> Option<bool>,
{
    let tags = distribute_tags(runas_cmds);

    let mut i = 0;
    while i < tags.len() {
        let (last_runas, tag) = &tags[i];
        match command_verdict(runas_cmds, i, *last_runas, verdict) {
            Some(true) => result = Some(tag.clone()),
            Some(false) => result = None,
            None => {}
        }
        i += 1;
    }

    result
}

/// The verdict on the `i`-th command in `runas_cmds`, where `last_runas` is the position of the
/// RunAs specification that applies to it (see [distribute_tags])
fn command_verdict<Verdict>(
    runas_cmds: &[(Option<RunAs>, CommandSpec)],
    i: usize,
    last_runas: Option<usize>,
    verdict: &Verdict,
) -> Option<bool>
where
    Verdict: Fn(Option<&RunAs>, &Spec<Command>) -> Option<bool>,
{
    let runas = match last_runas {
        Some(j) => runas_cmds[j].0.as_ref(),
        None => None,
    };
    let (_, CommandSpec(_, cmd)) = &runas_cmds[i];

    verdict(runas, cmd)
}

/// returns the positions (in `rules` and in their `permissions`) of the host/command lists of the
/// `User_Spec`s that match `invoking_user` and `hostname`
fn matching_permissions(
    rules: &[PermissionSpec],
    aliases: &AliasTable,
    invoking_user: &impl UnixUser,
    hostname: &system::Hostname,
) -> Vec<(usize, usize)> {
    let user_matcher = &match_user(invoking_user);
    let host_matcher = &match_token(hostname);
    let user_aliases = get_aliases(&aliases.user, user_matcher);
    let host_aliases = get_aliases(&aliases.host, host_matcher);

    let mut result = Vec::new();
    let mut i = 0;
    while i < rules.len() {
        if find_item(&rules[i].users, user_matcher, &user_aliases) {
            let permissions = &rules[i].permissions;
            let mut j = 0;
            while j < permissions.len() {
                if find_item(&permissions[j].0, host_matcher, &host_aliases) {
                    result.push((i, j));
                }
                j += 1;
            }
        }
        i += 1;
    }

    result
}

/// Process a raw parsed AST bit of RunAs + Command specifications:
/// - RunAs specifications distribute over the commands that follow (until overridden)
/// - Tags accumulate over the entire line
///
/// For every command, this returns the position of the RunAs specification that applies to it (if
/// any) and its tags.
fn distribute_tags(runas_cmds: &[(Option<RunAs>, CommandSpec)]) -> Vec<(Option<usize>, Tag)> {
    let mut last_runas = None;
    let mut tag = Tag::default();

    let mut result = Vec::new();
    let mut i = 0;
    while i < runas_cmds.len() {
        let (runas, CommandSpec(mods, cmd)) = &runas_cmds[i];
        if runas.is_some() {
            last_runas = Some(i);
        }
        apply_modifiers(mods, &mut tag);
        result.push((last_runas, command_tag(&tag, cmd)));
        i += 1;
    }

    result
}

fn apply_modifiers(mods: &[Modifier], tag: &mut Tag) {
    let mut i = 0;
    while i < mods.len() {
        mods[i].apply(tag);
        i += 1;
    }
}

/// The tags of a single command, given the tags that have accumulated
fn command_tag(tag: &Tag, cmd: &Spec<Command>) -> Tag {
    match cmd {
        Qualified::Allow(Meta::All) if tag.env != EnvironmentControl::Nosetenv => Tag {
            // "ALL" has an implicit "SETENV" that doesn't distribute
            env: EnvironmentControl::Setenv,
            ..tag.clone()
        },
        _ => tag.clone(),
    }
}

/// A type to represent positive or negative association with an alias; i.e. if a key maps to true,
/// the alias affirms membership, if a key maps to false, the alias denies membership; if a key
/// isn't present membership is affirmed nor denied.
///
/// This is a plain list (where later entries take precedence) instead of a map, so that it can be
/// formally verified.
#[derive(Default)]
struct FoundAliases(Vec<(String, bool)>);

impl FoundAliases {
    fn insert(&mut self, alias: String, found: bool) {
        self.0.push((alias, found));
    }

    fn get(&self, alias: &str) -> Option<bool> {
        let mut result = None;
        let mut i = 0;
        while i < self.0.len() {
            let (name, found) = &self.0[i];
            if name.as_str() == alias {
                result = Some(*found);
            }
            i += 1;
        }

        result
    }
}

/// Find an item matching a certain predicate in an collection (optionally attributed) list of
/// identifiers; identifiers can be directly identifying, wildcards, and can either be positive or
/// negative (i.e. preceeded by an even number of exclamation marks in the sudoers file)
fn find_item<Predicate, T>(items: &[Spec<T>], matches: &Predicate, aliases: &FoundAliases) -> bool
where
    Predicate: Fn(&T) -> bool,
{
    find_item_after(false, items, matches, aliases)
}

/// Like [find_item], but `result` is the outcome for some items that precede `items`
fn find_item_after<Predicate, T>(
    mut result: bool,
    items: &[Spec<T>],
    matches: &Predicate,
    aliases: &FoundAliases,
) -> bool
where
    Predicate: Fn(&T) -> bool,
{
    let mut i = 0;
    while i < items.len() {
        if let Some(judgement) = item_verdict(&items[i], matches, aliases) {
            result = judgement;
        }
        i += 1;
    }

    result
}

/// Whether a single item of a list processed by [find_item] includes (`Some(true)`) or excludes
/// (`Some(false)`) the object, or does not apply to it (`None`)
fn item_verdict<Predicate, T>(
    item: &Spec<T>,
    matches: &Predicate,
    aliases: &FoundAliases,
) -> Option<bool>
where
    Predicate: Fn(&T) -> bool,
{
    let (judgement, who) = match item {
        Qualified::Forbid(x) => (false, x),
        Qualified::Allow(x) => (true, x),
    };
    match who {
        Meta::All => Some(judgement),
        Meta::Only(ident) if matches(ident) => Some(judgement),
        Meta::Alias(id) => match aliases.get(id) {
            Some(true) => Some(judgement),
            // in this case, an explicit negation in the alias applies
            Some(false) => Some(!judgement),
            None => None,
        },
        _ => None,
    }
}

/// Now follow a collection of functions used as closures for `find_item`
fn match_user(user: &impl UnixUser) -> impl Fn(&UserSpecifier) -> bool + '_ {
    move |spec| match spec {
        UserSpecifier::User(id) => match_identifier(user, id),
        UserSpecifier::Group(Identifier::Name(name)) => user.in_group_by_name(name.as_cstr()),
        UserSpecifier::Group(Identifier::ID(num)) => user.in_group_by_gid(GroupId::new(*num)),
        // nonunix-groups, netgroups, etc. are not implemented
        UserSpecifier::NonunixGroup(group) => {
            warn_ignored(Ignored::NonunixGroup(group));
            false
        }
    }
}

fn in_group(user: &impl UnixUser, group: &impl UnixGroup) -> bool {
    user.in_group_by_gid(group.as_gid())
}

fn match_group(group: &impl UnixGroup) -> impl Fn(&Identifier) -> bool + '_ {
    move |id| match id {
        Identifier::ID(num) => group.as_gid() == GroupId::new(*num),
        Identifier::Name(name) => group.try_as_name().is_some_and(|s| name == s),
    }
}

fn match_group_alias(group: &impl UnixGroup) -> impl Fn(&UserSpecifier) -> bool + '_ {
    move |spec| match spec {
        UserSpecifier::User(ident) => match_group(group)(ident),
        /* the parser does not allow this, but can happen due to Runas_Alias,
         * see https://github.com/trifectatechfoundation/sudo-rs/issues/13 */
        _ => {
            warn_ignored(Ignored::GroupInRunasAlias);
            false
        }
    }
}

/// User specifiers that are not supported and are skipped (with a warning) while matching
enum Ignored<'a> {
    NonunixGroup(&'a Identifier),
    GroupInRunasAlias,
}

/// The only side effect of the permission check; it is kept opaque for the formal verification
/// (see `package.metadata.charon` in `Cargo.toml`)
fn warn_ignored(item: Ignored) {
    #[cfg(test)]
    test::record_ignored(&item);

    match item {
        Ignored::NonunixGroup(group) => auth_warn!("warning: non-unix group {group} was ignored"),
        Ignored::GroupInRunasAlias => {
            auth_warn!("warning: ignoring %group syntax in runas_alias for checking sudo -g")
        }
    }
}

fn match_token<T: std::ops::Deref<Target = String>>(text: &str) -> impl Fn(&T) -> bool + '_ {
    move |token| token.as_str() == text
}

fn match_command<'a>((cmd, args): (&'a Path, &'a [OsString])) -> impl Fn(&Command) -> bool + 'a {
    let opts = glob::MatchOptions {
        require_literal_separator: true,
        ..glob::MatchOptions::new()
    };
    move |(cmdpat, argpat)| {
        cmdpat.matches_path_with(cmd, opts)
            && match argpat {
                Args::Prefix(vec) => args.starts_with(vec),
                Args::Exact(vec) => args == vec.as_ref(),
            }
    }
}

/// Find all the aliases that a object is a member of; this requires [sanitize_alias_table] to have run first;
/// I.e. this function should not be "pub".
fn get_aliases<Predicate, T>(table: &VecOrd<Def<T>>, pred: &Predicate) -> FoundAliases
where
    Predicate: Fn(&T) -> bool,
{
    let VecOrd(order, defs) = table;

    let mut set = FoundAliases::default();
    let mut i = 0;
    while i < order.len() {
        let Def(id, list) = &defs[order[i]];
        if find_item(list, pred, &set) {
            set.insert(id.clone(), true);
        } else if !find_item_after(true, list, pred, &set) {
            // the item wasn't found even if we prepend ALL to the list of definitions; that means
            // it is explicitly excluded by the alias definition.
            set.insert(id.clone(), false);
        }
        i += 1;
    }

    set
}

/// Code to map an ast::Identifier to the UnixUser trait
fn match_identifier(user: &impl UnixUser, ident: &ast::Identifier) -> bool {
    match ident {
        Identifier::Name(name) => user.has_name(name),
        Identifier::ID(num) => user.has_uid(UserId::new(*num)),
    }
}

/// Read a sudoers file: parse its text and [analyze] the items. `path` is the file the text was
/// read from. Pure apart from the include oracle ([include_file], [include_dir_files]), which
/// only items that include other files reach.
fn analyze_text(path: &Path, text: &[char]) -> (Sudoers, Vec<Error>) {
    analyze(path, parse_sudoers(text))
}

/// Process a sudoers-parsing file into a workable AST: the rules, the alias definitions and the
/// `Defaults` of the file at `path` and of the files it includes, in file order (an include
/// directive stands for the items of the included file), then the processing order of the alias
/// tables ([sanitize_alias_tables]). The diagnostics are those of the items in the same order,
/// then those of the alias tables.
fn analyze(path: &Path, items: Vec<basic_parser::Parsed<Sudo>>) -> (Sudoers, Vec<Error>) {
    let mut result: Sudoers = Default::default();
    let mut diagnostics = Vec::new();

    process(
        &mut result,
        path,
        items,
        &mut diagnostics,
        &mut IncludeState::Allowed(0),
    );

    sanitize_alias_tables(&mut result.aliases, &mut diagnostics);

    (result, diagnostics)
}

/// The IncludeState allows to tell whether including new files is allowed.
/// There are two situations:
/// - inclusion is forbidden (as when the @socket directive is used)
/// - inclusion is allowed but we need to ensure we didn't go beyond the limit: `Allowed(n)`
///   counts the include files opened (or attempted) so far, in the whole tree of includes
#[derive(Clone, Copy)]
#[repr(u32)]
enum IncludeState {
    #[cfg(feature = "unstable-remote-sudoers")]
    Forbidden = HARDENED_ENUM_VALUE_0,
    Allowed(u8) = HARDENED_ENUM_VALUE_1,
}

impl IncludeState {
    /// Count an include file that is opened (whether or not that succeeds).
    fn inc(&mut self) {
        match self {
            #[cfg(feature = "unstable-remote-sudoers")]
            IncludeState::Forbidden => {}
            IncludeState::Allowed(x) => *x += 1,
        }
    }

    fn limit_reached(&self) -> bool {
        match self {
            #[cfg(feature = "unstable-remote-sudoers")]
            IncludeState::Forbidden => true,
            IncludeState::Allowed(x) => *x >= INCLUDE_LIMIT,
        }
    }
}

/// A file that an include directive names, for [include_file].
#[repr(u32)]
enum IncludeFile {
    /// `@include path`: the path as written; a relative path is relative to the directory of
    /// the including file
    Named(String) = HARDENED_ENUM_VALUE_0,
    /// an entry of the directory of an `@includedir` ([include_dir_files])
    Listed(PathBuf) = HARDENED_ENUM_VALUE_1,
    /// `@socket path` (an absolute path) with its peer credentials
    #[cfg(feature = "unstable-remote-sudoers")]
    Socket(String, PeerSpec) = HARDENED_ENUM_VALUE_2,
}

/// The items of the file at `cur_path`, in order.
fn process(
    cfg: &mut Sudoers,
    cur_path: &Path,
    items: Vec<basic_parser::Parsed<Sudo>>,
    diagnostics: &mut Vec<Error>,
    include_state: &mut IncludeState,
) {
    let mut items = items.into_iter();
    let mut more = true;
    while more {
        match items.next() {
            Some(item) => process_item(cfg, cur_path, item, diagnostics, include_state),
            None => more = false,
        }
    }
}

/// One item of the file at `cur_path`.
fn process_item(
    cfg: &mut Sudoers,
    cur_path: &Path,
    item: basic_parser::Parsed<Sudo>,
    diagnostics: &mut Vec<Error>,
    include_state: &mut IncludeState,
) {
    use Directive::*;

    match item {
        Ok(Sudo::LineComment) => {}

        Ok(Sudo::Spec(permission)) => {
            ignored_tags(cur_path, &permission, diagnostics);
            cfg.rules.push(permission);
        }

        Ok(Sudo::Decl(HostAlias(def))) => append_defs(&mut cfg.aliases.host.1, def),
        Ok(Sudo::Decl(UserAlias(def))) => append_defs(&mut cfg.aliases.user.1, def),
        Ok(Sudo::Decl(RunasAlias(def))) => append_defs(&mut cfg.aliases.runas.1, def),
        Ok(Sudo::Decl(CmndAlias(def))) => append_defs(&mut cfg.aliases.cmnd.1, def),

        Ok(Sudo::Decl(Defaults(params, ConfigScope::Command(specs)))) => {
            cfg.customisers.cmnd.push((command_scope(specs), params))
        }
        Ok(Sudo::Decl(Defaults(params, scope))) => cfg.customisers.non_cmnd.push((scope, params)),

        Ok(Sudo::Include(path, span)) => include(
            cfg,
            cur_path,
            IncludeFile::Named(path),
            span,
            diagnostics,
            include_state,
        ),

        #[cfg(feature = "unstable-remote-sudoers")]
        Ok(Sudo::Remote(path, peer_spec, span)) => include_remote(
            cfg,
            cur_path,
            path,
            peer_spec,
            span,
            diagnostics,
            include_state,
        ),

        Ok(Sudo::IncludeDir(path, span)) => {
            include_dir(cfg, cur_path, path, span, diagnostics, include_state)
        }

        Err(basic_parser::Status::Fatal(pos, kind)) => {
            report(diagnostics, cur_path, pos, fatal_message(&kind))
        }
        Err(basic_parser::Status::Reject) => panic!("internal parser error"),
    }
}

/// A diagnostic for the item at `span` of the file at `cur_path`.
fn report(diagnostics: &mut Vec<Error>, cur_path: &Path, span: Span, message: String) {
    diagnostics.push(Error {
        source: Some(cur_path.to_path_buf()),
        location: Some(span),
        message,
    });
}

/// The message of a fatal parse error (the `Display` of its kind). Opaque for Charon: the
/// formatting is not extracted.
fn fatal_message(kind: &basic_parser::ErrorKind) -> String {
    kind.to_string()
}

/// One diagnostic for every tag of the rule that sudo-rs ignores (`Modifier::Ignored`), in the
/// order of the rule.
fn ignored_tags(cur_path: &Path, permission: &PermissionSpec, diagnostics: &mut Vec<Error>) {
    let permissions = &permission.permissions;
    let mut i = 0;
    while i < permissions.len() {
        let runas_cmds = &permissions[i].1;
        let mut j = 0;
        while j < runas_cmds.len() {
            let (_, CommandSpec(modifiers, _)) = &runas_cmds[j];
            ignored_modifiers(cur_path, modifiers, diagnostics);
            j += 1;
        }
        i += 1;
    }
}

/// The diagnostics of [ignored_tags] for the modifiers of one command.
fn ignored_modifiers(cur_path: &Path, modifiers: &[Modifier], diagnostics: &mut Vec<Error>) {
    let mut i = 0;
    while i < modifiers.len() {
        if let Modifier::Ignored(span) = &modifiers[i] {
            let message = String::from("this tag is ignored by sudo-rs");
            report(diagnostics, cur_path, *span, message);
        }
        i += 1;
    }
}

/// Append the definitions of one alias line to a table, in order.
fn append_defs<T>(table: &mut Vec<Def<T>>, mut defs: Defs<T>) {
    table.append(&mut defs);
}

/// The scope of a `Defaults!` line as commands: every command with any arguments.
fn command_scope(specs: SpecList<SimpleCommand>) -> SpecList<Command> {
    let mut result = Vec::with_capacity(specs.len());
    let mut specs = specs.into_iter();
    let mut more = true;
    while more {
        match specs.next() {
            Some(spec) => result.push(any_arguments(spec)),
            None => more = false,
        }
    }
    result
}

/// One item of [command_scope].
fn any_arguments(spec: Spec<SimpleCommand>) -> Spec<Command> {
    match spec {
        Qualified::Allow(meta) => Qualified::Allow(any_arguments_meta(meta)),
        Qualified::Forbid(meta) => Qualified::Forbid(any_arguments_meta(meta)),
    }
}

fn any_arguments_meta(meta: Meta<SimpleCommand>) -> Meta<Command> {
    match meta {
        Meta::All => Meta::All,
        Meta::Alias(alias) => Meta::Alias(alias),
        Meta::Only(simple_command) => Meta::Only((simple_command, Args::Prefix(Box::default()))),
    }
}

/// An include file (`@include`, or an entry of `@includedir`), at `span` of the file at
/// `cur_path`. If the include limit is reached the result is a diagnostic; otherwise the file
/// is opened and counted (whether or not opening succeeds), and its items are processed in
/// place of the directive, or the failure is a diagnostic.
fn include(
    cfg: &mut Sudoers,
    cur_path: &Path,
    file: IncludeFile,
    span: Span,
    diagnostics: &mut Vec<Error>,
    include_state: &mut IncludeState,
) {
    let refused = include_state.limit_reached();
    let refusal = if refused { Some(*include_state) } else { None };
    let opened = include_file(cur_path, file, refusal);
    if !refused {
        include_state.inc();
    }
    match opened {
        Ok((path, items)) => process(cfg, path.as_path(), items, diagnostics, include_state),
        Err(message) => report(diagnostics, cur_path, span, message),
    }
}

/// An `@includedir` directive at `span` of the file at `cur_path`: every file of the listing
/// [include_dir_files] in order, or the diagnostic.
fn include_dir(
    cfg: &mut Sudoers,
    cur_path: &Path,
    path: String,
    span: Span,
    diagnostics: &mut Vec<Error>,
    include_state: &mut IncludeState,
) {
    match include_dir_files(cur_path, path) {
        Ok(files) => {
            let mut files = files.into_iter();
            let mut more = true;
            while more {
                match files.next() {
                    Some(file) => include(
                        cfg,
                        cur_path,
                        IncludeFile::Listed(file),
                        span,
                        diagnostics,
                        include_state,
                    ),
                    None => more = false,
                }
            }
        }
        Err(message) => report(diagnostics, cur_path, span, message),
    }
}

/// An `@socket` directive at `span` of the file at `cur_path`: as [include], but the socket is
/// not counted, and the items it provides may not include anything.
#[cfg(feature = "unstable-remote-sudoers")]
fn include_remote(
    cfg: &mut Sudoers,
    cur_path: &Path,
    path: String,
    peer_spec: PeerSpec,
    span: Span,
    diagnostics: &mut Vec<Error>,
    include_state: &mut IncludeState,
) {
    if Path::new(&path).is_relative() {
        let message = format!("cannot open socket {path}: path must be absolute");
        report(diagnostics, cur_path, span, message);
    } else {
        let refusal = if include_state.limit_reached() {
            Some(*include_state)
        } else {
            None
        };
        match include_file(cur_path, IncludeFile::Socket(path, peer_spec), refusal) {
            Ok((path, items)) => process(
                cfg,
                path.as_path(),
                items,
                diagnostics,
                &mut IncludeState::Forbidden,
            ),
            Err(message) => report(diagnostics, cur_path, span, message),
        }
    }
}

/// The include oracle, part 1 (`proofs/parser/ANALYSIS.md`); opaque for Charon. One include
/// file named in the file at `cur_path`: its path (a relative `@include` path is resolved
/// against the directory of `cur_path`) and, when `refusal` is the state in which the include
/// limit was reached, the message of that diagnostic without opening the file; otherwise the
/// file opened and parsed (its path, which is the source of its diagnostics and the base of its
/// relative includes, and its items), or the message of the failure.
fn include_file(
    cur_path: &Path,
    file: IncludeFile,
    refusal: Option<IncludeState>,
) -> Result<(PathBuf, Vec<basic_parser::Parsed<Sudo>>), String> {
    #[cfg(feature = "unstable-remote-sudoers")]
    let directive = match &file {
        IncludeFile::Named(_) => "@include",
        IncludeFile::Listed(_) => "@includedir",
        IncludeFile::Socket(..) => "@socket",
    };
    #[cfg(feature = "unstable-remote-sudoers")]
    let mut peer = None;
    let path = match file {
        IncludeFile::Named(path) => resolve_relative(cur_path, path),
        IncludeFile::Listed(path) => path,
        #[cfg(feature = "unstable-remote-sudoers")]
        IncludeFile::Socket(path, peer_spec) => {
            peer = Some(peer_spec);
            PathBuf::from(path)
        }
    };

    match refusal {
        Some(IncludeState::Allowed(_)) => Err(format!(
            "include file limit reached opening '{}'",
            path.display()
        )),
        #[cfg(feature = "unstable-remote-sudoers")]
        Some(IncludeState::Forbidden) => Err(format!("{directive} forbidden at this stage")),
        None => {
            #[cfg(feature = "unstable-remote-sudoers")]
            let (res, kind) = match &peer {
                Some(peer) => (open_remote_sudoers(&path, peer), "socket"),
                None => (open_sudoers(&path), "file"),
            };
            #[cfg(not(feature = "unstable-remote-sudoers"))]
            let (res, kind) = (open_sudoers(&path), "file");

            match res {
                Ok(text) => Ok((path, parse_sudoers(&text))),
                Err(e) => Err(if e.kind() == io::ErrorKind::NotFound {
                    // improve the error message in this case
                    format!("cannot open sudoers {} '{}'", kind, path.display())
                } else {
                    e.to_string()
                }),
            }
        }
    }
}

/// The include oracle, part 2; opaque for Charon. The files of the directory of an
/// `@includedir path` in the file at `cur_path` (resolved as in [include_file]) that sudo
/// reads, in sorted order: names without `.` that do not end in `~`. Or the message of the
/// diagnostic: for a path with `%h`, or a directory that cannot be read.
fn include_dir_files(cur_path: &Path, path: String) -> Result<Vec<PathBuf>, String> {
    if path.contains("%h") {
        return Err(format!(
            "cannot open sudoers file {path}: \
             percent escape %h in includedir is unsupported"
        ));
    }

    let path = resolve_relative(cur_path, path);
    let Ok(files) = std::fs::read_dir(&path) else {
        return Err(format!("cannot open sudoers file {}", path.display()));
    };
    let mut safe_files = files
        .filter_map(|direntry| {
            let path = direntry.ok()?.path();
            let text = path.file_name()?.to_str()?;
            if text.ends_with('~') || text.contains('.') {
                None
            } else {
                Some(path)
            }
        })
        .collect::<Vec<_>>();
    safe_files.sort();
    Ok(safe_files)
}

fn resolve_relative(base: &Path, path: String) -> PathBuf {
    if Path::new(&path).is_relative() {
        // there should always be a parent since we start with /etc/sudoers, and make every other path
        // absolute based on previous inputs; not having a parent is therefore a serious bug
        base.parent()
            .expect("invalid hardcoded path in sudo-rs")
            .join(path)
    } else {
        PathBuf::from(path)
    }
}

/// Apply the modifiers of one `Defaults` line, in order.
fn apply_settings(modifiers: Vec<defaults::SettingsModifier>, settings: &mut Settings) {
    let mut modifiers = modifiers.into_iter();
    let mut more = true;
    while more {
        match modifiers.next() {
            Some(modifier) => modifier.apply(settings),
            None => more = false,
        }
    }
}

/// Compute the processing order of every alias table, in the order user, host, command, runas
/// (see [sanitize_alias_table]); diagnostics are appended in that order.
fn sanitize_alias_tables(alias: &mut AliasTable, diagnostics: &mut Vec<Error>) {
    alias.user.0 = sanitize_alias_table(&alias.user.1, diagnostics);
    alias.host.0 = sanitize_alias_table(&alias.host.1, diagnostics);
    alias.cmnd.0 = sanitize_alias_table(&alias.cmnd.1, diagnostics);
    alias.runas.0 = sanitize_alias_table(&alias.runas.1, diagnostics);
}

enum AliasDiagnostic {
    Undefined,
    Recursive,
    Duplicate,
}

fn alias_diagnostic(diagnostics: &mut Vec<Error>, kind: AliasDiagnostic, name: &str) {
    let message = match kind {
        AliasDiagnostic::Undefined => format!("undefined alias: '{name}'"),
        AliasDiagnostic::Recursive => format!("recursive alias: '{name}'"),
        AliasDiagnostic::Duplicate => format!("multiple occurrences of '{name}'"),
    };
    diagnostics.push(Error {
        source: None,
        location: None,
        message,
    });
}

/// Alias definition inin a Sudoers file can come in any order; and aliases can refer to other aliases, etc.
/// It is much easier if they are presented in a "definitional order" (i.e. aliases that use other aliases occur later)
/// At the same time, this is a good place to detect problems in the aliases, such as unknown aliases and cycles.
fn sanitize_alias_table<T>(table: &Vec<Def<T>>, diagnostics: &mut Vec<Error>) -> Vec<usize> {
    fn remqualify<U>(item: &Qualified<U>) -> &U {
        match item {
            Qualified::Allow(x) => x,
            Qualified::Forbid(x) => x,
        }
    }

    fn dependency_position<T>(table: &[Def<T>], name: &String) -> Option<usize> {
        let mut i = 0;
        while i < table.len() {
            if &table[i].0 == name {
                return Some(i);
            }
            i += 1;
        }
        None
    }

    // perform a topological sort (hattip david@tweedegolf.com) to produce a derangement
    struct Visitor<'a, T> {
        seen: HashSet<usize>,
        table: &'a Vec<Def<T>>,
        order: Vec<usize>,
        diagnostics: &'a mut Vec<Error>,
    }

    impl<T> Visitor<'_, T> {
        fn visit(&mut self, pos: usize) {
            if self.seen.insert(pos) {
                let Def(_, members) = &self.table[pos];
                for elem in members.iter() {
                    let Meta::Alias(name) = remqualify(elem) else {
                        continue;
                    };
                    let Some(dependency) = dependency_position(self.table, name) else {
                        alias_diagnostic(self.diagnostics, AliasDiagnostic::Undefined, name);
                        continue;
                    };
                    self.visit(dependency);
                }
                self.order.push(pos);
            } else if !self.order.contains(&pos) {
                let Def(id, _) = &self.table[pos];
                alias_diagnostic(self.diagnostics, AliasDiagnostic::Recursive, id);
            }
        }
    }

    let mut visitor = Visitor {
        seen: HashSet::new(),
        table,
        order: Vec::with_capacity(table.len()),
        diagnostics,
    };

    let mut dupe = HashSet::new();
    for (i, Def(name, _)) in table.iter().enumerate() {
        if !dupe.insert(name) {
            alias_diagnostic(visitor.diagnostics, AliasDiagnostic::Duplicate, name);
        } else {
            visitor.visit(i);
        }
    }

    visitor.order
}

#[cfg(test)]
mod test;
