use super::ast_names::UserFriendly;
use super::basic_parser::*;
use super::char_stream::chars_of;
use super::tokens::sudo_string_text;
use super::tokens::*;
use crate::common::SudoString;
use crate::common::{
    HARDENED_ENUM_VALUE_0, HARDENED_ENUM_VALUE_1, HARDENED_ENUM_VALUE_2, HARDENED_ENUM_VALUE_3,
    HARDENED_ENUM_VALUE_4, HARDENED_ENUM_VALUE_5,
};
use crate::defaults;

/// The Sudoers file allows negating items with the exclamation mark.
#[cfg_attr(test, derive(Debug, Eq))]
#[derive(Clone, PartialEq)]
#[repr(u32)]
pub enum Qualified<T> {
    Allow(T) = HARDENED_ENUM_VALUE_0,
    Forbid(T) = HARDENED_ENUM_VALUE_1,
}

/// Type aliases; many items can be replaced by ALL, aliases, and negated.
pub type Spec<T> = Qualified<Meta<T>>;
pub type SpecList<T> = Vec<Spec<T>>;

/// The host list of a rule (`SpecList<Hostname>`): a named instance of the generic list parser,
/// so that the extraction (`Cargo.toml` `[package.metadata.charon]`) has one item for it.
pub(super) fn host_list(stream: &mut CharStream) -> Parsed<SpecList<Hostname>> {
    try_nonterminal(stream)
}

/// The user list of a rule (`SpecList<UserSpecifier>`), as `try_nonterminal`: a named instance
/// for the extraction, called by `Sudo::parse` and `RunAs::parse`.
pub(super) fn user_list(stream: &mut CharStream) -> Parsed<SpecList<UserSpecifier>> {
    try_nonterminal(stream)
}

/// The user list of a rule, as `expect_nonterminal`: a named instance for the extraction.
pub(super) fn expect_user_list(stream: &mut CharStream) -> Parsed<SpecList<UserSpecifier>> {
    expect_nonterminal(stream)
}

/// The permissions of one rule: `hostlist = [runas] cmds` groups separated by `:`.
pub type Permissions = PairVec<SpecList<Hostname>, (Option<RunAs>, CommandSpec)>;

/// The permissions of a rule (`hosts = [runas] commands : …`), as `expect_nonterminal`: a named
/// instance for the extraction, called by `Sudo::parse`.
pub(super) fn permissions(stream: &mut CharStream) -> Parsed<Permissions> {
    expect_nonterminal(stream)
}

/// `parse_lines::<Sudo>`: the whole file, one item per line with per-line error recovery. A
/// monomorphic instance, and the entry point of the extraction (`Cargo.toml`
/// `[package.metadata.charon]`); `parse_sudoers` in `mod.rs` calls it.
pub(super) fn parse_sudo_lines(stream: &mut CharStream) -> Vec<Parsed<Sudo>> {
    parse_lines(stream)
}

/// A generic mapping function (only used for turning `Spec<SimpleCommand>` into `Spec<Command>`)
#[cfg(test)]
impl<T> Spec<T> {
    pub fn map<U>(self, f: impl Fn(T) -> U) -> Spec<U> {
        let transform = |meta| match meta {
            Meta::All => Meta::All,
            Meta::Alias(alias) => Meta::Alias(alias),
            Meta::Only(x) => Meta::Only(f(x)),
        };

        match self {
            Qualified::Allow(x) => Qualified::Allow(transform(x)),
            Qualified::Forbid(x) => Qualified::Forbid(transform(x)),
        }
    }
}

/// An identifier is a name or a #number
#[cfg_attr(test, derive(Clone, Debug, PartialEq, Eq))]
#[repr(u32)]
pub enum Identifier {
    Name(SudoString) = HARDENED_ENUM_VALUE_0,
    ID(u32) = HARDENED_ENUM_VALUE_1,
}

impl std::fmt::Display for Identifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Self::Name(name) => write!(f, "{name}"),
            Self::ID(id) => write!(f, "#{id}"),
        }
    }
}

/// A userspecifier is either a username, or a (non-unix) group name, or netgroup
#[cfg_attr(test, derive(Clone, Debug, PartialEq, Eq))]
#[repr(u32)]
pub enum UserSpecifier {
    User(Identifier) = HARDENED_ENUM_VALUE_0,
    Group(Identifier) = HARDENED_ENUM_VALUE_1,
    NonunixGroup(Identifier) = HARDENED_ENUM_VALUE_2,
}

/// Peer credentials specification for @socket directive
#[cfg(feature = "unstable-remote-sudoers")]
#[cfg_attr(test, derive(Clone, Debug))]
pub struct PeerSpec {
    pub user: Identifier,
    pub group: Option<Identifier>,
}

/// The RunAs specification consists of a (possibly empty) list of userspecifiers, followed by a (possibly empty) list of groups.
pub struct RunAs {
    pub users: SpecList<UserSpecifier>,
    pub groups: SpecList<Identifier>,
}

// `sudo -l l` calls this the `authenticate` option
#[derive(Copy, Clone, Default, PartialEq)]
#[cfg_attr(test, derive(Debug, Eq))]
#[repr(u32)]
pub enum Authenticate {
    #[default]
    None = HARDENED_ENUM_VALUE_0,
    // PASSWD:
    Passwd = HARDENED_ENUM_VALUE_1,
    // NOPASSWD:
    Nopasswd = HARDENED_ENUM_VALUE_2,
}

#[derive(Copy, Clone, Default, PartialEq)]
#[cfg_attr(test, derive(Debug, Eq))]
#[repr(u32)]
pub enum EnvironmentControl {
    #[default]
    Implicit = HARDENED_ENUM_VALUE_0,
    // PASSWD:
    Setenv = HARDENED_ENUM_VALUE_1,
    // NOPASSWD:
    Nosetenv = HARDENED_ENUM_VALUE_2,
}

#[derive(Copy, Clone, Default, PartialEq)]
#[cfg_attr(test, derive(Debug, Eq))]
#[repr(u32)]
pub enum ExecControl {
    #[default]
    Implicit = HARDENED_ENUM_VALUE_0,
    // PASSWD:
    Exec = HARDENED_ENUM_VALUE_1,
    // NOPASSWD:
    Noexec = HARDENED_ENUM_VALUE_2,
}

/// Commands in /etc/sudoers can have attributes attached to them, such as NOPASSWD, NOEXEC, ...
#[derive(Default, Clone, PartialEq)]
#[cfg_attr(test, derive(Debug, Eq))]
pub struct Tag {
    pub(super) authenticate: Authenticate,
    pub(super) cwd: Option<ChDir>,
    pub(super) env: EnvironmentControl,
    pub(super) apparmor_profile: Option<String>,
    pub(super) noexec: ExecControl,
    pub(super) ignored: Vec<Span>,
}

impl Tag {
    pub fn needs_passwd(&self) -> bool {
        matches!(self.authenticate, Authenticate::None | Authenticate::Passwd)
    }
}

/// Commands with attached attributes.
pub struct CommandSpec(pub Vec<Modifier>, pub Spec<Command>);

/// The main AST object for one sudoer-permission line
type PairVec<A, B> = Vec<(A, Vec<B>)>;

pub struct PermissionSpec {
    pub users: SpecList<UserSpecifier>,
    pub permissions: PairVec<SpecList<Hostname>, (Option<RunAs>, CommandSpec)>,
}

pub type Defs<T> = Vec<Def<T>>;
pub struct Def<T>(pub String, pub SpecList<T>);

/// AST object for directive specifications (aliases, arguments, etc)
#[repr(u32)]
pub enum Directive {
    UserAlias(Defs<UserSpecifier>) = HARDENED_ENUM_VALUE_0,
    HostAlias(Defs<Hostname>) = HARDENED_ENUM_VALUE_1,
    CmndAlias(Defs<Command>) = HARDENED_ENUM_VALUE_2,
    RunasAlias(Defs<UserSpecifier>) = HARDENED_ENUM_VALUE_3,
    Defaults(Vec<defaults::SettingsModifier>, ConfigScope) = HARDENED_ENUM_VALUE_4,
}

/// AST object for the 'context' (host, user, cmnd, runas) of a Defaults directive
#[repr(u32)]
pub enum ConfigScope {
    // "Defaults entries are parsed in the following order:
    // generic, host and user Defaults first, then runas Defaults and finally command defaults."
    Generic = HARDENED_ENUM_VALUE_0,
    Host(SpecList<Hostname>) = HARDENED_ENUM_VALUE_1,
    User(SpecList<UserSpecifier>) = HARDENED_ENUM_VALUE_2,
    RunAs(SpecList<UserSpecifier>) = HARDENED_ENUM_VALUE_3,
    Command(SpecList<SimpleCommand>) = HARDENED_ENUM_VALUE_4,
}

/// The Sudoers file can contain permissions and directives
#[repr(u32)]
pub enum Sudo {
    Spec(PermissionSpec) = HARDENED_ENUM_VALUE_0,
    Decl(Directive) = HARDENED_ENUM_VALUE_1,
    Include(String, Span) = HARDENED_ENUM_VALUE_2,
    IncludeDir(String, Span) = HARDENED_ENUM_VALUE_3,
    #[cfg(feature = "unstable-remote-sudoers")]
    Remote(String, PeerSpec, Span) = HARDENED_ENUM_VALUE_4,
    LineComment = HARDENED_ENUM_VALUE_5,
}

/// grammar:
/// ```text
/// identifier = name
///            | #<numerical id>
/// ```
impl Parse for Identifier {
    fn parse(stream: &mut CharStream) -> Parsed<Self> {
        if stream.eat_char('#') {
            let DigitsU32(guid) = expect_nonterminal(stream)?;
            make(Identifier::ID(guid))
        } else {
            let Username(name) = try_nonterminal(stream)?;
            make(Identifier::Name(name))
        }
    }
}

impl Many for Identifier {}

/// grammar:
/// ```text
/// qualified<T> = T | "!", qualified<T>
/// ```
///
/// This computes the correct negation with multiple exclamation marks in the parsing stage so we
/// are not bothered by it later.
impl<T: Parse + UserFriendly> Parse for Qualified<T> {
    fn parse(stream: &mut CharStream) -> Parsed<Self> {
        if is_syntax('!', stream)? {
            let mut neg = true;
            let mut failure = None;
            let mut more = true;
            while more {
                match is_syntax('!', stream) {
                    Ok(true) => neg = !neg,
                    Ok(false) => more = false,
                    Err(status) => {
                        failure = Some(status);
                        more = false;
                    }
                }
            }
            if let Some(status) = failure {
                return Err(status);
            }
            let ident = expect_nonterminal(stream)?;
            if neg {
                make(Qualified::Forbid(ident))
            } else {
                make(Qualified::Allow(ident))
            }
        } else {
            let ident = try_nonterminal(stream)?;
            make(Qualified::Allow(ident))
        }
    }
}

impl<T: Many> Many for Qualified<T> {
    const SEP: char = T::SEP;
    const LIMIT: usize = T::LIMIT;
}

/// The user-name case of `Meta<T>` for a `T` that is not a token (`parse_meta`).
trait FromUsername {
    fn from_username(name: SudoString) -> Self;
}

impl FromUsername for Identifier {
    fn from_username(name: SudoString) -> Self {
        Identifier::Name(name)
    }
}

impl FromUsername for UserSpecifier {
    fn from_username(name: SudoString) -> Self {
        UserSpecifier::User(Identifier::Name(name))
    }
}

/// Helper function for parsing `Meta<T>` things where T is not a token
fn parse_meta<T: Parse + FromUsername>(stream: &mut CharStream) -> Parsed<Meta<T>> {
    match try_nonterminal::<Option<Meta<Username>>>(stream)? {
        Some(Meta::All) => make(Meta::All),
        Some(Meta::Alias(alias)) => make(Meta::Alias(alias)),
        Some(Meta::Only(Username(name))) => make(Meta::Only(T::from_username(name))),
        None => make(Meta::Only(T::parse(stream)?)),
    }
}

/// Since Identifier is not a token, add the parser for `Meta<Identifier>`
impl Parse for Meta<Identifier> {
    fn parse(stream: &mut CharStream) -> Parsed<Self> {
        parse_meta(stream)
    }
}

/// grammar:
/// ```text
/// userspec = identifier
///          | %identifier
///          | %:identifier
///          | +netgroup
/// ```
impl Parse for UserSpecifier {
    fn parse(stream: &mut CharStream) -> Parsed<Self> {
        fn parse_user(stream: &mut CharStream) -> Parsed<UserSpecifier> {
            if stream.eat_char('%') {
                let nonunix = stream.eat_char(':');
                // in this case we must fail 'hard', since input has been consumed
                let group = expect_nonterminal(stream)?;
                if nonunix {
                    make(UserSpecifier::NonunixGroup(group))
                } else {
                    make(UserSpecifier::Group(group))
                }
            } else if stream.eat_char('+') {
                // TODO Netgroups
                fatal_here(stream, ErrorKind::NetgroupsNotSupported)
            } else {
                // in this case we must fail 'softly', since no input has been consumed yet
                make(UserSpecifier::User(try_nonterminal(stream)?))
            }
        }

        // if we see a quote, first parse the quoted text as a token and then
        // re-parse whatever we found inside; this is a lazy solution but it works
        if stream.eat_char('"') {
            let begin_pos = stream.get_pos();
            let Unquoted(text, _): Unquoted<Username> = expect_nonterminal(stream)?;
            let chars = super::char_stream::chars_of(&text);
            let result = parse_user(&mut CharStream::new_with_pos(&chars, begin_pos))?;
            expect_syntax('"', stream)?;

            Ok(result)
        } else {
            parse_user(stream)
        }
    }
}

impl Many for UserSpecifier {}

/// UserSpecifier is not a token, implement the parser for `Meta<UserSpecifier>`
impl Parse for Meta<UserSpecifier> {
    fn parse(stream: &mut CharStream) -> Parsed<Self> {
        parse_meta(stream)
    }
}

/// grammar:
/// ```text
/// runas = "(", userlist, (":", grouplist?)?, ")"
/// ```
impl Parse for RunAs {
    fn parse(stream: &mut CharStream) -> Parsed<Self> {
        try_syntax('(', stream)?;
        // `try_nonterminal(stream).unwrap_or_default()`: any error, fatal ones included, is an
        // empty user list. Written as a `match` (`unwrap_or_default` has no Aeneas model).
        #[allow(clippy::manual_unwrap_or_default)]
        let users = match user_list(stream) {
            Ok(users) => users,
            // the status is bound (moved), so that every arm consumes the scrutinee
            Err(_status) => Vec::new(),
        };
        // `maybe(try_syntax(':', stream).and_then(|_| try_nonterminal(stream)))?
        //      .unwrap_or_default()`
        let groups = match try_syntax(':', stream) {
            Ok(()) => match try_nonterminal(stream) {
                Ok(groups) => groups,
                Err(Status::Reject) => Vec::new(),
                Err(status) => return Err(status),
            },
            Err(Status::Reject) => Vec::new(),
            Err(status) => return Err(status),
        };
        expect_syntax(')', stream)?;

        make(RunAs { users, groups })
    }
}

/// Implementing the trait Parse for `Meta<flag>`. Wrapped in an own object to avoid
/// conflicting with a potential future generic parse definition for [Meta].
///
/// The reason for combining a parser for these two unrelated categories is that this is one spot
/// where the sudoer grammar isn't nicely LL(1); so at the same place where "NOPASSWD" can appear,
/// we could also see "ALL".
struct MetaOrTag(Meta<Modifier>);

/// A `Modifier` is something that updates the `Tag`.
pub enum Modifier {
    Passwd,
    Nopasswd,
    Setenv,
    Nosetenv,
    Exec,
    Noexec,
    Cwd(ChDir),
    AppArmorProfile(String),
    Ignored(Span),
    NoOp,
}

impl Modifier {
    pub fn apply(&self, tag: &mut Tag) {
        match self {
            Modifier::Passwd => tag.authenticate = Authenticate::Passwd,
            Modifier::Nopasswd => tag.authenticate = Authenticate::Nopasswd,
            Modifier::Setenv => tag.env = EnvironmentControl::Setenv,
            Modifier::Nosetenv => tag.env = EnvironmentControl::Nosetenv,
            Modifier::Exec => tag.noexec = ExecControl::Exec,
            Modifier::Noexec => tag.noexec = ExecControl::Noexec,
            Modifier::Cwd(path) => tag.cwd = Some(path.clone()),
            Modifier::AppArmorProfile(profile) => tag.apparmor_profile = Some(profile.clone()),
            Modifier::Ignored(span) => tag.ignored.push(*span),
            Modifier::NoOp => {}
        }
    }
}

// note: at present, "ALL" can be distinguished from a tag using a lookup of 1, since no tag starts with an "A"; but this feels like hanging onto
// the parseability by a thread (although the original sudo also has some ugly parts, like 'sha224' being an illegal user name).
// to be more general, we impl Parse for Meta<Tag> so a future tag like "AFOOBAR" can be added with no problem

/// A tag that only needs its colon: `expect_syntax(':')`, then the modifier.
fn switch(modifier: Modifier, stream: &mut CharStream) -> Parsed<Modifier> {
    expect_syntax(':', stream)?;
    make(modifier)
}

impl Parse for MetaOrTag {
    fn parse(stream: &mut CharStream) -> Parsed<Self> {
        let start_pos = stream.get_pos();
        let AliasName(keyword) = try_nonterminal(stream)?;

        let result: Modifier = match keyword.as_str() {
            "EXEC" => switch(Modifier::Exec, stream)?,
            "NOEXEC" => switch(Modifier::Noexec, stream)?,

            "SETENV" => switch(Modifier::Setenv, stream)?,
            "NOSETENV" => switch(Modifier::Nosetenv, stream)?,
            "PASSWD" => switch(Modifier::Passwd, stream)?,
            "NOPASSWD" => switch(Modifier::Nopasswd, stream)?,

            "CWD" => {
                expect_syntax('=', stream)?;
                let path: ChDir = expect_nonterminal(stream)?;
                Modifier::Cwd(path)
            }

            // we do not support these, and that should make sudo-rs "fail safe"
            "INTERCEPT" | "CHROOT" | "TIMEOUT" | "NOTBEFORE" | "NOTAFTER" => {
                return fatal_from(start_pos, stream, ErrorKind::TagNotSupported(keyword));
            }
            "ROLE" | "TYPE" => {
                return fatal_from(start_pos, stream, ErrorKind::SelinuxNotSupported);
            }

            // this is less fatal
            "LOG_INPUT" | "NOLOG_INPUT" | "LOG_OUTPUT" | "NOLOG_OUTPUT" | "MAIL" | "NOMAIL"
            | "FOLLOW" => {
                let ignored_location = Span {
                    start: start_pos,
                    end: stream.get_pos(),
                };
                expect_syntax(':', stream)?;
                Modifier::Ignored(ignored_location)
            }

            // 'NOFOLLOW' and 'NOINTERCEPT' are the default behaviour.
            "NOFOLLOW" | "NOINTERCEPT" => switch(Modifier::NoOp, stream)?,

            "APPARMOR_PROFILE" => {
                expect_syntax('=', stream)?;
                let StringParameter(profile) = expect_nonterminal(stream)?;
                Modifier::AppArmorProfile(profile)
            }

            "ALL" => return make(MetaOrTag(Meta::All)),
            _ => {
                if is_syntax('=', stream)? {
                    return fatal_from(start_pos, stream, ErrorKind::UnsupportedModifier(keyword));
                } else {
                    return make(MetaOrTag(Meta::Alias(keyword)));
                }
            }
        };

        make(MetaOrTag(Meta::Only(result)))
    }
}

/// Read one tag, or return the end of the tag list. An alias or `ALL` also supplies
/// the command, so the inner option distinguishes those from an ordinary command.
fn command_tag_step(
    stream: &mut CharStream,
    tags: &mut Vec<Modifier>,
) -> Parsed<Option<Option<Meta<Command>>>> {
    match try_nonterminal::<Option<MetaOrTag>>(stream)? {
        Some(MetaOrTag(Meta::Only(modifier))) => {
            tags.push(modifier);
            if tags.len() > <Identifier as Many>::LIMIT {
                fatal_here(stream, ErrorKind::TooManyTags)
            } else {
                make(None)
            }
        }
        Some(MetaOrTag(Meta::All)) => make(Some(Some(Meta::All))),
        Some(MetaOrTag(Meta::Alias(name))) => make(Some(Some(Meta::Alias(name)))),
        None => make(Some(None)),
    }
}

/// grammar:
/// ```text
/// commandspec = [tag modifiers]*, command
/// ```
impl Parse for CommandSpec {
    fn parse(stream: &mut CharStream) -> Parsed<Self> {
        let mut tags = Vec::new();
        // the loop ends on an error, on `ALL` or an alias (`found`), or on anything else
        let mut failure = None;
        let mut found = None;
        let mut more = true;
        while more {
            match command_tag_step(stream, &mut tags) {
                Ok(None) => {}
                Ok(Some(command)) => {
                    found = command;
                    more = false;
                }
                Err(status) => {
                    failure = Some(status);
                    more = false;
                }
            }
        }

        if let Some(status) = failure {
            return Err(status);
        }
        match found {
            Some(meta) => make(CommandSpec(tags, Qualified::Allow(meta))),
            None => {
                let cmd: Spec<Command> = expect_nonterminal(stream)?;
                make(CommandSpec(tags, cmd))
            }
        }
    }
}

/// Parsing for a tuple of hostname, runas specifier and commandspec.
/// grammar:
/// ```text
/// (host,runas,commandspec) = hostlist, "=", [runas?, commandspec]+
/// ```
impl Parse for (SpecList<Hostname>, Vec<(Option<RunAs>, CommandSpec)>) {
    fn parse(stream: &mut CharStream) -> Parsed<Self> {
        let hosts = host_list(stream)?;
        expect_syntax('=', stream)?;
        let runas_cmds = expect_nonterminal(stream)?;

        make((hosts, runas_cmds))
    }
}

/// A hostname, runas specifier, commandspec combination can occur multiple times in a single
/// sudoer line (separated by ":")
impl Many for (SpecList<Hostname>, Vec<(Option<RunAs>, CommandSpec)>) {
    const SEP: char = ':';
}

/// Parsing for a tuple of hostname, runas specifier and commandspec.
/// grammar:
/// ```text
/// (runas,commandspec) = runas?, commandspec
/// ```
impl Parse for (Option<RunAs>, CommandSpec) {
    fn parse(stream: &mut CharStream) -> Parsed<Self> {
        let runas: Option<RunAs> = try_nonterminal(stream)?;
        let cmd = match runas {
            Some(_) => expect_nonterminal(stream)?,
            None => try_nonterminal(stream)?,
        };

        make((runas, cmd))
    }
}

/// A runas specifier, commandspec combination can occur multiple times in a single
/// sudoer line (separated by ","); there is some ambiguity in the original grammar:
/// commands can also occur multiple times; we parse that here as if they have an omitted
/// "runas" specifier (which has to be placed correctly during the AST analysis phase)
impl Many for (Option<RunAs>, CommandSpec) {}

/// Directives such as "Defaults" and "HostAlias" also could be parsed as part of a
/// UserSpecifier list. We need to detect to give a parse error in cases where the syntax
/// seems to suggest they are used in that manner.
/// Technically, "Defaults@host" is also a valid username, but the logic can disambiguate
/// those cases clearly. E.g. "Defaults@host1,host2 secure_path=/bin/sh" is technically
/// ambiguous but it can be parsed. Time flies like an arrow, fruit flies like a banana.
impl Directive {
    fn could_be_username(&self) -> bool {
        matches!(
            self,
            Self::Defaults(_, ConfigScope::Generic)
                | Self::UserAlias(_)
                | Self::HostAlias(_)
                | Self::CmndAlias(_)
                | Self::RunasAlias(_)
        )
    }
}

/// grammar:
/// ```text
/// sudo = permissionspec
///      | Keyword_Alias identifier = identifier_list
///      | Defaults (name [+-]?= ...)+
/// ```
/// There is a syntactical ambiguity in the sudoer Directive and Permission specifications, so we
/// have to parse them 'together' and do a delayed decision on which category we are in.
impl Parse for Sudo {
    // note: original sudo would reject:
    //   "User_Alias, user machine = command"
    // but accept:
    //   "user, User_Alias machine = command"; this does the same
    fn parse(stream: &mut CharStream) -> Parsed<Sudo> {
        if stream.eat_char('@') {
            return parse_include(stream);
        }

        // the existence of "#include" forces us to handle lines that start with #<ID> explicitly
        if stream.peek() == Some('#') {
            return match try_nonterminal::<Identifier>(stream) {
                Ok(ident) => {
                    let first_user = Qualified::Allow(Meta::Only(UserSpecifier::User(ident)));
                    let users = if is_syntax(',', stream)? {
                        // parse the rest of the userlist and add the already-parsed user in front
                        let mut rest = expect_user_list(stream)?;
                        rest.insert(0, first_user);
                        rest
                    } else {
                        vec![first_user]
                    };
                    // no need to check get_directive as no other directive starts with #
                    let permissions = permissions(stream)?;
                    make(Sudo::Spec(PermissionSpec { users, permissions }))
                }
                Err(_status) => {
                    // the failed "try_nonterminal::<Identifier>" will have consumed the '#'
                    // the most ignominious part of sudoers: having to parse bits of comments
                    match parse_include(stream) {
                        Ok(item) => make(item),
                        Err(_status) => {
                            stream.skip_to_newline();
                            make(Sudo::LineComment)
                        }
                    }
                }
            };
        }

        let start_state = stream.clone();
        if stream.peek() == Some('"') {
            // a quoted userlist follows; this forces us to read a userlist
            let users = expect_user_list(stream)?;
            let permissions = permissions(stream)?;
            return make(Sudo::Spec(PermissionSpec { users, permissions }));
        }

        let users = match maybe(user_list(stream))? {
            Some(users) => users,
            None => {
                // this will leave whatever could not be parsed on the input stream
                return make(Sudo::LineComment);
            }
        };

        // this could be the start of a Defaults or Alias definition, so distinguish.
        // element 1 always exists (parse_list fails on an empty list)
        let key = &users[0];
        let start_pos = start_state.get_pos();
        match maybe(get_directive(key, stream, start_state))? {
            Some(directive) => {
                if users.len() != 1 && directive.could_be_username() {
                    // this is here to guard against User_Alias,foo ALIAS=def being accepted
                    return fatal_from(start_pos, stream, ErrorKind::AmbiguousSyntax);
                }
                make(Sudo::Decl(directive))
            }
            None => {
                let permissions = permissions(stream)?;
                make(Sudo::Spec(PermissionSpec { users, permissions }))
            }
        }
    }
}

#[cfg(feature = "unstable-remote-sudoers")]
impl Parse for PeerSpec {
    fn parse(stream: &mut CharStream) -> Parsed<Self> {
        try_syntax('(', stream)?;

        let user = expect_nonterminal(stream)?;

        let group = if is_syntax(':', stream)? {
            Some(expect_nonterminal(stream)?)
        } else {
            None
        };

        expect_syntax(')', stream)?;
        make(PeerSpec { user, group })
    }
}

/// Parse the include/include dir part that comes after the '#' or '@' prefix symbol
fn parse_include(stream: &mut CharStream) -> Parsed<Sudo> {
    let key_pos = stream.get_pos();
    match try_nonterminal::<Option<Username>>(stream)? {
        Some(Username(key)) => {
            let keyword = sudo_string_text(&key);
            if equals_str(&keyword, INCLUDE) {
                let (path, span) = include_path(stream, key_pos)?;
                make(Sudo::Include(path, span))
            } else if equals_str(&keyword, INCLUDEDIR) {
                let (path, span) = include_path(stream, key_pos)?;
                make(Sudo::IncludeDir(path, span))
            } else {
                parse_remote(&keyword, stream, key_pos)
            }
        }
        None => fatal_from(key_pos, stream, ErrorKind::UnknownDirective),
    }
}

/// The `socket` directive, which exists only with `unstable-remote-sudoers`.
fn parse_remote(
    keyword: &String,
    stream: &mut CharStream,
    key_pos: (usize, usize),
) -> Parsed<Sudo> {
    #[cfg(feature = "unstable-remote-sudoers")]
    {
        if equals_str(keyword, SOCKET) {
            let peer_spec = expect_nonterminal(stream)?;
            let (path, span) = include_path(stream, key_pos)?;
            make(Sudo::Remote(path, peer_spec, span))
        } else {
            fatal_from(key_pos, stream, ErrorKind::UnknownDirective)
        }
    }
    #[cfg(not(feature = "unstable-remote-sudoers"))]
    {
        let _ = keyword;
        fatal_from(key_pos, stream, ErrorKind::UnknownDirective)
    }
}

const INCLUDE: &[char] = &['i', 'n', 'c', 'l', 'u', 'd', 'e'];
const INCLUDEDIR: &[char] = &['i', 'n', 'c', 'l', 'u', 'd', 'e', 'd', 'i', 'r'];
#[cfg(feature = "unstable-remote-sudoers")]
const SOCKET: &[char] = &['s', 'o', 'c', 'k', 'e', 't'];
const DEFAULTS: &[char] = &['D', 'e', 'f', 'a', 'u', 'l', 't', 's'];
const ALIAS_ALL: &[char] = &['A', 'L', 'L'];
const ALIAS_CHROOT: &[char] = &['C', 'H', 'R', 'O', 'O', 'T'];
const ALIAS_CWD: &[char] = &['C', 'W', 'D'];
const ALIAS_NOTAFTER: &[char] = &['N', 'O', 'T', 'A', 'F', 'T', 'E', 'R'];
const ALIAS_NOTBEFORE: &[char] = &['N', 'O', 'T', 'B', 'E', 'F', 'O', 'R', 'E'];
const ALIAS_ROLE: &[char] = &['R', 'O', 'L', 'E'];
const ALIAS_TIMEOUT: &[char] = &['T', 'I', 'M', 'E', 'O', 'U', 'T'];
const ALIAS_TYPE: &[char] = &['T', 'Y', 'P', 'E'];

/// The path of an `@include`/`@includedir` directive and its span.
fn include_path(stream: &mut CharStream, key_pos: (usize, usize)) -> Parsed<(String, Span)> {
    if stream.eat_char('"') {
        let QuotedIncludePath(path) = expect_nonterminal(stream)?;
        expect_syntax('"', stream)?;
        make((
            path,
            Span {
                start: key_pos,
                end: stream.get_pos(),
            },
        ))
    } else {
        let value_pos = stream.get_pos();
        let IncludePath(path) = expect_nonterminal(stream)?;
        if stream.peek() == Some('\n') {
            make((
                path,
                Span {
                    start: key_pos,
                    end: stream.get_pos(),
                },
            ))
        } else {
            fatal_from(value_pos, stream, ErrorKind::QuotesAroundFilenames)
        }
    }
}

/// `text == word` for a `String` and a character sequence.
fn equals_str(text: &String, word: &[char]) -> bool {
    super::tokens::equals_text(&chars_of(text), word)
}

fn is_reserved_alias(name: &String) -> bool {
    equals_str(name, ALIAS_ALL)
        || equals_str(name, ALIAS_CHROOT)
        || equals_str(name, ALIAS_CWD)
        || equals_str(name, ALIAS_NOTAFTER)
        || equals_str(name, ALIAS_NOTBEFORE)
        || equals_str(name, ALIAS_ROLE)
        || equals_str(name, ALIAS_TIMEOUT)
        || equals_str(name, ALIAS_TYPE)
}

/// grammar:
/// ```text
/// name = definition [ : name = definition [ : ... ] ]
/// ```
///
impl<T> Parse for Def<T>
where
    T: UserFriendly,
    Meta<T>: Parse + Many,
{
    fn parse(stream: &mut CharStream) -> Parsed<Self> {
        let begin_pos = stream.get_pos();
        let AliasName(name) = try_nonterminal(stream)?;
        if is_reserved_alias(&name) {
            return fatal_from(begin_pos, stream, ErrorKind::ReservedAlias(name));
        }
        expect_syntax('=', stream)?;

        make(Def(name, expect_nonterminal(stream)?))
    }
}

impl<T> Many for Def<T> {
    const SEP: char = ':';
}

// NOTE: This function is a bit of a hack, since it relies on the fact that all directives
// occur in the spot of a username, and are of a form that would otherwise be a legal user name.
// I.e. after a valid username has been parsed, we check if it isn't actually a valid start of a
// directive. A more robust solution would be to use the approach taken by the `MetaOrTag` above.

fn get_directive<'a>(
    perhaps_keyword: &Spec<UserSpecifier>,
    stream: &mut CharStream<'a>,
    begin_state: CharStream<'a>,
) -> Parsed<Directive> {
    let keyword = match perhaps_keyword {
        Qualified::Allow(Meta::Only(UserSpecifier::User(Identifier::Name(name)))) => {
            sudo_string_text(name)
        }
        _ => return reject(),
    };

    let begin_pos = begin_state.get_pos();

    if equals_str(&keyword, ALIAS_KW_USER) {
        make(Directive::UserAlias(expect_nonterminal(stream)?))
    } else if equals_str(&keyword, ALIAS_KW_HOST) {
        make(Directive::HostAlias(expect_nonterminal(stream)?))
    } else if equals_str(&keyword, ALIAS_KW_CMND) || equals_str(&keyword, ALIAS_KW_CMD) {
        make(Directive::CmndAlias(expect_nonterminal(stream)?))
    } else if equals_str(&keyword, ALIAS_KW_RUNAS) {
        make(Directive::RunasAlias(expect_nonterminal(stream)?))
    } else if starts_with_str(&keyword, DEFAULTS) {
        let scope = defaults_scope(&keyword, stream, begin_state, begin_pos)?;

        make(Directive::Defaults(expect_nonterminal(stream)?, scope))
    } else {
        reject()
    }
}

/// The `Defaults` line length, `"Defaults".len()`; no space is allowed between `Defaults`
/// and `!>@:` (HACK #1 of `get_directive`).
const DEFAULTS_LEN: usize = 8;

const ALIAS_KW_USER: &[char] = &[
    'U', 's', 'e', 'r', '_', 'A', 'l', 'i', 'a', 's',
];
const ALIAS_KW_HOST: &[char] = &[
    'H', 'o', 's', 't', '_', 'A', 'l', 'i', 'a', 's',
];
const ALIAS_KW_CMND: &[char] = &[
    'C', 'm', 'n', 'd', '_', 'A', 'l', 'i', 'a', 's',
];
const ALIAS_KW_CMD: &[char] = &['C', 'm', 'd', '_', 'A', 'l', 'i', 'a', 's'];
const ALIAS_KW_RUNAS: &[char] = &[
    'R', 'u', 'n', 'a', 's', '_', 'A', 'l', 'i', 'a', 's',
];

/// `text.starts_with(prefix)` for a `String` and a character sequence.
fn starts_with_str(text: &String, prefix: &[char]) -> bool {
    super::tokens::starts_with_text(&chars_of(text), prefix)
}

/// The scope of a `Defaults` line, which decides where the settings apply.
///
/// HACK #2 of `get_directive`: `@` can be part of a username, so it has already been parsed; an
/// acceptable hostname is a subset of an acceptable username, so that is actually fine.
fn defaults_scope<'a>(
    keyword: &String,
    stream: &mut CharStream<'a>,
    begin_state: CharStream<'a>,
    begin_pos: (usize, usize),
) -> Parsed<ConfigScope> {
    let chars = chars_of(keyword);
    let scope_at = chars.len() > DEFAULTS_LEN && chars[DEFAULTS_LEN] == '@';
    let scope_adjacent = stream.get_pos().0 == begin_pos.0
        && stream.get_pos().1 - begin_pos.1 == DEFAULTS_LEN;

    if !scope_at && !scope_adjacent {
        return make(ConfigScope::Generic);
    }
    if scope_at {
        // Backtrack and start parsing following the '@' sign
        *stream = begin_state;
        stream.advance(DEFAULTS_LEN + 1);
        skip_trailing_whitespace(stream)?;

        return make(ConfigScope::Host(expect_nonterminal(stream)?));
    }
    if is_syntax(':', stream)? {
        make(ConfigScope::User(expect_nonterminal(stream)?))
    } else if is_syntax('!', stream)? {
        make(ConfigScope::Command(expect_nonterminal(stream)?))
    } else if is_syntax('>', stream)? {
        make(ConfigScope::RunAs(expect_nonterminal(stream)?))
    } else {
        make(ConfigScope::Generic)
    }
}

/// grammar:
/// ```text
/// parameter = name [+-]?= ...
/// ```
impl Parse for defaults::SettingsModifier {
    fn parse(stream: &mut CharStream) -> Parsed<Self> {
        let id_pos = stream.get_pos();

        if is_syntax('!', stream)? {
            let value_pos = stream.get_pos();
            let DefaultName(name) = expect_nonterminal(stream)?;
            match defaults::negate(name.as_str()) {
                Some(modifier) => make(modifier),
                None => {
                    if defaults::set(name.as_str()).is_some() {
                        fatal_from(value_pos, stream, ErrorKind::CannotUseInBoolean(name))
                    } else {
                        fatal_from(value_pos, stream, ErrorKind::UnknownSetting(name))
                    }
                }
            }
        } else {
            let DefaultName(name) = try_nonterminal(stream)?;
            let cfg = match defaults::set(name.as_str()) {
                Some(cfg) => cfg,
                None => return fatal_from(id_pos, stream, ErrorKind::UnknownSetting(name)),
            };

            if is_syntax('+', stream)? {
                parse_defaults_list(defaults::ListMode::Add, name, cfg, id_pos, stream)
            } else if is_syntax('-', stream)? {
                parse_defaults_list(defaults::ListMode::Del, name, cfg, id_pos, stream)
            } else if is_syntax('=', stream)? {
                let value_pos = stream.get_pos();
                match cfg {
                    defaults::SettingKind::Flag(_) => {
                        fatal_here(stream, ErrorKind::CannotAssignBoolean(name))
                    }
                    defaults::SettingKind::Integer(setting) => {
                        let Numeric(denotation) = expect_nonterminal(stream)?;
                        match defaults::check_integer(setting, denotation.as_str()) {
                            Some(modifier) => make(modifier),
                            None => fatal_from(
                                value_pos,
                                stream,
                                ErrorKind::InvalidSettingValue(denotation, name),
                            ),
                        }
                    }
                    defaults::SettingKind::List(setting) => {
                        let items = parse_defaults_vars(stream)?;

                        make(defaults::build_list(setting, defaults::ListMode::Set, items))
                    }
                    defaults::SettingKind::Text(setting) => {
                        let text = parse_defaults_text(stream)?;
                        match defaults::check_text(setting, text.as_str()) {
                            Some(modifier) => make(modifier),
                            None => fatal_from(
                                value_pos,
                                stream,
                                ErrorKind::InvalidSettingValue(text, name),
                            ),
                        }
                    }
                }
            } else {
                match cfg {
                    defaults::SettingKind::Flag(modifier) => make(modifier),
                    _ => fatal_from(id_pos, stream, ErrorKind::NotABooleanSetting(name)),
                }
            }
        }
    }
}

/// The remainder of a list setting: `=`, then `name is not a list parameter` unless `cfg` is a
/// list, then the variable list.
fn parse_defaults_list(
    mode: defaults::ListMode,
    name: String,
    cfg: defaults::SettingKind,
    id_pos: (usize, usize),
    stream: &mut CharStream,
) -> Parsed<defaults::SettingsModifier> {
    expect_syntax('=', stream)?;
    match cfg {
        defaults::SettingKind::List(setting) => {
            let items = parse_defaults_vars(stream)?;

            make(defaults::build_list(setting, mode, items))
        }
        _ => fatal_from(id_pos, stream, ErrorKind::NotAListParameter(name)),
    }
}

/// The entries of a list setting: a quoted list of `VAR` and `VAR=value`, or one unquoted name.
fn parse_defaults_vars(stream: &mut CharStream) -> Parsed<Vec<String>> {
    if stream.eat_char('"') {
        let mut result = Vec::new();
        let mut failure = None;
        let mut more = true;
        while more {
            match try_nonterminal::<Option<EnvVar>>(stream) {
                Ok(Some(EnvVar(name))) => {
                    match is_syntax('=', stream) {
                        Ok(true) => match expect_nonterminal::<StringParameter>(stream) {
                            Ok(StringParameter(value)) => result.push(join_var(name, &value)),
                            Err(status) => {
                                failure = Some(status);
                                more = false;
                            }
                        },
                        Ok(false) => result.push(name),
                        Err(status) => {
                            failure = Some(status);
                            more = false;
                        }
                    }
                    if more && result.len() > <Identifier as Many>::LIMIT {
                        let pos = stream.get_pos();
                        failure = Some(Status::Fatal(
                            Span {
                                start: pos,
                                end: pos,
                            },
                            ErrorKind::EnvironmentListTooLong,
                        ));
                        more = false;
                    }
                }
                Ok(None) => more = false,
                Err(status) => {
                    failure = Some(status);
                    more = false;
                }
            }
        }
        if let Some(status) = failure {
            return Err(status);
        }
        expect_syntax('"', stream)?;
        if result.is_empty() {
            return fatal_here(stream, ErrorKind::EmptyStringNotAllowed);
        }

        make(result)
    } else {
        let EnvVar(name) = expect_nonterminal(stream)?;
        if is_syntax('=', stream)? {
            fatal_here(stream, ErrorKind::QuotesRequiredForVarValue)
        } else {
            make(vec![name])
        }
    }
}

/// `name + "=" + value`, the entry of a list setting.
fn join_var(name: String, value: &String) -> String {
    let mut entry = name;
    entry.push('=');
    let chars = chars_of(value);
    let mut i = 0;
    while i < chars.len() {
        entry.push(chars[i]);
        i += 1;
    }
    entry
}

/// A text setting's value: quoted or bare.
fn parse_defaults_text(stream: &mut CharStream) -> Parsed<String> {
    if stream.eat_char('"') {
        let QuotedStringParameter(text) = expect_nonterminal(stream)?;
        expect_syntax('"', stream)?;
        make(text)
    } else {
        let StringParameter(name) = expect_nonterminal(stream)?;
        make(name)
    }
}

impl Many for defaults::SettingsModifier {}
