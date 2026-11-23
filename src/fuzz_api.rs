//! Entry points for the libFuzzer targets in `fuzz/`.
//!
//! This module only exists when the crate is compiled with `--cfg fuzzing`, which cargo-fuzz
//! sets; normal builds do not contain it. Every function is a thin wrapper that calls the same
//! crate-private code the binaries call and returns its results in plain types that the fuzz
//! targets can compare. Nothing here alters what that code does.

use std::ffi::{CStr, OsString};
use std::fs::File;
use std::io;
use std::path::{Path, PathBuf};
use std::time::Duration;

use crate::common::resolve::AuthUser;
use crate::common::{CommandAndArguments, SudoPath, SudoString};
use crate::sudoers::{
    AuthenticatingUser, Authentication, AuthenticationScope, Authorization, DirChange,
    ListRequest, Logging, Request, Restrictions, Sudoers,
};
use crate::system::interface::{DeviceId, GroupId, ProcessId, UnixGroup, UnixUser, UserId};
use crate::system::time::ProcessCreateTime;
use crate::system::timestamp::{RecordScope, SessionRecord, SessionRecordFile, TouchResult};
use crate::system::{Hostname, User};

/// The file the fuzzed policy text claims to come from. Its directory does not exist, so
/// relative `@include`/`@includedir` directives resolve to missing files.
pub const SUDOERS_PATH: &str = "/nonexistent/sudo-rs-fuzz/sudoers";

// ------------------------------------------------------------------ sudoers file

/// One diagnostic of [Sudoers::read], in plain types.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Diagnostic {
    pub source: Option<PathBuf>,
    /// `(start, end)`, each `(line, column)` as produced by the parser
    pub span: Option<((usize, usize), (usize, usize))>,
    pub message: String,
}

/// Read a sudoers file the way `Sudoers::open` does after opening it (read the whole input as
/// UTF-8, `parse_lines`, `analyze`). `Err` is the I/O error of reading (invalid UTF-8).
pub fn sudoers_read(bytes: &[u8]) -> io::Result<Vec<Diagnostic>> {
    let (_sudoers, errors) = Sudoers::read(bytes, SUDOERS_PATH)?;
    Ok(errors
        .into_iter()
        .map(|e| Diagnostic {
            source: e.source,
            span: e.location.map(|s| (s.start, s.end)),
            message: e.message,
        })
        .collect())
}

/// The restricted-style sudoers parser against the legacy parser it replaced
/// (`sudoers::equiv::compare`: items, spans, message texts, and the effect of every `Defaults`
/// modifier on two base settings). `Err` describes the first difference. Bytes that are not
/// UTF-8 never reach the parser (`Sudoers::read` fails first) and give `Ok`.
pub fn sudoers_parser_equiv(bytes: &[u8]) -> Result<(), String> {
    match std::str::from_utf8(bytes) {
        Ok(text) => crate::sudoers::equiv::compare(text).map(|_| ()),
        Err(_) => Ok(()),
    }
}

// ------------------------------------------------------------------ users and groups

/// A group of the fuzzed user database.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FuzzGroup {
    pub name: Option<String>,
    pub gid: u32,
}

/// A user of the fuzzed user database: a name, ids and group memberships, without any
/// lookup in the host's databases.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FuzzUser {
    pub name: String,
    pub uid: u32,
    pub primary: FuzzGroup,
    pub supplementary: Vec<FuzzGroup>,
}

impl FuzzUser {
    fn groups(&self) -> impl Iterator<Item = &FuzzGroup> {
        std::iter::once(&self.primary).chain(&self.supplementary)
    }
}

impl UnixUser for FuzzUser {
    fn has_name(&self, name: &str) -> bool {
        self.name == name
    }
    fn has_uid(&self, uid: UserId) -> bool {
        UserId::new(self.uid) == uid
    }
    fn is_root(&self) -> bool {
        self.uid == 0
    }
    fn in_group_by_name(&self, name: &CStr) -> bool {
        let Ok(name) = name.to_str() else {
            return false;
        };
        self.groups().any(|g| g.name.as_deref() == Some(name))
    }
    fn in_group_by_gid(&self, gid: GroupId) -> bool {
        self.groups().any(|g| GroupId::new(g.gid) == gid)
    }
    type Group = FuzzGroup;
    fn group(&self) -> FuzzGroup {
        self.primary.clone()
    }
}

impl UnixGroup for FuzzGroup {
    fn as_gid(&self) -> GroupId {
        GroupId::new(self.gid)
    }
    fn try_as_name(&self) -> Option<&str> {
        self.name.as_deref()
    }
}

// ------------------------------------------------------------------ policy decisions

/// A `sudo` request against a policy text.
#[derive(Debug, Clone)]
pub struct DecisionInput {
    pub policy: String,
    pub hostname: String,
    pub invoking_user: FuzzUser,
    pub target_user: FuzzUser,
    pub target_group: FuzzGroup,
    pub command: PathBuf,
    pub arguments: Vec<OsString>,
}

/// [Authentication] in plain types.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AuthSummary {
    pub must_authenticate: bool,
    /// 0: invoking user, 1: root, 2: target user
    pub credential: u8,
    pub allowed_attempts: u16,
    pub prior_validity: Duration,
    pub pwfeedback: bool,
    pub password_timeout: Option<Duration>,
    pub noninteractive_auth: bool,
    /// 0: tty, 1: parent pid
    pub scope: u8,
}

/// [Restrictions] in plain types (sets sorted).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RestrictionSummary {
    pub use_pty: bool,
    pub trust_environment: bool,
    pub noexec: bool,
    pub env_keep: Vec<String>,
    pub env_check: Vec<String>,
    /// `None`: any directory; `Some(d)`: strict, `d` the directory if one is fixed
    pub chdir: Option<Option<PathBuf>>,
    pub path: Option<String>,
    pub umask: String,
    pub log: bool,
}

fn auth_summary(auth: &Authentication) -> AuthSummary {
    AuthSummary {
        must_authenticate: auth.must_authenticate,
        credential: match auth.credential {
            AuthenticatingUser::InvokingUser => 0,
            AuthenticatingUser::Root => 1,
            AuthenticatingUser::TargetUser => 2,
        },
        allowed_attempts: auth.allowed_attempts,
        prior_validity: auth.prior_validity,
        pwfeedback: auth.pwfeedback,
        password_timeout: auth.password_timeout,
        noninteractive_auth: auth.noninteractive_auth,
        scope: match auth.scope {
            AuthenticationScope::Tty => 0,
            AuthenticationScope::PPid => 1,
        },
    }
}

fn restriction_summary(r: &Restrictions) -> RestrictionSummary {
    let sorted = |set: &std::collections::HashSet<String>| {
        let mut v: Vec<String> = set.iter().cloned().collect();
        v.sort();
        v
    };
    RestrictionSummary {
        use_pty: r.use_pty,
        trust_environment: r.trust_environment,
        noexec: r.noexec,
        env_keep: sorted(r.env_keep),
        env_check: sorted(r.env_check),
        chdir: match &r.chdir {
            DirChange::Any => None,
            DirChange::Strict(dir) => Some(dir.as_ref().map(|d| PathBuf::from(d.as_ref()))),
        },
        path: r.path.map(str::to_owned),
        umask: format!("{:?}", r.umask),
        log: matches!(r.log, Logging::Auth),
    }
}

/// The result of `sudo <command>`, `sudo -v` and `sudo -l` for one request.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Decision {
    /// `Sudoers::check`: `None` if forbidden
    pub run: Option<(AuthSummary, RestrictionSummary)>,
    /// `Sudoers::check_validate_permission` (`sudo -v`)
    pub validate: Option<AuthSummary>,
    /// `Sudoers::check_list_permission` for the invoking user's own permissions (`sudo -l`)
    pub list_self: Option<AuthSummary>,
    /// `Sudoers::check_list_permission` for the target user's permissions (`sudo -l -U`)
    pub list_other: Option<AuthSummary>,
    /// the `sudo -l` and `sudo -ll` listing of `Sudoers::matching_entries`
    pub listing: Vec<String>,
    pub listing_verbose: Vec<String>,
    pub diagnostics: usize,
}

fn read_policy(policy: &str) -> (Sudoers, usize) {
    let (sudoers, errors) =
        Sudoers::read(policy.as_bytes(), SUDOERS_PATH).expect("reading a &str cannot fail");
    (sudoers, errors.len())
}

/// Decide `input` as `sudo` would: each question is asked of a freshly read policy, as each
/// invocation of the binary reads the policy once and asks one question.
pub fn sudoers_decide(input: &DecisionInput) -> Decision {
    let host = Hostname::fake(&input.hostname);
    let am = &input.invoking_user;

    let (mut sudoers, diagnostics) = read_policy(&input.policy);
    let judgement = sudoers.check(
        am,
        &host,
        Request {
            user: &input.target_user,
            group: &input.target_group,
            command: &input.command,
            arguments: &input.arguments,
        },
    );
    let run = match judgement.authorization() {
        Authorization::Allowed(auth, restrictions) => {
            Some((auth_summary(&auth), restriction_summary(&restrictions)))
        }
        Authorization::Forbidden => None,
    };

    let allowed = |a: Authorization| match a {
        Authorization::Allowed(auth, ()) => Some(auth_summary(&auth)),
        Authorization::Forbidden => None,
    };

    let validate = allowed(read_policy(&input.policy).0.check_validate_permission(am, &host));
    let list_self = allowed(read_policy(&input.policy).0.check_list_permission(
        am,
        &host,
        ListRequest {
            inspected_user: am,
            target_user: &input.target_user,
            target_group: &input.target_group,
        },
    ));
    let list_other = allowed(read_policy(&input.policy).0.check_list_permission(
        am,
        &host,
        ListRequest {
            inspected_user: &input.target_user,
            target_user: &input.target_user,
            target_group: &input.target_group,
        },
    ));

    let (sudoers, _) = read_policy(&input.policy);
    let listing = sudoers
        .matching_entries(am, &host)
        .map(|entry| entry.to_string())
        .collect();
    let listing_verbose = sudoers
        .matching_entries(am, &host)
        .map(|entry| entry.verbose().to_string())
        .collect();

    Decision {
        run,
        validate,
        list_self,
        list_other,
        listing,
        listing_verbose,
        diagnostics,
    }
}

/// The settings a policy's `Defaults` produce, as `sudo` reads them after `Sudoers::check`
/// (for the decision), `Sudoers::search_path` (`secure_path`) and `visudo_editor_path`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SettingsOutcome {
    pub decision: Option<(AuthSummary, RestrictionSummary)>,
    pub secure_path: Option<String>,
    pub editor: Option<(PathBuf, Vec<OsString>)>,
    pub diagnostics: Vec<Diagnostic>,
}

fn plain_user(user: &FuzzUser) -> User {
    User {
        uid: UserId::new(user.uid),
        gid: GroupId::new(user.primary.gid),
        name: SudoString::new(user.name.replace('\0', "")).expect("NUL bytes removed"),
        home: SudoPath::new(PathBuf::from("/nonexistent")).expect("no NUL byte"),
        shell: PathBuf::from("/bin/sh"),
        groups: user.groups().map(|g| GroupId::new(g.gid)).collect(),
    }
}

/// Apply the `Defaults` of `input.policy` for `input`'s request and read back every setting
/// the binaries use.
pub fn sudoers_settings(input: &DecisionInput) -> SettingsOutcome {
    let host = Hostname::fake(&input.hostname);
    let am = &input.invoking_user;

    let (mut sudoers, errors) =
        Sudoers::read(input.policy.as_bytes(), SUDOERS_PATH).expect("reading a &str cannot fail");
    let diagnostics = errors
        .into_iter()
        .map(|e| Diagnostic {
            source: e.source,
            span: e.location.map(|s| (s.start, s.end)),
            message: e.message,
        })
        .collect();
    let judgement = sudoers.check(
        am,
        &host,
        Request {
            user: &input.target_user,
            group: &input.target_group,
            command: &input.command,
            arguments: &input.arguments,
        },
    );
    let decision = match judgement.authorization() {
        Authorization::Allowed(auth, restrictions) => {
            Some((auth_summary(&auth), restriction_summary(&restrictions)))
        }
        Authorization::Forbidden => None,
    };

    let (current, target) = (plain_user(am), plain_user(&input.target_user));
    let secure_path = read_policy(&input.policy)
        .0
        .search_path(&host, &current, &target)
        .map(str::to_owned);
    let editor = read_policy(&input.policy)
        .0
        .visudo_editor_path(&host, &current, &target);

    SettingsOutcome {
        decision,
        secure_path,
        editor,
        diagnostics,
    }
}

// ------------------------------------------------------------------ command lines

/// `sudo`'s argument parser and validation (`SudoAction::try_parse_from`); `Ok` holds the
/// action and its options, rendered as text, and the positional arguments.
pub fn sudo_cli(args: &[OsString]) -> Result<(String, Vec<OsString>), String> {
    use crate::sudo::SudoAction;
    let action = SudoAction::try_parse_from(args.iter().cloned())?;
    Ok(match action {
        SudoAction::Run(o) => (
            format!(
                "run askpass={} bell={} background={} k={} n={} S={} p={:?} D={:?} g={:?} u={:?} env={:?} i={} s={}",
                o.askpass,
                o.bell,
                o.background,
                o.reset_timestamp,
                o.non_interactive,
                o.stdin,
                o.prompt,
                o.chdir.as_ref().map(|p| p.to_path_buf()),
                o.group.as_deref(),
                o.user.as_deref(),
                o.env_var_list,
                o.login,
                o.shell
            ),
            o.positional_args,
        ),
        SudoAction::Edit(o) => (
            format!(
                "edit askpass={} bell={} k={} n={} S={} p={:?} D={:?} g={:?} u={:?}",
                o.askpass,
                o.bell,
                o.reset_timestamp,
                o.non_interactive,
                o.stdin,
                o.prompt,
                o.chdir.as_ref().map(|p| p.to_path_buf()),
                o.group.as_deref(),
                o.user.as_deref()
            ),
            o.positional_args,
        ),
        SudoAction::List(o) => (
            format!(
                "list verbose={} askpass={} bell={} k={} n={} S={} p={:?} g={:?} U={:?} u={:?}",
                o.list.is_verbose(),
                o.askpass,
                o.bell,
                o.reset_timestamp,
                o.non_interactive,
                o.stdin,
                o.prompt,
                o.group.as_deref(),
                o.other_user.as_deref(),
                o.user.as_deref()
            ),
            o.positional_args,
        ),
        SudoAction::Validate(o) => (
            format!(
                "validate askpass={} bell={} k={} n={} S={} p={:?} g={:?} u={:?}",
                o.askpass,
                o.bell,
                o.reset_timestamp,
                o.non_interactive,
                o.stdin,
                o.prompt,
                o.group.as_deref(),
                o.user.as_deref()
            ),
            Vec::new(),
        ),
        SudoAction::Help(_) => ("help".to_owned(), Vec::new()),
        SudoAction::Version(_) => ("version".to_owned(), Vec::new()),
        SudoAction::RemoveTimestamp(_) => ("remove-timestamp".to_owned(), Vec::new()),
        SudoAction::ResetTimestamp(_) => ("reset-timestamp".to_owned(), Vec::new()),
    })
}

/// `su`'s argument parser and validation; `Ok` holds the action rendered as text and, for a
/// run, the target user followed by the arguments for the shell.
pub fn su_cli(args: Vec<String>) -> Result<(String, Vec<String>), String> {
    crate::su::fuzz_parse_cli(args)
}

/// `visudo`'s argument parser; `Ok` holds the options rendered as text.
pub fn visudo_cli(args: Vec<String>) -> Result<String, String> {
    crate::visudo::fuzz_parse_cli(args)
}

// ------------------------------------------------------------------ timestamp records

/// `SessionRecord::from_bytes` (decoding one record of a timestamp file); `Ok` holds the
/// record re-encoded with `SessionRecord::as_bytes`.
pub fn timestamp_record(data: &[u8]) -> io::Result<Vec<u8>> {
    SessionRecord::from_bytes(data)?.as_bytes()
}

/// One operation on a timestamp file.
#[derive(Debug, Clone, Copy)]
pub enum TimestampOp {
    Touch,
    Create,
    Disable,
}

/// A record scope and the user it authenticates, from small numbers.
#[derive(Debug, Clone, Copy)]
pub struct TimestampKey {
    pub tty: bool,
    pub pid: i32,
    pub session: i32,
    pub start_secs: i64,
    pub start_nsecs: i64,
    pub auth_uid: u32,
}

impl TimestampKey {
    fn scope(&self) -> RecordScope {
        let init_time = ProcessCreateTime::new(self.start_secs, self.start_nsecs);
        if self.tty {
            RecordScope::Tty {
                tty_device: DeviceId::new(self.pid as libc::dev_t),
                session_pid: ProcessId::new(self.session),
                init_time,
            }
        } else {
            RecordScope::Ppid {
                group_pid: ProcessId::new(self.pid),
                session_pid: ProcessId::new(self.session),
                init_time,
            }
        }
    }

    fn auth_user(&self) -> AuthUser {
        AuthUser::from_user_for_targetpw(User {
            uid: UserId::new(self.auth_uid),
            gid: GroupId::new(0),
            name: SudoString::new("fuzz".to_owned()).expect("no NUL byte"),
            home: SudoPath::new(PathBuf::from("/nonexistent")).expect("no NUL byte"),
            shell: PathBuf::from("/bin/sh"),
            groups: vec![],
        })
    }
}

/// What a timestamp operation returned.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TimestampOutcome {
    Updated,
    Outdated,
    NotFound,
    Created,
    Disabled,
}

/// Open `file` as the timestamp file of `uid` (`SessionRecordFile::new`, which checks and
/// repairs the header) with the given timeout.
pub struct TimestampFile(SessionRecordFile);

impl TimestampFile {
    pub fn open(uid: u32, file: File, timeout: Duration) -> io::Result<Self> {
        SessionRecordFile::new(UserId::new(uid), file, timeout).map(Self)
    }

    pub fn apply(&mut self, op: TimestampOp, key: &TimestampKey) -> io::Result<TimestampOutcome> {
        let (scope, user) = (key.scope(), key.auth_user());
        Ok(match op {
            TimestampOp::Touch => match self.0.touch(scope, &user)? {
                TouchResult::Updated { .. } => TimestampOutcome::Updated,
                TouchResult::Outdated { .. } => TimestampOutcome::Outdated,
                TouchResult::NotFound => TimestampOutcome::NotFound,
            },
            TimestampOp::Create => {
                self.0.create(scope, &user)?;
                TimestampOutcome::Created
            }
            TimestampOp::Disable => {
                self.0.disable(scope)?;
                TimestampOutcome::Disabled
            }
        })
    }
}

// ------------------------------------------------------------------ names, ids, escaping

/// `NameOrId::parse` as `sudo -u`/`-g` and `su` apply it to user names (ids are `UserId`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NameOrId {
    Name(String),
    Id(u32),
}

/// `None` if `input` contains a NUL byte (no `SudoString` exists for it) or if
/// `NameOrId::parse` rejects it.
pub fn name_or_id(input: &str) -> Option<NameOrId> {
    let input = SudoString::new(input.to_owned()).ok()?;
    crate::common::resolve::fuzz_name_or_id(&input)
}

/// The argument escaping of `sudo -s`/`sudo -i` (`escaped` in `common::command`).
pub fn escaped(arguments: Vec<OsString>) -> OsString {
    crate::common::command::fuzz_escaped(arguments)
}

/// `CommandAndArguments::build_from_args` with a shell (`sudo -s`/`-i`): the arguments
/// handed to the shell.
pub fn shell_arguments(shell: &Path, arguments: Vec<OsString>) -> Vec<OsString> {
    CommandAndArguments::build_from_args(Some(shell.to_owned()), arguments, "").arguments
}
