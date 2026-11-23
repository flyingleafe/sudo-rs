//! Data types and traits that represent what the "terms and conditions" are after a successful
//! permission check.
//!
//! The trait definitions can be part of some global crate in the future, if we support more
//! than just the sudoers file.

use super::{Judgement, Sudoers};
use crate::common::{
    HARDENED_ENUM_VALUE_0, HARDENED_ENUM_VALUE_1, HARDENED_ENUM_VALUE_2, SudoPath,
};
use crate::defaults::enums;
use crate::exec::Umask;
use crate::sudoers::ast::{EnvironmentControl, ExecControl, Tag};
use crate::system::{Hostname, User};
use std::collections::HashSet;
use std::time::Duration;
use std::{ffi::OsString, path::PathBuf};

#[must_use]
#[cfg_attr(test, derive(Debug, PartialEq))]
#[repr(u32)]
pub enum Authorization<T = ()> {
    Allowed(Authentication, T) = HARDENED_ENUM_VALUE_0,
    Forbidden = HARDENED_ENUM_VALUE_1,
}

#[cfg_attr(test, derive(Debug, PartialEq))]
#[must_use]
pub struct Authentication {
    pub must_authenticate: bool,
    pub credential: AuthenticatingUser,
    pub allowed_attempts: u16,
    pub prior_validity: Duration,
    pub pwfeedback: bool,
    pub password_timeout: Option<Duration>,
    pub noninteractive_auth: bool,
    pub scope: AuthenticationScope,
}

impl super::Settings {
    pub(super) fn to_auth(&self, tag: &Tag) -> Authentication {
        Authentication {
            must_authenticate: tag.needs_passwd(),
            allowed_attempts: self.passwd_tries().try_into().unwrap(),
            prior_validity: Duration::from_secs(self.timestamp_timeout()),
            pwfeedback: self.pwfeedback(),
            password_timeout: match self.passwd_timeout() {
                0 => None,
                timeout => Some(Duration::from_secs(timeout)),
            },
            scope: match self.timestamp_type() {
                enums::timestamp_type::tty => AuthenticationScope::Tty,
                enums::timestamp_type::ppid => AuthenticationScope::PPid,
            },
            noninteractive_auth: self.noninteractive_auth(),
            credential: if self.rootpw() {
                AuthenticatingUser::Root
            } else if self.targetpw() {
                AuthenticatingUser::TargetUser
            } else {
                AuthenticatingUser::InvokingUser
            },
        }
    }
}

#[must_use]
#[cfg_attr(test, derive(Debug, PartialEq))]
pub struct Restrictions<'a> {
    pub use_pty: bool,
    pub trust_environment: bool,
    pub noexec: bool,
    pub env_keep: &'a HashSet<String>,
    pub env_check: &'a HashSet<String>,
    pub chdir: DirChange,
    pub path: Option<&'a str>,
    pub umask: Umask,
    pub log: Logging,
    #[cfg(feature = "apparmor")]
    pub apparmor_profile: Option<String>,
}

#[must_use]
#[cfg_attr(test, derive(Debug, PartialEq))]
#[repr(u32)]
pub enum DirChange {
    Strict(Option<SudoPath>) = HARDENED_ENUM_VALUE_0,
    Any = HARDENED_ENUM_VALUE_1,
}

#[must_use]
#[cfg_attr(test, derive(Debug, PartialEq))]
#[repr(u32)]
pub enum Logging {
    Auth = HARDENED_ENUM_VALUE_0,
    Disabled = HARDENED_ENUM_VALUE_1,
}

#[cfg_attr(test, derive(Debug, PartialEq))]
#[repr(u32)]
pub enum AuthenticatingUser {
    InvokingUser = HARDENED_ENUM_VALUE_0,
    Root = HARDENED_ENUM_VALUE_1,
    TargetUser = HARDENED_ENUM_VALUE_2,
}

#[cfg_attr(test, derive(Debug, PartialEq))]
#[repr(u32)]
/// The scope for the authentication being re-used:
/// - Tty: valid for all future invocations in this TTY
/// - PPid: valid for all future invocations under the current parent
pub enum AuthenticationScope {
    Tty = HARDENED_ENUM_VALUE_0,
    PPid = HARDENED_ENUM_VALUE_1,
}

impl Judgement {
    pub fn authorization(&self) -> Authorization<Restrictions<'_>> {
        // NOTE: we should add conditional compilation to the DSL; this avoids getting
        // an unused warning message
        #[cfg(not(feature = "apparmor"))]
        let _ = &self.settings.apparmor_profile();

        if let Some(tag) = &self.flags {
            Authorization::Allowed(
                self.settings.to_auth(tag),
                Restrictions {
                    use_pty: self.settings.use_pty(),
                    trust_environment: match tag.env {
                        EnvironmentControl::Implicit => self.settings.setenv(),
                        EnvironmentControl::Setenv => true,
                        EnvironmentControl::Nosetenv => false,
                    },
                    noexec: match tag.noexec {
                        ExecControl::Implicit => self.settings.noexec(),
                        ExecControl::Exec => false,
                        ExecControl::Noexec => true,
                    },
                    env_keep: self.settings.env_keep(),
                    env_check: self.settings.env_check(),
                    chdir: match tag.cwd.clone().or_else(|| {
                        // a `runcwd` default acts as the working directory when no explicit CWD was set
                        self.settings.runcwd().and_then(|s| {
                            super::basic_parser::Token::construct(String::from(s)).ok()
                        })
                    }) {
                        None => DirChange::Strict(None),
                        Some(super::ChDir::Any) => DirChange::Any,
                        Some(super::ChDir::Path(path)) => DirChange::Strict(Some(path)),
                    },
                    path: self.settings.secure_path(),
                    umask: {
                        let mask = self
                            .settings
                            .umask()
                            .try_into()
                            .expect("the umask parser should have prevented overflow");
                        if mask == 0o777 {
                            Umask::Preserve
                        } else if self.settings.umask_override() {
                            Umask::Override(mask)
                        } else {
                            Umask::Extend(mask)
                        }
                    },
                    log: if self.settings.log_allowed() {
                        Logging::Auth
                    } else {
                        Logging::Disabled
                    },
                    #[cfg(feature = "apparmor")]
                    apparmor_profile: tag
                        .apparmor_profile
                        .as_deref()
                        .or(self.settings.apparmor_profile())
                        .map(|x| x.to_string()),
                },
            )
        } else {
            Authorization::Forbidden
        }
    }

    pub(crate) fn preferred_editor(&self) -> (PathBuf, Vec<OsString>) {
        // if no editor could be selected, fall back to /bin/vi;
        // note that /bin/vi is also likely to have been tried as part of
        // the "editor" setting, so this is a last-resort
        super::select_editor(&self.settings, true)
            .unwrap_or_else(|| (std::path::PathBuf::from("/usr/bin/vi"), vec![]))
    }
}

impl Sudoers {
    pub fn search_path(
        &mut self,
        on_host: &Hostname,
        current_user: &User,
        target_user: &User,
    ) -> Option<&str> {
        self.specify_host_user_runas(on_host, current_user, Some(target_user));
        self.settings.secure_path()
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::sudoers::{
        ast::{Authenticate, Tag},
        tokens::ChDir,
    };

    impl Judgement {
        fn mod_flag(&mut self, mut modify: impl FnMut(&mut Tag)) {
            let mut tag: Tag = self.flags.clone().unwrap_or_default();
            modify(&mut tag);
            self.flags = Some(tag);
        }
    }

    #[test]
    fn authority_xlat_test() {
        let mut judge: Judgement = Default::default();
        assert_eq!(judge.authorization(), Authorization::Forbidden);
        judge.mod_flag(|tag| tag.authenticate = Authenticate::Passwd);
        let Authorization::Allowed(auth, restrictions) = judge.authorization() else {
            panic!();
        };
        assert_eq!(
            auth,
            Authentication {
                must_authenticate: true,
                allowed_attempts: 3,
                prior_validity: Duration::from_secs(15 * 60),
                credential: AuthenticatingUser::InvokingUser,
                pwfeedback: true,
                noninteractive_auth: false,
                password_timeout: Some(Duration::from_secs(300)),
                scope: AuthenticationScope::Tty,
            },
        );

        let mut judge = judge.clone();
        judge.mod_flag(|tag| tag.authenticate = Authenticate::Nopasswd);
        let Authorization::Allowed(auth, restrictions2) = judge.authorization() else {
            panic!();
        };
        assert_eq!(
            auth,
            Authentication {
                must_authenticate: false,
                allowed_attempts: 3,
                prior_validity: Duration::from_secs(15 * 60),
                credential: AuthenticatingUser::InvokingUser,
                pwfeedback: true,
                noninteractive_auth: false,
                password_timeout: Some(Duration::from_secs(300)),
                scope: AuthenticationScope::Tty,
            },
        );
        assert_eq!(restrictions, restrictions2);
    }

    #[test]
    fn chdir_test() {
        let mut judge = Judgement {
            flags: Some(Tag::default()),
            ..Default::default()
        };
        fn chdir(judge: &mut Judgement) -> DirChange {
            let Authorization::Allowed(_, ctl) = judge.authorization() else {
                panic!()
            };
            ctl.chdir
        }
        assert_eq!(chdir(&mut judge), DirChange::Strict(None));
        judge.mod_flag(|tag| tag.cwd = Some(ChDir::Any));
        assert_eq!(chdir(&mut judge), DirChange::Any);
        judge.mod_flag(|tag| tag.cwd = Some(ChDir::Path("/usr".into())));
        assert_eq!(chdir(&mut judge), (DirChange::Strict(Some("/usr".into()))));
        judge.mod_flag(|tag| tag.cwd = Some(ChDir::Path("/bin".into())));
        assert_eq!(chdir(&mut judge), (DirChange::Strict(Some("/bin".into()))));
    }

    fn set_text(judge: &mut Judgement, name: &str, value: &str) {
        let Some(crate::defaults::SettingKind::Text(setting)) = crate::defaults::set(name) else {
            panic!()
        };
        crate::defaults::check_text(setting, value)
            .unwrap()
            .apply(&mut judge.settings);
    }

    fn set_integer(judge: &mut Judgement, name: &str, value: &str) {
        let Some(crate::defaults::SettingKind::Integer(setting)) = crate::defaults::set(name)
        else {
            panic!()
        };
        crate::defaults::check_integer(setting, value)
            .unwrap()
            .apply(&mut judge.settings);
    }

    fn set_flag(judge: &mut Judgement, name: &str) {
        let Some(crate::defaults::SettingKind::Flag(f)) = crate::defaults::set(name) else {
            panic!()
        };
        f.apply(&mut judge.settings);
    }

    fn negate(judge: &mut Judgement, name: &str) {
        crate::defaults::negate(name)
            .unwrap()
            .apply(&mut judge.settings);
    }

    #[test]
    fn runcwd_test() {
        let mut judge = Judgement {
            flags: Some(Tag::default()),
            ..Default::default()
        };
        fn chdir(judge: &Judgement) -> DirChange {
            let Authorization::Allowed(_, ctl) = judge.authorization() else {
                panic!()
            };
            ctl.chdir
        }
        set_text(&mut judge, "runcwd", "*");
        assert_eq!(chdir(&judge), DirChange::Any);
        set_text(&mut judge, "runcwd", "/tmp");
        assert_eq!(chdir(&judge), DirChange::Strict(Some("/tmp".into())));
        set_text(&mut judge, "runcwd", "~");
        assert_eq!(chdir(&judge), DirChange::Strict(Some("~".into())));
        // unlike a CWD= tag, the default is not checked by the token parser (first character)
        set_text(&mut judge, "runcwd", "relative");
        assert_eq!(chdir(&judge), DirChange::Strict(Some("relative".into())));
        // a value containing '*' other than "*" itself is dropped
        set_text(&mut judge, "runcwd", "/tmp/*");
        assert_eq!(chdir(&judge), DirChange::Strict(None));
        // so is a value with a NUL character
        set_text(&mut judge, "runcwd", "/tmp\0");
        assert_eq!(chdir(&judge), DirChange::Strict(None));
        // an explicit CWD tag wins over the default
        set_text(&mut judge, "runcwd", "/tmp");
        judge.mod_flag(|tag| tag.cwd = Some(ChDir::Path("/usr".into())));
        assert_eq!(chdir(&judge), DirChange::Strict(Some("/usr".into())));
        judge.mod_flag(|tag| tag.cwd = Some(ChDir::Any));
        assert_eq!(chdir(&judge), DirChange::Any);
        judge.mod_flag(|tag| tag.cwd = None);
        negate(&mut judge, "runcwd");
        assert_eq!(chdir(&judge), DirChange::Strict(None));
    }

    #[test]
    fn restrictions_test() {
        let mut judge = Judgement {
            flags: Some(Tag::default()),
            ..Default::default()
        };
        fn get(judge: &Judgement) -> (Authentication, bool, bool, Umask, Logging) {
            let Authorization::Allowed(auth, ctl) = judge.authorization() else {
                panic!()
            };
            (auth, ctl.trust_environment, ctl.noexec, ctl.umask, ctl.log)
        }

        let (auth, setenv, noexec, umask, log) = get(&judge);
        assert_eq!(auth.credential, AuthenticatingUser::InvokingUser);
        assert!(!setenv && !noexec);
        assert_eq!(umask, Umask::Extend(0o022));
        assert_eq!(log, Logging::Auth);

        set_flag(&mut judge, "setenv");
        set_flag(&mut judge, "noexec");
        set_flag(&mut judge, "targetpw");
        set_integer(&mut judge, "umask", "077");
        negate(&mut judge, "log_allowed");
        let (auth, setenv, noexec, umask, log) = get(&judge);
        assert_eq!(auth.credential, AuthenticatingUser::TargetUser);
        assert!(setenv && noexec);
        assert_eq!(umask, Umask::Extend(0o077));
        assert_eq!(log, Logging::Disabled);

        // explicit tags win over the defaults
        judge.mod_flag(|tag| {
            tag.env = EnvironmentControl::Nosetenv;
            tag.noexec = ExecControl::Exec;
        });
        set_flag(&mut judge, "rootpw");
        set_flag(&mut judge, "umask_override");
        let (auth, setenv, noexec, umask, _) = get(&judge);
        assert_eq!(auth.credential, AuthenticatingUser::Root);
        assert!(!setenv && !noexec);
        assert_eq!(umask, Umask::Override(0o077));

        negate(&mut judge, "setenv");
        negate(&mut judge, "noexec");
        judge.mod_flag(|tag| {
            tag.env = EnvironmentControl::Setenv;
            tag.noexec = ExecControl::Noexec;
        });
        set_integer(&mut judge, "umask", "0777");
        let (_, setenv, noexec, umask, _) = get(&judge);
        assert!(setenv && noexec);
        assert_eq!(umask, Umask::Preserve);
    }
}
