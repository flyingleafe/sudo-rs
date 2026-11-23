#![forbid(unsafe_code)]
use std::collections::HashSet;

#[cfg_attr(test, derive(Clone, Copy, Debug, PartialEq, Eq))]
pub enum ListMode {
    Set,
    Add,
    Del,
}

/// How a setting takes its value in a `Defaults` line (see `set`): a flag takes none and carries
/// the modifier that sets it; the other kinds carry the setting, and `check_integer`,
/// `check_text` and `build_list` turn a value into its modifier.
#[repr(u32)]
#[cfg_attr(test, derive(Debug, PartialEq, Eq))]
pub enum SettingKind {
    Flag(SettingsModifier) = crate::common::HARDENED_ENUM_VALUE_0,
    Integer(IntegerSetting) = crate::common::HARDENED_ENUM_VALUE_1,
    Text(TextSetting) = crate::common::HARDENED_ENUM_VALUE_2,
    List(ListSetting) = crate::common::HARDENED_ENUM_VALUE_3,
}

mod settings_dsl;
use settings_dsl::{
    apply_of, defaults, emit, ifdef, initializer_of, integer_check, kind_of, kind_tables,
    payload_of, referent_of, result_of, standard_negation, storage_of, text_check,
};

#[cfg(test)]
pub(crate) mod legacy;

pub const SYSTEM_EDITOR: &str = if cfg!(target_os = "linux") {
    "/usr/bin/editor:/usr/bin/nano:/usr/bin/vi"
} else {
    "/usr/bin/vi"
};

defaults! {
    always_query_group_plugin = false  #ignored
    always_set_home           = false  #ignored
    env_reset                 = true   #ignored
    fqdn                      = false  #ignored
    ignore_dot                = true   #ignored
    lecture                   = never (!= never) [always, once, never] #ignored
    mailerpath                = None (!= None) #ignored
    mail_badpass              = true   #ignored
    match_group_by_gid        = false  #ignored
    use_pty                   = true
    visiblepw                 = false  #ignored
    pwfeedback                = true
    rootpw                    = false
    targetpw                  = false
    noexec                    = false
    noninteractive_auth       = false

    log_allowed               = true
    log_denied                = true #ignored

    insults                   = false  #ignored

    setenv                    = false
    runcwd                    = None (!= None)
    apparmor_profile          = None (!= None)
    umask                     = 0o022 (!= 0o777) {octal_mode}
    umask_override            = false

    passwd_tries              = 3 [0..=1000]

    secure_path               = None (!= None)

    verifypw                  = all (!= never) [all, always, any, never] #ignored

    passwd_timeout            = (5*60) (!= 0) {fractional_minutes}
    timestamp_timeout         = (15*60) (!= 0) {fractional_minutes}
    timestamp_type            = tty [tty, ppid]

    editor                    = SYSTEM_EDITOR
    env_editor                = true

    env_keep                  = ["COLORS", "DISPLAY", "HOSTNAME", "KRB5CCNAME", "LS_COLORS", "PATH",
                                 "PS1", "PS2", "XAUTHORITY", "XAUTHORIZATION", "XDG_CURRENT_DESKTOP"]

    env_check                 = ["COLORTERM", "LANG", "LANGUAGE", "LC_*", "LINGUAS", "TERM", "TZ"]

    env_delete                = ["IFS", "CDPATH", "LOCALDOMAIN", "RES_OPTIONS", "HOSTALIASES",
                                "NLSPATH", "PATH_LOCALE", "LD_*", "_RLD*", "TERMINFO", "TERMINFO_DIRS",
                                "TERMPATH", "TERMCAP", "ENV", "BASH_ENV", "PS4", "GLOBIGNORE",
                                "BASHOPTS", "SHELLOPTS", "JAVA_TOOL_OPTIONS", "PERLIO_DEBUG",
                                "PERLLIB", "PERL5LIB", "PERL5OPT", "PERL5DB", "FPATH", "NULLCMD",
                                "READNULLCMD", "ZDOTDIR", "TMPPREFIX", "PYTHONHOME", "PYTHONPATH",
                                "PYTHONINSPECT", "PYTHONUSERBASE", "RUBYLIB", "RUBYOPT", "*=()*"] #ignored
}

/// The effect of a modifier of the list `set`: `items` replace it, are added to it, or are
/// removed from it. (`HashSet::new` and `insert` build the set that `collect` and `extend`
/// build.)
fn apply_list(set: &mut HashSet<String>, mode: ListMode, items: Vec<String>) {
    match mode {
        ListMode::Set => {
            *set = HashSet::new();
            for item in items {
                set.insert(item);
            }
        }
        ListMode::Add => {
            for item in items {
                set.insert(item);
            }
        }
        ListMode::Del => {
            for key in items {
                set.remove(&key);
            }
        }
    }
}

/// The integer denoted by `text` in base `radix`, if it lies in `first..=last`.
fn integer_in_range(text: &str, radix: u32, first: u64, last: u64) -> Option<u64> {
    match u64::from_str_radix(text, radix) {
        Ok(value) => {
            if first <= value && value <= last {
                Some(value)
            } else {
                None
            }
        }
        Err(_) => None,
    }
}

/// The position of the first `.` in `input`, or its length if there is none.
fn find_dot(input: &[u8]) -> usize {
    let mut dot = input.len();
    let mut i = 0;
    while i < input.len() && dot == input.len() {
        if input[i] == b'.' {
            dot = i;
        }
        i += 1;
    }
    dot
}

/// The value of `input.parse::<u64>()` (which is `u64::from_str_radix(input, 10)`), if it is a
/// number.
#[allow(clippy::from_str_radix_10)]
fn decimal(input: &str) -> Option<u64> {
    u64::from_str_radix(input, 10).ok()
}

fn octal_mode(input: &str) -> Option<u64> {
    // `input.strip_prefix('0')`: '0' is one byte
    let bytes = input.as_bytes();
    if bytes.is_empty() || bytes[0] != b'0' {
        return None;
    }
    let (_, digits) = input.split_at(1);
    match <libc::mode_t>::from_str_radix(digits, 8) {
        Ok(mode) => Some(u64::from(mode)),
        Err(_) => None,
    }
}

/// A custom parser to parse seconds as fractional "minutes", the format used by
/// passwd_timeout and timestamp_timeout.
// no `?` on `Option`: Aeneas has no model of `Try` for `Option`
#[allow(clippy::question_mark)]
fn fractional_minutes(input: &str) -> Option<u64> {
    // `input.split_once('.')`: '.' is one byte
    let dot = find_dot(input.as_bytes());
    if dot < input.len() {
        let (integral, rest) = input.split_at(dot);
        let (_, fractional) = rest.split_at(1);
        // - 'input' is maximally 18 characters, making fractional.len() at most 17;
        //   1e17 < 2**63, so the definition of 'shift' will not overflow.
        // - for the same reason, if both parses in the definition of 'seconds' succeed,
        //   we will have constructed an integer < 1e17.
        //-  1e17 * 60 = 6e18 < 9e18 < 2**63, so the final line also will not overflow
        let shift = match u32::try_from(fractional.len()) {
            Ok(digits) => 10u64.pow(digits),
            Err(_) => return None,
        };
        let scaled = match decimal(integral) {
            Some(integral) => integral * shift,
            None => return None,
        };
        let seconds = match decimal(fractional) {
            Some(fractional) => scaled + fractional,
            None => return None,
        };

        Some(seconds * 60 / shift)
    } else {
        match decimal(input) {
            Some(minutes) => minutes.checked_mul(60),
            None => None,
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[allow(clippy::bool_assert_comparison)]
    #[test]
    fn check() {
        let mut def = Settings::default();
        assert_eq! { def.always_query_group_plugin, false };
        assert_eq! { def.always_set_home, false };
        assert_eq! { def.env_reset, true };
        assert_eq! { def.mail_badpass, true };
        assert_eq! { def.match_group_by_gid, false };
        assert_eq! { def.use_pty, true };
        assert_eq! { def.visiblepw, false };
        assert_eq! { def.env_editor, true };
        assert_eq! { def.passwd_tries, 3 };
        assert_eq! { def.secure_path, None };
        assert_eq! { def.env_check, ["COLORTERM", "LANG", "LANGUAGE", "LC_*", "LINGUAS", "TERM", "TZ"].iter().map(|s| s.to_string()).collect() };
        assert_eq! { def.verifypw, enums::verifypw::all };

        negate("env_check").unwrap().apply(&mut def);
        negate("env_reset").unwrap().apply(&mut def);
        negate("secure_path").unwrap().apply(&mut def);
        negate("verifypw").unwrap().apply(&mut def);
        assert_eq! { def.always_query_group_plugin, false };
        assert_eq! { def.always_set_home, false };
        assert_eq! { def.env_reset, false };
        assert_eq! { def.mail_badpass, true };
        assert_eq! { def.match_group_by_gid, false };
        assert_eq! { def.use_pty, true };
        assert_eq! { def.visiblepw, false };
        assert_eq! { def.env_editor, true };
        assert_eq! { def.passwd_tries, 3 };
        assert_eq! { def.secure_path, None };
        assert! { def.env_check.is_empty() };
        assert_eq! { def.verifypw, enums::verifypw::never };

        let SettingKind::Text(f) = set("lecture").unwrap() else {
            panic!()
        };
        check_text(f, "always").unwrap().apply(&mut def);
        assert_eq! { def.lecture, enums::lecture::always };
        check_text(f, "once").unwrap().apply(&mut def);
        assert_eq! { def.lecture, enums::lecture::once };
        check_text(f, "never").unwrap().apply(&mut def);
        assert_eq! { def.lecture, enums::lecture::never};
        negate("lecture").unwrap().apply(&mut def);
        assert_eq! { def.lecture, enums::lecture::never };

        let SettingKind::Flag(f) = set("env_reset").unwrap() else {
            panic!()
        };
        f.apply(&mut def);
        let SettingKind::Text(f) = set("secure_path").unwrap() else {
            panic!()
        };
        check_text(f, "/bin").unwrap().apply(&mut def);
        let SettingKind::Integer(f) = set("passwd_tries").unwrap() else {
            panic!()
        };
        check_integer(f, "5").unwrap().apply(&mut def);
        let SettingKind::Text(f) = set("verifypw").unwrap() else {
            panic!()
        };
        check_text(f, "any").unwrap().apply(&mut def);
        let SettingKind::Integer(f) = set("timestamp_timeout").unwrap() else {
            panic!()
        };
        check_integer(f, "25.25").unwrap().apply(&mut def);
        assert_eq! { def.always_query_group_plugin, false };
        assert_eq! { def.always_set_home, false };
        assert_eq! { def.env_reset, true };
        assert_eq! { def.mail_badpass, true };
        assert_eq! { def.match_group_by_gid, false };
        assert_eq! { def.use_pty, true };
        assert_eq! { def.visiblepw, false };
        assert_eq! { def.env_editor, true };
        assert_eq! { def.passwd_tries, 5 };
        assert_eq! { def.timestamp_timeout, 25*60 + 60/4 };
        assert_eq! { def.secure_path, Some("/bin".into()) };
        assert! { def.env_check.is_empty() };
        assert_eq! { def.verifypw, enums::verifypw::any };

        assert!(set("notanoption").is_none());
        assert!(check_integer(f, "notanoption").is_none());
    }
}
