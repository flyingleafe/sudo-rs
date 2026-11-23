macro_rules! storage_of {
    ($id:ident, true) => { bool };
    ($id:ident, false) => { bool };
    ($id:ident, [ $($value: expr),* ]) => { std::collections::HashSet<String> };
    ($id:ident, $(=int $check: expr;)+ $_: expr) => { u64 };
    ($id:ident, $(=enum $k: ident;)+ $_: ident) => { $crate::defaults::enums::$id };
    ($id:ident, None) => { Option<Box<str>> };
    ($id:ident, $_: expr) => { Box<str> };
}

macro_rules! referent_of {
    ($id:ident, true) => { bool };
    ($id:ident, false) => { bool };
    ($id:ident, [ $($value: expr),* ]) => { &std::collections::HashSet<String> };
    ($id:ident, $(=int $check: expr;)+ $_: expr) => { u64 };
    ($id:ident, $(=enum $k: ident;)+ $_: ident) => { $crate::defaults::enums::$id };
    ($id:ident, None) => { Option<&str> };
    ($id:ident, $_: expr) => { &str };
}

macro_rules! initializer_of {
    ($id:ident, true) => { true };
    ($id:ident, false) => { false };
    ($id:ident, [ $($value: expr),* ]) => { [$($value),*].into_iter().map(|s: &str| s.to_string()).collect::<std::collections::HashSet<_>>() };
    ($id:ident, $(=int $check: expr;)+ $value: expr) => { $value };
    ($id:ident, $(=enum $k: ident;)+ $value: ident) => { $crate::defaults::enums::$id::$value };
    ($id:ident, None) => { None };
    ($id:ident, $value: expr) => { $value.into() };
    ($id:ident, $($_: tt)*) => { return None };
}

macro_rules! result_of {
    ($id:expr, true) => {
        $id
    };
    ($id:expr, false) => {
        $id
    };
    ($id:expr, [ $($value: expr),* ]) => {
        &$id
    };
    ($id:expr, $(=value $k: expr;)+ $_: expr) => {
        $id
    };
    ($id:expr, None) => {
        $id.as_deref()
    };
    ($id:expr, $_: expr) => {
        $id.as_ref()
    };
}

macro_rules! modifier_of {
    ($id:ident, true) => {
        $crate::defaults::SettingKind::Flag(Box::new(move |obj: &mut Settings| obj.$id = true))
    };
    ($id:ident, false) => {
        $crate::defaults::SettingKind::Flag(Box::new(move |obj: &mut Settings| obj.$id = true))
    };
    ($id:ident, [ $($value: expr),* ]) => {
        $crate::defaults::SettingKind::List(|mode, list| {
            Box::new(move |obj: &mut Settings| match mode {
                ListMode::Set => obj.$id = list.into_iter().collect(),
                ListMode::Add => obj.$id.extend(list),
                ListMode::Del => {
                    for key in list {
                        obj.$id.remove(&key);
                    }
                }
            })
        })
    };
    ($id:ident, =int $first:literal ..= $last: literal $(@ $radix: literal)?; $value: expr) => {
        #[allow(clippy::from_str_radix_10)]
        $crate::defaults::SettingKind::Integer(|text| {
            u64::from_str_radix(text, 10$(*0 + $radix)?)
                .ok()
                .filter(|val| ($first ..= $last).contains(val))
                .map(|i| {
                    Box::new(move |obj: &mut Settings| obj.$id = i) as SettingsModifier
                })
        })
    };
    ($id:ident, =int $fn: expr; $value: expr) => {
        $crate::defaults::SettingKind::Integer(|text| {
            $fn(&text).map(|i| {
                Box::new(move |obj: &mut Settings| obj.$id = i) as SettingsModifier
            })
        })
    };
    ($id:ident, $(=int $check: expr;)+ $value: expr) => { compile_error!("bla") };
    ($id:ident, $(=enum $key: ident;)+ $value: ident) => {
        $crate::defaults::SettingKind::Text(|key| match key {
            $(
            stringify!($key) => {
                Some(Box::new(move |obj: &mut Settings| obj.$id = $crate::defaults::enums::$id::$key))
            },
            )*
            _ => None,
        })
    };
    ($id:ident, None) => {
        $crate::defaults::SettingKind::Text(|text| {
            let text = text.into();
            Some(Box::new(move |obj: &mut Settings| obj.$id = Some(text)))
        })
    };
    ($id:ident, $value: expr) => {
        $crate::defaults::SettingKind::Text(|text| {
            let text = text.into();
            Some(Box::new(move |obj: &mut Settings| obj.$id = text))
        })
    };
}

macro_rules! has_standard_negator {
    (true) => {
        true
    };
    (false) => {
        true
    };
    ([$($_: expr),*]) => {
        true
    };
    ($($_: tt)*) => {
        false
    };
}

// this macro allows us to help the compiler generate more efficient code in 'fn negate'
// and enables the way 'fn set' is made
macro_rules! ifdef {
    (; $then: expr; $else: expr) => {
        $else
    };
    ($($_: expr)+; $then: expr; $else: expr) => {
        $then
    };
}

macro_rules! emit {
    (ignored; $($def: tt)*) => { };
    ( ; $($def: tt)*) => { $($def)* };
}

macro_rules! defaults {
    ($($name:ident = $value:tt $((!= $negate:tt))? $([$($key:ident),*])? $([$first:literal ..= $last:literal$(; radix: $radix: expr)?])? $({$fn: expr})? $(#$attribute:ident)?)*) => {
        #[allow(non_camel_case_types)]
        pub(crate) mod enums {
            $($(
                #[derive(Clone,Copy,Debug,Default)]
                #[cfg_attr(test, derive(PartialEq, Eq))]
                pub(crate) enum $name { #[default] $($key),* }
            )?)*
        }

        #[derive(Clone)]
        pub(crate) struct Settings {
            $($name: storage_of!($name, $(=int $fn;)?$(=int $first;)?$($(=enum $key;)*)? $value)),*
        }

        // we add setters to make sure the settings-object is read only, and to generate 'unused variable' warnings
        impl Settings {
            $(
            emit! { $($attribute)?;
                pub(crate) fn $name(&self) -> referent_of!($name, $(=int $fn;)?$(=int $first;)?$($(=enum $key;)*)? $value) {
                    result_of!(self.$name, $(=value $fn;)?$(=value $first;)?$($(=value $key;)*)? $value)
                }
            }
            )*
        }

        // test-only observer: every field in declaration order, rendered by `DumpValue`
        #[cfg(any(test, fuzzing))]
        impl Settings {
            pub(crate) fn dump_fields(&self) -> Vec<(&'static str, String)> {
                use $crate::defaults::settings_dsl::DumpValue;
                vec![$((stringify!($name), self.$name.dump_value())),*]
            }
        }

        $($(
            #[cfg(any(test, fuzzing))]
            impl $crate::defaults::settings_dsl::DumpValue for enums::$name {
                fn dump_value(&self) -> String {
                    match self { $(Self::$key => stringify!($key)),* }.to_string()
                }
            }
        )?)*

        impl Default for Settings {
            fn default() -> Self {
                Self {
                    $($name: initializer_of!($name, $(=int $fn;)?$(=int $first;)?$($(=enum $key;)*)? $value)),*
                }
            }
        }

        pub(crate) fn negate(name: &str) -> Option<SettingsModifier> {
            match name {
                $(
                stringify!($name) if ifdef!($($negate)?; true; has_standard_negator!($value)) => {
                    let value = ifdef!($($negate)?;
                        // this setting has an explicit negation; use that
                        initializer_of!($name, $(=int $fn;)?$(=int $first;)?$($(=enum $key;)*)? $($negate)?);
                        // for bool and sets, false/empty works (for other types this is dead code)
                        Default::default()
                    );
                    Some(Box::new(move |obj: &mut Settings| obj.$name = value))
                },
                )*
                _ => None
            }
        }

        pub(crate) fn set(name: &str) -> Option<SettingKind> {
            match name {
            $(
                stringify!($name) => Some(modifier_of!($name, $(=int $fn;)?$(=int $first ..= $last $(@ $radix)?;)?$($(=enum $key;)*)? $value)),
            )*
                _ => None,
            }
        }
    };
}

pub(super) use defaults;
pub(super) use emit;
pub(super) use has_standard_negator;
pub(super) use ifdef;
pub(super) use initializer_of;
pub(super) use modifier_of;
pub(super) use referent_of;
pub(super) use result_of;
pub(super) use storage_of;

/// Test-only rendering of a setting's value (see `proofs/parser/DUMP.md`): `true`/`false`,
/// decimal integers, enum variant names, quoted strings, `none`/`(some "..")`, and sets as
/// `[..]` of quoted strings in ascending order.
#[cfg(any(test, fuzzing))]
pub(crate) trait DumpValue {
    fn dump_value(&self) -> String;
}

/// Quoted string: printable ASCII other than `"` and `\` verbatim, `\"`, `\\`, and `\u{h}` (lowercase
/// hexadecimal, no leading zeros) for every other code point.
#[cfg(any(test, fuzzing))]
pub(crate) fn dump_quoted(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            ' '..='~' => out.push(c),
            _ => out.push_str(&format!("\\u{{{:x}}}", c as u32)),
        }
    }
    out.push('"');
    out
}

#[cfg(any(test, fuzzing))]
impl DumpValue for bool {
    fn dump_value(&self) -> String {
        self.to_string()
    }
}

#[cfg(any(test, fuzzing))]
impl DumpValue for u64 {
    fn dump_value(&self) -> String {
        self.to_string()
    }
}

#[cfg(any(test, fuzzing))]
impl DumpValue for Box<str> {
    fn dump_value(&self) -> String {
        dump_quoted(self)
    }
}

#[cfg(any(test, fuzzing))]
impl DumpValue for Option<Box<str>> {
    fn dump_value(&self) -> String {
        match self {
            None => "none".to_string(),
            Some(s) => format!("(some {})", dump_quoted(s)),
        }
    }
}

#[cfg(any(test, fuzzing))]
impl DumpValue for std::collections::HashSet<String> {
    fn dump_value(&self) -> String {
        let mut items: Vec<&String> = self.iter().collect();
        items.sort();
        let items: Vec<String> = items.into_iter().map(|s| dump_quoted(s)).collect();
        format!("[{}]", items.join(" "))
    }
}

#[cfg(test)]
mod dump_test {
    use super::super::{Settings, negate};

    #[test]
    fn dump_fields_renders_every_field() {
        let mut settings = Settings::default();
        let fields = settings.dump_fields();
        assert_eq!(fields.len(), 35);
        assert_eq!(fields[0], ("always_query_group_plugin", "false".to_string()));
        assert_eq!(fields[5], ("lecture", "never".to_string()));
        assert_eq!(fields[6], ("mailerpath", "none".to_string()));
        assert_eq!(fields[22], ("umask", "18".to_string()));
        assert_eq!(
            fields[33],
            (
                "env_check",
                r#"["COLORTERM" "LANG" "LANGUAGE" "LC_*" "LINGUAS" "TERM" "TZ"]"#.to_string()
            )
        );
        negate("env_reset").unwrap()(&mut settings);
        assert_eq!(settings.dump_fields()[2], ("env_reset", "false".to_string()));
        assert_eq!(super::dump_quoted("a\"\\\u{e9}\n"), r#""a\"\\\u{e9}\u{a}""#);
    }
}
