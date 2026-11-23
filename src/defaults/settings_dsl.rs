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
    ($id:ident, [ $($value: expr),* ]) => {{
        // Reserve for all entries, as collect did, without introducing iterator adapters.
        const LEN: usize = 0 $(+ { let _ = stringify!($value); 1 })*;
        let mut keys = std::collections::HashSet::with_capacity(LEN);
        $(keys.insert(String::from($value));)*
        keys
    }};
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

// the payload of a setting's variant of 'SettingsModifier': the new value of the setting, or for
// a list the change to make to it
macro_rules! payload_of {
    ($id:ident, true) => { bool };
    ($id:ident, false) => { bool };
    ($id:ident, [ $($value: expr),* ]) => { ($crate::defaults::ListMode, Vec<String>) };
    ($id:ident, $($spec: tt)*) => { storage_of!($id, $($spec)*) };
}

// the effect of a setting's variant of 'SettingsModifier' (in 'SettingsModifier::apply')
macro_rules! apply_of {
    ($obj:ident . $id:ident = $payload:ident; [ $($value: expr),* ]) => {{
        let (mode, items) = $payload;
        $crate::defaults::apply_list(&mut $obj.$id, mode, items)
    }};
    ($obj:ident . $id:ident = $payload:ident; $value: tt) => {
        $obj.$id = $payload
    };
}

// what 'fn set' returns for a setting
macro_rules! kind_of {
    ($id:ident, true) => {
        $crate::defaults::SettingKind::Flag($crate::defaults::SettingsModifier::$id(true))
    };
    ($id:ident, false) => {
        $crate::defaults::SettingKind::Flag($crate::defaults::SettingsModifier::$id(true))
    };
    ($id:ident, [ $($value: expr),* ]) => {
        $crate::defaults::SettingKind::List($crate::defaults::ListSetting::$id)
    };
    ($id:ident, =int $($spec: tt)*) => {
        $crate::defaults::SettingKind::Integer($crate::defaults::IntegerSetting::$id)
    };
    ($id:ident, $($spec: tt)*) => {
        $crate::defaults::SettingKind::Text($crate::defaults::TextSetting::$id)
    };
}

// what 'fn negate' returns for a setting that has no explicit negation: flags become false and
// lists empty; other settings cannot be negated
macro_rules! standard_negation {
    ($id:ident, true) => {
        Some($crate::defaults::SettingsModifier::$id(false))
    };
    ($id:ident, false) => {
        Some($crate::defaults::SettingsModifier::$id(false))
    };
    ($id:ident, [ $($value: expr),* ]) => {
        Some($crate::defaults::SettingsModifier::$id((
            $crate::defaults::ListMode::Set,
            Vec::new(),
        )))
    };
    ($id:ident, $($spec: tt)*) => {
        None
    };
}

// the arm of 'fn check_integer' for a setting
macro_rules! integer_check {
    ($id:ident, $text:ident; =int $first:literal ..= $last: literal $(@ $radix: expr)?; $value: tt) => {
        match $crate::defaults::integer_in_range($text, 10$(*0 + $radix)?, $first, $last) {
            Some(value) => Some($crate::defaults::SettingsModifier::$id(value)),
            None => None,
        }
    };
    ($id:ident, $text:ident; =int $fn: expr; $value: tt) => {
        match $fn($text) {
            Some(value) => Some($crate::defaults::SettingsModifier::$id(value)),
            None => None,
        }
    };
}

// the arm of 'fn check_text' for a setting
macro_rules! text_check {
    ($id:ident, $text:ident; $(=enum $key: ident;)+ $value: ident) => {
        match $text {
            $(
            stringify!($key) => Some($crate::defaults::SettingsModifier::$id($crate::defaults::enums::$id::$key)),
            )+
            _ => None,
        }
    };
    ($id:ident, $text:ident; None) => {
        Some($crate::defaults::SettingsModifier::$id(Some($text.into())))
    };
    ($id:ident, $text:ident; $value: expr) => {
        Some($crate::defaults::SettingsModifier::$id($text.into()))
    };
}

// sorts the settings by kind; for each kind that takes a value, generates the enumeration of
// its settings and the function that turns a value into a modifier
macro_rules! kind_tables {
    ([$({ $int:ident; $($int_spec: tt)* })*] [$({ $text:ident; $($text_spec: tt)* })*] [$($list:ident)*]) => {
        /// The settings that take an integer (`SettingKind::Integer`).
        #[allow(non_camel_case_types)]
        #[derive(Clone, Copy)]
        #[cfg_attr(test, derive(Debug, PartialEq, Eq))]
        pub(crate) enum IntegerSetting { $($int),* }

        /// The settings that take a text or one of a set of keywords (`SettingKind::Text`).
        #[allow(non_camel_case_types)]
        #[derive(Clone, Copy)]
        #[cfg_attr(test, derive(Debug, PartialEq, Eq))]
        pub(crate) enum TextSetting { $($text),* }

        /// The settings that are sets of strings (`SettingKind::List`).
        #[allow(non_camel_case_types)]
        #[derive(Clone, Copy)]
        #[cfg_attr(test, derive(Debug, PartialEq, Eq))]
        pub(crate) enum ListSetting { $($list),* }

        /// The modifier that gives `setting` the integer denoted by `text`, if that is a valid value.
        pub(crate) fn check_integer(setting: IntegerSetting, text: &str) -> Option<SettingsModifier> {
            match setting {
                $(IntegerSetting::$int => integer_check!($int, text; $($int_spec)*),)*
            }
        }

        /// The modifier that gives `setting` the value `text`, if that is a valid value.
        pub(crate) fn check_text(setting: TextSetting, text: &str) -> Option<SettingsModifier> {
            match setting {
                $(TextSetting::$text => text_check!($text, text; $($text_spec)*),)*
            }
        }

        /// The modifier that changes the list `setting` by `items` as `mode` says.
        pub(crate) fn build_list(setting: ListSetting, mode: ListMode, items: Vec<String>) -> SettingsModifier {
            match setting {
                $(ListSetting::$list => SettingsModifier::$list((mode, items)),)*
            }
        }
    };
    ($int:tt $text:tt $list:tt { $id:ident; true } $($rest: tt)*) => {
        kind_tables! { $int $text $list $($rest)* }
    };
    ($int:tt $text:tt $list:tt { $id:ident; false } $($rest: tt)*) => {
        kind_tables! { $int $text $list $($rest)* }
    };
    ([$($int: tt)*] $text:tt $list:tt { $id:ident; =int $($spec: tt)* } $($rest: tt)*) => {
        kind_tables! { [$($int)* { $id; =int $($spec)* }] $text $list $($rest)* }
    };
    ($int:tt $text:tt [$($list: tt)*] { $id:ident; [ $($value: tt)* ] } $($rest: tt)*) => {
        kind_tables! { $int $text [$($list)* $id] $($rest)* }
    };
    ($int:tt [$($text: tt)*] $list:tt { $id:ident; $($spec: tt)* } $($rest: tt)*) => {
        kind_tables! { $int [$($text)* { $id; $($spec)* }] $list $($rest)* }
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
        #[cfg_attr(test, derive(Debug, PartialEq, Eq))]
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

        /// A change to the settings made by one entry of a `Defaults` line: for every setting
        /// its new value, for a list the change to make to it (see `apply`).
        #[allow(non_camel_case_types)]
        #[cfg_attr(any(test, fuzzing), derive(Debug))]
        #[cfg_attr(test, derive(PartialEq, Eq))]
        pub(crate) enum SettingsModifier {
            $($name(payload_of!($name, $(=int $fn;)?$(=int $first;)?$($(=enum $key;)*)? $value))),*
        }

        impl SettingsModifier {
            pub(crate) fn apply(self, obj: &mut Settings) {
                match self {
                    $(Self::$name(value) => apply_of!(obj.$name = value; $value),)*
                }
            }
        }

        #[cfg(test)]
        pub(crate) use $crate::defaults::settings_dsl::dump_quoted as quote_for_dump;

        #[cfg(test)]
        impl SettingsModifier {
            /// A parsed modifier's setting name and payload, without applying it.
            pub(crate) fn dump_modifier(&self) -> String {
                use $crate::defaults::settings_dsl::DumpValue;
                match self {
                    $(Self::$name(value) => format!(
                        "(setting {} {})", stringify!($name), value.dump_value()
                    ),)*
                }
            }
        }

        /// Every setting.
        #[allow(non_camel_case_types)]
        #[derive(Clone, Copy)]
        #[cfg_attr(test, derive(Debug, PartialEq, Eq))]
        pub(crate) enum Setting {
            $($name),*
        }

        /// The position of every setting in the table.
        #[allow(non_upper_case_globals)]
        mod setting_index {
            $(pub(super) const $name: usize = super::Setting::$name as usize;)*
        }

        /// The setting at position `index` of the table, with its name.
        fn setting_at(index: usize) -> Option<(&'static str, Setting)> {
            match index {
                $(setting_index::$name => Some((stringify!($name), Setting::$name)),)*
                _ => None,
            }
        }

        /// The setting called `name`, if any. (A loop over the table rather than a `match` on
        /// strings: the comparisons of a string `match` nest one level per setting in the
        /// extracted code. Aeneas translates neither promoted constants nor references to a
        /// `static`, so the table is a function.)
        fn setting_named(name: &str) -> Option<Setting> {
            let mut found = None;
            let mut index = 0;
            let mut more = true;
            while more {
                match setting_at(index) {
                    Some((key, setting)) => {
                        if *key == *name {
                            found = Some(setting);
                            more = false;
                        }
                        index += 1;
                    }
                    None => more = false,
                }
            }
            found
        }

        pub(crate) fn negate(name: &str) -> Option<SettingsModifier> {
            match setting_named(name) {
                $(
                Some(Setting::$name) => ifdef!($($negate)?;
                    // this setting has an explicit negation; use that
                    Some(SettingsModifier::$name(initializer_of!($name, $(=int $fn;)?$(=int $first;)?$($(=enum $key;)*)? $($negate)?)));
                    // flags and lists have a standard negation (other settings have none)
                    standard_negation!($name, $value)
                ),
                )*
                None => None
            }
        }

        pub(crate) fn set(name: &str) -> Option<SettingKind> {
            match setting_named(name) {
            $(
                Some(Setting::$name) => Some(kind_of!($name, $(=int $fn;)?$(=int $first;)?$($(=enum $key;)*)? $value)),
            )*
                None => None,
            }
        }

        kind_tables! { [] [] [] $({ $name; $(=int $fn;)?$(=int $first ..= $last $(@ $radix)?;)?$($(=enum $key;)*)? $value })* }
    };
}

pub(super) use apply_of;
pub(super) use defaults;
pub(super) use emit;
pub(super) use ifdef;
pub(super) use initializer_of;
pub(super) use integer_check;
pub(super) use kind_of;
pub(super) use kind_tables;
pub(super) use payload_of;
pub(super) use referent_of;
pub(super) use result_of;
pub(super) use standard_negation;
pub(super) use storage_of;
pub(super) use text_check;

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
impl DumpValue for (super::ListMode, Vec<String>) {
    fn dump_value(&self) -> String {
        use super::ListMode;

        let (mode, items) = self;
        let mode = match mode {
            ListMode::Set => "set",
            ListMode::Add => "add",
            ListMode::Del => "del",
        };
        let mut out = format!("({mode} [");
        for (i, item) in items.iter().enumerate() {
            if i != 0 {
                out.push(' ');
            }
            out.push_str(&dump_quoted(item));
        }
        out.push_str("])");
        out
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
        negate("env_reset").unwrap().apply(&mut settings);
        assert_eq!(settings.dump_fields()[2], ("env_reset", "false".to_string()));
        assert_eq!(super::dump_quoted("a\"\\\u{e9}\n"), r#""a\"\\\u{e9}\u{a}""#);
    }
}
