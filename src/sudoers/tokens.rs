//! Various tokens

use crate::common::{SudoPath, SudoString};
use std::ffi::OsString;

use super::basic_parser::{ErrorKind, Many, Token, escape_char};
use super::char_stream::chars_of;
use crate::common::{HARDENED_ENUM_VALUE_0, HARDENED_ENUM_VALUE_1, HARDENED_ENUM_VALUE_2};

#[cfg_attr(test, derive(Clone, PartialEq, Eq))]
pub struct Username(pub SudoString);

/// A username consists of alphanumeric characters as well as ".", "-", "_".
/// Furthermore, it may contain embedded "@" characters (but not start with them) and end in a "$".
// See: https://systemd.io/USER_NAMES/
impl Token for Username {
    fn construct(text: String) -> Result<Self, ErrorKind> {
        // if a '$' occurs in a username, it has to be the final character
        if embedded_dollar(&chars_of(&text)) {
            return Err(ErrorKind::EmbeddedDollar);
        }

        match sudo_string(text) {
            Ok(name) => Ok(Username(name)),
            Err(kind) => Err(kind),
        }
    }

    fn accept(c: char) -> bool {
        c.is_alphanumeric() || c == '.' || c == '-' || c == '_' || c == '@' || c == '$'
    }

    fn accept_1st(c: char) -> bool {
        c != '@' && Self::accept(c)
    }

    const ALLOW_ESCAPE: bool = true;
    fn escaped(c: char) -> bool {
        c == escape_char()
            || c == '"'
            || c == ','
            || c == ':'
            || c == '='
            || c == '!'
            || c == '('
            || c == ')'
            || c == ' '
    }
}

/// `text.strip_suffix('$').unwrap_or(&text).contains('$')`: a `$` before the last character.
fn embedded_dollar(text: &[char]) -> bool {
    let len = text.len();
    let body_len = if len > 0 && text[len - 1] == '$' {
        len - 1
    } else {
        len
    };
    contains_char(text, body_len, '$')
}

/// Whether `c` occurs among the first `len` characters of `text`.
fn contains_char(text: &[char], len: usize, c: char) -> bool {
    let mut found = false;
    let mut i = 0;
    while !found && i < len {
        found = text[i] == c;
        i += 1;
    }
    found
}

/// `text == word`, characterwise.
fn equals_text(text: &[char], word: &[char]) -> bool {
    text.len() == word.len() && starts_with_text(text, word)
}

/// `text.starts_with(prefix)`, characterwise.
fn starts_with_text(text: &[char], prefix: &[char]) -> bool {
    let mut ok = prefix.len() <= text.len();
    let mut i = 0;
    while ok && i < prefix.len() {
        ok = text[i] == prefix[i];
        i += 1;
    }
    ok
}

/// `SudoString::new(text)`, with the error as an [ErrorKind]. Kept opaque for Charon
/// (`Cargo.toml`): `crate::common::string` is opaque, and the error type of `SudoString::new`
/// carries I/O errors; `FunsExternal.lean` models it.
pub(super) fn sudo_string(text: String) -> Result<SudoString, ErrorKind> {
    match SudoString::new(text) {
        Ok(name) => Ok(name),
        Err(crate::common::Error::StringValidation(text)) => Err(ErrorKind::NulInString(text)),
        Err(_) => unreachable!("SudoString::new only returns StringValidation"),
    }
}

impl Many for Username {}

pub struct DigitsU32(pub u32);

impl Token for DigitsU32 {
    const MAX_LEN: usize = 10;

    fn construct(s: String) -> Result<Self, ErrorKind> {
        match parse_u32(&chars_of(&s)) {
            Some(value) => Ok(DigitsU32(value)),
            None => Err(ErrorKind::ValueTooLarge),
        }
    }

    fn accept(c: char) -> bool {
        c.is_ascii_digit()
    }
}

/// `s.parse::<u32>().ok()` for a text of decimal digits (what the `DigitsU32` token accepts):
/// `None` on overflow, on an empty text and on any other character.
fn parse_u32(text: &[char]) -> Option<u32> {
    let mut value: u32 = 0;
    let mut ok = !text.is_empty();
    let mut i = 0;
    while ok && i < text.len() {
        match text[i].to_digit(10) {
            Some(digit) => match value.checked_mul(10) {
                Some(shifted) => match shifted.checked_add(digit) {
                    Some(sum) => value = sum,
                    None => ok = false,
                },
                None => ok = false,
            },
            None => ok = false,
        }
        i += 1;
    }
    if ok { Some(value) } else { None }
}

pub struct Numeric(pub String);

impl Token for Numeric {
    const MAX_LEN: usize = 18;

    fn construct(s: String) -> Result<Self, ErrorKind> {
        Ok(Numeric(s))
    }

    fn accept(c: char) -> bool {
        c.is_ascii_hexdigit() || c == '.'
    }
}

/// A hostname consists of alphanumeric characters and ".", "-",  "_"
pub struct Hostname(pub String);

impl std::ops::Deref for Hostname {
    type Target = String;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Token for Hostname {
    fn construct(text: String) -> Result<Self, ErrorKind> {
        // reject hostnames that resemble IPv4 addresses too closely
        // (IPv6 addresses will already be reject since ':' is not in the accept-set)
        if resembles_ipv4(&chars_of(&text)) {
            return Err(ErrorKind::HostIpv4);
        }

        Ok(Hostname(text))
    }

    fn accept(c: char) -> bool {
        c.is_ascii_alphanumeric() || c == '.' || c == '-' || c == '_'
    }
}

/// The IPv4 test of `Hostname::construct`. The legacy code was
/// ```text
/// let mut chunks = text.rsplitn(5, '.');
/// (&mut chunks).take(4).all(|part| !part.is_empty() && part.len() <= 3 && part.chars().all(char::is_numeric))
///     && chunks.next().is_none()
/// ```
/// that is: at most four `.`-separated parts, each of one to three bytes (UTF-8), all of them
/// numeric characters. One pass from the left; `ok` turns false as soon as that fails.
fn resembles_ipv4(text: &[char]) -> bool {
    let mut parts: usize = 1; // parts begun so far
    let mut part_len: usize = 0; // UTF-8 length of the current part
    let mut ok = true;
    let mut i = 0;
    while ok && i < text.len() {
        let c = text[i];
        if c == '.' {
            // the finished part is not empty, and a fifth part may not begin
            ok = part_len != 0 && parts < 4;
            parts += 1;
            part_len = 0;
        } else {
            part_len += c.len_utf8();
            ok = part_len <= 3 && c.is_numeric();
        }
        i += 1;
    }
    ok && part_len != 0
}

impl Many for Hostname {}

/// This enum allows items to use the ALL wildcard or be specified with aliases, or directly.
/// (Maybe this is better defined not as a Token but simply directly as an implementation of [crate::sudoers::basic_parser::Parse])
#[cfg_attr(test, derive(Debug, PartialEq, Eq))]
#[repr(u32)]
pub enum Meta<T> {
    All = HARDENED_ENUM_VALUE_0,
    Only(T) = HARDENED_ENUM_VALUE_1,
    Alias(String) = HARDENED_ENUM_VALUE_2,
}

impl<T: Token> Token for Meta<T> {
    fn construct(raw: String) -> Result<Self, ErrorKind> {
        // `T` may accept whitespace resulting in `raw` having trailing whitespace which would make
        // the first two checks below fail. the `cooked` version (the first `cooked_len`
        // characters, `raw.trim_end()`) has no trailing whitespace
        let chars = chars_of(&raw);
        let cooked_len = trimmed_len(&chars);

        if is_all(&chars, cooked_len) {
            Ok(Meta::All)
        } else if is_alias_name(&chars, cooked_len) {
            Ok(Meta::Alias(string_of(&chars, cooked_len)))
        } else {
            match T::construct(raw) {
                Ok(item) => Ok(Meta::Only(item)),
                Err(kind) => Err(kind),
            }
        }
    }

    const MAX_LEN: usize = T::MAX_LEN;

    fn accept(c: char) -> bool {
        T::accept(c) || c.is_uppercase()
    }
    fn accept_1st(c: char) -> bool {
        T::accept_1st(c) || c.is_uppercase()
    }

    const ALLOW_ESCAPE: bool = T::ALLOW_ESCAPE;

    fn escaped(c: char) -> bool {
        T::escaped(c)
    }
}

impl<T: Many> Many for Meta<T> {
    const SEP: char = T::SEP;
    const LIMIT: usize = T::LIMIT;
}

/// The length of `text.trim_end()`: the prefix up to the last character that is not whitespace.
fn trimmed_len(text: &[char]) -> usize {
    let mut len = 0;
    let mut i = 0;
    while i < text.len() {
        if !text[i].is_whitespace() {
            len = i + 1;
        }
        i += 1;
    }
    len
}

/// `cooked == "ALL"` for the first `len` characters of `text`.
fn is_all(text: &[char], len: usize) -> bool {
    len == 3 && text[0] == 'A' && text[1] == 'L' && text[2] == 'L'
}

/// `cooked.starts_with(AliasName::accept_1st) && cooked.chars().skip(1).all(AliasName::accept)`
/// for the first `len` characters of `text`.
fn is_alias_name(text: &[char], len: usize) -> bool {
    let mut ok = len > 0 && AliasName::accept_1st(text[0]);
    let mut i = 1;
    while ok && i < len {
        ok = AliasName::accept(text[i]);
        i += 1;
    }
    ok
}

/// The first `len` characters of `text` as a `String`.
fn string_of(text: &[char], len: usize) -> String {
    let mut s = String::new();
    let mut i = 0;
    while i < len {
        s.push(text[i]);
        i += 1;
    }
    s
}

/// An identifier that consists of only uppercase characters.
pub struct AliasName(pub String);

impl Token for AliasName {
    fn construct(s: String) -> Result<Self, ErrorKind> {
        Ok(AliasName(s))
    }

    fn accept_1st(c: char) -> bool {
        c.is_ascii_uppercase()
    }

    fn accept(c: char) -> bool {
        Self::accept_1st(c) || c.is_ascii_digit() || c == '_'
    }
}

/// A struct that represents valid command strings; this can contain escape sequences and are
/// limited to 1024 characters.
#[derive(PartialEq)]
#[repr(u32)]
pub enum Args {
    Prefix(Box<[OsString]>) = HARDENED_ENUM_VALUE_0,
    Exact(Box<[OsString]>) = HARDENED_ENUM_VALUE_1,
}

pub type Command = (SimpleCommand, Args);

/// A type that is specific to 'only commands', that can only happen in "Defaults!command" contexts;
/// which is essentially a subset of "Command"
pub type SimpleCommand = glob::Pattern;

impl Token for Command {
    const MAX_LEN: usize = 1024;

    fn construct(s: String) -> Result<Self, ErrorKind> {
        // the words of the token, `s.split_whitespace()`
        let chars = chars_of(&s);
        let words = split_words(&chars);
        // the tokenizer should not give us a token that consists of only whitespace
        let first = if !words.is_empty() {
            let (start, end) = words[0];
            Some(word_text(&chars, start, end))
        } else {
            None
        };
        let cmd = first.unwrap();
        let is_list = cmd.as_str() == "list";
        let n_args = words.len() - 1;

        let command = SimpleCommand::construct(cmd)?;

        // `argpat == Args::Prefix(Box::default())`: no arguments, or only the magic `*`
        let mut unrestricted = true;
        let argpat = if n_args == 0 {
            // if no arguments are mentioned, anything is allowed
            Args::Prefix(Vec::new().into_boxed_slice())
        } else {
            if chars[words[1].0] == '^' {
                // regular expressions are not supported, give an error message. If there is only a
                // terminating '$', this is not treated as a malformed regex by millersudo, so we don't
                // need to seperately check for that
                return Err(ErrorKind::RegexNotSupported);
            }
            let (last_start, last_end) = words[n_args];
            // the arguments that remain after the magic last one
            let mut kept = n_args;
            let mut prefix = false;
            if last_end - last_start == 1 && chars[last_start] == '*' {
                // if the magic * appears, any further arguments are allowed
                kept = n_args - 1;
                prefix = true;
            } else if last_end - last_start == 2
                && chars[last_start] == '"'
                && chars[last_start + 1] == '"'
            {
                // if the magic "" appears, no (further) arguments are allowed
                kept = n_args - 1;
            }

            if any_glob(&chars, &words, kept + 1) {
                return Err(ErrorKind::GlobInArguments);
            }

            let args = os_strings(&chars, &words, kept + 1).into_boxed_slice();
            unrestricted = prefix && kept == 0;
            if prefix {
                Args::Prefix(args)
            } else {
                Args::Exact(args)
            }
        };

        // `command.as_str() == "list"`: the pattern text of `SimpleCommand::construct` is `list`
        // exactly when its input is (every other result starts with `/` or is `sudoedit`)
        if is_list && !unrestricted {
            return Err(ErrorKind::ListArguments);
        }

        Ok((command, argpat))
    }

    // all commands start with "/" except "sudoedit" or "list"
    fn accept_1st(c: char) -> bool {
        SimpleCommand::accept_1st(c)
    }

    fn accept(c: char) -> bool {
        SimpleCommand::accept(c) || c == ' ' || c == '\t'
    }

    const ALLOW_ESCAPE: bool = SimpleCommand::ALLOW_ESCAPE;
    fn escaped(c: char) -> bool {
        SimpleCommand::escaped(c)
    }
}

/// `text.split_whitespace()` as ranges into `text`, without storing another copy of each word.
fn split_words(text: &[char]) -> Vec<(usize, usize)> {
    let mut words = Vec::new();
    let mut start = skip_word_class(text, 0, true);
    while start < text.len() {
        let end = skip_word_class(text, start, false);
        words.push((start, end));
        start = skip_word_class(text, end, true);
    }
    words
}

/// Advance over contiguous characters with the requested whitespace classification.
fn skip_word_class(text: &[char], mut pos: usize, whitespace: bool) -> usize {
    let mut more = true;
    while more && pos < text.len() {
        if text[pos].is_whitespace() == whitespace {
            pos += 1;
        } else {
            more = false;
        }
    }
    pos
}

/// Whether one of the arguments `words[1..end]` contains `?`, `*` or `[` (in UTF-8 these bytes
/// only occur as these characters).
fn any_glob(text: &[char], words: &[(usize, usize)], end: usize) -> bool {
    let mut found = false;
    let mut i = 1;
    while !found && i < end {
        let (start, stop) = words[i];
        found = has_glob_char(text, start, stop);
        i += 1;
    }
    found
}

fn has_glob_char(text: &[char], mut i: usize, end: usize) -> bool {
    let mut found = false;
    while !found && i < end {
        let c = text[i];
        if c == '?' || c == '*' || c == '[' {
            found = true;
        }
        i += 1;
    }
    found
}

/// Encode one word from its range in the token.
fn word_text(text: &[char], mut i: usize, end: usize) -> String {
    let mut word = String::new();
    while i < end {
        word.push(text[i]);
        i += 1;
    }
    word
}

/// The arguments `words[1..end]` as `OsString`s.
fn os_strings(text: &[char], words: &[(usize, usize)], end: usize) -> Vec<OsString> {
    let mut args = Vec::with_capacity(end - 1);
    let mut i = 1;
    while i < end {
        let (start, stop) = words[i];
        args.push(os_string(word_text(text, start, stop)));
        i += 1;
    }
    args
}

/// `OsString::from(text)`. The opaque Lean oracle takes UTF-8 text and returns the same
/// `OsString` type used by the decision proofs.
pub(super) fn os_string(text: String) -> OsString {
    OsString::from(text)
}

impl Token for SimpleCommand {
    const MAX_LEN: usize = 1024;

    fn construct(cmd: String) -> Result<Self, ErrorKind> {
        let chars = chars_of(&cmd);

        // detect the two edges cases
        if equals_text(&chars, &['l', 'i', 's', 't'])
            || equals_text(&chars, &['s', 'u', 'd', 'o', 'e', 'd', 'i', 't'])
        {
            return compile_pattern(&cmd);
        } else if starts_with_text(&chars, &['s', 'h', 'a']) {
            return Err(ErrorKind::DigestNotSupported);
        } else if starts_with_text(&chars, &['^']) {
            return Err(ErrorKind::RegexNotSupported);
        } else if !starts_with_text(&chars, &['/']) {
            return Err(ErrorKind::FullyQualifiedPath);
        }

        // record if the cmd ends in a slash and remove it if it does (`cmd` starts with '/')
        let len = chars.len();
        let is_dir = chars[len - 1] == '/';
        let mut cmd = if is_dir { string_of(&chars, len - 1) } else { cmd };

        // canonicalize path (if possible)
        match canonical(&cmd) {
            Canonical::Unresolved => {}
            Canonical::Resolved(real_cmd) => cmd = real_cmd,
            Canonical::NotUtf8 => return Err(ErrorKind::NonUtf8Path),
        }

        // if the cmd ends with a slash, any command in that directory is allowed
        if is_dir {
            cmd.push('/');
            cmd.push('*');
        }

        compile_pattern(&cmd)
    }

    // all commands start with "/" except "sudoedit" or "list"
    fn accept_1st(c: char) -> bool {
        c == '/' || c == 's' || c == 'l'
    }

    fn accept(c: char) -> bool {
        // '=' is allowed both escaped and un-escaped
        (!Self::escaped(c) && !c.is_control()) || c == '='
    }

    const ALLOW_ESCAPE: bool = true;
    fn escaped(c: char) -> bool {
        c == escape_char() || c == ',' || c == ':' || c == '=' || c == '#' || c == ' '
    }
}

/// The outcome of `common::resolve::canonicalize` on a command path.
pub enum Canonical {
    /// `canonicalize` failed: the path is kept as written
    Unresolved,
    /// the canonical path
    Resolved(String),
    /// the canonical path is not UTF-8
    NotUtf8,
}

/// `common::resolve::canonicalize(path)` and `to_str` of the result: file-system state. Kept
/// opaque for Charon (`Cargo.toml`); an `opaque` constant (oracle) in `FunsExternal.lean`.
#[allow(clippy::ptr_arg)] // `&String`, not `&str`: the model works on the Lean `String`
pub(super) fn canonical(path: &String) -> Canonical {
    match crate::common::resolve::canonicalize(path) {
        Err(_) => Canonical::Unresolved,
        Ok(real_cmd) => match real_cmd.to_str() {
            Some(text) => Canonical::Resolved(text.to_string()),
            None => Canonical::NotUtf8,
        },
    }
}

/// `glob::Pattern::new(text)`, its error rendered as in the legacy parser. Kept opaque for
/// Charon (`Cargo.toml`); an `opaque` constant (oracle) in `FunsExternal.lean`.
#[allow(clippy::ptr_arg)] // `&String`, not `&str`: the model works on the Lean `String`
pub(super) fn compile_pattern(text: &String) -> Result<glob::Pattern, ErrorKind> {
    match glob::Pattern::new(text) {
        Ok(pattern) => Ok(pattern),
        Err(error) => Err(ErrorKind::WildcardPattern(error.to_string())),
    }
}

impl Many for Command {}
impl Many for SimpleCommand {}

pub struct DefaultName(pub String);

impl Token for DefaultName {
    fn construct(text: String) -> Result<Self, ErrorKind> {
        Ok(DefaultName(text))
    }

    fn accept(c: char) -> bool {
        c.is_ascii_alphanumeric() || c == '_'
    }
}

pub struct EnvVar(pub String);

impl Token for EnvVar {
    fn construct(text: String) -> Result<Self, ErrorKind> {
        Ok(EnvVar(text))
    }

    fn accept(c: char) -> bool {
        !c.is_control() && !c.is_whitespace() && !Self::escaped(c)
    }

    const ALLOW_ESCAPE: bool = true;
    fn escaped(c: char) -> bool {
        matches!(c, '\\' | '=' | '#' | '"' | ',')
    }
}

/// A token with a very liberal inner tokenizer; compare StringParameter below
pub struct QuotedStringParameter(pub String);

impl Token for QuotedStringParameter {
    const MAX_LEN: usize = 1024;

    fn construct(s: String) -> Result<Self, ErrorKind> {
        Ok(Self(s))
    }

    fn accept(c: char) -> bool {
        !Self::escaped(c)
    }

    const ALLOW_ESCAPE: bool = true;
    fn escaped(c: char) -> bool {
        matches!(c, '\\' | '"') || c.is_control()
    }
}

/// Similar to QuotedStringParameter but treats backslashes differently
/// Compare IncludePath below.
// `@include "some/path"`
//           ^^^^^^^^^^^
pub struct QuotedIncludePath(pub String);

impl Token for QuotedIncludePath {
    const MAX_LEN: usize = 1024;

    fn construct(s: String) -> Result<Self, ErrorKind> {
        Ok(Self(s))
    }

    fn accept(c: char) -> bool {
        !Self::escaped(c)
    }

    const ALLOW_ESCAPE: bool = true;
    fn escaped(c: char) -> bool {
        matches!(c, '"') || c.is_control()
    }
}

pub struct IncludePath(pub String);

impl Token for IncludePath {
    const MAX_LEN: usize = 1024;

    fn construct(s: String) -> Result<Self, ErrorKind> {
        Ok(IncludePath(s))
    }

    fn accept(c: char) -> bool {
        !c.is_control() && !Self::escaped(c)
    }

    const ALLOW_ESCAPE: bool = true;
    fn escaped(c: char) -> bool {
        matches!(c, '\\' | '"' | ' ')
    }
}

// used for Defaults where quotes around some items are optional
pub struct StringParameter(pub String);

impl Token for StringParameter {
    const MAX_LEN: usize = QuotedStringParameter::MAX_LEN;

    fn construct(s: String) -> Result<Self, ErrorKind> {
        Ok(StringParameter(s))
    }

    fn accept(c: char) -> bool {
        !c.is_control() && !Self::escaped(c)
    }

    const ALLOW_ESCAPE: bool = true;
    fn escaped(c: char) -> bool {
        c == escape_char() || c == '"' || c == ' ' || c == '#' || c == ','
    }
}

// a path used for in CWD and CHROOT specs
#[derive(Clone, PartialEq)]
#[cfg_attr(test, derive(Debug, Eq))]
#[repr(u32)]
pub enum ChDir {
    Path(SudoPath) = HARDENED_ENUM_VALUE_0,
    Any = HARDENED_ENUM_VALUE_1,
}

impl Token for ChDir {
    const MAX_LEN: usize = 1024;

    fn construct(s: String) -> Result<Self, ErrorKind> {
        match classify_chdir(&s) {
            ChDirForm::Any => Ok(ChDir::Any),
            ChDirForm::ContainsStar => Err(ErrorKind::StarInPath),
            ChDirForm::Path => match sudo_path(s) {
                Ok(path) => Ok(ChDir::Path(path)),
                Err(kind) => Err(kind),
            },
        }
    }

    fn accept(c: char) -> bool {
        !c.is_control() && !Self::escaped(c)
    }

    fn accept_1st(c: char) -> bool {
        c == '~' || c == '/' || c == '*'
    }

    const ALLOW_ESCAPE: bool = true;
    fn escaped(c: char) -> bool {
        c == escape_char() || c == '"' || c == ' '
    }
}

enum ChDirForm {
    Any,
    ContainsStar,
    Path,
}

/// The two star checks use UTF-8 bytes directly. The model is total on Lean strings:
/// `construct_ok_eq` has no representability premise.
#[allow(clippy::ptr_arg)] // Match the existing Lean `String` model without a bounded `Str`.
fn classify_chdir(s: &String) -> ChDirForm {
    if s.as_bytes() == b"*" {
        ChDirForm::Any
    } else if s.as_bytes().contains(&b'*') {
        ChDirForm::ContainsStar
    } else {
        ChDirForm::Path
    }
}

/// The `String`-to-path boundary. Modelled without the platform-specific path conversions.
fn sudo_path(s: String) -> Result<SudoPath, ErrorKind> {
    match SudoPath::try_from(s) {
        Ok(path) => Ok(path),
        Err(crate::common::Error::PathValidation(path)) => {
            // The input to `try_from` was a `String`, so the rejected path is UTF-8.
            Err(ErrorKind::NulInPath(path.into_os_string().into_string().unwrap()))
        }
        Err(_) => unreachable!("SudoPath::try_from only returns PathValidation"),
    }
}

/// Some tokens that support escape characters also support being surrounded by quotes to avoid escaping directly.
pub struct Unquoted<T>(pub String, pub std::marker::PhantomData<T>);

impl<T: Token> Token for Unquoted<T> {
    const MAX_LEN: usize = 1024;

    fn construct(text: String) -> Result<Self, ErrorKind> {
        let chars = chars_of(&text);
        let mut quoted = String::new();
        let mut i = 0;
        while i < chars.len() {
            let ch = chars[i];
            if T::escaped(ch) {
                quoted.push(escape_char());
            }
            quoted.push(ch);
            i += 1;
        }

        Ok(Self(quoted, std::marker::PhantomData))
    }

    fn accept(c: char) -> bool {
        c != '"' && !c.is_control()
    }
}
