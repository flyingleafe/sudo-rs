//! Building blocks for a recursive descent LL(1) parsing method.
//!
//! The general idea is that a grammar (without left recursion) is translated to a series of
//! conditional and unconditional 'acceptance' methods.
//!
//! For example, assuming we have a parser for integers:
//!
//! sum = integer | integer + sum
//!
//! Can get translated as: (representing a sum as `LinkedList<u32>`):
//!
//! ```ignore
//! impl<T: Parse> Parse for LinkedList<T> {
//!     fn parse(stream: &mut CharStream) -> Parsed<LinkedList<T>> {
//!         let x = try_nonterminal(stream)?;
//!         let mut tail = if is_syntax('+', stream)? {
//!             expect_nonterminal(stream)?
//!         } else {
//!             LinkedList::new()
//!         };
//!         tail.push_front(x);
//!
//!         make(tail)
//!     }
//! }
//! ```
//!
//! This module is written in the restricted style of `proofs/parser/RESTYLE.md` (no closures,
//! no `fn` pointers, no `str` pattern API, no `?` or `return` inside loops, error kinds instead
//! of formatted messages), so that Charon and Aeneas translate it to Lean.

use std::fmt;

/// Type holding a parsed object (or error information if parsing failed)
pub type Parsed<T> = Result<T, Status>;

#[derive(Copy, Clone, PartialEq)]
#[cfg_attr(test, derive(Debug, Eq))]
pub struct Span {
    pub start: (usize, usize),
    pub end: (usize, usize),
}

#[cfg_attr(test, derive(Debug, PartialEq))]
pub enum Status {
    Fatal(Span, ErrorKind), // not recoverable; stream in inconsistent state
    Reject,                 // parsing failed by no input consumed
}

/// The cause of a fatal error. Its `Display` impl is the only place where the message text of a
/// diagnostic is produced.
#[cfg_attr(test, derive(Debug, PartialEq))]
pub enum ErrorKind {
    /// blanks at the end of the input
    SuperfluousWhitespace,
    /// a backslash in trailing whitespace that does not continue the line
    StrayEscape,
    /// `expect_syntax`: the expected character and the one found (`None` at the end of input)
    Expecting(char, Option<char>),
    /// `expect_nonterminal`: the description of the nonterminal
    Expected(&'static str),
    /// a backslash in a token that escapes nothing the token allows
    IllegalEscape,
    TokenTooLong,
    TooManyItems,
    MissingLineTerminator,
    GarbageAtEndOfLine,
    /// `Hostname::construct`: the text resembles an IPv4 address
    HostIpv4,
    /// `Username::construct`: a `$` that is not the last character
    EmbeddedDollar,
    /// `SudoString::new` rejected the text (a NUL character); the text
    NulInString(String),
    /// `SudoPath::try_from` rejected the text (a NUL character); the text
    NulInPath(String),
    /// `DigitsU32::construct`: not a `u32`
    ValueTooLarge,
    /// `Command`/`SimpleCommand::construct`: an argument or a command starting with `^`
    RegexNotSupported,
    /// `Command::construct`: `?`, `*` or `[` in an argument
    GlobInArguments,
    /// `Command::construct`: `list` with arguments
    ListArguments,
    /// `SimpleCommand::construct`: `glob::Pattern::new` failed; its message
    WildcardPattern(String),
    /// `SimpleCommand::construct`: a command starting with `sha`
    DigestNotSupported,
    /// `SimpleCommand::construct`: a command not starting with `/`
    FullyQualifiedPath,
    /// `SimpleCommand::construct`: the canonical path is not UTF-8
    NonUtf8Path,
    /// `ChDir::construct`: a `*` in a path
    StarInPath,
    /// `UserSpecifier::parse`: `+netgroup`
    NetgroupsNotSupported,
    /// `MetaOrTag::parse`: `INTERCEPT`, `CHROOT`, `TIMEOUT`, `NOTBEFORE`, `NOTAFTER`; the keyword
    TagNotSupported(String),
    /// `MetaOrTag::parse`: `ROLE`, `TYPE`
    SelinuxNotSupported,
    /// `MetaOrTag::parse`: `NAME=` with an unknown name; the name
    UnsupportedModifier(String),
    /// `CommandSpec::parse`: more than 127 tags
    TooManyTags,
    /// `Sudo::parse`: a directive keyword after other users (`User_Alias,foo ALIAS=def`)
    AmbiguousSyntax,
    /// `parse_include`: a directive other than `include`/`includedir` (`socket`)
    UnknownDirective,
    /// `parse_include`: blanks after an unquoted path
    QuotesAroundFilenames,
    /// `Def<T>::parse`: a reserved word as the alias name; the word
    ReservedAlias(String),
    /// `SettingsModifier::parse`: `!name` for a setting that has no negation; the name
    CannotUseInBoolean(String),
    /// `SettingsModifier::parse`: an unknown setting name; the name
    UnknownSetting(String),
    /// `SettingsModifier::parse`: `name+=`/`name-=` for a setting that is not a list; the name
    NotAListParameter(String),
    /// `SettingsModifier::parse`: `name=` for a flag; the name
    CannotAssignBoolean(String),
    /// `SettingsModifier::parse`: `name` without a value for a setting that is not a flag;
    /// the name
    NotABooleanSetting(String),
    /// `SettingsModifier::parse`: a value a checker rejected; the value and the setting name
    InvalidSettingValue(String, String),
    /// `SettingsModifier::parse`: more than 127 entries in a quoted variable list
    EnvironmentListTooLong,
    /// `SettingsModifier::parse`: `""`
    EmptyStringNotAllowed,
    /// `SettingsModifier::parse`: an unquoted `VAR=value`
    QuotesRequiredForVarValue,
    /// An already formatted message. No production of the live parser produces it: it is test
    /// scaffolding for the legacy `Defaults` parser copy in `test/legacy_defaults.rs` (which
    /// compares the closure-based modifiers with the data-based ones) and for the test-only
    /// `expect_complete`.
    #[allow(dead_code)]
    Message(String),
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ErrorKind::SuperfluousWhitespace => f.write_str("superfluous whitespace"),
            ErrorKind::StrayEscape => f.write_str("stray escape sequence"),
            ErrorKind::Expecting(syntax, Some(c)) => {
                write!(f, "expecting '{syntax}' but found '{c}'")
            }
            ErrorKind::Expecting(syntax, None) => write!(f, "expecting '{syntax}' but found 'EOF'"),
            ErrorKind::Expected(description) => write!(f, "expected {description}"),
            ErrorKind::IllegalEscape => f.write_str("illegal escape sequence"),
            ErrorKind::TokenTooLong => f.write_str("token exceeds maximum length"),
            ErrorKind::TooManyItems => f.write_str("too many items in list"),
            ErrorKind::MissingLineTerminator => {
                f.write_str("missing line terminator at end of file")
            }
            ErrorKind::GarbageAtEndOfLine => f.write_str("garbage at end of line"),
            ErrorKind::HostIpv4 => f.write_str("hosts cannot be specified using an IPv4 address"),
            ErrorKind::EmbeddedDollar => f.write_str("embedded $ in username"),
            ErrorKind::NulInString(text) => {
                fmt::Display::fmt(&crate::common::Error::StringValidation(text.clone()), f)
            }
            ErrorKind::NulInPath(text) => {
                fmt::Display::fmt(&crate::common::Error::PathValidation(text.into()), f)
            }
            ErrorKind::ValueTooLarge => f.write_str("value too large"),
            ErrorKind::RegexNotSupported => f.write_str("regular expressions are not supported"),
            ErrorKind::GlobInArguments => {
                f.write_str("glob patterns are not allowed in command arguments")
            }
            ErrorKind::ListArguments => f.write_str("list does not take arguments"),
            ErrorKind::WildcardPattern(error) => write!(f, "wildcard pattern error {error}"),
            ErrorKind::DigestNotSupported => f.write_str("digest specifications are not supported"),
            ErrorKind::FullyQualifiedPath => f.write_str("fully qualified path needed"),
            ErrorKind::NonUtf8Path => f.write_str("non-UTF8 characters in filesystem"),
            ErrorKind::StarInPath => f.write_str("path cannot contain '*'"),
            ErrorKind::NetgroupsNotSupported => f.write_str("netgroups are not supported yet"),
            ErrorKind::TagNotSupported(spec) => write!(f, "{spec} is not supported by sudo-rs"),
            ErrorKind::SelinuxNotSupported => {
                f.write_str("SELinux role based access control is not yet supported by sudo-rs")
            }
            ErrorKind::UnsupportedModifier(alias) => write!(f, "unsupported modifier '{alias}'"),
            ErrorKind::TooManyTags => f.write_str("too many tags for command specifier"),
            ErrorKind::AmbiguousSyntax => f.write_str("ambiguous syntax"),
            ErrorKind::UnknownDirective => f.write_str("unknown directive"),
            ErrorKind::QuotesAroundFilenames => {
                f.write_str("use quotes around filenames or escape whitespace")
            }
            ErrorKind::ReservedAlias(name) => {
                write!(f, "reserved word {name} used as an alias name")
            }
            ErrorKind::CannotUseInBoolean(name) => {
                write!(f, "'{name}' cannot be used in a boolean context")
            }
            ErrorKind::UnknownSetting(name) => write!(f, "unknown setting: '{name}'"),
            ErrorKind::NotAListParameter(name) => write!(f, "{name} is not a list parameter"),
            ErrorKind::CannotAssignBoolean(name) => {
                write!(f, "can't assign to boolean setting '{name}'")
            }
            ErrorKind::NotABooleanSetting(name) => write!(f, "'{name}' is not a boolean setting"),
            ErrorKind::InvalidSettingValue(value, name) => {
                write!(f, "'{value}' is not a valid value for {name}")
            }
            ErrorKind::EnvironmentListTooLong => {
                f.write_str("environment variable list too long")
            }
            ErrorKind::EmptyStringNotAllowed => f.write_str("empty string not allowed"),
            ErrorKind::QuotesRequiredForVarValue => {
                f.write_str("double quotes are required for VAR=value pairs")
            }
            ErrorKind::Message(message) => f.write_str(message),
        }
    }
}

pub fn make<T>(value: T) -> Parsed<T> {
    Ok(value)
}

pub fn reject<T>() -> Parsed<T> {
    Err(Status::Reject)
}

/// A fatal error whose span runs from `start` to the current position.
pub fn fatal_from<T>(start: (usize, usize), stream: &CharStream, kind: ErrorKind) -> Parsed<T> {
    Err(Status::Fatal(
        Span {
            start,
            end: stream.get_pos(),
        },
        kind,
    ))
}

/// A fatal error at the current position.
pub fn fatal_here<T>(stream: &CharStream, kind: ErrorKind) -> Parsed<T> {
    let pos = stream.get_pos();
    Err(Status::Fatal(
        Span {
            start: pos,
            end: pos,
        },
        kind,
    ))
}

/// Return a fatal error with a formatted message (`ErrorKind::Message`); test scaffolding only
/// (`test/legacy_defaults.rs`, `expect_complete`).
#[allow(unused_macros)]
macro_rules! unrecoverable {
    (pos=$pos:expr, $stream:ident, $($str:expr),*) => {
        return crate::sudoers::basic_parser::fatal_from($pos, $stream, crate::sudoers::basic_parser::ErrorKind::Message(format!($($str),*)))
    };
    ($stream:ident, $($str:expr),*) => {
        return crate::sudoers::basic_parser::fatal_here($stream, crate::sudoers::basic_parser::ErrorKind::Message(format!($($str),*)))
    };
}

#[allow(unused_imports)]
pub(super) use unrecoverable;

/// This recovers from a failed parsing.
pub fn maybe<T>(status: Parsed<T>) -> Parsed<Option<T>> {
    match status {
        Ok(x) => Ok(Some(x)),
        Err(Status::Reject) => Ok(None),
        Err(err) => Err(err),
    }
}

pub use super::char_stream::CharStream;

/// All implementations of the Parse trait must satisfy this contract:
/// If the `parse` method of this trait returns None, the iterator is not advanced; otherwise it is
/// advanced beyond the accepted part of the input. i.e. if some input is consumed the method
/// *MUST* be producing a `Some` value.
pub trait Parse {
    fn parse(stream: &mut CharStream) -> Parsed<Self>
    where
        Self: Sized;
}

/// Structures representing whitespace (trailing whitespace can contain comments)
#[cfg_attr(test, derive(PartialEq, Eq))]
struct LeadingWhitespace;

#[cfg_attr(test, derive(PartialEq, Eq))]
struct TrailingWhitespace;

#[cfg_attr(test, derive(Debug, PartialEq, Eq))]
struct Comment;

/// The escape character `'\\'`. Kept opaque for Charon (`Cargo.toml`): the pinned Aeneas prints
/// this literal as `'\'`, which Lean rejects; `FunsExternal.lean` defines it as `'\\'`.
pub fn escape_char() -> char {
    '\\'
}

/// Accept zero or more whitespace characters; fails if the whitespace is not "leading" to something
/// (which can be used to detect end-of-input).
impl Parse for LeadingWhitespace {
    fn parse(stream: &mut CharStream) -> Parsed<Self> {
        let mut more = true;
        while more {
            match stream.peek() {
                Some(c) if c == '\t' || c == ' ' => stream.bump(c),
                _ => more = false,
            }
        }

        match stream.peek() {
            Some(_) => make(LeadingWhitespace {}),
            None => fatal_here(stream, ErrorKind::SuperfluousWhitespace),
        }
    }
}

/// Accept zero or more whitespace characters; since this accepts zero characters, it
/// always succeeds (unless some serious error occurs). This parser also accepts comments,
/// since those can form part of trailing white space.
impl Parse for TrailingWhitespace {
    fn parse(stream: &mut CharStream) -> Parsed<Self> {
        let mut stray = false;
        let mut more = true;
        while more {
            let _ = LeadingWhitespace::parse(stream); // don't propagate any errors

            // line continuations
            if stream.eat_char(escape_char()) {
                // do the equivalent of expect_syntax('\n', stream)?, without recursion
                if !stream.eat_char('\n') {
                    stray = true;
                    more = false;
                }
            } else {
                more = false;
            }
        }

        if stray {
            fatal_here(stream, ErrorKind::StrayEscape)
        } else {
            make(TrailingWhitespace {})
        }
    }
}

/// Parses a comment
impl Parse for Comment {
    fn parse(stream: &mut CharStream) -> Parsed<Self> {
        if !stream.eat_char('#') {
            return Err(Status::Reject);
        }
        stream.skip_to_newline();
        make(Comment {})
    }
}

pub(super) fn skip_trailing_whitespace(stream: &mut CharStream) -> Parsed<()> {
    TrailingWhitespace::parse(stream)?;
    make(())
}

/// Adheres to the contract of the [Parse] trait, accepts one character and consumes trailing whitespace.
pub fn try_syntax(syntax: char, stream: &mut CharStream) -> Parsed<()> {
    if !stream.eat_char(syntax) {
        return Err(Status::Reject);
    }
    skip_trailing_whitespace(stream)?;
    make(())
}

/// Similar to [try_syntax], but aborts parsing if the expected character is not found.
pub fn expect_syntax(syntax: char, stream: &mut CharStream) -> Parsed<()> {
    match try_syntax(syntax, stream) {
        Ok(()) => make(()),
        Err(_) => {
            let found = stream.peek();
            fatal_here(stream, ErrorKind::Expecting(syntax, found))
        }
    }
}

/// Convenience function: usually try_syntax is called as a test criterion; if this returns true, the input was consumed.
pub fn is_syntax(syntax: char, stream: &mut CharStream) -> Parsed<bool> {
    match maybe(try_syntax(syntax, stream))? {
        Some(()) => make(true),
        None => make(false),
    }
}

/// Interface for working with types that implement the [Parse] trait; this allows parsing to use
/// type inference. Use this instead of calling [Parse::parse] directly.
pub fn try_nonterminal<T: Parse>(stream: &mut CharStream) -> Parsed<T> {
    let result = T::parse(stream)?;
    skip_trailing_whitespace(stream)?;
    make(result)
}

/// Interface for working with types that implement the [Parse] trait; this expects to parse
/// the given type or gives a fatal parse error if this did not succeed.
use super::ast_names::UserFriendly;

pub fn expect_nonterminal<T: Parse + UserFriendly>(stream: &mut CharStream) -> Parsed<T> {
    let begin_pos = stream.get_pos();
    match try_nonterminal(stream) {
        Err(Status::Reject) => fatal_from(begin_pos, stream, ErrorKind::Expected(T::DESCRIPTION)),
        result => result,
    }
}

/// Something that implements the Token trait is a token (i.e. a string of characters defined by a
/// maximum length, character classes, and possible escaping). The class for the first character of
/// the token can be different than that of the rest.
pub trait Token: Sized {
    /// The maximum length of the token text in bytes (UTF-8).
    const MAX_LEN: usize = 255;

    fn construct(s: String) -> Result<Self, ErrorKind>;

    fn accept(c: char) -> bool;
    fn accept_1st(c: char) -> bool {
        Self::accept(c)
    }

    const ALLOW_ESCAPE: bool = false;
    fn escaped(_: char) -> bool {
        false
    }
}

/// The character class of the first (`first`) or of a later character of a token.
fn accepts<T: Token>(first: bool, c: char) -> bool {
    if first {
        T::accept_1st(c)
    } else {
        T::accept(c)
    }
}

/// One character of a token, possibly escaped.
fn accept_escaped<T: Token>(first: bool, stream: &mut CharStream) -> Parsed<char> {
    let escape = escape_char();
    if T::ALLOW_ESCAPE && stream.eat_char(escape) {
        match stream.peek() {
            Some(c) if T::escaped(c) => {
                stream.bump(c);
                Ok(c)
            }
            _ => {
                if accepts::<T>(first, escape) {
                    Ok(escape)
                } else if stream.eat_char('\n') {
                    if accepts::<T>(first, ' ') {
                        // escape + newline = line continuation (whitespace)
                        Ok(' ')
                    } else {
                        reject()
                    }
                } else {
                    fatal_here(stream, ErrorKind::IllegalEscape)
                }
            }
        }
    } else {
        match stream.peek() {
            Some(c) if accepts::<T>(first, c) => {
                stream.bump(c);
                Ok(c)
            }
            _ => reject(),
        }
    }
}

/// Implementation of the [Parse] trait for anything that implements [Token]
impl<T: Token> Parse for T {
    fn parse(stream: &mut CharStream) -> Parsed<Self> {
        let start_pos = stream.get_pos();
        let first = accept_escaped::<T>(true, stream)?;
        let mut text = String::new();
        text.push(first);

        let mut failure = None;
        let mut more = true;
        while more {
            match accept_escaped::<T>(false, stream) {
                Ok(c) => {
                    if text.len() >= T::MAX_LEN {
                        let pos = stream.get_pos();
                        failure = Some(Status::Fatal(
                            Span {
                                start: pos,
                                end: pos,
                            },
                            ErrorKind::TokenTooLong,
                        ));
                        more = false;
                    } else {
                        text.push(c);
                    }
                }
                Err(Status::Reject) => more = false,
                Err(status) => {
                    failure = Some(status);
                    more = false;
                }
            }
        }

        match failure {
            Some(status) => Err(status),
            None => match T::construct(text) {
                Ok(result) => make(result),
                Err(kind) => fatal_from(start_pos, stream, kind),
            },
        }
    }
}

/// Parser for `Option<T>` (this can be used to make the code more readable)
impl<T: Parse> Parse for Option<T> {
    fn parse(stream: &mut CharStream) -> Parsed<Self> {
        maybe(T::parse(stream))
    }
}

/// Parsing method for lists of items separated by a given character; this adheres to the contract of the [Parse] trait.
pub(super) fn parse_list<T: Parse + UserFriendly>(
    sep_by: char,
    max: usize,
    stream: &mut CharStream,
) -> Parsed<Vec<T>> {
    let mut elems = Vec::new();
    elems.push(try_nonterminal(stream)?);

    let mut failure = None;
    let mut more = true;
    while more {
        match try_syntax(sep_by, stream) {
            Ok(()) => {
                if elems.len() >= max {
                    let pos = stream.get_pos();
                    failure = Some(Status::Fatal(
                        Span {
                            start: pos,
                            end: pos,
                        },
                        ErrorKind::TooManyItems,
                    ));
                    more = false;
                } else {
                    match expect_nonterminal(stream) {
                        Ok(elem) => elems.push(elem),
                        Err(status) => {
                            failure = Some(status);
                            more = false;
                        }
                    }
                }
            }
            Err(Status::Reject) => more = false,
            Err(status) => {
                failure = Some(status);
                more = false;
            }
        }
    }

    match failure {
        Some(status) => Err(status),
        None => make(elems),
    }
}

/// Types that implement the Many trait can be parsed multiple tokens into a `Vec<T>`; they are
/// separated by `SEP`. There should also be a limit on the number of items.
pub trait Many {
    const SEP: char = ',';
    const LIMIT: usize = 127;
}

/// Generic implementation for parsing multiple items of a type `T` that implements the [Parse] and
/// [Many] traits.
impl<T: Parse + Many + UserFriendly> Parse for Vec<T> {
    fn parse(stream: &mut CharStream) -> Parsed<Self> {
        parse_list(T::SEP, T::LIMIT, stream)
    }
}

/// `LeadingWhitespace::parse(stream).is_ok()`: whether another line follows.
#[allow(clippy::redundant_pattern_matching)] // `Result::is_ok` has no Aeneas model
fn line_follows(stream: &mut CharStream) -> bool {
    match LeadingWhitespace::parse(stream) {
        Ok(_) => true,
        Err(_) => false,
    }
}

/// Entry point utility function; parse a `Vec<T>` but with fatal error recovery per line
#[allow(clippy::redundant_pattern_matching)] // `Result::is_ok` has no Aeneas model
pub fn parse_lines<T>(stream: &mut CharStream) -> Vec<Parsed<T>>
where
    T: Parse + UserFriendly,
{
    let mut result = Vec::new();

    // this will terminate; if the inner accept_if is an error, either a character will be consumed
    // by the second accept_if (making progress), or the end of the stream will have been reacherd
    // (which will cause the next iteration to fall through)

    let mut more = line_follows(stream);
    while more {
        let item = expect_nonterminal(stream);
        let parsed_item_ok = matches!(item, Ok(_));
        result.push(item);

        let _ = maybe(Comment::parse(stream));
        if !stream.eat_char('\n') {
            if parsed_item_ok {
                let kind = match stream.peek() {
                    None => ErrorKind::MissingLineTerminator,
                    Some(_) => ErrorKind::GarbageAtEndOfLine,
                };
                result.push(fatal_here(stream, kind));
            }
            stream.skip_to_newline();
        }
        more = line_follows(stream);
    }

    result
}

#[cfg(test)]
fn expect_complete<T: Parse>(stream: &mut CharStream) -> Parsed<T> {
    let result = expect_nonterminal(stream)?;
    if let Some(c) = stream.peek() {
        unrecoverable!(stream, "garbage at end of line: {c}")
    }
    make(result)
}

/// Convenience function (especially useful for writing test cases, to avoid having to write out the
/// AST constructors by hand.
#[cfg(test)]
pub fn parse_string<T: Parse>(text: &str) -> Parsed<T> {
    CharStream::with_text(text, expect_complete)
}

#[cfg(test)]
pub fn parse_eval<T: Parse>(text: &str) -> T {
    parse_string(text).unwrap()
}

#[cfg(test)]
pub fn parse_fatal<T: Parse>(text: &str) -> String {
    let Err(Status::Fatal(_, kind)) = parse_string::<T>(text) else {
        panic!("not a fatal error");
    };

    kind.to_string()
}

#[cfg(test)]
mod test {
    use super::*;

    impl Token for String {
        fn construct(val: String) -> Result<Self, ErrorKind> {
            Ok(val)
        }

        fn accept(c: char) -> bool {
            c.is_ascii_alphanumeric()
        }
    }

    impl Many for String {}

    #[test]
    fn superfluous_whitespace_at_eof() {
        let mut stream = CharStream::from_chars(&[' ', '\t']);
        match LeadingWhitespace::parse(&mut stream) {
            Err(Status::Fatal(span, kind @ ErrorKind::SuperfluousWhitespace)) => {
                assert_eq!(span.start, (1, 3));
                assert_eq!(span.end, (1, 3));
                assert_eq!(kind.to_string(), "superfluous whitespace");
            }
            _ => panic!("expected the leading-whitespace EOF sentinel"),
        }
    }

    #[test]
    fn comment_test() {
        assert_eq!(parse_eval::<Comment>("# hello"), Comment);
    }
    #[test]
    #[should_panic]
    fn comment_test_fail() {
        assert_eq!(parse_eval::<Comment>("# hello\nsomething"), Comment);
    }

    #[test]
    fn lines_test() {
        let input = |text: &str| CharStream::with_text(text, parse_lines);

        let s = |text: &str| Ok(text.to_string());
        assert_eq!(input("hello\nworld\n"), vec![s("hello"), s("world")]);
        assert_eq!(input("   hello\nworld\n"), vec![s("hello"), s("world")]);
        assert_eq!(input("hello  \nworld\n"), vec![s("hello"), s("world")]);
        assert_eq!(input("hello\n   world\n"), vec![s("hello"), s("world")]);
        assert_eq!(input("hello\nworld  \n"), vec![s("hello"), s("world")]);
        assert_eq!(input("hello\nworld")[0..2], vec![s("hello"), s("world")]);
        let Err(_) = input("hello\nworld")[2] else {
            panic!()
        };
        let Err(_) = input("hello\nworld:\n")[2] else {
            panic!()
        };
    }
    #[test]
    fn whitespace_test() {
        assert_eq!(
            parse_eval::<Vec<String>>("hello,something"),
            vec!["hello", "something"]
        );
        assert_eq!(
            parse_eval::<Vec<String>>("hello , something"),
            vec!["hello", "something"]
        );
        assert_eq!(
            parse_eval::<Vec<String>>("hello, something"),
            vec!["hello", "something"]
        );
        assert_eq!(
            parse_eval::<Vec<String>>("hello ,something"),
            vec!["hello", "something"]
        );
        assert_eq!(
            parse_eval::<Vec<String>>("hello\\\n,something"),
            vec!["hello", "something"]
        );
    }
}
