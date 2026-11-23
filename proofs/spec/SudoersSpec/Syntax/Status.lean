import SudoersSpec.Syntax.CharStream

/-!
# `basic_parser.rs` `Status` and `Parsed`; the diagnostic messages

Rust carries a fatal error as `Status::Fatal(Span, String)`, the string produced by a
`format!` at one of the 30 `unrecoverable!` sites (`basic_parser.rs`, `ast.rs`) or returned by a
`Token::construct` (`tokens.rs`). Here the message is an `ErrKind`: one constructor per message
template, its payload the interpolated values. `ErrKind.render` gives the Rust text byte for byte
(without the `gettext` feature, which is off by default: then `xlat!` is the identity).

Messages produced by code outside the parser (`SudoString::new`, `SudoPath::try_from`,
`glob::Pattern::new`) are carried as opaque text, exactly the `String` that code returns.
-/

namespace SudoersSpec.Syntax

/-- The message of a fatal parse error. One constructor per message template of the legacy
parser. The doc comment of each constructor gives the Rust template and its sites. -/
inductive ErrKind where
  /-- `"superfluous whitespace"`: `LeadingWhitespace::parse` at the end of the input. -/
  | superfluousWhitespace
  /-- `"stray escape sequence"`: `TrailingWhitespace::parse`, a `\` not followed by a newline. -/
  | strayEscapeSequence
  /-- `"expecting '{syntax}' but found '{str}'"`: `expect_syntax`; `str` is the next character or
  `EOF` (`found = none`). -/
  | expectingSyntax (sym : Char) (found : Option Char)
  /-- `"expected {}"` with `T::DESCRIPTION`: `expect_nonterminal`. -/
  | expected (description : String)
  /-- `"illegal escape sequence"`: `accept_escaped` in `impl<T: Token> Parse for T`. -/
  | illegalEscapeSequence
  /-- `"token exceeds maximum length"`: the token loop of `impl<T: Token> Parse for T`. -/
  | tokenExceedsMaximumLength
  /-- `"too many items in list"`: `parse_list`. -/
  | tooManyItemsInList
  /-- `"missing line terminator at end of file"`: `parse_lines`. -/
  | missingLineTerminator
  /-- `"garbage at end of line"`: `parse_lines`. -/
  | garbageAtEndOfLine
  /-- `"garbage at end of line: {c}"`: `expect_complete`, `#[cfg(test)]` only. -/
  | garbageAtEndOfLineChar (c : Char)
  /-- `"netgroups are not supported yet"`: `UserSpecifier::parse`. -/
  | netgroupsNotSupported
  /-- `"{spec} is not supported by sudo-rs"`: `MetaOrTag::parse` for `INTERCEPT`, `CHROOT`,
  `TIMEOUT`, `NOTBEFORE`, `NOTAFTER`. -/
  | notSupported (spec : String)
  /-- `"SELinux role based access control is not yet supported by sudo-rs"`: `MetaOrTag::parse`
  for `ROLE`, `TYPE`. -/
  | selinuxNotSupported
  /-- `"unsupported modifier '{}'"`: `MetaOrTag::parse`, an unknown keyword followed by `=`. -/
  | unsupportedModifier (name : String)
  /-- `"too many tags for command specifier"`: `CommandSpec::parse`. -/
  | tooManyTags
  /-- `"ambiguous syntax"`: `Sudo::parse`. -/
  | ambiguousSyntax
  /-- `"use quotes around filenames or escape whitespace"`: `parse_include`. -/
  | useQuotesAroundFilenames
  /-- `"unknown directive"`: `parse_include`. -/
  | unknownDirective
  /-- `"reserved word {} used as an alias name"`: `Def<T>::parse`. -/
  | reservedAliasName (name : String)
  /-- `"environment variable list too long"`: `SettingsModifier::parse` (`parse_vars`). -/
  | envVarListTooLong
  /-- `"empty string not allowed"`: `SettingsModifier::parse` (`parse_vars`). -/
  | emptyStringNotAllowed
  /-- `"double quotes are required for VAR=value pairs"`: `SettingsModifier::parse`. -/
  | doubleQuotesRequired
  /-- `"{name} is not a list parameter"`: `SettingsModifier::parse` (`list_items`). -/
  | notAListParameter (name : String)
  /-- `"'{name}' cannot be used in a boolean context"`: `SettingsModifier::parse`. -/
  | cannotBeUsedInBooleanContext (name : String)
  /-- `"unknown setting: '{name}'"`: `SettingsModifier::parse` (two sites). -/
  | unknownSetting (name : String)
  /-- `"can't assign to boolean setting '{name}'"`: `SettingsModifier::parse`. -/
  | cannotAssignToBoolean (name : String)
  /-- `"'{value}' is not a valid value for {name}"`: `SettingsModifier::parse`, integer
  (`{denotation}`) and text (`{text}`) settings. -/
  | invalidValue (value name : String)
  /-- `"'{name}' is not a boolean setting"`: `SettingsModifier::parse`. -/
  | notABooleanSetting (name : String)
  /-- `"embedded $ in username"`: `Username::construct`. -/
  | embeddedDollarInUsername
  /-- `SudoString::new(..).map_err(|e| e.to_string())` in `Username::construct`: the text of
  `Error::StringValidation`, opaque (`"Unexpected null character in input: {string:?}"`). -/
  | sudoStringValidation (msg : String)
  /-- `"value too large"`: `DigitsU32::construct`. -/
  | valueTooLarge
  /-- `"hosts cannot be specified using an IPv4 address"`: `Hostname::construct`. -/
  | hostIPv4Address
  /-- `"regular expressions are not supported"`: `Command::construct`,
  `SimpleCommand::construct`. -/
  | regularExpressionsNotSupported
  /-- `"glob patterns are not allowed in command arguments"`: `Command::construct`. -/
  | globInCommandArguments
  /-- `"list does not take arguments"`: `Command::construct`. -/
  | listTakesNoArguments
  /-- `"wildcard pattern error {err}"`: `SimpleCommand::construct`; `err` is the `Display` of
  `glob::PatternError`, opaque. -/
  | wildcardPatternError (err : String)
  /-- `"digest specifications are not supported"`: `SimpleCommand::construct`. -/
  | digestNotSupported
  /-- `"fully qualified path needed"`: `SimpleCommand::construct`. -/
  | fullyQualifiedPathNeeded
  /-- `"non-UTF8 characters in filesystem"`: `SimpleCommand::construct`. -/
  | nonUtf8Filesystem
  /-- `"path cannot contain '*'"`: `ChDir::construct`. -/
  | pathContainsStar
  /-- `SudoPath::try_from(s).map_err(|e| e.to_string())` in `ChDir::construct`: the text of
  `Error::PathValidation`, opaque. -/
  | sudoPathValidation (msg : String)
  deriving DecidableEq, Repr, Inhabited

/-- The Rust message text of an `ErrKind`, byte for byte. -/
def ErrKind.render : ErrKind → String
  | .superfluousWhitespace => "superfluous whitespace"
  | .strayEscapeSequence => "stray escape sequence"
  | .expectingSyntax sym found =>
    "expecting '" ++ sym.toString ++ "' but found '" ++
      (match found with | some c => c.toString | none => "EOF") ++ "'"
  | .expected description => "expected " ++ description
  | .illegalEscapeSequence => "illegal escape sequence"
  | .tokenExceedsMaximumLength => "token exceeds maximum length"
  | .tooManyItemsInList => "too many items in list"
  | .missingLineTerminator => "missing line terminator at end of file"
  | .garbageAtEndOfLine => "garbage at end of line"
  | .garbageAtEndOfLineChar c => "garbage at end of line: " ++ c.toString
  | .netgroupsNotSupported => "netgroups are not supported yet"
  | .notSupported spec => spec ++ " is not supported by sudo-rs"
  | .selinuxNotSupported => "SELinux role based access control is not yet supported by sudo-rs"
  | .unsupportedModifier name => "unsupported modifier '" ++ name ++ "'"
  | .tooManyTags => "too many tags for command specifier"
  | .ambiguousSyntax => "ambiguous syntax"
  | .useQuotesAroundFilenames => "use quotes around filenames or escape whitespace"
  | .unknownDirective => "unknown directive"
  | .reservedAliasName name => "reserved word " ++ name ++ " used as an alias name"
  | .envVarListTooLong => "environment variable list too long"
  | .emptyStringNotAllowed => "empty string not allowed"
  | .doubleQuotesRequired => "double quotes are required for VAR=value pairs"
  | .notAListParameter name => name ++ " is not a list parameter"
  | .cannotBeUsedInBooleanContext name => "'" ++ name ++ "' cannot be used in a boolean context"
  | .unknownSetting name => "unknown setting: '" ++ name ++ "'"
  | .cannotAssignToBoolean name => "can't assign to boolean setting '" ++ name ++ "'"
  | .invalidValue value name => "'" ++ value ++ "' is not a valid value for " ++ name
  | .notABooleanSetting name => "'" ++ name ++ "' is not a boolean setting"
  | .embeddedDollarInUsername => "embedded $ in username"
  | .sudoStringValidation msg => msg
  | .valueTooLarge => "value too large"
  | .hostIPv4Address => "hosts cannot be specified using an IPv4 address"
  | .regularExpressionsNotSupported => "regular expressions are not supported"
  | .globInCommandArguments => "glob patterns are not allowed in command arguments"
  | .listTakesNoArguments => "list does not take arguments"
  | .wildcardPatternError err => "wildcard pattern error " ++ err
  | .digestNotSupported => "digest specifications are not supported"
  | .fullyQualifiedPathNeeded => "fully qualified path needed"
  | .nonUtf8Filesystem => "non-UTF8 characters in filesystem"
  | .pathContainsStar => "path cannot contain '*'"
  | .sudoPathValidation msg => msg

/-- `basic_parser.rs` `Status`: `Fatal(Span, String)` (not recoverable) or `Reject` (the
production does not apply). The `String` is `kind.render`. -/
inductive Status where
  | fatal (span : Span) (kind : ErrKind)
  | reject
  deriving DecidableEq, Repr, Inhabited

/-- The Rust `Status` value: the span and the rendered message, or `none` for `Reject`. -/
def Status.render : Status → Option (Span × String)
  | .fatal span kind => some (span, kind.render)
  | .reject => none

deriving instance DecidableEq for Except

/-- `basic_parser.rs` `Parsed<T> = Result<T, Status>`. -/
abbrev Parsed (α : Type) := Except Status α

/-- `basic_parser::maybe`: recover from a `Reject`; fatal errors stay. -/
def maybe : Parsed α → Parsed (Option α)
  | .ok x => .ok (some x)
  | .error .reject => .ok none
  | .error err => .error err

@[simp] theorem maybe_ok (x : α) : maybe (.ok x) = .ok (some x) := rfl
@[simp] theorem maybe_reject : maybe (.error .reject : Parsed α) = .ok none := rfl
@[simp] theorem maybe_fatal (sp : Span) (k : ErrKind) :
    maybe (.error (.fatal sp k) : Parsed α) = .error (.fatal sp k) := rfl

end SudoersSpec.Syntax
