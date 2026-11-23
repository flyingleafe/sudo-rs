/-!
# `ast_names.rs`: `UserFriendly::DESCRIPTION`

The names `expect_nonterminal` puts into `"expected {}"`. In Rust they are associated
constants; here they are the fields of a record, because there are two tables: the release table
(`mod names`, `#[cfg(not(test))]`) and the test table (`#[cfg(test)]`: a blanket
`impl<T: Parse> UserFriendly for T` with `"elem"` for every type). A comparison with a dump
produced by a `#[cfg(test)]` Rust build must use `Descriptions.test`.

Generic types delegate to their parameter (`Vec<T>`, `Meta<T>`, `Qualified<T>`, `Unquoted<T>`:
`T::DESCRIPTION`), so they have no field; the productions use the field of `T`.
-/

namespace SudoersSpec.Syntax

/-- `UserFriendly::DESCRIPTION` for every type that has its own entry in `ast_names.rs`. -/
structure Descriptions where
  /-- `tokens::DigitsU32`. -/
  digitsU32 : String
  /-- `tokens::Numeric`. -/
  numeric : String
  /-- `Identifier`. -/
  identifier : String
  /-- `tokens::Command`. -/
  command : String
  /-- `tokens::SimpleCommand`. -/
  simpleCommand : String
  /-- `(SpecList<Hostname>, Vec<(Option<RunAs>, CommandSpec)>)`: `Hostname::DESCRIPTION` in
  release builds. -/
  hostsRunasCommands : String
  /-- `(Option<RunAs>, CommandSpec)`. -/
  runasCommand : String
  /-- `Sudo` ("this can never happen, as parse<Sudo> always succeeds"). -/
  sudo : String
  /-- `UserSpecifier`. -/
  userSpecifier : String
  /-- `tokens::Username`. -/
  username : String
  /-- `tokens::Hostname`. -/
  hostname : String
  /-- `tokens::QuotedStringParameter`. -/
  quotedStringParameter : String
  /-- `tokens::QuotedIncludePath`. -/
  quotedIncludePath : String
  /-- `tokens::StringParameter`: `QuotedStringParameter::DESCRIPTION` in release builds. -/
  stringParameter : String
  /-- `tokens::IncludePath`. -/
  includePath : String
  /-- `tokens::AliasName`. -/
  aliasName : String
  /-- `tokens::DefaultName`. -/
  defaultName : String
  /-- `tokens::EnvVar`. -/
  envVar : String
  /-- `CommandSpec`: `Command::DESCRIPTION` in release builds. -/
  commandSpec : String
  /-- `tokens::ChDir`. -/
  chDir : String
  /-- `defaults::SettingsModifier`. -/
  settingsModifier : String
  /-- `Def<T>`. -/
  def_ : String
  /-- `PeerSpec` (feature `unstable-remote-sudoers`). -/
  peerSpec : String
  deriving DecidableEq, Repr

/-- `mod names` (`#[cfg(not(test))]`): the descriptions of a release build. -/
def Descriptions.release : Descriptions where
  digitsU32 := "number"
  numeric := "nonnegative number"
  identifier := "identifier"
  command := "path to binary (or sudoedit)"
  simpleCommand := "path to binary (or sudoedit)"
  hostsRunasCommands := "host name"
  runasCommand := "(users:groups) specification"
  sudo := "nothing"
  userSpecifier := "user"
  username := "user"
  hostname := "host name"
  quotedStringParameter := "non-empty string"
  quotedIncludePath := "non-empty string"
  stringParameter := "non-empty string"
  includePath := "path to file"
  aliasName := "alias name"
  defaultName := "configuration option"
  envVar := "environment variable"
  commandSpec := "path to binary (or sudoedit)"
  chDir := "directory or '*'"
  settingsModifier := "parameter"
  def_ := "alias definition"
  peerSpec := "user credentials in parentheses"

/-- `#[cfg(test)] impl<T: Parse> UserFriendly for T`: `"elem"` everywhere. -/
def Descriptions.test : Descriptions where
  digitsU32 := "elem"
  numeric := "elem"
  identifier := "elem"
  command := "elem"
  simpleCommand := "elem"
  hostsRunasCommands := "elem"
  runasCommand := "elem"
  sudo := "elem"
  userSpecifier := "elem"
  username := "elem"
  hostname := "elem"
  quotedStringParameter := "elem"
  quotedIncludePath := "elem"
  stringParameter := "elem"
  includePath := "elem"
  aliasName := "elem"
  defaultName := "elem"
  envVar := "elem"
  commandSpec := "elem"
  chDir := "elem"
  settingsModifier := "elem"
  def_ := "elem"
  peerSpec := "elem"

end SudoersSpec.Syntax
