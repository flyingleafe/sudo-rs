import SudoersSpec.Syntax.Ast
import SudoersSpec.Settings.Model

/-!
# `ast.rs`: `impl Parse for defaults::SettingsModifier`

The parser of one entry of a `Defaults` line, over the settings model `SudoersSpec.Settings`
(`set`, `negate`, `checkInteger`, `checkText`, `buildList`, `SettingsModifier`).
-/

namespace SudoersSpec.Syntax

open Parser

/-- One iteration of the loop of `parse_vars`, after an `EnvVar` was read:
```
if is_syntax('=', stream)? {
    let StringParameter(value) = expect_nonterminal(stream)?;
    result.push(name + "=" + &value);
} else { result.push(name); }
if result.len() > Identifier::LIMIT { unrecoverable!(stream, "environment variable list too long") }
```
-/
def parseVarsBody (O : Oracles) (D : Descriptions) (result : List String) (name : String) :
    Parser (Step (List String) (List String)) := do
  let eq ← isSyntax '='
  let result ← if eq then do
      let value ← expectNonterminal D.stringParameter (token (stringParameterToken O.char))
      pure (result ++ [name ++ "=" ++ value])
    else
      pure (result ++ [name])
  if result.length > identifierMany.limit then
    fatalHere .envVarListTooLong
  else
    pure (.next result)

/-- `parse_vars` in `SettingsModifier::parse`: a quoted, space-separated list of `EnvVar` or
`EnvVar=StringParameter` (at most 127, not empty), or one unquoted `EnvVar` (`=` after it is
fatal). -/
def parseVars (O : Oracles) (D : Descriptions) : Parser (List String) := do
  let quote ← eatChar '"'
  if quote then
    let result ← whileSome (tryNonterminal (parseOption (token (envVarToken O.char))))
      (tryNonterminal_parseOption_consumesSome (token_consumes _)) (parseVarsBody O D) id []
    expectSyntax '"'
    if result.isEmpty then fatalHere .emptyStringNotAllowed else pure result
  else
    let name ← expectNonterminal D.envVar (token (envVarToken O.char))
    let eq ← isSyntax '='
    if eq then fatalHere .doubleQuotesRequired else pure [name]

/-- `list_items` in `SettingsModifier::parse`: `=` (expected) before the kind is checked. -/
def listItems (O : Oracles) (D : Descriptions) (idPos : Nat × Nat) (mode : Settings.ListMode)
    (name : String) (cfg : Settings.SettingKind) : Parser Settings.SettingsModifier := do
  expectSyntax '='
  match cfg with
  | .List s =>
    let items ← parseVars O D
    pure (Settings.buildList s mode items)
  | _ => fatalFrom idPos (.notAListParameter name)

/-- `text_item` in `SettingsModifier::parse`: a quoted `QuotedStringParameter` or an unquoted
`StringParameter`. -/
def textItem (O : Oracles) (D : Descriptions) : Parser String := do
  let quote ← eatChar '"'
  if quote then
    let text ← expectNonterminal D.quotedStringParameter
      (token (quotedStringParameterToken O.char))
    expectSyntax '"'
    pure text
  else
    expectNonterminal D.stringParameter (token (stringParameterToken O.char))

/-- `impl Parse for defaults::SettingsModifier`: `!name`, `name`, `name+=..`, `name-=..`,
`name=..`. The integer checkers are the panic-free `Settings.checkInteger`: the parser gives them
a `Numeric` token of at most 18 bytes, where `fractional_minutes` cannot panic
(`Settings.fractionalMinutesRun_eq`). -/
def settingsModifier (O : Oracles) (D : Descriptions) : Parser Settings.SettingsModifier := do
  let idPos ← getPos
  let bang ← isSyntax '!'
  if bang then
    let valuePos ← getPos
    let name ← expectNonterminal D.defaultName (token defaultNameToken)
    match Settings.negate name with
    | some m => pure m
    | none =>
      if (Settings.set name).isSome then
        fatalFrom valuePos (.cannotBeUsedInBooleanContext name)
      else
        fatalFrom valuePos (.unknownSetting name)
  else
    let name ← tryNonterminal (token defaultNameToken)
    match Settings.set name with
    | none => fatalFrom idPos (.unknownSetting name)
    | some cfg =>
      let plus ← isSyntax '+'
      if plus then
        listItems O D idPos .Add name cfg
      else
        let minus ← isSyntax '-'
        if minus then
          listItems O D idPos .Del name cfg
        else
          let eq ← isSyntax '='
          if eq then
            let valuePos ← getPos
            match cfg with
            | .Flag _ => fatalHere (.cannotAssignToBoolean name)
            | .Integer s =>
              let denotation ← expectNonterminal D.numeric (token numericToken)
              match Settings.checkInteger s denotation with
              | some m => pure m
              | none => fatalFrom valuePos (.invalidValue denotation name)
            | .List s =>
              let items ← parseVars O D
              pure (Settings.buildList s .Set items)
            | .Text s =>
              let text ← textItem O D
              match Settings.checkText s text with
              | some m => pure m
              | none => fatalFrom valuePos (.invalidValue text name)
          else
            match cfg with
            | .Flag m => pure m
            | _ => fatalFrom idPos (.notABooleanSetting name)

/-- `impl Many for defaults::SettingsModifier {}`. -/
def settingsModifierMany : Many := {}

end SudoersSpec.Syntax
