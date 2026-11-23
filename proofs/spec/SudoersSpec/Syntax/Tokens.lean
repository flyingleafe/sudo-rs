import SudoersSpec.Syntax.BasicParser
import SudoersSpec.Syntax.Oracles

/-!
# `tokens.rs` (core part): `Hostname`, `AliasName`, `Meta<T>`

Each `impl Token for X` is a `TokenSpec`; the parser of the token is `token spec`. Tokens whose
classes use a Unicode-aware predicate take the `CharOracle`.

Helpers for the `str` methods the constructors call (`rsplitn`, `trim_end`, `starts_with` with
a predicate) are defined on `List Char` next to the token that uses them.
-/

namespace SudoersSpec.Syntax

/-! ## `str` helpers -/

/-- `str::splitn(n, sep)` with a `char` separator: at most `n` pieces from the left, the last one
holding the unsplit rest; no piece for `n = 0`. -/
def splitn : Nat → Char → List Char → List (List Char)
  | 0, _, _ => []
  | 1, _, s => [s]
  | n + 2, sep, s =>
    match s.span (· != sep) with
    | (piece, []) => [piece]
    | (piece, _ :: rest) => piece :: splitn (n + 1) sep rest

/-- `str::rsplitn(n, sep)` with a `char` separator: at most `n` pieces from the right (last
piece first), the last one holding the unsplit beginning. -/
def rsplitn (n : Nat) (sep : Char) (s : List Char) : List (List Char) :=
  (splitn n sep s.reverse).map List.reverse

/-- `str::trim_end`: drop trailing characters with `char::is_whitespace`. -/
def trimEnd (O : CharOracle) (s : List Char) : List Char :=
  (s.reverse.dropWhile O.isWhitespace).reverse

/-- `str::starts_with` with a `char` predicate: the first character exists and satisfies it. -/
def startsWithPred (s : List Char) (f : Char → Bool) : Bool :=
  match s with
  | c :: _ => f c
  | [] => false

/-! ## `AliasName` -/

/-- `AliasName::accept_1st`: `c.is_ascii_uppercase()`. -/
def AliasName.accept1st (c : Char) : Bool :=
  isAsciiUppercase c

/-- `AliasName::accept`: `Self::accept_1st(c) || c.is_ascii_digit() || c == '_'`. -/
def AliasName.accept (c : Char) : Bool :=
  AliasName.accept1st c || isAsciiDigit c || c == '_'

/-- `impl Token for AliasName`: an uppercase identifier; `construct` always succeeds. -/
def aliasNameToken : TokenSpec String where
  construct s := .ok (String.ofList s)
  accept := AliasName.accept
  accept1st := AliasName.accept1st

/-! ## `Hostname` -/

/-- `Hostname::accept`: `c.is_ascii_alphanumeric() || ".-_".contains(c)`. -/
def Hostname.accept (c : Char) : Bool :=
  isAsciiAlphanumeric c || c == '.' || c == '-' || c == '_'

/-- The test of `Hostname::construct`: the pieces of `text.rsplitn(5, '.')`; the first (up to)
four are non-empty, at most 3 bytes long and `char::is_numeric`, and there is no fifth. So a
name of at most four dot-separated numeric parts is refused: `1.2.3.4`, but also `1.2.3` and
`123`. -/
def Hostname.looksLikeIPv4 (O : CharOracle) (text : List Char) : Bool :=
  let chunks := rsplitn 5 '.' text
  (chunks.take 4).all (fun part => !part.isEmpty && utf8Len part ≤ 3 && part.all O.isNumeric) &&
    (chunks.drop 4).isEmpty

/-- `Hostname::construct`. -/
def Hostname.construct (O : CharOracle) (text : List Char) : Except ErrKind Hostname :=
  if Hostname.looksLikeIPv4 O text then
    .error .hostIPv4Address
  else
    .ok (String.ofList text)

/-- `impl Token for Hostname`. -/
def hostnameToken (O : CharOracle) : TokenSpec Hostname where
  construct := Hostname.construct O
  accept := Hostname.accept

/-- `impl Many for Hostname {}`: `,` and 127. -/
def hostnameMany : Many := {}

/-! ## `Meta<T>` -/

/-- `Meta::<T>::construct`: `ALL`, an alias name (decided on the text without trailing
whitespace), or `Meta::Only(T::construct(raw)?)` on the raw text. -/
def Meta.construct (O : CharOracle) (T : TokenSpec α) (raw : List Char) :
    Except ErrKind (Meta α) :=
  let cooked := trimEnd O raw
  if cooked == "ALL".toList then
    .ok .all
  else if startsWithPred cooked AliasName.accept1st && (cooked.drop 1).all AliasName.accept then
    .ok (.alias (String.ofList cooked))
  else
    match T.construct raw with
    | .ok x => .ok (.only x)
    | .error e => .error e

/-- `impl<T: Token> Token for Meta<T>`: the classes of `T` widened by `char::is_uppercase`;
`MAX_LEN`, `ALLOW_ESCAPE` and `escaped` of `T`. -/
def metaToken (O : CharOracle) (T : TokenSpec α) : TokenSpec (Meta α) where
  maxLen := T.maxLen
  construct := Meta.construct O T
  accept c := T.accept c || O.isUppercase c
  accept1st c := T.accept1st c || O.isUppercase c
  allowEscape := T.allowEscape
  escaped := T.escaped

/-- `impl<T: Many> Many for Meta<T>`: the separator and limit of `T`. -/
def metaMany (m : Many) : Many := m

/-! ## Number parsing (`str::parse`, `from_str_radix`) -/

/-- `char::to_digit(radix)` for `radix ≤ 36`. -/
def charToDigit (radix : Nat) (c : Char) : Option Nat :=
  let d :=
    if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'z' then some (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c && c ≤ 'Z' then some (c.toNat - 'A'.toNat + 10)
    else none
  match d with
  | some v => if v < radix then some v else none
  | none => none

/-- The value of a list of digits in `radix`, most significant first. -/
def digitsValue (radix : Nat) : List Char → Option Nat :=
  List.foldl (fun acc c => match acc, charToDigit radix c with
    | some v, some d => some (v * radix + d)
    | _, _ => none) (some 0)

/-- `uN::from_str_radix(s, radix)` for an unsigned type of `bits` bits (also `s.parse::<uN>()`
with `radix = 10`): an optional `+`, then at least one digit; the value must fit. -/
def fromStrRadix (radix bits : Nat) (s : List Char) : Option Nat :=
  let digits : Option (List Char) :=
    match s with
    | [] => none
    | ['+'] | ['-'] => none
    | '+' :: rest => some rest
    | _ => some s
  match digits with
  | none => none
  | some ds =>
    match digitsValue radix ds with
    | some v => if v < 2 ^ bits then some v else none
    | none => none

/-! ## `str` helpers (continued) -/

/-- `str::split(pred)`: the pieces between the characters `pred` accepts (empty pieces kept). -/
def splitWhen (p : Char → Bool) : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    if p c then [] :: splitWhen p cs
    else
      match splitWhen p cs with
      | w :: ws => (c :: w) :: ws
      | [] => [[c]]

/-- `str::split_whitespace`: the non-empty pieces between `char::is_whitespace` characters. -/
def splitWhitespace (O : CharOracle) (s : List Char) : List (List Char) :=
  (splitWhen O.isWhitespace s).filter (fun w => !w.isEmpty)

/-- `str::split_once(c)`. -/
def splitOnce (sep : Char) (s : List Char) : Option (List Char × List Char) :=
  match s.span (· != sep) with
  | (_, []) => none
  | (a, _ :: b) => some (a, b)

/-! ## `SudoString`, `SudoPath` (`src/common/{string,path}.rs`) -/

/-- `SudoString::new(s).map_err(|e| e.to_string())`: a string without NUL characters. -/
def sudoStringNew (O : Oracles) (s : List Char) : Except ErrKind String :=
  if s.contains '\x00' then
    .error (.sudoStringValidation
      ("Unexpected null character in input: " ++ O.fmt.debugStr (String.ofList s)))
  else
    .ok (String.ofList s)

/-- `SudoPath::try_from(s).map_err(|e| e.to_string())`: a path without NUL bytes (a `String`
is always UTF-8, so the second check of `SudoPath::new` never fails). -/
def sudoPathTryFrom (O : Oracles) (s : List Char) : Except ErrKind String :=
  if s.contains '\x00' then
    .error (.sudoPathValidation
      ("Unexpected null character in input: " ++ O.fmt.debugPath (String.ofList s)))
  else
    .ok (String.ofList s)

/-! ## `Username` -/

/-- `Username::accept`: `c.is_alphanumeric() || ".-_@$".contains(c)`. -/
def Username.accept (O : CharOracle) (c : Char) : Bool :=
  O.isAlphanumeric c || c == '.' || c == '-' || c == '_' || c == '@' || c == '$'

/-- `Username::accept_1st`: `c != '@' && Self::accept(c)`. -/
def Username.accept1st (O : CharOracle) (c : Char) : Bool :=
  c != '@' && Username.accept O c

/-- `Username::escaped`. -/
def Username.escaped (c : Char) : Bool :=
  c == '\\' || c == '"' || c == ',' || c == ':' || c == '=' || c == '!' || c == '(' ||
    c == ')' || c == ' '

/-- `Username::construct`: a `$` only at the end, then `SudoString::new`. -/
def Username.construct (O : Oracles) (text : List Char) : Except ErrKind String :=
  let stripped := if text.getLast? == some '$' then text.dropLast else text
  if stripped.contains '$' then
    .error .embeddedDollarInUsername
  else
    sudoStringNew O text

/-- `impl Token for Username`. -/
def usernameToken (O : Oracles) : TokenSpec String where
  construct := Username.construct O
  accept := Username.accept O.char
  accept1st := Username.accept1st O.char
  allowEscape := true
  escaped := Username.escaped

/-! ## `DigitsU32`, `Numeric` -/

/-- `impl Token for DigitsU32`: `s.parse::<u32>()`, else `"value too large"`. -/
def digitsU32Token : TokenSpec Nat where
  maxLen := 10
  construct s :=
    match fromStrRadix 10 32 s with
    | some v => .ok v
    | none => .error .valueTooLarge
  accept := isAsciiDigit

/-- `impl Token for Numeric`. -/
def numericToken : TokenSpec String where
  maxLen := 18
  construct s := .ok (String.ofList s)
  accept c := isAsciiHexdigit c || c == '.'

/-! ## `SimpleCommand`, `Command` -/

/-- `SimpleCommand::escaped`. -/
def SimpleCommand.escaped (c : Char) : Bool :=
  c == '\\' || c == ',' || c == ':' || c == '=' || c == '#' || c == ' '

/-- `SimpleCommand::accept_1st`: `c == '/' || c == 's' || c == 'l'`. -/
def SimpleCommand.accept1st (c : Char) : Bool :=
  c == '/' || c == 's' || c == 'l'

/-- `SimpleCommand::accept`: `(!Self::escaped(c) && !c.is_control()) || c == '='`. -/
def SimpleCommand.accept (O : CharOracle) (c : Char) : Bool :=
  (!SimpleCommand.escaped c && !O.isControl c) || c == '='

/-- `cvt_err(glob::Pattern::new(&cmd))` in `SimpleCommand::construct`. -/
def SimpleCommand.compile (O : Oracles) (cmd : List Char) : Except ErrKind String :=
  match O.glob.compile (String.ofList cmd) with
  | none => .ok (String.ofList cmd)
  | some e => .error (.wildcardPatternError e.render)

/-- `SimpleCommand::construct`: `list` and `sudoedit` as they are; refuse digests, regular
expressions and relative paths; drop a final `/` (remembered), canonicalize if possible, put
back `/*` for a directory; compile as a glob. The value is the pattern text. -/
def SimpleCommand.construct (O : Oracles) (cmd : List Char) : Except ErrKind String :=
  if cmd == "list".toList || cmd == "sudoedit".toList then
    SimpleCommand.compile O cmd
  else if "sha".toList.isPrefixOf cmd then
    .error .digestNotSupported
  else if cmd.head? == some '^' then
    .error .regularExpressionsNotSupported
  else if cmd.head? != some '/' then
    .error .fullyQualifiedPathNeeded
  else
    let isDir := cmd.getLast? == some '/'
    let cmd := if isDir then cmd.dropLast else cmd
    let canon : Except ErrKind (List Char) :=
      match O.fs.canonicalize (String.ofList cmd) with
      | .ok real => .ok real.toList
      | .okNonUtf8 => .error .nonUtf8Filesystem
      | .err => .ok cmd
    match canon with
    | .error e => .error e
    | .ok cmd => SimpleCommand.compile O (if isDir then cmd ++ "/*".toList else cmd)

/-- `impl Token for SimpleCommand` (`SimpleCommand = glob::Pattern`, kept as its text). -/
def simpleCommandToken (O : Oracles) : TokenSpec String where
  maxLen := 1024
  construct := SimpleCommand.construct O
  accept := SimpleCommand.accept O.char
  accept1st := SimpleCommand.accept1st
  allowEscape := true
  escaped := SimpleCommand.escaped

/-- The argument pattern of `Command::construct`, from the words after the command. -/
def Command.argPattern (args : List (List Char)) : Except ErrKind Args :=
  if args.isEmpty then
    .ok (.prefix [])
  else if (args.head?.bind List.head?) == some '^' then
    .error .regularExpressionsNotSupported
  else
    let (args, isPrefix) :=
      if args.getLast? == some ['*'] then (args.dropLast, true)
      else if args.getLast? == some ['"', '"'] then (args.dropLast, false)
      else (args, false)
    if args.any (fun a => a.any (fun c => c == '?' || c == '*' || c == '[')) then
      .error .globInCommandArguments
    else
      let args := args.map String.ofList
      .ok (if isPrefix then .prefix args else .exact args)

/-- `Command::construct`: split at whitespace; the first word is a `SimpleCommand`, the others
the argument pattern (`*` last: any further arguments; `""` last: no further arguments); `list`
takes no arguments. -/
def Command.construct (O : Oracles) (s : List Char) : Except ErrKind Command :=
  match splitWhitespace O.char s with
  | [] => .error .unwrapNone
  | cmd :: args =>
    match SimpleCommand.construct O cmd with
    | .error e => .error e
    | .ok command =>
      match Command.argPattern args with
      | .error e => .error e
      | .ok argpat =>
        if command == "list" && argpat != .prefix [] then
          .error .listTakesNoArguments
        else
          .ok ⟨command, argpat⟩

/-- `impl Token for Command`: the classes of `SimpleCommand`, plus space and tab after the
first character. -/
def commandToken (O : Oracles) : TokenSpec Command where
  maxLen := 1024
  construct := Command.construct O
  accept c := SimpleCommand.accept O.char c || c == ' ' || c == '\t'
  accept1st := SimpleCommand.accept1st
  allowEscape := true
  escaped := SimpleCommand.escaped

/-! ## `DefaultName`, `EnvVar`, parameters, paths -/

/-- `impl Token for DefaultName`. -/
def defaultNameToken : TokenSpec String where
  construct s := .ok (String.ofList s)
  accept c := isAsciiAlphanumeric c || c == '_'

/-- `EnvVar::escaped`. -/
def EnvVar.escaped (c : Char) : Bool :=
  c == '\\' || c == '=' || c == '#' || c == '"' || c == ','

/-- `impl Token for EnvVar`. -/
def envVarToken (O : CharOracle) : TokenSpec String where
  construct s := .ok (String.ofList s)
  accept c := !O.isControl c && !O.isWhitespace c && !EnvVar.escaped c
  allowEscape := true
  escaped := EnvVar.escaped

/-- `QuotedStringParameter::escaped`. -/
def QuotedStringParameter.escaped (O : CharOracle) (c : Char) : Bool :=
  c == '\\' || c == '"' || O.isControl c

/-- `impl Token for QuotedStringParameter`. -/
def quotedStringParameterToken (O : CharOracle) : TokenSpec String where
  maxLen := 1024
  construct s := .ok (String.ofList s)
  accept c := !QuotedStringParameter.escaped O c
  allowEscape := true
  escaped := QuotedStringParameter.escaped O

/-- `QuotedIncludePath::escaped`. -/
def QuotedIncludePath.escaped (O : CharOracle) (c : Char) : Bool :=
  c == '"' || O.isControl c

/-- `impl Token for QuotedIncludePath`: like `QuotedStringParameter`, but `\` is not escaped,
so `\` followed by anything else is kept literally. -/
def quotedIncludePathToken (O : CharOracle) : TokenSpec String where
  maxLen := 1024
  construct s := .ok (String.ofList s)
  accept c := !QuotedIncludePath.escaped O c
  allowEscape := true
  escaped := QuotedIncludePath.escaped O

/-- `IncludePath::escaped`. -/
def IncludePath.escaped (c : Char) : Bool :=
  c == '\\' || c == '"' || c == ' '

/-- `impl Token for IncludePath`. -/
def includePathToken (O : CharOracle) : TokenSpec String where
  maxLen := 1024
  construct s := .ok (String.ofList s)
  accept c := !O.isControl c && !IncludePath.escaped c
  allowEscape := true
  escaped := IncludePath.escaped

/-- `StringParameter::escaped`. -/
def StringParameter.escaped (c : Char) : Bool :=
  c == '\\' || c == '"' || c == ' ' || c == '#' || c == ','

/-- `impl Token for StringParameter` (`MAX_LEN = QuotedStringParameter::MAX_LEN`). -/
def stringParameterToken (O : CharOracle) : TokenSpec String where
  maxLen := 1024
  construct s := .ok (String.ofList s)
  accept c := !O.isControl c && !StringParameter.escaped c
  allowEscape := true
  escaped := StringParameter.escaped

/-- `ChDir::escaped`. -/
def ChDir.escaped (c : Char) : Bool :=
  c == '\\' || c == '"' || c == ' '

/-- `ChDir::construct`: `*`, or a path without `*` (`SudoPath::try_from`). -/
def ChDir.construct (O : Oracles) (s : List Char) : Except ErrKind ChDir :=
  if s == ['*'] then
    .ok .any
  else if s.contains '*' then
    .error .pathContainsStar
  else
    match sudoPathTryFrom O s with
    | .ok p => .ok (.path p)
    | .error e => .error e

/-- `impl Token for ChDir`: first character `~`, `/` or `*`. -/
def chDirToken (O : Oracles) : TokenSpec ChDir where
  maxLen := 1024
  construct := ChDir.construct O
  accept c := !O.char.isControl c && !ChDir.escaped c
  accept1st c := c == '~' || c == '/' || c == '*'
  allowEscape := true
  escaped := ChDir.escaped

/-! ## `Unquoted<T>` -/

/-- `Unquoted::<T>::construct`: put a `\` before every character `T` escapes. -/
def Unquoted.construct (T : TokenSpec α) (text : List Char) : Except ErrKind String :=
  .ok (String.ofList (text.flatMap fun ch => if T.escaped ch then ['\\', ch] else [ch]))

/-- `impl<T: Token> Token for Unquoted<T>`: any character but `"` and control characters, no
escapes; the text is re-escaped for `T`. -/
def unquotedToken (O : CharOracle) (T : TokenSpec α) : TokenSpec String where
  maxLen := 1024
  construct := Unquoted.construct T
  accept c := c != '"' && !O.isControl c

end SudoersSpec.Syntax
