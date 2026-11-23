import SudoersSpec.Syntax.BasicParser

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

end SudoersSpec.Syntax
