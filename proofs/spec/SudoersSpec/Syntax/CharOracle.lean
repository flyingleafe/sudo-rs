import SudoersSpec.Syntax.Status

/-!
# Character classes

The parser uses nine `char` predicates. Four are ASCII classes and are definitions here. Five
depend on the Unicode tables of the Rust standard library and are the fields of `CharOracle`
(PLAN.md section 5.3): the reference parser is a function of the oracle.

`CharOracle.latin1` is an instance for tests, equal to the Rust predicates on the code points
`0x00` to `0xFF` and `false` above. Inputs of the tests in this directory stay in that range.
-/

namespace SudoersSpec.Syntax

/-- `char::is_ascii_digit`: `'0'..='9'`. -/
def isAsciiDigit (c : Char) : Bool :=
  '0' ≤ c && c ≤ '9'

/-- `char::is_ascii_uppercase`: `'A'..='Z'`. -/
def isAsciiUppercase (c : Char) : Bool :=
  'A' ≤ c && c ≤ 'Z'

/-- `char::is_ascii_lowercase`: `'a'..='z'` (used by `is_ascii_alphanumeric`). -/
def isAsciiLowercase (c : Char) : Bool :=
  'a' ≤ c && c ≤ 'z'

/-- `char::is_ascii_alphanumeric`. -/
def isAsciiAlphanumeric (c : Char) : Bool :=
  isAsciiDigit c || isAsciiUppercase c || isAsciiLowercase c

/-- `char::is_ascii_hexdigit`: `'0'..='9' | 'A'..='F' | 'a'..='f'`. -/
def isAsciiHexdigit (c : Char) : Bool :=
  isAsciiDigit c || ('A' ≤ c && c ≤ 'F') || ('a' ≤ c && c ≤ 'f')

/-- The Unicode-aware `char` predicates of the Rust standard library that the parser calls. -/
structure CharOracle where
  /-- `char::is_alphanumeric` (`Alphabetic` or `Numeric`). -/
  isAlphanumeric : Char → Bool
  /-- `char::is_uppercase` (derived property `Uppercase`). -/
  isUppercase : Char → Bool
  /-- `char::is_numeric` (general categories `Nd`, `Nl`, `No`). -/
  isNumeric : Char → Bool
  /-- `char::is_control` (general category `Cc`). -/
  isControl : Char → Bool
  /-- `char::is_whitespace` (property `White_Space`). -/
  isWhitespace : Char → Bool

/-- Test instance: the Rust predicates on `U+0000..=U+00FF`, `false` above. Checked against
`rustc` 1.99 for all 256 code points when it was written; see `Syntax/README.md`. -/
def CharOracle.latin1 : CharOracle where
  isAlphanumeric c :=
    isAsciiAlphanumeric c || c.val == 0xAA || c.val == 0xB2 || c.val == 0xB3 ||
      c.val == 0xB5 || c.val == 0xB9 || c.val == 0xBA || (0xBC ≤ c.val && c.val ≤ 0xBE) ||
      (0xC0 ≤ c.val && c.val ≤ 0xFF && c.val != 0xD7 && c.val != 0xF7)
  isUppercase c :=
    isAsciiUppercase c || (0xC0 ≤ c.val && c.val ≤ 0xDE && c.val != 0xD7)
  isNumeric c :=
    isAsciiDigit c || c.val == 0xB2 || c.val == 0xB3 || c.val == 0xB9 ||
      (0xBC ≤ c.val && c.val ≤ 0xBE)
  isControl c :=
    c.val < 0x20 || (0x7F ≤ c.val && c.val ≤ 0x9F)
  isWhitespace c :=
    (0x09 ≤ c.val && c.val ≤ 0x0D) || c.val == 0x20 || c.val == 0x85 || c.val == 0xA0

end SudoersSpec.Syntax
