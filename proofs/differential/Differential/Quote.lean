/-!
# The quoting rule of the parser dump (`proofs/parser/DUMP.md`)

A string is written as `"` + its characters + `"`: printable ASCII (U+0020 to U+007E) other
than `"` and `\` as is, `"` as `\"`, `\` as `\\`, and every other code point as `\u{h}` with
`h` its lowercase hexadecimal value without leading zeros. The image is printable ASCII and
`unquote` inverts `quote`.
-/

namespace Differential.Quote

/-- Lowercase hexadecimal, no leading zeros (`0` for zero). -/
def hex (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

def quote (s : String) : String := Id.run do
  let mut out := "\""
  for c in s.toList do
    if c == '"' then out := out ++ "\\\""
    else if c == '\\' then out := out ++ "\\\\"
    else if 0x20 ≤ c.toNat && c.toNat ≤ 0x7e then out := out.push c
    else out := out ++ "\\u{" ++ hex c.toNat ++ "}"
  return out ++ "\""

/-- Value of a lowercase or uppercase hexadecimal digit. -/
def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Decode one quoted string at the start of `cs`; returns it and the rest. -/
partial def unquoteChars (cs : List Char) : Option (String × List Char) :=
  match cs with
  | '"' :: rest => go rest ""
  | _ => none
where
  go : List Char → String → Option (String × List Char)
  | '"' :: rest, acc => some (acc, rest)
  | '\\' :: '"' :: rest, acc => go rest (acc.push '"')
  | '\\' :: '\\' :: rest, acc => go rest (acc.push '\\')
  | '\\' :: 'u' :: '{' :: rest, acc => hexes rest 0 0 acc
  | c :: rest, acc =>
    if c != '\\' && 0x20 ≤ c.toNat && c.toNat ≤ 0x7e then go rest (acc.push c) else none
  | [], _ => none
  hexes : List Char → Nat → Nat → String → Option (String × List Char)
  | '}' :: rest, n, k, acc =>
    if k == 0 || n > 0x10FFFF || (0xD800 ≤ n && n ≤ 0xDFFF) then none
    else go rest (acc.push (Char.ofNat n))
  | c :: rest, n, k, acc => do
    let d ← hexDigit? c
    if k ≥ 6 then none else hexes rest (n * 16 + d) (k + 1) acc
  | [], _, _, _ => none

/-- Decode a string that consists of exactly one quoted string. -/
def unquote? (s : String) : Option String :=
  match unquoteChars s.toList with
  | some (r, []) => some r
  | _ => none

end Differential.Quote
