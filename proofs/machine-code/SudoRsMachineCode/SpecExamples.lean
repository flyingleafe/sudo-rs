module

public import SudoRsMachineCode.Spec

/-!
# Kernel-checked examples of the specification

Each example evaluates `nameOrIdParseUid` on a concrete argument of `sudo -u` (bytes of the
`SudoString` contents, without the trailing NUL) by `decide`, i.e. by kernel evaluation. They
document what the contract says on the inputs that matter for CVE-2019-14287 (`#-1`,
`#4294967295`): sudo-rs rejects `#-1` (unsigned parse, no sign), but accepts `#4294967295` as
the uid `u32::MAX`; the contract only states what `NameOrId::parse` returns, not whether later
code accepts that uid.
-/

namespace SudoRsMachineCode

open Arm64

/-- ASCII bytes of a string literal. -/
def ascii (s : String) : List (BitVec 8) :=
  s.toList.map fun c => BitVec.ofNat 8 c.toNat

example : nameOrIdParseUid (ascii "") = none := by decide
example : nameOrIdParseUid (ascii "root") = some .name := by decide
example : nameOrIdParseUid (ascii "1337") = some .name := by decide
example : nameOrIdParseUid (ascii "#1337") = some (.id 1337#32) := by decide
example : nameOrIdParseUid (ascii "#0") = some (.id 0#32) := by decide
example : nameOrIdParseUid (ascii "#007") = some (.id 7#32) := by decide
example : nameOrIdParseUid (ascii "#+5") = some (.id 5#32) := by decide
example : nameOrIdParseUid (ascii "#") = none := by decide
example : nameOrIdParseUid (ascii "#+") = none := by decide
example : nameOrIdParseUid (ascii "#-") = none := by decide
example : nameOrIdParseUid (ascii "#-1") = none := by decide
example : nameOrIdParseUid (ascii "#++5") = none := by decide
example : nameOrIdParseUid (ascii "# 5") = none := by decide
example : nameOrIdParseUid (ascii "#5 ") = none := by decide
example : nameOrIdParseUid (ascii "#1_000") = none := by decide
example : nameOrIdParseUid (ascii "#4294967295") = some (.id 0xffffffff#32) := by decide
example : nameOrIdParseUid (ascii "#4294967296") = none := by decide
example : nameOrIdParseUid (ascii "#18446744073709551615") = none := by decide
example : nameOrIdParseUid (ascii "#00000000000000000001") = some (.id 1#32) := by decide
example : nameOrIdParseUid (ascii "##1") = none := by decide
example : nameOrIdParseUid (ascii "x#1") = some .name := by decide

end SudoRsMachineCode
