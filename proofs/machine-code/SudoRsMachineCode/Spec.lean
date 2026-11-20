module

public import Arm64

/-!
# Specification of `NameOrId::<UserId>::parse` at the machine-code level

The function under proof is sudo-rs's

```rust
impl<'a, T: FromStr> NameOrId<'a, T> {
    pub fn parse(input: &'a SudoString) -> Option<Self> {
        if input.is_empty() {
            None
        } else if let Some(stripped) = input.strip_prefix('#') {
            stripped.parse::<T>().ok().map(|id| Self::Id(id))
        } else {
            Some(Self::Name(input))
        }
    }
}
```

(`src/common/resolve.rs`) at `T = UserId`, whose `FromStr` is `s.parse::<libc::uid_t>()`
(`src/system/interface.rs`). It decides whether `sudo -u <arg>` names a user or a numeric uid
(`#<uid>`), the input class of CVE-2019-14287. It is compiled through the monomorphic wrapper
`sudo_rs_name_or_id_parse_uid(input, name_out, id_out) -> u32` of
`proofs/machine-code/rust/src/lib.rs`, which reports the `Option<NameOrId<UserId>>` as
`0` (`None`), `1` (`Name(name)`, `*name_out = name`) or `2` (`Id(uid)`, `*id_out = uid`).

This file is the whole specification: the Rust semantics as a Lean function and the `c_spec`
contract. It imports only the engine's trusted vocabulary (`Arm64`), not `ProofLib`.
-/

@[expose] public section

namespace SudoRsMachineCode

open Arm64

/-- `<u32 as core::str::FromStr>::from_str(src).ok()` of Rust 1.98.1 (`core::num`,
    `from_ascii_radix(src, 10)`): an optional leading `'+'`, then one or more ASCII digits
    (leading zeros allowed) whose value is below `2 ^ 32`. The empty string, a lone `'+'` or
    `'-'`, any other byte (`'-'`, whitespace, `'_'`, non-ASCII) and overflow are errors, all
    mapped to `none` by `.ok()`. `parseDecimalU32` is the engine's trusted digits-only parser
    (`Arm64.Trusted.Spec.AsciiNum`): `none` on `[]` or any non-digit byte, otherwise the value if
    it is below `2 ^ 32`. -/
def rustParseU32 : List (BitVec 8) → Option (BitVec 32)
  | 0x2b#8 :: digits => parseDecimalU32 digits
  | src => parseDecimalU32 src

/-- The value of `Option<NameOrId<'_, UserId>>` without the borrowed name (the `Name` payload is
    always the input reference itself; the contract below pins it to `input`). -/
inductive ParsedUser where
  /-- `Some(NameOrId::Name(input))`. -/
  | name
  /-- `Some(NameOrId::Id(UserId(uid)))`. -/
  | id (uid : BitVec 32)
  deriving DecidableEq, Repr

/-- `NameOrId::<UserId>::parse` on a `SudoString` whose contents (without the trailing NUL that
    `SudoString` stores) are `content`: empty is `None`; a leading `'#'` (`0x23`) makes the rest
    a `u32` uid (`None` if it does not parse); anything else is a user name. -/
def nameOrIdParseUid : List (BitVec 8) → Option ParsedUser
  | [] => none
  | 0x23#8 :: rest => (rustParseU32 rest).map ParsedUser.id
  | _ :: _ => some .name

/-- The wrapper's return code for each result. -/
def resultCode : Option ParsedUser → BitVec 32
  | none => 0#32
  | some .name => 1#32
  | some (.id _) => 2#32

/-- The value `*name_out` holds after the call. -/
def nameOutAfter (input oldName : BitVec 64) : Option ParsedUser → BitVec 64
  | some .name => input
  | _ => oldName

/-- The value `*id_out` holds after the call. -/
def idOutAfter (oldId : BitVec 32) : Option ParsedUser → BitVec 32
  | some (.id uid) => uid
  | _ => oldId

/-- Contract of `sudo_rs_name_or_id_parse_uid(input, name_out, id_out)`.

    `input` points to a `SudoString`, i.e. an `alloc::string::String` header (rustc 1.98.1
    layout on aarch64: capacity at `+0`, buffer pointer at `+8`, length at `+16`) whose buffer
    holds `content` followed by the NUL byte `SudoString` keeps at the end. The header and the
    buffer are owned read-only (`↦ᵣ`); the two out-parameters are owned writable; the callee
    may use the 16 bytes below the stack pointer. Any `content` of any length is allowed
    (not only UTF-8 without interior NULs, as `SudoString` guarantees).

    On return: `w0 = resultCode r` for `r = nameOrIdParseUid content`, `*name_out` and
    `*id_out` hold `nameOutAfter`/`idOutAfter`, the header and the buffer are unchanged, and
    (from `subroutine_ok`) the call terminated normally, without panic, exit or fault, with the
    stack pointer and the callee-saved registers restored and every byte outside these regions
    (the frame) unchanged. -/
c_spec parseUidSpec (input nameOut idOut : ptr)
    (ghost cap buf : u64) (ghost content : List (BitVec 8))
    (ghost oldName : u64) (ghost oldId : u32) : u32
  requires_pure content.length + 1 < 2 ^ 64
  preserves (input ↦₆₄ᵣ cap) ∗ ((input + 8#64) ↦₆₄ᵣ buf) ∗
    ((input + 16#64) ↦₆₄ᵣ BitVec.ofNat 64 (content.length + 1)) ∗
    (buf ↦ᵣ (content ++ [0#8]))
  requires (nameOut ↦₆₄ oldName) ∗ (idOut ↦₃₂ oldId)
  stack16
  returns resultCode (nameOrIdParseUid content)
  ensures (nameOut ↦₆₄ nameOutAfter input oldName (nameOrIdParseUid content)) ∗
    (idOut ↦₃₂ idOutAfter oldId (nameOrIdParseUid content))

end SudoRsMachineCode
