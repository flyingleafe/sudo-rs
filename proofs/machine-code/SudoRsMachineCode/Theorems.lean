module

public import SudoRsMachineCode.Proof
public import SudoRsMachineCode.Generated.SudoRsParseUidPlacedObj
public import SudoRsMachineCode.Generated.SudoRsParseUidPlacedWitness
public import ProofLib.Placed.Fetch

/-!
# The machine-code theorem for every placement of the compiled library

`parseUid_codeAt_ok` (`SudoRsMachineCode.Proof`) holds for any program that has the 81 proved
instruction words at the entry address. This file discharges that hypothesis for the library
`rust-obj2lean` exported from the compiled object (`sudoRsParseUidLib`, the relocatable text
block of `sudo_rs_name_or_id_parse_uid` and the functions next to it): under every placement the
linker may choose (`Placeable`), the placed program has exactly those words at the function's
address. The result is the engine's layout-generic contract `PlacedLib.subroutineOk`.
-/

@[expose] public section

namespace SudoRsMachineCode

open Arm64
open ProofLib

private theorem patchRelocs_nil (words : List (BitVec 32)) (a : BitVec 64)
    (resolve : String → BitVec 64) :
    Obj.patchRelocs [] words a resolve = words := by
  unfold Obj.patchRelocs
  have h : ∀ (ws : List (BitVec 32)) (k : Nat),
      (ws.zipIdx k).map (fun (w, _) => w) = ws := by
    intro ws
    induction ws with
    | nil => intro _; rfl
    | cons w ws ih => intro k; simp [List.zipIdx_cons, ih]
  exact h words 0

/-- `sudo_rs_name_or_id_parse_uid` starts at byte `0x224` of the library's text block. -/
theorem parseUid_symbol :
    Obj.lookup "sudo_rs_name_or_id_parse_uid" sudoRsParseUidLib.text.symbols = some 0x224 := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Under every valid placement, the placed program holds `parseUidWords` at the function's
    address (no relocation falls inside these words, so they do not depend on the placement). -/
theorem parseUid_placed_hasWords (pl : Obj.Placement) (hP : sudoRsParseUidLib.Placeable pl) :
    (sudoRsParseUidLib.program pl).hasWords
      ((sudoRsParseUidLib.program pl).fnAddr "sudo_rs_name_or_id_parse_uid") parseUidWords := by
  have ⟨hfn, hfn'⟩ := Obj.PlacedLib.fnAddr_program (X := fun _ => none) (O := fun _ => none)
    (svc := Syscall.standard) (pl := pl) parseUid_symbol
  rw [hfn, hfn']
  have hw := (Obj.CodeBlock.hasWords_of_checkSegment (prog := sudoRsParseUidLib.program pl)
    (fo := 0x224) (ws := parseUidWords) (R := []) hP.text rfl rfl (by decide +kernel)
    (Obj.PlacedLib.hookFree_program_noOverrides hP.text (by decide +kernel))).1
  rw [patchRelocs_nil] at hw
  exact hw

/-- **Main theorem.** For every placement `pl` under which the compiled library is `Placeable`,
    the machine code of `sudo_rs_name_or_id_parse_uid` (rustc 1.98.1, aarch64, `opt-level = 3`)
    satisfies `parseUidSpec`: it terminates normally (no panic, exit or fault) and returns, it
    reads only the `String` header and `content ++ [0]`, writes only `*name_out`, `*id_out` and
    its 16-byte stack frame, restores the stack pointer and the callee-saved registers, and its
    return code and outputs are those of `NameOrId::<UserId>::parse` (`nameOrIdParseUid`), for
    every `content` with `content.length + 1 < 2 ^ 64`. -/
theorem parseUid_placed_ok :
    sudoRsParseUidLib.subroutineOk "sudo_rs_name_or_id_parse_uid" (fun _ => parseUidSpec) :=
  ⟨by decide +kernel, fun pl hP =>
    parseUid_codeAt_ok _ _ (by
      have h := parseUid_placed_hasWords pl hP
      rwa [(Obj.PlacedLib.fnAddr_program (X := fun _ => none) (O := fun _ => none)
        (svc := Syscall.standard) (pl := pl) parseUid_symbol).1] at h)⟩

/-- Non-vacuity: some placement satisfies the hypothesis of `parseUid_placed_ok` (the generated,
    kernel-checked canonical placement of `SudoRsParseUidPlacedWitness`). -/
theorem parseUid_placed_nonvacuous : ∃ pl, sudoRsParseUidLib.Placeable pl :=
  sudoRsParseUidLib_exists_placeable

/-- The contract admits no abnormal outcome: its panic, exit and out-of-memory postconditions
    are `⌜False⌝` (the `c_spec` defaults), so `subroutine_ok … parseUidSpec` means that every
    run returns normally. -/
theorem parseUidSpec_no_abnormal_outcome :
    (∀ x s sf, parseUidSpec.onPanic x s sf = ⌜False⌝) ∧
    (∀ x c s sf, parseUidSpec.onExit x c s sf = ⌜False⌝) ∧
    (∀ x s sf, parseUidSpec.onOom x s sf = ⌜False⌝) :=
  ⟨fun _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩

end SudoRsMachineCode

#print axioms SudoRsMachineCode.parseUid_codeAt_ok
#print axioms SudoRsMachineCode.parseUid_placed_hasWords
#print axioms SudoRsMachineCode.parseUid_placed_ok
#print axioms SudoRsMachineCode.parseUidSpec_no_abnormal_outcome
#print axioms SudoRsMachineCode.parseUid_placed_nonvacuous
#print axioms SudoRsMachineCode.parseDecimalU32_of_digits
#print axioms SudoRsMachineCode.parseDecimalU32_of_nondigit
#print axioms SudoRsMachineCode.parseDecimalU32_of_big
