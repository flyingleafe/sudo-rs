import SudoRs

/-!
# Generic helpers for the refinement proofs

* turning a spec `x ⦃ y => y = v ⦄` into an equation `x = ok v`;
* the string model of `SudoRs/FunsExternal.lean`: `Fits`, `stringBytes` injectivity, and the
  specs of `String::as_str` / `Deref<str>` / `str == str`.
-/

open Aeneas Aeneas.Std Result

namespace SudoRsProofs

/-- A specification whose postcondition pins the value down is an equation. -/
theorem eq_ok_of_spec {α : Type _} {x : Result α} {v : α} (h : x ⦃ y => y = v ⦄) :
    x = ok v := by
  cases x <;> simp_all

/-- Conversely, an equation gives every postcondition that holds of the value. -/
theorem spec_of_eq_ok {α : Type _} {x : Result α} {v : α} {P : α → Prop} (h : x = ok v)
    (hP : P v) : x ⦃ P ⦄ := by
  subst h; simpa using hP

theorem spec_eq_iff {α : Type _} {x : Result α} {v : α} : x ⦃ y => y = v ⦄ ↔ x = ok v :=
  ⟨eq_ok_of_spec, fun h => spec_of_eq_ok h rfl⟩

/-- A specification means: the computation returns `ok v` for some `v` satisfying the
postcondition (no panic, no divergence). -/
theorem exists_eq_ok_of_spec {α : Type _} {x : Result α} {P : α → Prop} (h : x ⦃ P ⦄) :
    ∃ v, x = ok v ∧ P v := by
  cases x <;> simp_all

/-! ## Strings -/

/-- A Lean `String` that can be a Rust `String`: its UTF-8 encoding fits in `usize`. Every
Rust `String` satisfies it (Rust caps allocations at `isize::MAX` bytes). -/
def Fits (s : String) : Prop := (sudo_rs.stringBytes s).length ≤ Usize.max

/-- The `&str` of a string that fits. -/
def strOf (s : String) (h : Fits s) : Str := Slice.from (sudo_rs.stringBytes s) h

@[simp] theorem strOf_val (s : String) (h : Fits s) : (strOf s h).val = sudo_rs.stringBytes s := by
  exact Slice.from_val _ _

theorem stringBytes_inj {s t : String} : sudo_rs.stringBytes s = sudo_rs.stringBytes t ↔ s = t := by
  constructor
  · intro h
    simp only [sudo_rs.stringBytes] at h
    have h1 : s.toByteArray.data.toList = t.toByteArray.data.toList := by
      refine List.map_injective_iff.mpr ?_ h
      intro a b hab
      simp only [UScalar.mk.injEq] at hab
      exact UInt8.toBitVec_inj.mp hab
    have h2 : s.toByteArray = t.toByteArray := by
      cases hs : s.toByteArray; cases ht : t.toByteArray
      rw [hs, ht] at h1
      simp_all [Array.toList_inj]
    exact String.toByteArray_inj.mp h2
  · rintro rfl; rfl

theorem strOfString_eq {s : String} (h : Fits s) : sudo_rs.strOfString s = ok (strOf s h) := by
  have h' : (sudo_rs.stringBytes s).length ≤ Usize.max := h
  unfold sudo_rs.strOfString
  simp only [h', _root_.dite_true]; rfl

@[step]
theorem String.as_str_spec (s : String) (h : Fits s) :
    alloc.string.String.as_str s ⦃ r => r.val = sudo_rs.stringBytes s ⦄ := by
  simp [alloc.string.String.as_str, strOfString_eq h]

@[step]
theorem String.deref_spec (s : String) (h : Fits s) :
    alloc.string.String.Insts.CoreOpsDerefDerefStr.deref s ⦃ r => r.val = sudo_rs.stringBytes s ⦄ := by
  simp [alloc.string.String.Insts.CoreOpsDerefDerefStr.deref, strOfString_eq h]

@[step]
theorem Str.eq_spec (a b : Str) :
    Str.Insts.CoreCmpPartialEqStr.eq a b ⦃ r => r = decide (a.val = b.val) ⦄ := by
  simp [Str.Insts.CoreCmpPartialEqStr.eq]
  exact Slice.eq_iff a b

@[step]
theorem String.clone_spec (s : String) :
    alloc.string.String.Insts.CoreCloneClone.clone s ⦃ r => r = s ⦄ := by
  simp [alloc.string.String.Insts.CoreCloneClone.clone]

/-! ## Vec / slices -/

@[simp] theorem Vec.deref_val {T : Type _} (v : alloc.vec.Vec T) :
    (alloc.vec.Vec.deref v).val = v.val :=
  Slice.from_val _ _

end SudoRsProofs
