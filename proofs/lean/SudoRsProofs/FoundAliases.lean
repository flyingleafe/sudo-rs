import SudoRsProofs.Abs

/-!
# `FoundAliases::get` / `insert` refine lookup / update
-/

open Aeneas Aeneas.Std Result

namespace SudoRsProofs

/-- `get` on raw bytes: the last entry whose name has the bytes `a`, starting from `r`. -/
def lookupBytes (l : List (String × Bool)) (a : List U8) (r : Option Bool) : Option Bool :=
  l.foldl (fun r p => if sudo_rs.stringBytes p.1 = a then some p.2 else r) r

theorem get_loop_spec (v : sudo_rs.sudoers.FoundAliases) (a : Str) (r : Option Bool)
    (i : Usize) (hv : FoundFits v) :
    sudo_rs.sudoers.FoundAliases.get_loop v a r i
      ⦃ r' => r' = lookupBytes (v.val.drop i.val) a.val r ⦄ := by
  unfold sudo_rs.sudoers.FoundAliases.get_loop
  dsimp only
  split
  · rename_i hlt
    simp only [alloc.vec.Vec.index_slice_index]
    have hi : i.val < v.val.length := by scalar_tac
    have hdrop := List.drop_eq_getElem_cons hi
    step as ⟨nm, found, hnf⟩
    have hfit : Fits nm := by
      have := hv _ (List.getElem_mem hi); rw [← hnf] at this; exact this
    step as ⟨s, hs⟩
    step as ⟨b, hb⟩
    split <;> step as ⟨i2, hi2⟩ <;> step as ⟨r', hr'⟩ <;>
      rw [hr', lookupBytes, lookupBytes, hdrop, List.foldl_cons, ← hnf] <;> simp_all
  · rename_i hge
    have : v.val.length ≤ i.val := by scalar_tac
    simp [List.drop_eq_nil_of_le this, lookupBytes]
termination_by v.length - i.val
decreasing_by all_goals (simp_all; scalar_tac)

/-- `get` on raw bytes. -/
theorem get_bytes_spec (v : sudo_rs.sudoers.FoundAliases) (a : Str) (hv : FoundFits v) :
    sudo_rs.sudoers.FoundAliases.get v a ⦃ r => r = lookupBytes v.val a.val none ⦄ := by
  simpa using get_loop_spec v a none 0#usize hv

theorem lookupBytes_stringBytes (v : sudo_rs.sudoers.FoundAliases) (k : String) :
    lookupBytes v.val (sudo_rs.stringBytes k) none = absFound v k := by
  rw [absFound_apply, lookupBytes]
  congr
  funext r p
  simp [stringBytes_inj]

/-- **`FoundAliases::get` is lookup**: called with the `&str` of an alias name `k`, it returns
the abstract map's entry for `k`. -/
@[step]
theorem FoundAliases.get_spec (v : sudo_rs.sudoers.FoundAliases) (k : String) (a : Str)
    (hv : FoundFits v) (ha : a.val = sudo_rs.stringBytes k) :
    sudo_rs.sudoers.FoundAliases.get v a ⦃ r => r = absFound v k ⦄ := by
  have := get_bytes_spec v a hv
  rw [ha, lookupBytes_stringBytes] at this
  exact this

/-- **`FoundAliases::insert` is update** (and appends to the underlying list). -/
@[step]
theorem FoundAliases.insert_spec (v : sudo_rs.sudoers.FoundAliases) (k : String) (b : Bool)
    (h : v.val.length < Usize.max) :
    sudo_rs.sudoers.FoundAliases.insert v k b
      ⦃ v' => absFound v' = (absFound v).insert k b ∧ v'.val = v.val ++ [(k, b)] ⦄ := by
  unfold sudo_rs.sudoers.FoundAliases.insert
  step as ⟨v', hv'⟩
  exact ⟨absFound_push v v' k b hv', hv'⟩

/-- `FoundAliases::default()` is the empty map. -/
@[step]
theorem FoundAliases.default_spec :
    sudo_rs.sudoers.FoundAliases.Insts.CoreDefaultDefault.default
      ⦃ v => v.val = [] ∧ absFound v = SudoersSpec.FoundAliases.empty ⦄ := by
  simp [sudo_rs.sudoers.FoundAliases.Insts.CoreDefaultDefault.default,
    alloc.vec.Vec.Insts.CoreDefaultDefault.default, absFound]

end SudoRsProofs
