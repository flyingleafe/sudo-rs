import SudoRsProofs.FindItem

/-!
# `get_aliases` refines `SudoersSpec.getAliases`
-/

open Aeneas Aeneas.Std Result

namespace SudoRsProofs

variable {P : Type _} {T β : Type}

/-- One iteration of `get_aliases` on an abstracted definition, in the shape of the Rust code. -/
theorem getAliasesStep_absDef (p : β → Bool) (A : SudoersSpec.FoundAliases) (f : T → β)
    (id : String) (list : alloc.vec.Vec (RSpec T)) :
    SudoersSpec.getAliasesStep p A (absDef f (id, list)) =
      if (SudoersSpec.findItem p A (SudoersSpec.withUnit (absSpecList f list.val))).isSome then
        A.insert id true
      else if (SudoersSpec.findItem p A
          (initialItems true ++ SudoersSpec.withUnit (absSpecList f list.val))).isSome then A
      else A.insert id false := by
  simp only [SudoersSpec.getAliasesStep, absDef, initialItems, ite_true, List.singleton_append,
    Option.isNone_iff_eq_none, ← Option.not_isSome_iff_eq_none]
  by_cases h1 : (SudoersSpec.findItem p A (SudoersSpec.withUnit (absSpecList f list.val))).isSome
  · simp [h1]
  · by_cases h2 : (SudoersSpec.findItem p A ((SudoersSpec.Qualified.allow SudoersSpec.Meta.all, ()) ::
        SudoersSpec.withUnit (absSpecList f list.val))).isSome <;> simp [h1, h2]

theorem get_aliases_loop_spec (inst : core.ops.function.Fn P T Bool) (pred : P) (f : T → β)
    (p : β → Bool) (hp : ∀ x, inst.call pred x = ok (p (f x)))
    (order : alloc.vec.Vec Usize) (defs : alloc.vec.Vec (RDef T))
    (set : sudo_rs.sudoers.FoundAliases) (i : Usize)
    (hwf : ∀ j ∈ order.val, j.val < defs.val.length)
    (hfit : ∀ d ∈ defs.val, Fits d.1 ∧ ItemsFit d.2.val)
    (hset : FoundFits set) (hlen : set.val.length ≤ i.val) :
    sudo_rs.sudoers.get_aliases_loop inst pred order defs set i ⦃ r =>
      absFound r = (((order.val.drop i.val).filterMap fun j => defs.val[j.val]?).map
        (absDef f)).foldl (SudoersSpec.getAliasesStep p) (absFound set) ∧ FoundFits r ⦄ := by
  unfold sudo_rs.sudoers.get_aliases_loop
  dsimp only
  split
  · have hlt : i.val < order.val.length := by scalar_tac
    have hdrop := List.drop_eq_getElem_cons hlt
    simp only [alloc.vec.Vec.index_slice_index]
    step as ⟨j, hj⟩
    have hjlt : j.val < defs.val.length := hwf j (by rw [hj]; exact List.getElem_mem hlt)
    apply WP.spec_bind (alloc.vec.Vec.index_usize_spec defs j hjlt)
    intro d hd
    obtain ⟨hdn, hdi⟩ := hfit d (by rw [hd]; exact List.getElem_mem hjlt)
    have hfm : ((order.val.drop i.val).filterMap fun j => defs.val[j.val]?) =
        d :: ((order.val.drop (i.val + 1)).filterMap fun j => defs.val[j.val]?) := by
      rw [hdrop, List.filterMap_cons, ← hj, List.getElem?_eq_getElem hjlt, ← hd]
    rw [hfm, List.map_cons, List.foldl_cons]
    obtain ⟨id, list⟩ := d
    have hmax : set.val.length < Usize.max := by scalar_tac
    simp only [getAliasesStep_absDef]
    have hdi' : ItemsFit (alloc.vec.Vec.deref list).val := by simpa using hdi
    step with find_item_spec inst pred f p hp (alloc.vec.Vec.deref list) set hset hdi' as ⟨b, hb⟩
    simp only [Vec.deref_val] at hb
    -- what the recursive call needs from the new set
    have hrec : ∀ set1 : sudo_rs.sudoers.FoundAliases, FoundFits set1 →
        set1.val.length ≤ i.val + 1 →
        (do
          let i3 ← i + 1#usize
          sudo_rs.sudoers.get_aliases_loop inst pred order defs set1 i3) ⦃ r =>
          absFound r = (((order.val.drop (i.val + 1)).filterMap fun j => defs.val[j.val]?).map
            (absDef f)).foldl (SudoersSpec.getAliasesStep p) (absFound set1) ∧ FoundFits r ⦄ := by
      intro set1 hfit1 hlen1
      step as ⟨i3, hi3⟩
      have hlen3 : set1.val.length ≤ i3.val := by scalar_tac
      step with get_aliases_loop_spec inst pred f p hp order defs set1 i3 hwf hfit hfit1 hlen3
        as ⟨r, hr, hrfit⟩
      exact ⟨by rw [hr, hi3], hrfit⟩
    have hins : ∀ bv : Bool, ∀ set1 : sudo_rs.sudoers.FoundAliases,
        set1.val = set.val ++ [(id, bv)] → FoundFits set1 := by
      intro bv set1 h q hq
      rw [h, List.mem_append, List.mem_singleton] at hq
      rcases hq with hq | rfl
      · exact hset q hq
      · exact hdn
    split
    · rename_i hbt
      step as ⟨s1, hs1⟩
      step as ⟨set1, hset1, hset1v⟩
      subst hs1
      have := hrec set1 (hins true set1 hset1v) (by simp [hset1v]; scalar_tac)
      rw [← hb, hbt, ← hset1]
      simpa using this
    · rename_i hbf
      have hbf' : (SudoersSpec.findItem p (absFound set)
          (SudoersSpec.withUnit (absSpecList f list.val))).isSome = false := by
        rw [← hb]; simpa using hbf
      step with find_item_after_spec inst pred f p hp true (alloc.vec.Vec.deref list) set hset
        hdi' as ⟨b1, hb1⟩
      simp only [Vec.deref_val] at hb1
      split
      · rename_i hb1t
        have := hrec set hset (Nat.le_succ_of_le hlen)
        rw [hbf', ← hb1, hb1t]
        simpa using this
      · rename_i hb1f
        step as ⟨s2, hs2⟩
        step as ⟨set1, hset1, hset1v⟩
        subst hs2
        have := hrec set1 (hins false set1 hset1v) (by simp [hset1v]; scalar_tac)
        have hb1f' : b1 = false := by simpa using hb1f
        rw [hbf', ← hb1, hb1f', ← hset1]
        simpa using this
  · have : order.val.length ≤ i.val := by scalar_tac
    simp [List.drop_eq_nil_of_le this, hset]
termination_by order.val.length - i.val
decreasing_by all_goals (simp_all; scalar_tac)

/-- **`get_aliases` is `getAliases`**: for a well-formed table (`TableWF`: every position in the
processing order is valid) whose names fit in memory, the returned `FoundAliases` abstracts to
`SudoersSpec.getAliases` on the abstracted table; all names it stores fit in memory. -/
@[step]
theorem get_aliases_spec (inst : core.ops.function.Fn P T Bool) (pred : P) (f : T → β)
    (p : β → Bool) (hp : ∀ x, inst.call pred x = ok (p (f x)))
    (table : sudo_rs.sudoers.VecOrd (RDef T)) (hwf : TableWF table) (hfit : TableFits table) :
    sudo_rs.sudoers.get_aliases inst table pred ⦃ r =>
      absFound r = SudoersSpec.getAliases (absTable f table) p ∧ FoundFits r ⦄ := by
  obtain ⟨order, defs⟩ := table
  unfold sudo_rs.sudoers.get_aliases
  step as ⟨set, hsv, hsabs⟩
  have hset : FoundFits set := by intro q hq; simp [hsv] at hq
  step with get_aliases_loop_spec inst pred f p hp order defs set 0#usize hwf hfit hset
    (by simp [hsv]) as ⟨r, hr, hrfit⟩
  refine ⟨?_, hrfit⟩
  rw [hr, hsabs]
  rfl

/-- `get_aliases_spec` as an equation: the call terminates without panicking. -/
theorem get_aliases_eq (inst : core.ops.function.Fn P T Bool) (pred : P) (f : T → β)
    (p : β → Bool) (hp : ∀ x, inst.call pred x = ok (p (f x)))
    (table : sudo_rs.sudoers.VecOrd (RDef T)) (hwf : TableWF table) (hfit : TableFits table) :
    ∃ r, sudo_rs.sudoers.get_aliases inst table pred = ok r ∧
      absFound r = SudoersSpec.getAliases (absTable f table) p :=
  exists_eq_ok_of_spec (get_aliases_spec inst pred f p hp table hwf hfit) |>.imp
    fun _ h => ⟨h.1, h.2.1⟩

end SudoRsProofs
