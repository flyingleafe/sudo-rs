import SudoRsProofs.SanitizeTables

/-!
# Alias preprocessing always returns

Total correctness of the extracted `sanitize_alias_table` and `sanitize_alias_tables`: they
return `ok` (no panic, no divergence) for every input whose strings fit in memory and whose
diagnostics vector cannot overflow. The hypotheses are representability conditions only:

* the names of definitions and of referenced aliases fit (`TableFits`; they are dereferenced
  to `&str` for diagnostics);
* the diagnostics already present, plus one per definition and one per member, fit in a
  `Vec` (`Vec::push` fails beyond `usize::MAX` elements).

The measure for the mutual recursion `visit`/`visit_loop` is the number of positions not yet
in `seen`, then the number of remaining members. Facts about the state after a recursive call
come from the partial-correctness postcondition `Post` of `SanitizeOrder.lean`, including the
potential `pot` that bounds the diagnostics added so far.
-/

open Aeneas Aeneas.Std Result
open Aeneas.Std.alloc.vec (Vec)
open sudo_rs sudo_rs.sudoers

namespace SudoRsProofs
namespace Sanitize

variable {T : Type}

theorem length_le_of_lt {D : List (RDef T)} {l : List Usize} (hnd : l.Nodup)
    (hlt : ∀ q ∈ l, q.val < D.length) : l.length ≤ D.length := by
  have hinj : Function.Injective (fun q : Usize => q.val) :=
    fun a b h => UScalar.val_eq_imp_iff.mpr h
  have hsub : (l.map (·.val)).Subperm (List.range D.length) :=
    (hnd.map hinj).subperm fun x hx => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
      exact List.mem_range.2 (hlt q hq)
  simpa using hsub.length_le

theorem index_eq {α : Type} (defs : Vec α) (i : Usize) (hi : i.val < defs.val.length) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) defs i = ok defs.val[i.val] := by
  rw [alloc.vec.Vec.index_slice_index]
  exact eq_ok_of_spec (alloc.vec.Vec.index_usize_spec defs i hi)

theorem deref_ok (s : String) (h : Fits s) :
    ∃ r, alloc.string.String.Insts.CoreOpsDerefDerefStr.deref s = ok r :=
  (exists_eq_ok_of_spec (String.deref_spec s h)).imp fun _ h => h.1

/-- Every definition name and every referenced alias name fits in memory. -/
def DefsFit (D : List (RDef T)) : Prop := ∀ d ∈ D, Fits (defName d) ∧ ItemsFit (defItems d)

/-- `visit` returns from every state at most `N` positions away from visiting everything. -/
def VisitTerm (defs : Vec (RDef T)) (N : Nat) : Prop :=
  ∀ (V : AliasVisitor T) (pos : Usize), V.table = defs → Inv defs.val V.seen V.order.val →
    defs.val.length - V.seen.length ≤ N → pos.val < defs.val.length →
    V.diagnostics.val.length + pot defs.val V.seen + 1 ≤ Usize.max →
    ∃ r, sanitize_alias_table.Visitor.visit V pos = ok r

/-- The member loop returns from every state at most `N` positions away from visiting
everything. -/
def LoopTerm (defs : Vec (RDef T)) (N : Nat) : Prop :=
  ∀ (it : core.slice.iter.Iter (RSpec T)) (back : Diags → Diags) (seen : HashKeys Usize)
    (order : Vec Usize) (diags : Diags),
    Inv defs.val seen order.val → defs.val.length - seen.length ≤ N →
    (∀ s ∈ it.slice.val.drop it.i, ∀ k, aliasName s = some k → Fits k) →
    diags.val.length + pot defs.val seen + (it.slice.val.drop it.i).length ≤ Usize.max →
    ∃ r, sanitize_alias_table.Visitor.visit_loop it back seen defs order diags = ok r

/-- The member loop terminates if `visit` does at the same distance: by induction on the
remaining members. -/
theorem loop_term {defs : Vec (RDef T)} {N : Nat} (hvisit : VisitTerm defs N) :
    LoopTerm defs N := by
  suffices h : ∀ m (it : core.slice.iter.Iter (RSpec T)) back seen (order : Vec Usize)
      (diags : Diags), (it.slice.val.drop it.i).length = m → Inv defs.val seen order.val →
      defs.val.length - seen.length ≤ N →
      (∀ s ∈ it.slice.val.drop it.i, ∀ k, aliasName s = some k → Fits k) →
      diags.val.length + pot defs.val seen + m ≤ Usize.max →
      ∃ r, sanitize_alias_table.Visitor.visit_loop it back seen defs order diags = ok r by
    intro it back seen order diags hinv hN hfit hbud
    exact h _ it back seen order diags rfl hinv hN hfit hbud
  intro m
  induction m with
  | zero =>
    intro it back seen order diags hm hinv hN hfit hbud
    have hrem : it.slice.val.drop it.i = [] := List.eq_nil_of_length_eq_zero hm
    rw [sanitize_alias_table.Visitor.visit_loop.eq_1, slice_next_nil it hrem]
    simp only [Std.bind_ok, uncurry_apply_pair]
    exact ⟨_, rfl⟩
  | succ m ih =>
    intro it back seen order diags hm hinv hN hfit hbud
    rcases hrem : it.slice.val.drop it.i with _ | ⟨elem, rest⟩
    · rw [hrem] at hm; cases hm
    rw [hrem] at hm hfit
    have hlen : rest.length = m := by simpa using hm
    obtain ⟨hnext, hrest⟩ := slice_next_cons it hrem
    have hfit' : ∀ s ∈ rest, ∀ k, aliasName s = some k → Fits k :=
      fun s hs k hk => hfit s (List.mem_cons_of_mem _ hs) k hk
    have hcont : ∀ back1 seen1 (order1 : Vec Usize) (diags1 : Diags),
        Inv defs.val seen1 order1.val → defs.val.length - seen1.length ≤ N →
        diags1.val.length + pot defs.val seen1 + m ≤ Usize.max →
        ∃ r, sanitize_alias_table.Visitor.visit_loop { it with i := it.i + 1 } back1 seen1 defs
          order1 diags1 = ok r := by
      intro back1 seen1 order1 diags1 hinv1 hN1 hbud1
      exact ih { it with i := it.i + 1 } back1 seen1 order1 diags1 (by simp [hrest, hlen]) hinv1
        hN1 (by simpa [hrest] using hfit') hbud1
    rw [sanitize_alias_table.Visitor.visit_loop.eq_1, hnext]
    simp only [Std.bind_ok, uncurry_apply_pair]
    have helem := hfit elem List.mem_cons_self
    cases elem with
    | Allow mt | Forbid mt =>
      simp only [sanitize_alias_table.remqualify, Std.bind_ok]
      cases mt with
      | All => exact hcont back seen order diags hinv hN (by omega)
      | Only _ => exact hcont back seen order diags hinv hN (by omega)
      | Alias k =>
        obtain ⟨o1, ho1, hpos⟩ := dependency_position_eq (alloc.vec.Vec.deref defs) k
        dsimp only
        rw [ho1]
        simp only [Std.bind_ok]
        cases o1 with
        | none =>
          obtain ⟨s1, hs1⟩ := deref_ok k (helem k rfl)
          rw [hs1]
          simp only [Std.bind_ok]
          obtain ⟨d1, hd1, hl1⟩ :=
            alias_diagnostic_eq diags sudoers.AliasDiagnostic.Undefined s1 (by omega)
          rw [hd1]
          simp only [Std.bind_ok]
          exact hcont back seen order d1 hinv hN (by omega)
        | some q =>
          dsimp only
          obtain ⟨hq, -⟩ := hpos q rfl
          simp only [Vec.deref_val] at hq
          obtain ⟨⟨V1, vb⟩, hv⟩ :=
            hvisit { seen := seen, table := defs, order := order, diagnostics := diags } q rfl
              hinv hN hq (by simp only; omega)
          obtain ⟨htab1, -, hpost1⟩ := visitor_spec.2 _ q hinv _ hv
          simp only at htab1 hpost1
          rw [hv]
          simp only [Std.bind_ok, uncurry_apply_pair]
          rw [htab1]
          have hpot1 := hpost1.pot
          have hlen1 : seen.length ≤ V1.seen.length :=
            (hinv.seen_nodup.subperm fun q hq => hpost1.seen_sub q hq).length_le
          exact hcont _ V1.seen V1.order V1.diagnostics hpost1.inv (by omega) (by omega)

/-- `visit` terminates if the member loop does at every smaller distance. -/
theorem visit_term {defs : Vec (RDef T)} (hfit : DefsFit defs.val) {N : Nat}
    (hloop : ∀ N' < N, LoopTerm defs N') : VisitTerm defs N := by
  intro V pos htab hinv hN hpos hbud
  have hmax : defs.val.length ≤ Usize.max := by scalar_tac
  obtain ⟨hfn, hfi⟩ := hfit _ (List.getElem_mem hpos)
  rw [sanitize_alias_table.Visitor.visit.eq_1, insert_usize]
  by_cases hs : pos ∈ V.seen
  · simp only [hs, ↓reduceIte, Std.bind_ok, uncurry_apply_pair, Bool.false_eq_true]
    rw [contains_usize]
    simp only [Std.bind_ok, Vec.deref_val]
    by_cases ho : pos ∈ V.order.val
    · simp only [ho, decide_true, ↓reduceIte]
      exact ⟨_, rfl⟩
    · simp only [ho, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [htab, index_eq defs pos hpos]
      simp only [Std.bind_ok]
      generalize defs.val[pos.val] = d at hfn
      obtain ⟨nm, members⟩ := d
      simp only [uncurry_apply_pair]
      obtain ⟨s1, hs1⟩ := deref_ok nm hfn
      rw [hs1]
      simp only [Std.bind_ok]
      obtain ⟨d1, hd1, -⟩ :=
        alias_diagnostic_eq V.diagnostics sudoers.AliasDiagnostic.Recursive s1 (by omega)
      rw [hd1]
      simp only [Std.bind_ok]
      exact ⟨_, rfl⟩
  · simp only [hs, ↓reduceIte, Std.bind_ok, uncurry_apply_pair]
    rw [htab, index_eq defs pos hpos]
    simp only [Std.bind_ok]
    have hinv1 := hinv.insert hs hpos
    have hpot := pot_insert hpos hs
    have hslen := length_le_of_lt hinv1.seen_nodup hinv1.seen_lt
    simp only [List.length_cons] at hslen
    have hitems : itemsAt defs.val pos = defItems defs.val[pos.val] := by
      simp [itemsAt, List.getElem?_eq_getElem hpos]
    generalize defs.val[pos.val] = d at hfn hfi hitems
    obtain ⟨nm, members⟩ := d
    simp only [defItems_mk] at hitems hfi
    rw [hitems] at hpot
    simp only [uncurry_apply_pair, core.slice.Slice.iter, Std.bind_ok]
    obtain ⟨r1, hr1⟩ := hloop (defs.val.length - (V.seen.length + 1)) (by omega)
      ⟨alloc.vec.Vec.deref members, 0⟩ (fun v3 => v3) (pos :: V.seen) V.order V.diagnostics
      hinv1 (by simp) (by simpa [ItemsFit] using hfi) (by simp; omega)
    rw [hr1]
    obtain ⟨seen2, defs2, order2, diags2, back2⟩ := r1
    obtain ⟨-, -, hpost⟩ := visitor_spec.1 _ _ _ _ _ _ (fun _ => rfl) hinv1 _ hr1
    simp only [Vec.deref_val, List.drop_zero, ← hitems] at hpost
    have hinv3 := (Post.visit_fresh hinv hs hpos hpost).inv
    have hl3 := length_le_of_lt hinv3.order_nodup
      (fun q hq => hinv3.seen_lt q (hinv3.order_sub q hq))
    simp only [List.length_append, List.length_singleton] at hl3
    simp only [Std.bind_ok, uncurry_apply_pair]
    obtain ⟨o3, ho3, -⟩ := push_eq order2 pos (by omega)
    rw [ho3]
    simp only [Std.bind_ok]
    exact ⟨_, rfl⟩

theorem visitor_term {defs : Vec (RDef T)} (hfit : DefsFit defs.val) (N : Nat) :
    VisitTerm defs N ∧ LoopTerm defs N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    have hv : VisitTerm defs N := visit_term hfit fun N' hN' => (ih N' hN').2
    exact ⟨hv, loop_term hv⟩

/-- The loop over the definitions terminates: by induction on the definitions left. -/
theorem roots_term {defs : Vec (RDef T)} (hfit : DefsFit defs.val) :
    ∀ m (e : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter (RDef T))) back seen
      (order : Vec Usize) (diags : Diags) dupe,
      defs.val.length - e.iter.i = m → e.iter.slice.val = defs.val → e.count.val = e.iter.i →
      Inv defs.val seen order.val →
      diags.val.length + pot defs.val seen + m ≤ Usize.max →
      ∃ r, sanitize_alias_table_loop e back seen defs order diags dupe = ok r := by
  have hmax : defs.val.length ≤ Usize.max := by scalar_tac
  intro m
  induction m with
  | zero =>
    intro e back seen order diags dupe hm hsl hcnt hinv hbud
    have hrem : defs.val.drop e.iter.i = [] := List.drop_eq_nil_of_le (by omega)
    rw [sanitize_alias_table_loop.eq_1, enumerate_next_nil e (by rw [hsl]; exact hrem)]
    simp only [Std.bind_ok, uncurry_apply_pair]
    exact ⟨_, rfl⟩
  | succ m ih =>
    intro e back seen order diags dupe hm hsl hcnt hinv hbud
    have hlt : e.iter.i < defs.val.length := by omega
    have hrem : defs.val.drop e.iter.i = defs.val[e.iter.i] :: defs.val.drop (e.iter.i + 1) :=
      List.drop_eq_getElem_cons hlt
    obtain ⟨hfn, -⟩ := hfit _ (List.getElem_mem hlt)
    generalize defs.val[e.iter.i] = d at hrem hfn
    obtain ⟨c, hc, hnext⟩ := enumerate_next_cons e (by rw [hsl]; exact hrem) (by omega)
    rw [sanitize_alias_table_loop.eq_1, hnext]
    simp only [Std.bind_ok, uncurry_apply_pair]
    obtain ⟨nm, members⟩ := d
    simp only [uncurry_apply_pair]
    rw [insert_string]
    have hcnt' : c.val = e.iter.i + 1 := by rw [hc, hcnt]
    have hm' : defs.val.length - (e.iter.i + 1) = m := by omega
    by_cases hn : nm ∈ dupe
    · simp only [hn, ↓reduceIte, Std.bind_ok, uncurry_apply_pair, Bool.false_eq_true]
      obtain ⟨s1, hs1⟩ := deref_ok nm hfn
      rw [hs1]
      simp only [Std.bind_ok]
      obtain ⟨d1, hd1, hl1⟩ :=
        alias_diagnostic_eq diags sudoers.AliasDiagnostic.Duplicate s1 (by omega)
      rw [hd1]
      simp only [Std.bind_ok]
      exact ih _ back seen order d1 dupe hm' hsl hcnt' hinv (by omega)
    · simp only [hn, ↓reduceIte, Std.bind_ok, uncurry_apply_pair]
      obtain ⟨⟨V1, vb⟩, hv⟩ := (visitor_term hfit _).1
        { seen := seen, table := defs, order := order, diagnostics := diags } e.count rfl hinv
        le_rfl (by omega) (by simp only; omega)
      obtain ⟨htab1, -, hpost1⟩ := visitor_spec.2 _ e.count hinv _ hv
      simp only at htab1 hpost1
      rw [hv]
      simp only [Std.bind_ok, uncurry_apply_pair]
      rw [htab1]
      have hpot1 := hpost1.pot
      exact ih _ _ V1.seen V1.order V1.diagnostics _ hm' hsl hcnt' hpost1.inv (by omega)

end Sanitize

open Sanitize in
/-- **The sanitizer always returns.** For every table whose names fit in memory and every
diagnostics vector with room for one more diagnostic per definition and per member, the
extracted `sanitize_alias_table` returns `ok`: no panic (index, arithmetic or allocation
failure) and no divergence. -/
theorem sanitize_alias_table_returns {T : Type} (defs : Vec (RDef T))
    (diags : Vec sudoers.Error) (hfit : ∀ d ∈ defs.val, Fits d.1 ∧ ItemsFit d.2.val)
    (hlen : diags.val.length + defs.val.length + (defs.val.map fun d => d.2.val.length).sum ≤
      Usize.max) :
    ∃ r, sanitize_alias_table defs diags = ok r := by
  unfold sanitize_alias_table
  simp only [std.collections.hash.set.HashSetTRandomStateGlobal.new, core.slice.Slice.iter,
    core.iter.traits.iterator.Iterator.enumerate.trait_default,
    core.iter.traits.iterator.Iterator.enumerate.default, Std.bind_ok]
  have hinv0 : Inv defs.val [] (alloc.vec.Vec.with_capacity Usize (alloc.vec.Vec.len defs)).val :=
    ⟨by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new],
      by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new], by simp, List.nodup_nil⟩
  have hpot : pot defs.val [] = (defs.val.map fun d => d.2.val.length).sum := pot_nil defs.val
  exact roots_term hfit _ _ _ [] _ diags [] rfl (by simp) (by simp) hinv0 (by simp; omega)

/-- The definitions plus the members of a table: at most this many diagnostics are added
for it (`sanitize_alias_table_distinct`). -/
def tableSize {T : Type} (t : VecOrd (RDef T)) : Nat :=
  t.2.val.length + (t.2.val.map fun d => d.2.val.length).sum

/-- **`sanitize_alias_tables` always returns** for tables whose names fit in memory, if the
diagnostics vector has room for one diagnostic per definition and per member of all four
tables. -/
theorem sanitize_alias_tables_returns (t : AliasTable) (diags : Vec sudoers.Error)
    (hu : TableFits t.user) (hh : TableFits t.host) (hc : TableFits t.cmnd)
    (hr : TableFits t.runas)
    (hlen : diags.val.length + tableSize t.user + tableSize t.host + tableSize t.cmnd +
      tableSize t.runas ≤ Usize.max) :
    ∃ r, sanitize_alias_tables t diags = ok r := by
  rcases t with ⟨⟨ou, du⟩, ⟨oh, dh⟩, ⟨oc, dc⟩, ⟨or, dr⟩⟩
  simp only [tableSize] at hlen
  unfold sanitize_alias_tables
  simp only [uncurry_apply_pair]
  obtain ⟨⟨o1, d1⟩, h1⟩ := sanitize_alias_table_returns du diags hu (by omega)
  have b1 := (sanitize_alias_table_distinct _ _ h1).2.2
  rw [h1]
  simp only [Std.bind_ok, uncurry_apply_pair]
  obtain ⟨⟨o2, d2⟩, h2⟩ := sanitize_alias_table_returns dh d1 hh (by omega)
  have b2 := (sanitize_alias_table_distinct _ _ h2).2.2
  rw [h2]
  simp only [Std.bind_ok, uncurry_apply_pair]
  obtain ⟨⟨o3, d3⟩, h3⟩ := sanitize_alias_table_returns dc d2 hc (by omega)
  have b3 := (sanitize_alias_table_distinct _ _ h3).2.2
  rw [h3]
  simp only [Std.bind_ok, uncurry_apply_pair]
  obtain ⟨⟨o4, d4⟩, h4⟩ := sanitize_alias_table_returns dr d3 hr (by omega)
  rw [h4]
  simp only [Std.bind_ok, uncurry_apply_pair]
  exact ⟨_, rfl⟩

end SudoRsProofs
