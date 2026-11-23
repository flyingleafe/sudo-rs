import SudoRsProofs.SanitizeTotal
import SudoersSpec.Analysis.AliasOrder
import Init.Data.String.Lemmas.Lossy

/-! Exact analyzer order, including duplicate, missing, and recursive alias diagnostics. -/

open Aeneas Aeneas.Std Result
open Aeneas.Std.alloc.vec (Vec)
open sudo_rs sudo_rs.sudoers

namespace SudoRsProofs
namespace AliasOrder

open Sanitize SudoersSpec.Analysis
open SudoersSpec.Analysis.AliasOrder (State visitRefs visit roots defAt)

variable {T β : Type}

private def modelTable (f : T → β) (defs : Vec (RDef T)) : Array (SudoersSpec.Def β) :=
  (defs.val.map (absDef f)).toArray

/-- Project the live visitor state, ignoring the diagnostics present at entry. -/
private def state (base : Nat) (seen : List Usize) (order : Vec Usize) (d : Diags) : State :=
  ⟨seen.map (·.val), (order.val.map (·.val)).toArray,
    ((d.val.drop base).map sudoers.Error.message).toArray⟩

private theorem state_push (base : Nat) (seen : List Usize) (d : Diags)
    {order order' : Vec Usize} {i : Usize} (h : alloc.vec.Vec.push order i = ok order') :
    state base seen order' d = { state base seen order d with
      order := (state base seen order d).order.push i.val } := by
  simp [state, push_ok h]

private def message (k : sudoers.AliasDiagnostic) (n : String) : String :=
  match k with
  | .Undefined => SudoersSpec.Analysis.AliasOrder.undefinedMessage n
  | .Recursive => SudoersSpec.Analysis.AliasOrder.recursiveMessage n
  | .Duplicate => SudoersSpec.Analysis.AliasOrder.duplicateMessage n

private theorem decode_deref {n : String} {s : Str}
    (h : alloc.string.String.Insts.CoreOpsDerefDerefStr.deref n = ok s) : stringOfStr s = n := by
  unfold alloc.string.String.Insts.CoreOpsDerefDerefStr.deref sudo_rs.strOfString at h
  split at h
  · obtain rfl := Result.ok_injective h
    have hbyte : ((fun u : U8 => UInt8.ofNat u.val) ∘ fun b : UInt8 =>
        (⟨b.toBitVec⟩ : U8)) = id := funext fun _ => UInt8.ofNat_toNat
    simp only [stringOfStr, Slice.from_val, sudo_rs.stringBytes, List.map_map,
      hbyte, List.map_id, Array.toArray_toList]
    exact String.fromUTF8Lossy_toByteArray
  · simp at h

private theorem state_diag {base : Nat} {d d' : Diags} {k : sudoers.AliasDiagnostic}
    {n : String} {s : Str} (hbase : base ≤ d.val.length)
    (hs : alloc.string.String.Insts.CoreOpsDerefDerefStr.deref n = ok s)
    (hd : sudoers.alias_diagnostic d k s = ok d') (seen : List Usize) (order : Vec Usize) :
    state base seen order d' = (state base seen order d).emit (message k n) ∧
      base ≤ d'.val.length := by
  unfold sudoers.alias_diagnostic at hd
  have he := push_ok hd
  refine ⟨?_, by rw [he]; simp; omega⟩
  have hdecode : String.fromUTF8Lossy ⟨(s.val.map fun b => UInt8.ofNat b.val).toArray⟩ = n :=
    decode_deref hs
  cases k <;>
    simp [state, SudoersSpec.Analysis.AliasOrder.State.emit, he,
      List.drop_append_of_le_length hbase, message,
      SudoersSpec.Analysis.AliasOrder.undefinedMessage,
      SudoersSpec.Analysis.AliasOrder.recursiveMessage,
      SudoersSpec.Analysis.AliasOrder.duplicateMessage, hdecode]

private theorem model_at (f : T → β) (defs : Vec (RDef T)) {i : Nat}
    (hi : i < defs.val.length) : defAt (modelTable f defs) i = absDef f defs.val[i] := by
  simp [defAt, modelTable, List.getElem?_eq_getElem hi]

private theorem refs_abs (f : T → β) (items : List (RSpec T)) :
    aliasRefsOf (absSpecList f items) = items.filterMap aliasName := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    cases item with
    | Allow m | Forbid m =>
      cases m <;> simp [aliasRefsOf, List.filterMap_cons, SudoersSpec.Qualified.who,
        absSpec, absQualified, absMeta, aliasName, ← ih]

/-- A lookup picks the first matching definition in its search suffix, not just any match. -/
private theorem dependency_exact (table : Slice (RDef T)) (k : String) (i : Usize) :
    ∃ o, sanitize_alias_table.dependency_position_loop table k i = ok o ∧
      o.map (·.val) = ((table.val.drop i.val).findIdx? (fun d => defName d == k)).map (i.val + ·) := by
  rw [sanitize_alias_table.dependency_position_loop.eq_1]
  split
  · have hlt : i.val < table.val.length := by scalar_tac
    have hindex := eq_ok_of_spec (Slice.index_usize_spec table i hlt)
    rw [hindex, List.drop_eq_getElem_cons hlt, List.findIdx?_cons]
    simp only [Std.bind_ok]
    generalize table.val[i.val] = d
    obtain ⟨nm, members⟩ := d
    simp only [uncurry_apply_pair, Std.bind_ok,
      alloc.string.String.Insts.CoreCmpPartialEqString.eq, defName_mk, beq_iff_eq]
    by_cases hnm : nm = k
    · simp [hnm]
    · simp only [hnm, ↓reduceIte]
      obtain ⟨j, hj, hjval⟩ := exists_eq_ok_of_spec
        (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
      have hs : j.val = i.val + 1 := by simpa using hjval
      obtain ⟨o, ho, he⟩ := dependency_exact table k j
      refine ⟨o, by rw [hj, Std.bind_ok, ho], ?_⟩
      rw [he, hs, Option.map_map]
      cases (table.val.drop (i.val + 1)).findIdx? (fun d => defName d == k) <;>
        simp [Function.comp_def, Nat.add_assoc, Nat.add_comm 1]
  · have hge : table.val.length ≤ i.val := by scalar_tac
    exact ⟨none, rfl, by simp [List.drop_eq_nil_of_le hge]⟩
termination_by table.val.length - i.val
decreasing_by omega

private theorem model_dependency (f : T → β) (defs : Vec (RDef T)) (k : String) :
    ∃ o, sanitize_alias_table.dependency_position (alloc.vec.Vec.deref defs) k = ok o ∧
      o.map (·.val) = (modelTable f defs).findIdx? (·.name == k) := by
  obtain ⟨o, ho, he⟩ := dependency_exact (alloc.vec.Vec.deref defs) k 0#usize
  exact ⟨o, ho, by simpa [modelTable, Function.comp_def, absDef, defName] using he⟩

/-- `n` counts the unvisited positions; the extra unit of fuel checks membership when every
position has already been seen. -/
private def VisitExact (f : T → β) (base n : Nat) : Prop :=
  ∀ (v : AliasVisitor T) (pos : Usize), Inv v.table.val v.seen v.order.val →
    v.table.val.length - v.seen.length ≤ n → base ≤ v.diagnostics.val.length →
    OnReturn (sanitize_alias_table.Visitor.visit v pos) fun r =>
      state base r.1.seen r.1.order r.1.diagnostics =
        visit (modelTable f v.table) (n + 1) pos.val (state base v.seen v.order v.diagnostics)

private theorem members_exact (f : T → β) {base n : Nat} (hvisit : VisitExact f base n)
    (defs : Vec (RDef T)) (it : core.slice.iter.Iter (RSpec T)) (back : Diags → Diags)
    (seen : List Usize) (order : Vec Usize) (d : Diags) (hinv : Inv defs.val seen order.val)
    (hn : defs.val.length - seen.length ≤ n) (hbase : base ≤ d.val.length) :
    OnReturn (sanitize_alias_table.Visitor.visit_loop it back seen defs order d) fun r =>
      state base r.1 r.2.2.1 r.2.2.2.1 =
        visitRefs (modelTable f defs) (visit (modelTable f defs) (n + 1))
          ((it.slice.val.drop it.i).filterMap aliasName) (state base seen order d) := by
  suffices h : ∀ (items : List (RSpec T)) it back seen order (d : Diags),
      it.slice.val.drop it.i = items → Inv defs.val seen order.val →
      defs.val.length - seen.length ≤ n → base ≤ d.val.length →
      OnReturn (sanitize_alias_table.Visitor.visit_loop it back seen defs order d) fun r =>
        state base r.1 r.2.2.1 r.2.2.2.1 =
          visitRefs (modelTable f defs) (visit (modelTable f defs) (n + 1))
            (items.filterMap aliasName) (state base seen order d) from
    h _ it back seen order d rfl hinv hn hbase
  intro items
  induction items with
  | nil =>
    intro it back seen order d hrem hinv hn hbase
    rw [sanitize_alias_table.Visitor.visit_loop.eq_1, slice_next_nil it hrem]
    simp only [Std.bind_ok, uncurry_apply_pair]
    exact OnReturn.pure rfl
  | cons item rest ih =>
    intro it back seen order d hrem hinv hn hbase
    obtain ⟨hnext, hrest⟩ := slice_next_cons it hrem
    rw [sanitize_alias_table.Visitor.visit_loop.eq_1, hnext]
    simp only [Std.bind_ok, uncurry_apply_pair]
    let it' := { it with i := it.i + 1 }
    have hskip := ih it' back seen order d hrest hinv hn hbase
    have halias (k : String) : OnReturn (do
        let o ← sanitize_alias_table.dependency_position (alloc.vec.Vec.deref defs) k
        match o with
        | none =>
          let s ← alloc.string.String.Insts.CoreOpsDerefDerefStr.deref k
          let d' ← sudoers.alias_diagnostic d .Undefined s
          sanitize_alias_table.Visitor.visit_loop { it with i := it.i + 1 } back seen defs order d'
        | some q =>
          let (v, vb) ← sanitize_alias_table.Visitor.visit
            { seen := seen, table := defs, order := order, diagnostics := d } q
          sanitize_alias_table.Visitor.visit_loop { it with i := it.i + 1 }
            (fun x => back (vb { v with diagnostics := x }).diagnostics)
            v.seen v.table v.order v.diagnostics) fun r =>
        state base r.1 r.2.2.1 r.2.2.2.1 =
          visitRefs (modelTable f defs) (visit (modelTable f defs) (n + 1))
            (k :: rest.filterMap aliasName) (state base seen order d) := by
      obtain ⟨o, ho, he⟩ := model_dependency f defs k
      rw [ho]
      simp only [Std.bind_ok, visitRefs, List.foldl_cons, ← he]
      cases o with
      | none =>
        simp only [Option.map_none]
        apply OnReturn.bind
        intro s hs
        apply OnReturn.bind
        intro d' hd
        obtain ⟨hstate, hb'⟩ := state_diag hbase hs hd seen order
        simp only [message] at hstate
        rw [← hstate]
        exact ih it' back seen order d' hrest hinv hn hb'
      | some q =>
        simp only [Option.map_some]
        apply OnReturn.bind
        rintro ⟨v, vb⟩ hv
        have hstate := hvisit _ q hinv hn hbase _ hv
        obtain ⟨htab, _, hp⟩ := visitor_spec.2 _ q hinv _ hv
        simp only at htab hp hstate
        simp only [uncurry_apply_pair]
        rw [htab, ← hstate]
        have hslen : seen.length ≤ v.seen.length :=
          (hinv.seen_nodup.subperm hp.seen_sub).length_le
        exact ih it' _ _ _ _ hrest hp.inv (by omega) (Nat.le_trans hbase hp.diag_prefix.length_le)
    cases item with
    | Allow m | Forbid m =>
      simp only [sanitize_alias_table.remqualify, Std.bind_ok]
      cases m with
      | All => exact hskip
      | Only _ => exact hskip
      | Alias k => exact halias k

private theorem visitor_exact (f : T → β) (base n : Nat) : VisitExact f base n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro v pos hinv hn hb
    rw [sanitize_alias_table.Visitor.visit.eq_1, insert_usize]
    by_cases hs : pos ∈ v.seen
    · have hseen := (mem_map_val (q := pos)).2 hs
      simp only [hs, ↓reduceIte, Std.bind_ok, uncurry_apply_pair, Bool.false_eq_true]
      rw [contains_usize]
      simp only [Std.bind_ok, Vec.deref_val]
      by_cases ho : pos ∈ v.order.val
      · simp [ho, visit, state, hseen, mem_map_val, OnReturn.pure]
      · simp only [ho, decide_false, Bool.false_eq_true, ↓reduceIte]
        apply OnReturn.bind
        rintro ⟨nm, members⟩ hindex
        obtain ⟨hi, he⟩ := index_ok hindex
        simp only [uncurry_apply_pair]
        apply OnReturn.bind
        intro s hs'
        apply OnReturn.bind
        intro d' hd
        have hname : (defAt (modelTable f v.table) pos.val).name = nm := by
          rw [model_at f v.table hi, ← he]; rfl
        exact OnReturn.pure (by
          simpa [visit, state, hseen, ho, mem_map_val, hname, message] using
            (state_diag hb hs' hd v.seen v.order).1)
    · simp only [hs, ↓reduceIte, Std.bind_ok, uncurry_apply_pair]
      apply OnReturn.bind
      rintro ⟨nm, members⟩ hindex
      obtain ⟨hi, he⟩ := index_ok hindex
      cases n with
      | zero =>
        have hlen := length_le_of_lt (hinv.insert hs hi).seen_nodup (hinv.insert hs hi).seen_lt
        simp only [List.length_cons] at hlen
        omega
      | succ n =>
        simp only [uncurry_apply_pair, core.slice.Slice.iter, Std.bind_ok]
        apply OnReturn.bind
        rintro ⟨seen', defs', order', d', back'⟩ hm
        have hinv' := hinv.insert hs hi
        have hn' : v.table.val.length - (pos :: v.seen).length ≤ n := by
          simp only [List.length_cons]; omega
        have hstate := members_exact f (ih n (Nat.lt_succ_self n)) v.table _ _ _ _ _ hinv' hn' hb _ hm
        simp only [Vec.deref_val, List.drop_zero] at hstate
        simp only [uncurry_apply_pair]
        apply OnReturn.bind
        intro order'' hpush
        have hitems : aliasRefsOf (defAt (modelTable f v.table) pos.val).items =
            members.val.filterMap aliasName := by
          rw [model_at f v.table hi, ← he]
          exact refs_abs f members.val
        exact OnReturn.pure (by
          simp only [visit, show pos.val ∉ (state base v.seen v.order v.diagnostics).seen from
            fun h => hs (mem_map_val.1 h), ↓reduceIte, hitems]
          rw [state_push base seen' d' hpush, hstate]
          rfl)

private theorem roots_exact (f : T → β) (base : Nat) (defs : Vec (RDef T)) :
    ∀ left (e : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter (RDef T))) back
      (seen : List Usize) (order : Vec Usize) (d : Diags) names,
      defs.val.length - e.iter.i = left → e.iter.slice.val = defs.val → e.count.val = e.iter.i →
      (∀ x, back x = x) → Inv defs.val seen order.val → base ≤ d.val.length →
      OnReturn (sanitize_alias_table_loop e back seen defs order d names) fun r =>
        let out := roots (modelTable f defs) left e.iter.i names (state base seen order d)
        (r.1.val.map (·.val)).toArray = out.order ∧
          ((r.2.val.drop base).map sudoers.Error.message).toArray = out.diags := by
  intro left
  induction left with
  | zero =>
    intro e back seen order d names hleft hsl hcnt hback hinv hb
    rw [sanitize_alias_table_loop.eq_1, enumerate_next_nil e (by
      rw [hsl]; exact List.drop_eq_nil_of_le (by omega))]
    simp only [Std.bind_ok, uncurry_apply_pair, hback]
    exact OnReturn.pure ⟨rfl, rfl⟩
  | succ left ih =>
    intro e back seen order d names hleft hsl hcnt hback hinv hb
    have hi : e.iter.i < defs.val.length := by omega
    have hmax : defs.val.length ≤ Usize.max := by scalar_tac
    have hrem : e.iter.slice.val.drop e.iter.i = defs.val[e.iter.i] :: defs.val.drop (e.iter.i + 1) := by
      rw [hsl, List.drop_eq_getElem_cons hi]
    have hname := model_at f defs hi
    generalize defs.val[e.iter.i] = defn at hname hrem
    obtain ⟨c, hc, hnext⟩ := enumerate_next_cons e hrem (by omega)
    rw [sanitize_alias_table_loop.eq_1, hnext]
    simp only [Std.bind_ok, uncurry_apply_pair]
    obtain ⟨nm, members⟩ := defn
    simp only [uncurry_apply_pair]
    rw [insert_string]
    have hname' : (defAt (modelTable f defs) e.iter.i).name = nm := congrArg (·.name) hname
    have hc' : c.val = e.iter.i + 1 := hc.trans (congrArg (· + 1) hcnt)
    have hleft' : defs.val.length - (e.iter.i + 1) = left := by omega
    by_cases hnm : nm ∈ names
    · simp only [hnm, roots, hname', ↓reduceIte, Std.bind_ok, uncurry_apply_pair, Bool.false_eq_true]
      apply OnReturn.bind
      intro s hs
      apply OnReturn.bind
      intro d' hd
      obtain ⟨hstate, hb'⟩ := state_diag hb hs hd seen order
      rw [← show state base seen order d' = (state base seen order d).emit
        (SudoersSpec.Analysis.AliasOrder.duplicateMessage nm) from hstate]
      exact ih _ back seen order d' names hleft' hsl hc' hback hinv hb'
    · simp only [hnm, roots, hname', ↓reduceIte, Std.bind_ok, uncurry_apply_pair]
      apply OnReturn.bind
      rintro ⟨v, vb⟩ hv
      obtain ⟨htab, hback', hp⟩ := visitor_spec.2 _ e.count hinv _ hv
      have hstate := visitor_exact f base defs.val.length _ e.count hinv (Nat.sub_le _ _) hb _ hv
      simp only at htab hback' hp hstate
      simp only [uncurry_apply_pair]
      rw [htab]
      have hsize : (modelTable f defs).size = defs.val.length := by simp [modelTable]
      simp only [hsize]
      rw [hcnt] at hstate
      rw [← hstate]
      exact ih _ _ _ _ _ _ hleft' hsl hc' (fun x => by simp [hback', hback]) hp.inv
        (Nat.le_trans hb hp.diag_prefix.length_le)

end AliasOrder

open SudoersSpec.Analysis in
/-- A successful per-table sanitizer returns the spec's exact definitions in processing order,
retains the original diagnostics, and appends the spec's messages. -/
theorem sanitize_alias_table_exact {T β : Type} (f : T → β) (defs : Vec (RDef T))
    (diags : Diags) {order : Vec Usize} {diags' : Diags}
    (h : sanitize_alias_table defs diags = ok (order, diags')) :
    absTable f (order, defs) = (SudoersSpec.Analysis.AliasOrder.table (defs.val.map (absDef f))).1 ∧
      diags.val <+: diags'.val ∧ diags'.val.map sudoers.Error.message =
        diags.val.map sudoers.Error.message ++
          (SudoersSpec.Analysis.AliasOrder.table (defs.val.map (absDef f))).2 := by
  have hwf := sanitize_alias_table_tableWF _ _ h
  have hpre := (sanitize_alias_table_distinct _ _ h).2.1
  unfold sanitize_alias_table at h
  simp only [std.collections.hash.set.HashSetTRandomStateGlobal.new, core.slice.Slice.iter,
    core.iter.traits.iterator.Iterator.enumerate.trait_default,
    core.iter.traits.iterator.Iterator.enumerate.default, Std.bind_ok] at h
  have hinv : Sanitize.Inv defs.val [] (alloc.vec.Vec.with_capacity Usize (alloc.vec.Vec.len defs)).val :=
    ⟨by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new],
      by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new], by simp, List.nodup_nil⟩
  have hempty : AliasOrder.state diags.val.length [] (alloc.vec.Vec.with_capacity Usize
      (alloc.vec.Vec.len defs)) diags = {} := by
    simp [AliasOrder.state, alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]
  obtain ⟨ho, hd⟩ := AliasOrder.roots_exact f diags.val.length defs defs.val.length _ _ [] _ diags []
    (by simp) (by simp) (by simp) (fun _ => rfl) hinv le_rfl _ h
  rw [hempty] at ho hd
  have ho' := congrArg Array.toList ho
  have hd' := congrArg Array.toList hd
  refine ⟨?_, hpre, ?_⟩
  · unfold absTable tableDefs SudoersSpec.Analysis.AliasOrder.table
    simp only [AliasOrder.modelTable, List.size_toArray, List.length_map] at ho' ⊢
    rw [← ho']
    simp only [List.map_map, List.map_filterMap]
    rw [← List.filterMap_eq_map']
    apply List.filterMap_congr
    intro i hi
    have hlt := hwf i hi
    change (defs.val[i.val]?).map (absDef f) =
      some (SudoersSpec.Analysis.AliasOrder.defAt (AliasOrder.modelTable f defs) i.val)
    rw [AliasOrder.model_at f defs hlt, List.getElem?_eq_getElem hlt]
    rfl
  · obtain ⟨tail, he⟩ := hpre
    rw [← he, List.drop_append_length] at hd'
    rw [← he, List.map_append]
    exact congrArg (diags.val.map sudoers.Error.message ++ ·) (by
      simpa [AliasOrder.modelTable, SudoersSpec.Analysis.AliasOrder.table] using hd')

/-- Total per-table refinement under the existing name and diagnostic size bounds. -/
theorem sanitize_alias_table_exact_returns {T β : Type} (f : T → β) (defs : Vec (RDef T))
    (diags : Diags) (hfit : ∀ d ∈ defs.val, Fits d.1 ∧ ItemsFit d.2.val)
    (hlen : diags.val.length + defs.val.length + (defs.val.map fun d => d.2.val.length).sum ≤
      Usize.max) :
    ∃ order diags', sanitize_alias_table defs diags = ok (order, diags') ∧
      absTable f (order, defs) = (SudoersSpec.Analysis.AliasOrder.table (defs.val.map (absDef f))).1 ∧
      diags.val <+: diags'.val ∧ diags'.val.map sudoers.Error.message =
        diags.val.map sudoers.Error.message ++
          (SudoersSpec.Analysis.AliasOrder.table (defs.val.map (absDef f))).2 := by
  obtain ⟨⟨order, diags'⟩, h⟩ := sanitize_alias_table_returns defs diags hfit hlen
  exact ⟨order, diags', h, sanitize_alias_table_exact f defs diags h⟩

/-- The definition lists before alias preprocessing, ignoring the existing processing orders. -/
def absWrittenAliasTable (A : GlobAbs) (t : sudoers.AliasTable) : SudoersSpec.AliasTable where
  user := t.user.2.val.map (absDef absUserSpecifier)
  host := t.host.2.val.map (absDef id)
  cmnd := t.cmnd.2.val.map (absDef (absCommand A))
  runas := t.runas.2.val.map (absDef absUserSpecifier)

/-- The four successful preprocessing calls agree with `orderAliases`, without a cleanliness
hypothesis. The original errors are a prefix, and the appended messages match in order. -/
theorem sanitize_alias_tables_exact (A : GlobAbs) {t t' : sudoers.AliasTable}
    {diags diags' : Diags} (h : sanitize_alias_tables t diags = ok (t', diags')) :
    absAliasTable A t' = (SudoersSpec.Analysis.orderAliases (absWrittenAliasTable A t)).1 ∧
      diags.val <+: diags'.val ∧ diags'.val.map sudoers.Error.message =
        diags.val.map sudoers.Error.message ++
          (SudoersSpec.Analysis.orderAliases (absWrittenAliasTable A t)).2 := by
  obtain ⟨d1, d2, d3, hu, hh, hc, hr, eu, eh, ec, er⟩ := sanitize_alias_tables_ok h
  obtain ⟨au, pu, mu⟩ := sanitize_alias_table_exact absUserSpecifier _ _ hu
  obtain ⟨ah, ph, mh⟩ := sanitize_alias_table_exact id _ _ hh
  obtain ⟨ac, pc, mc⟩ := sanitize_alias_table_exact (absCommand A) _ _ hc
  obtain ⟨ar, pr, mr⟩ := sanitize_alias_table_exact absUserSpecifier _ _ hr
  refine ⟨?_, pu.trans (ph.trans (pc.trans pr)), ?_⟩
  · simp only [absAliasTable, absWrittenAliasTable, SudoersSpec.Analysis.orderAliases,
      ← au, ← ah, ← ac, ← ar]
    simp [absTable, tableDefs, eu, eh, ec, er]
  · simpa [SudoersSpec.Analysis.orderAliases, absWrittenAliasTable, mu, mh, mc, List.append_assoc]
      using mr

/-- Total exact preprocessing, under the existing string and diagnostic size bounds. -/
theorem sanitize_alias_tables_exact_returns (A : GlobAbs) (t : sudoers.AliasTable) (diags : Diags)
    (hu : TableFits t.user) (hh : TableFits t.host) (hc : TableFits t.cmnd) (hr : TableFits t.runas)
    (hlen : diags.val.length + tableSize t.user + tableSize t.host + tableSize t.cmnd +
      tableSize t.runas ≤ Usize.max) :
    ∃ t' diags', sanitize_alias_tables t diags = ok (t', diags') ∧
      absAliasTable A t' = (SudoersSpec.Analysis.orderAliases (absWrittenAliasTable A t)).1 ∧
      diags.val <+: diags'.val ∧ diags'.val.map sudoers.Error.message =
        diags.val.map sudoers.Error.message ++
          (SudoersSpec.Analysis.orderAliases (absWrittenAliasTable A t)).2 := by
  obtain ⟨⟨t', diags'⟩, h⟩ := sanitize_alias_tables_returns t diags hu hh hc hr hlen
  exact ⟨t', diags', h, sanitize_alias_tables_exact A h⟩

end SudoRsProofs
