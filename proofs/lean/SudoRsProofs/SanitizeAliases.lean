import SudoRsProofs.AbsPolicy

/-!
# Alias preprocessing: bounds on successful returns

The extracted producer indexes the original definitions before appending a position.
Neither hash-set membership nor the result of dependency lookup needs to be correct for
this bound. No termination, diagnostics, malformed-input, or sorting property is proved.
-/

open Aeneas Aeneas.Std Result Lean.Order
open Aeneas.Std.alloc.vec (Vec)
open sudo_rs sudo_rs.sudoers

namespace SudoRsProofs

/-- Unlike `WP.dspec`, this predicate constrains neither failure nor divergence. -/
def OnReturn (r : Result α) (post : α → Prop) : Prop :=
  ∀ x, r = ok x → post x

theorem OnReturn.pure {post : α → Prop} {x : α} (h : post x) :
    OnReturn (ok x) post := by
  intro y hy
  simpa only [← Result.ok_injective hy] using h

theorem OnReturn.bind {r : Result α} {k : α → Result β} {post : β → Prop}
    (h : ∀ x, r = ok x → OnReturn (k x) post) : OnReturn (r >>= k) post := by
  cases r using Result.cases with
  | ret x => simpa only [bind_tc_ok] using h x rfl
  | vis e k' => simp only [OnReturn, bind_tc_vis, vis_not_ok, false_implies, implies_true]
  | div => simp only [OnReturn, bind_tc_div, div_not_ok, false_implies, implies_true]

section
unseal Result

theorem OnReturn.admissible (post : α → Prop) :
    admissible (fun r : Result α => OnReturn r post) := by
  intro c chain hAll x hx
  exact hAll (ok x) (Data.Coinductive.ITree.csup_ret_mem (E := RustEffect) (c := c) chain hx) x rfl

end

theorem index_lt_of_ok {α : Type} {defs : Vec α} {i : Usize} {x : α}
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) defs i = ok x) :
    i.val < defs.val.length := by
  rw [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize] at h
  by_contra hlt
  have he : defs.val[i.val]? = none := by simp [Nat.le_of_not_gt hlt]
  simp [he] at h

private theorem push_preserves {T : Type} {defs : Vec (RDef T)} {order order' : Vec Usize}
    {i : Usize} (h : TableWF (order, defs)) (hi : i.val < defs.val.length)
    (hpush : alloc.vec.Vec.push order i = ok order') : TableWF (order', defs) := by
  unfold alloc.vec.Vec.push at hpush
  dsimp only at hpush
  split at hpush
  · obtain rfl := Result.ok_injective hpush
    intro j hj
    have hj' : j ∈ order.val ∨ j = i := by simpa using hj
    rcases hj' with hj' | rfl
    · exact h j hj'
    · exact hi
  · simp at hpush

abbrev AliasVisitor := sanitize_alias_table.Visitor
abbrev HashKeys (T : Type) :=
  std.collections.hash.set.HashSet T std.hash.random.RandomState alloc.alloc.Global
abbrev Diags := Vec sudoers.Error
abbrev VisitResult (T : Type) := AliasVisitor T × (AliasVisitor T → AliasVisitor T)
abbrev MembersResult (T : Type) :=
  HashKeys Usize × Vec (RDef T) × Vec Usize × Diags × (Diags → Diags)

private def MembersPreserve {T : Type}
    (loop : core.slice.iter.Iter (RSpec T) → (Diags → Diags) → HashKeys Usize →
      Vec (RDef T) → Vec Usize → Diags → Result (MembersResult T)) : Prop :=
  ∀ iter back seen defs order diags, TableWF (order, defs) →
    OnReturn (loop iter back seen defs order diags)
      (fun result => result.2.1 = defs ∧ TableWF (result.2.2.1, defs))

private def VisitPreserves {T : Type}
    (visit : AliasVisitor T → Usize → Result (VisitResult T)) : Prop :=
  ∀ visitor i, TableWF (visitor.order, visitor.table) →
    OnReturn (visit visitor i)
      (fun result => result.1.table = visitor.table ∧
        TableWF (result.1.order, visitor.table))

-- Function suprema are pointwise. A successful return of the supremum must then
-- be a successful return of one chain member, at those same arguments.
scoped macro "prove_return_admissible" hAll:ident : tactic =>
  `(tactic| (
    simp only [← fun_csup_eq, fun_csup]
    refine OnReturn.admissible _ _ _ ?_
    intro r hmem
    repeat' (obtain ⟨r, hmem, heq⟩ := hmem)
    subst_vars
    apply ($hAll _ hmem) <;> assumption))

private theorem visitor_preserves {T : Type} :
    MembersPreserve (@sanitize_alias_table.Visitor.visit_loop T) ∧
    VisitPreserves (@sanitize_alias_table.Visitor.visit T) := by
  apply sanitize_alias_table.Visitor.visit_loop.mutual_fixpoint_induct
    (motive_1 := MembersPreserve) (motive_2 := VisitPreserves)
  · intro c hc hAll iter back seen defs order diags hwf
    prove_return_admissible hAll
  · intro c hc hAll visitor pos hwf
    prove_return_admissible hAll
  · intro loop visit ihLoop ihVisit iter back seen defs order diags hwf
    simp only
    apply OnReturn.bind
    rintro ⟨item, iter'⟩ _
    simp only [uncurry_apply_pair]
    cases item with
    | none => exact OnReturn.pure ⟨rfl, hwf⟩
    | some elem =>
      apply OnReturn.bind
      intro item _
      cases item with
      | All | Only => exact ihLoop _ _ _ _ _ _ hwf
      | Alias aliasName =>
        apply OnReturn.bind
        intro dependency _
        cases dependency with
        | none =>
          apply OnReturn.bind
          intro _ _
          apply OnReturn.bind
          intro diags' _
          exact ihLoop _ _ _ _ _ diags' hwf
        | some pos =>
          apply OnReturn.bind
          rintro ⟨visitor, visitBack⟩ hr
          obtain ⟨htable, horder⟩ := ihVisit _ _ hwf _ hr
          simp only [uncurry_apply_pair]
          have hwf' : TableWF (visitor.order, visitor.table) := htable.symm ▸ horder
          change visitor.table = defs at htable
          intro result hresult
          obtain ⟨hTableOut, hOrderOut⟩ := ihLoop _ _ _ _ _ _ hwf' result hresult
          exact ⟨hTableOut.trans htable, htable ▸ hOrderOut⟩
  · intro loop ihLoop visitor pos hwf
    simp only
    apply OnReturn.bind
    rintro ⟨inserted, seen⟩ _
    simp only [uncurry_apply_pair]
    split
    · apply OnReturn.bind
      rintro ⟨_, members⟩ hindex
      have hpos := index_lt_of_ok hindex
      simp only [uncurry_apply_pair]
      apply OnReturn.bind
      intro iter _
      apply OnReturn.bind
      rintro ⟨seen', defs', order', diags', back'⟩ hloop
      obtain ⟨rfl, horder⟩ := ihLoop _ _ _ _ _ _ hwf _ hloop
      simp only [uncurry_apply_pair]
      apply OnReturn.bind
      intro order'' hpush
      exact OnReturn.pure ⟨rfl, push_preserves horder hpos hpush⟩
    · apply OnReturn.bind
      intro present _
      split
      · exact OnReturn.pure ⟨rfl, hwf⟩
      · apply OnReturn.bind
        rintro ⟨_, _⟩ _
        simp only [uncurry_apply_pair]
        apply OnReturn.bind
        intro _ _
        apply OnReturn.bind
        intro _ _
        exact OnReturn.pure ⟨rfl, hwf⟩

private def RootsPreserve {T : Type}
    (loop : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter (RDef T)) →
      (Diags → Diags) → HashKeys Usize → Vec (RDef T) → Vec Usize → Diags →
      HashKeys String → Result (Vec Usize × Diags)) : Prop :=
  ∀ iter back seen defs order diags dupe, TableWF (order, defs) →
    OnReturn (loop iter back seen defs order diags dupe)
      (fun result => TableWF (result.1, defs))

private theorem roots_preserve {T : Type} : RootsPreserve (@sanitize_alias_table_loop T) := by
  apply sanitize_alias_table_loop.fixpoint_induct (motive := RootsPreserve)
  · intro c hc hAll iter back seen defs order diags dupe hwf
    prove_return_admissible hAll
  · intro loop ihLoop iter back seen defs order diags dupe hwf
    simp only
    apply OnReturn.bind
    rintro ⟨entry, iter'⟩ _
    simp only [uncurry_apply_pair]
    rcases entry with _ | ⟨pos, aliasName, _⟩
    · exact OnReturn.pure hwf
    · apply OnReturn.bind
      rintro ⟨inserted, dupe'⟩ _
      simp only [uncurry_apply_pair]
      split
      · apply OnReturn.bind
        rintro ⟨visitor, visitBack⟩ hr
        obtain ⟨htable, horder⟩ := visitor_preserves.2 _ _ hwf _ hr
        simp only [uncurry_apply_pair]
        have hwf' : TableWF (visitor.order, visitor.table) := htable.symm ▸ horder
        change visitor.table = defs at htable
        intro result hresult
        have hout := ihLoop _ _ _ _ _ _ _ hwf' result hresult
        exact htable ▸ hout
      · apply OnReturn.bind
        intro _ _
        apply OnReturn.bind
        intro diags' _
        exact ihLoop _ _ _ _ _ diags' dupe' hwf

/-- A successfully returned alias order only contains indices into the original definitions. -/
theorem sanitize_alias_table_tableWF {T : Type} (defs : Vec (RDef T)) (diags : Vec sudoers.Error)
    {order : Vec Usize} {diags' : Vec sudoers.Error}
    (h : sanitize_alias_table defs diags = ok (order, diags')) : TableWF (order, defs) := by
  suffices hBounds : OnReturn (sanitize_alias_table defs diags)
      (fun r => TableWF (r.1, defs)) from hBounds _ h
  unfold sanitize_alias_table
  apply OnReturn.bind
  intro seen _
  apply OnReturn.bind
  intro dupe _
  apply OnReturn.bind
  intro _ _
  apply OnReturn.bind
  intro iter _
  exact roots_preserve iter id seen defs _ diags dupe (by
    simp [TableWF, alloc.vec.Vec.with_capacity, alloc.vec.Vec.new])

/-- The four successful sanitizer calls discharge the index part of `AliasTableOK`;
the name and element conditions still have to come from the caller. -/
theorem AliasTableOK.of_sanitize {t : AliasTable}
    {userIn userOut hostIn hostOut cmndIn cmndOut runasIn runasOut : Vec sudoers.Error}
    (user : sanitize_alias_table t.user.2 userIn = ok (t.user.1, userOut))
    (host : sanitize_alias_table t.host.2 hostIn = ok (t.host.1, hostOut))
    (cmnd : sanitize_alias_table t.cmnd.2 cmndIn = ok (t.cmnd.1, cmndOut))
    (runas : sanitize_alias_table t.runas.2 runasIn = ok (t.runas.1, runasOut))
    (userFits : TableFits t.user) (userGood : TableGood UserSpecFits t.user)
    (hostFits : TableFits t.host) (hostGood : TableGood Fits t.host)
    (cmndFits : TableFits t.cmnd)
    (runasFits : TableFits t.runas) (runasGood : TableGood UserSpecFits t.runas) :
    AliasTableOK t :=
  ⟨⟨sanitize_alias_table_tableWF _ _ user, userFits, userGood⟩,
   ⟨sanitize_alias_table_tableWF _ _ host, hostFits, hostGood⟩,
   ⟨sanitize_alias_table_tableWF _ _ cmnd, cmndFits⟩,
   ⟨sanitize_alias_table_tableWF _ _ runas, runasFits, runasGood⟩⟩

end SudoRsProofs
