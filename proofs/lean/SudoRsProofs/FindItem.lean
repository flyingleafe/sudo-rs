import SudoRsProofs.FoundAliases

/-!
# `item_verdict`, `find_item_after`, `find_item` refine `SudoersSpec.findItem`

The Rust functions return `bool` (`find_item`) where the spec returns `Option τ`; with unit
satellite data (`SudoersSpec.withUnit`) the Rust `bool` is the spec's `isSome`.

The predicate argument is a Rust closure (`Fn(&T) -> bool`), extracted as a value `pred` with an
`Fn` instance; the theorems assume that calling it is pure and total:
`∀ x, inst.call pred x = ok (p (f x))`, where `f` abstracts the element type.
-/

open Aeneas Aeneas.Std Result

namespace SudoRsProofs

variable {P : Type _} {T β : Type}

/-- `item_verdict` at the level of the spec: what one entry says about the item, if anything. -/
def itemVerdict (p : β → Bool) (A : SudoersSpec.FoundAliases) (s : SudoersSpec.Spec β) :
    Option Bool :=
  let (j, who) : Bool × SudoersSpec.Meta β := match s with
    | .forbid x => (false, x)
    | .allow x => (true, x)
  match who with
  | .all => some j
  | .only x => if p x then some j else none
  | .alias n =>
    match A n with
    | some true => some j
    | some false => some (!j)
    | none => none

/-- The loop of `find_item_after` over spec entries, with a `bool` accumulator. -/
def verdictFold (p : β → Bool) (A : SudoersSpec.FoundAliases) (l : SudoersSpec.SpecList β)
    (r : Bool) : Bool :=
  l.foldl (fun r s => (itemVerdict p A s).getD r) r

/-! ## Spec-level glue: the `bool` loop is the `Option Unit` fold of `findItem` -/

theorem findItemStep_boolThen (p : β → Bool) (A : SudoersSpec.FoundAliases) (r : Bool)
    (s : SudoersSpec.Spec β) :
    SudoersSpec.findItemStep p A (SudoersSpec.boolThen r ()) (s, ()) =
      SudoersSpec.boolThen ((itemVerdict p A s).getD r) () := by
  cases s with
  | allow m | forbid m =>
    cases m with
    | all => rfl
    | «only» x => by_cases h : p x <;> simp [SudoersSpec.findItemStep, itemVerdict, h]
    | «alias» n =>
      rcases h : A n with _ | _ | _ <;> simp [SudoersSpec.findItemStep, itemVerdict, h]

theorem foldl_findItemStep_boolThen (p : β → Bool) (A : SudoersSpec.FoundAliases)
    (l : SudoersSpec.SpecList β) (r : Bool) :
    (SudoersSpec.withUnit l).foldl (SudoersSpec.findItemStep p A) (SudoersSpec.boolThen r ()) =
      SudoersSpec.boolThen (verdictFold p A l r) () := by
  induction l generalizing r with
  | nil => rfl
  | cons s l ih =>
    simp only [SudoersSpec.withUnit, List.map_cons, List.foldl_cons, verdictFold] at ih ⊢
    rw [findItemStep_boolThen, ih]

theorem isSome_boolThen (b : Bool) : (SudoersSpec.boolThen b ()).isSome = b := by
  cases b <;> rfl

/-- The entries `find_item_after` assumes in front of the list: `ALL` iff `result` starts
`true`. -/
def initialItems (r : Bool) : List (SudoersSpec.Spec β × Unit) :=
  if r then [(.allow .all, ())] else []

theorem findItem_initial (p : β → Bool) (A : SudoersSpec.FoundAliases)
    (l : SudoersSpec.SpecList β) (r : Bool) :
    (SudoersSpec.findItem p A (initialItems r ++ SudoersSpec.withUnit l)).isSome =
      verdictFold p A l r := by
  have h0 : (initialItems (β := β) r).foldl (SudoersSpec.findItemStep p A) none =
      SudoersSpec.boolThen r () := by
    cases r <;> rfl
  rw [SudoersSpec.findItem, List.foldl_append, h0, foldl_findItemStep_boolThen, isSome_boolThen]

/-! ## `item_verdict` -/

@[step]
theorem item_verdict_spec (inst : core.ops.function.Fn P T Bool) (pred : P) (f : T → β)
    (p : β → Bool) (Good : T → Prop) (hp : ∀ x, Good x → inst.call pred x = ok (p (f x)))
    (item : RSpec T) (v : sudo_rs.sudoers.FoundAliases) (hv : FoundFits v)
    (hi : ∀ n, aliasName item = some n → Fits n) (hg : ∀ x, onlyItem item = some x → Good x) :
    sudo_rs.sudoers.item_verdict inst item pred v
      ⦃ o => o = itemVerdict p (absFound v) (absSpec f item) ⦄ := by
  unfold sudo_rs.sudoers.item_verdict
  cases item with
  | Allow m | Forbid m =>
    cases m with
    | All => simp [absSpec, absQualified, absMeta, itemVerdict]
    | Only x =>
      have hx := hp x (hg x rfl)
      by_cases h : p (f x) <;> simp [hx, h, absSpec, absQualified, absMeta, itemVerdict]
    | Alias n =>
      have hn : Fits n := hi n rfl
      step as ⟨s, hs⟩
      step with FoundAliases.get_spec v n s hv hs as ⟨o, ho⟩
      rcases hA : absFound v n with _ | _ | _ <;>
        simp [ho, hA, absSpec, absQualified, absMeta, itemVerdict]

/-! ## `find_item_after` / `find_item`

`Good` is the domain on which the closure is pure and total (e.g. identifiers whose names fit in
memory); `ItemsGood Good items` says every directly named item lies in it. -/

theorem find_item_after_loop_spec (inst : core.ops.function.Fn P T Bool) (pred : P)
    (f : T → β) (p : β → Bool) (Good : T → Prop)
    (hp : ∀ x, Good x → inst.call pred x = ok (p (f x))) (r : Bool)
    (items : Slice (RSpec T)) (v : sudo_rs.sudoers.FoundAliases) (hv : FoundFits v)
    (hi : ItemsFit items.val) (hg : ItemsGood Good items.val) (i : Usize) :
    sudo_rs.sudoers.find_item_after_loop inst r items pred v i
      ⦃ b => b = verdictFold p (absFound v) (absSpecList f (items.val.drop i.val)) r ⦄ := by
  unfold sudo_rs.sudoers.find_item_after_loop
  dsimp only
  split
  · have hlt : i.val < items.val.length := by scalar_tac
    have hdrop := List.drop_eq_getElem_cons hlt
    step as ⟨q, hq⟩
    have hqm : q ∈ items.val := by rw [hq]; exact List.getElem_mem hlt
    step with item_verdict_spec inst pred f p Good hp q v hv (hi q hqm) (hg q hqm) as ⟨o, ho⟩
    cases o <;> dsimp only <;> step as ⟨i2, hi2⟩ <;> step as ⟨b, hb⟩ <;>
      (rw [hb, hdrop, absSpecList_cons]
       simp only [verdictFold, List.foldl_cons, hi2, ← hq, ← ho, Option.getD_none,
         Option.getD_some])
  · have : items.val.length ≤ i.val := by scalar_tac
    simp [List.drop_eq_nil_of_le this, verdictFold]
termination_by items.val.length - i.val
decreasing_by all_goals (simp_all; scalar_tac)

/-- **`find_item_after` is `findItem`** on the abstracted entries, preceded by `ALL` iff the
initial `result` is `true`. -/
@[step]
theorem find_item_after_spec (inst : core.ops.function.Fn P T Bool) (pred : P) (f : T → β)
    (p : β → Bool) (Good : T → Prop) (hp : ∀ x, Good x → inst.call pred x = ok (p (f x)))
    (r : Bool) (items : Slice (RSpec T)) (v : sudo_rs.sudoers.FoundAliases) (hv : FoundFits v)
    (hi : ItemsFit items.val) (hg : ItemsGood Good items.val) :
    sudo_rs.sudoers.find_item_after inst r items pred v
      ⦃ b => b = (SudoersSpec.findItem p (absFound v)
          (initialItems r ++ SudoersSpec.withUnit (absSpecList f items.val))).isSome ⦄ := by
  rw [findItem_initial]
  simpa using find_item_after_loop_spec inst pred f p Good hp r items v hv hi hg 0#usize

/-- **`find_item` is `findItem`** on the abstracted entries (`bool` = `isSome`). -/
@[step]
theorem find_item_spec (inst : core.ops.function.Fn P T Bool) (pred : P) (f : T → β)
    (p : β → Bool) (Good : T → Prop) (hp : ∀ x, Good x → inst.call pred x = ok (p (f x)))
    (items : Slice (RSpec T)) (v : sudo_rs.sudoers.FoundAliases) (hv : FoundFits v)
    (hi : ItemsFit items.val) (hg : ItemsGood Good items.val) :
    sudo_rs.sudoers.find_item inst items pred v
      ⦃ b => b = (SudoersSpec.findItem p (absFound v)
          (SudoersSpec.withUnit (absSpecList f items.val))).isSome ⦄ := by
  unfold sudo_rs.sudoers.find_item
  simpa [initialItems] using find_item_after_spec inst pred f p Good hp false items v hv hi hg

/-- `find_item_spec` as an equation. -/
theorem find_item_eq (inst : core.ops.function.Fn P T Bool) (pred : P) (f : T → β)
    (p : β → Bool) (Good : T → Prop) (hp : ∀ x, Good x → inst.call pred x = ok (p (f x)))
    (items : Slice (RSpec T)) (v : sudo_rs.sudoers.FoundAliases) (hv : FoundFits v)
    (hi : ItemsFit items.val) (hg : ItemsGood Good items.val) :
    sudo_rs.sudoers.find_item inst items pred v =
      ok (SudoersSpec.findItem p (absFound v) (SudoersSpec.withUnit (absSpecList f items.val))).isSome :=
  eq_ok_of_spec (find_item_spec inst pred f p Good hp items v hv hi hg)

end SudoRsProofs
