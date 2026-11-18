import SudoersSpec.Ast

/-!
# `find_item`: the last matching entry decides

`findItem` is the loop of `mod.rs` `find_item` written as a left fold (form (b));
`findItemSpec` states the decision as "the final matching entry decides" in the style of the
Why3 development `proofs/sudoers.mlw` (form (a)). `findItem_eq_spec` proves them equal and
`findItem_eq_some_iff` / `findItem_eq_none_iff` are the Why3 postconditions of `find_item`.

Items carry satellite data (`τ`, Rust `WithInfo::Info`): `Unit` for plain spec lists and the
distributed `Tag` for command specs.
-/

namespace SudoersSpec

/-- `mod.rs` `FoundAliases = HashMap<String, bool>` as a finite partial map: `some true` the
alias affirms membership, `some false` it explicitly denies it, `none` neither. -/
abbrev FoundAliases := String → Option Bool

/-- The empty map (`HashMap::new()`). -/
def FoundAliases.empty : FoundAliases := fun _ => none

/-- `HashMap::insert`. -/
def FoundAliases.insert (m : FoundAliases) (k : String) (b : Bool) : FoundAliases :=
  fun k' => if k' = k then some b else m k'

/-- `bool::then`. -/
def boolThen (b : Bool) (x : τ) : Option τ := if b then some x else none

/-- Attach unit satellite data to a plain spec list (`impl WithInfo for &Spec<T>`). -/
def withUnit (l : SpecList α) : List (Spec α × Unit) := l.map (·, ())

variable {α τ β : Type}

/-! ## Form (b): the Rust loop -/

/-- One iteration of the `for item in items` loop of `find_item`. -/
def findItemStep (pred : α → Bool) (aliases : FoundAliases) (result : Option τ)
    (item : Spec α × τ) : Option τ :=
  let (judgement, who) : Bool × Meta α := match item.1 with
    | .forbid x => (false, x)
    | .allow x => (true, x)
  match who with
  | .all => boolThen judgement item.2
  | .only ident => if pred ident then boolThen judgement item.2 else result
  | .alias id =>
    match aliases id with
    | some true => boolThen judgement item.2
    | some false => boolThen (!judgement) item.2
    | none => result

/-- `mod.rs` `find_item`. -/
def findItem (pred : α → Bool) (aliases : FoundAliases) (items : List (Spec α × τ)) : Option τ :=
  items.foldl (findItemStep pred aliases) none

/-! ## Form (a): the final matching entry decides -/

/-- Does an entry take part in the decision at all? (Why3 `matched_by`.) An alias reference
participates iff the alias table affirms or denies membership. -/
def matchedBy (aliases : FoundAliases) (pred : α → Bool) (s : Spec α) : Bool :=
  match s.who with
  | .all => true
  | .only x => pred x
  | .alias n => (aliases n).isSome

/-- What a participating entry decides (Why3 `condition`): a negated alias whose definition
excludes the item grants (substitution semantics). -/
def condition (aliases : FoundAliases) : Spec α × τ → Option τ
  | (.allow (.alias n), t) => if aliases n = some true then some t else none
  | (.forbid (.alias n), t) => if aliases n = some true then none else some t
  | (.allow _, t) => some t
  | (.forbid _, _) => none

/-- The last element of a list satisfying `p`. -/
def lastMatch (p : β → Bool) (l : List β) : Option β := (l.filter p).getLast?

/-- `x` is the final element of `l` satisfying `p` (Why3 `is_final_match`). -/
def IsFinalMatch (p : β → Bool) (l : List β) (x : β) : Prop :=
  ∃ pre post, l = pre ++ x :: post ∧ p x = true ∧ ∀ y ∈ post, p y = false

/-- Declarative `find_item`: the final matching entry decides; no match means `none`. -/
def findItemSpec (pred : α → Bool) (aliases : FoundAliases) (items : List (Spec α × τ)) :
    Option τ :=
  (lastMatch (fun x => matchedBy aliases pred x.1) items).bind (condition aliases)

/-! ## Lemmas on `lastMatch` -/

theorem lastMatch_nil (p : β → Bool) : lastMatch p [] = none := rfl

theorem lastMatch_append (p : β → Bool) (l₁ l₂ : List β) :
    lastMatch p (l₁ ++ l₂) = (lastMatch p l₂).or (lastMatch p l₁) := by
  simp [lastMatch, List.filter_append, List.getLast?_append]

theorem lastMatch_singleton (p : β → Bool) (x : β) :
    lastMatch p [x] = if p x then some x else none := by
  by_cases h : p x <;> simp [lastMatch, List.filter, h]

theorem lastMatch_cons (p : β → Bool) (x : β) (l : List β) :
    lastMatch p (x :: l) = (lastMatch p l).or (if p x then some x else none) := by
  rw [show x :: l = [x] ++ l from rfl, lastMatch_append, lastMatch_singleton]

theorem lastMatch_concat (p : β → Bool) (l : List β) (x : β) :
    lastMatch p (l ++ [x]) = if p x then some x else lastMatch p l := by
  rw [lastMatch_append, lastMatch_singleton]
  by_cases h : p x <;> simp [h]

theorem lastMatch_eq_none_iff (p : β → Bool) (l : List β) :
    lastMatch p l = none ↔ ∀ y ∈ l, p y = false := by
  simp [lastMatch]

theorem lastMatch_map (p : β → Bool) (f : α → β) (l : List α) :
    lastMatch p (l.map f) = (lastMatch (p ∘ f) l).map f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.map_cons, lastMatch_cons, ih]
    by_cases h : p (f x) <;> cases lastMatch (p ∘ f) l <;> simp [h, Function.comp]

theorem lastMatch_spec {p : β → Bool} {l : List β} {x : β} (h : lastMatch p l = some x) :
    x ∈ l ∧ p x = true := by
  simp only [lastMatch] at h
  have := List.mem_of_getLast? h
  simp only [List.mem_filter] at this
  exact this

theorem lastMatch_eq_some_iff (p : β → Bool) (l : List β) (x : β) :
    lastMatch p l = some x ↔ IsFinalMatch p l x := by
  constructor
  · intro h
    simp only [lastMatch, List.getLast?_eq_some_iff] at h
    obtain ⟨ys, hys⟩ := h
    rw [List.filter_eq_append_iff] at hys
    obtain ⟨l₁, l₂, rfl, -, h₂⟩ := hys
    rw [List.filter_eq_cons_iff] at h₂
    obtain ⟨m₁, m₂, rfl, hm₁, hx, hm₂⟩ := h₂
    refine ⟨l₁ ++ m₁, m₂, by simp, hx, ?_⟩
    rw [List.filter_eq_nil_iff] at hm₂
    intro y hy
    simpa using hm₂ y hy
  · rintro ⟨pre, post, rfl, hx, hpost⟩
    rw [lastMatch_append, lastMatch_cons, (lastMatch_eq_none_iff p post).2 hpost]
    simp [hx]

theorem IsFinalMatch.unique {p : β → Bool} {l : List β} {x y : β}
    (hx : IsFinalMatch p l x) (hy : IsFinalMatch p l y) : x = y := by
  rw [← lastMatch_eq_some_iff] at hx hy
  rw [hx] at hy
  exact Option.some.inj hy

/-- The folding scheme shared by all "last one wins" loops. -/
theorem foldl_ite_eq_lastMatch (p : β → Bool) (f : β → Option τ) (l : List β) (r : Option τ) :
    l.foldl (fun acc x => if p x then f x else acc) r = ((lastMatch p l).map f).getD r := by
  induction l generalizing r with
  | nil => rfl
  | cons x l ih =>
    rw [List.foldl_cons, ih, lastMatch_cons]
    cases hl : lastMatch p l with
    | some y => rfl
    | none => by_cases h : p x <;> simp [h]

/-! ## (a) = (b) for `find_item` -/

/-- One loop iteration either ignores the item or lets it decide. -/
theorem findItemStep_eq (pred : α → Bool) (aliases : FoundAliases) (r : Option τ)
    (x : Spec α × τ) :
    findItemStep pred aliases r x =
      if matchedBy aliases pred x.1 then condition aliases x else r := by
  obtain ⟨q, t⟩ := x
  cases q with
  | allow m =>
    cases m with
    | all => rfl
    | only i => by_cases h : pred i <;> simp [findItemStep, matchedBy, condition, boolThen, h, Qualified.who]
    | alias n =>
      cases h : aliases n with
      | none => simp [findItemStep, matchedBy, Qualified.who, h]
      | some b => cases b <;> simp [findItemStep, matchedBy, condition, boolThen, Qualified.who, h]
  | forbid m =>
    cases m with
    | all => rfl
    | only i => by_cases h : pred i <;> simp [findItemStep, matchedBy, condition, boolThen, h, Qualified.who]
    | alias n =>
      cases h : aliases n with
      | none => simp [findItemStep, matchedBy, Qualified.who, h]
      | some b => cases b <;> simp [findItemStep, matchedBy, condition, boolThen, Qualified.who, h]

/-- `find_item` from an arbitrary accumulator. -/
theorem foldl_findItemStep (pred : α → Bool) (aliases : FoundAliases) (l : List (Spec α × τ))
    (r : Option τ) :
    l.foldl (findItemStep pred aliases) r =
      ((lastMatch (fun x => matchedBy aliases pred x.1) l).map (condition aliases)).getD r := by
  have : findItemStep pred aliases (τ := τ) =
      fun acc x => if matchedBy aliases pred x.1 then condition aliases x else acc := by
    funext acc x; exact findItemStep_eq pred aliases acc x
  rw [this]
  exact foldl_ite_eq_lastMatch _ _ _ _

/-- **(a) = (b)** for `find_item`. -/
theorem findItem_eq_spec (pred : α → Bool) (aliases : FoundAliases) (items : List (Spec α × τ)) :
    findItem pred aliases items = findItemSpec pred aliases items := by
  simp only [findItem, findItemSpec, foldl_findItemStep]
  cases lastMatch (fun x => matchedBy aliases pred x.1) items <;> rfl

/-- Why3 postcondition of `find_item`, `Some` case: the result is the verdict of the final
matching entry. -/
theorem findItem_eq_some_iff (pred : α → Bool) (aliases : FoundAliases)
    (items : List (Spec α × τ)) (t : τ) :
    findItem pred aliases items = some t ↔
      ∃ x, IsFinalMatch (fun x => matchedBy aliases pred x.1) items x ∧
        condition aliases x = some t := by
  rw [findItem_eq_spec, findItemSpec]
  constructor
  · intro h
    obtain ⟨x, hx, hc⟩ := Option.bind_eq_some_iff.1 h
    exact ⟨x, (lastMatch_eq_some_iff _ _ _).1 hx, hc⟩
  · rintro ⟨x, hx, hc⟩
    rw [(lastMatch_eq_some_iff _ _ _).2 hx]
    exact hc

/-- Why3 postcondition of `find_item`, `None` case: no entry matches, or the final matching
entry denies. -/
theorem findItem_eq_none_iff (pred : α → Bool) (aliases : FoundAliases)
    (items : List (Spec α × τ)) :
    findItem pred aliases items = none ↔
      ∀ x, IsFinalMatch (fun x => matchedBy aliases pred x.1) items x →
        condition aliases x = none := by
  rw [findItem_eq_spec, findItemSpec]
  constructor
  · intro h x hx
    rw [(lastMatch_eq_some_iff _ _ _).2 hx] at h
    exact h
  · intro h
    cases hl : lastMatch (fun x => matchedBy aliases pred x.1) items with
    | none => rfl
    | some x => exact h x ((lastMatch_eq_some_iff _ _ _).1 hl)

/-- Default deny for `find_item`: without a participating entry the answer is `none`. -/
theorem findItem_of_no_match (pred : α → Bool) (aliases : FoundAliases)
    (items : List (Spec α × τ)) (h : ∀ x ∈ items, matchedBy aliases pred x.1 = false) :
    findItem pred aliases items = none := by
  rw [findItem_eq_spec, findItemSpec, ((lastMatch_eq_none_iff _ _).2 h)]
  rfl

/-- Appending entries: the later block wins as soon as one of its entries participates. -/
theorem findItem_append (pred : α → Bool) (aliases : FoundAliases)
    (l₁ l₂ : List (Spec α × τ)) :
    findItem pred aliases (l₁ ++ l₂) =
      ((lastMatch (fun x => matchedBy aliases pred x.1) l₂).map (condition aliases)).getD
        (findItem pred aliases l₁) := by
  rw [findItem, List.foldl_append, foldl_findItemStep]
  rfl

/-- One loop iteration only consults the alias the item refers to. -/
theorem findItemStep_congr (pred : α → Bool) {A B : FoundAliases} (r : Option τ)
    (x : Spec α × τ) (h : ∀ k, x.1.who = .alias k → A k = B k) :
    findItemStep pred A r x = findItemStep pred B r x := by
  obtain ⟨q, t⟩ := x
  cases q with
  | allow m =>
    cases m with
    | alias n => simp only [findItemStep]; rw [h n rfl]
    | _ => rfl
  | forbid m =>
    cases m with
    | alias n => simp only [findItemStep]; rw [h n rfl]
    | _ => rfl

/-- Two alias tables that agree on every alias referenced by the items give the same answer. -/
theorem findItem_congr (pred : α → Bool) {A B : FoundAliases} (items : List (Spec α × τ))
    (h : ∀ x ∈ items, ∀ k, x.1.who = .alias k → A k = B k) :
    findItem pred A items = findItem pred B items := by
  simp only [findItem]
  generalize (none : Option τ) = r
  induction items generalizing r with
  | nil => rfl
  | cons x l ih =>
    simp only [List.foldl_cons]
    rw [findItemStep_congr pred r x (h x List.mem_cons_self)]
    exact ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) _

end SudoersSpec
