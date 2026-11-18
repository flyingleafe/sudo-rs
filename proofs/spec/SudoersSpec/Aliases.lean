import SudoersSpec.FindItem

/-!
# Alias resolution

`getAliases` is `mod.rs` `get_aliases`: one pass over an alias table in processing order that
records, per alias, whether the item at hand is affirmed (`true`), explicitly excluded
(`false`) or not mentioned (absent). `find_item` then consults this table instead of expanding
aliases.

The main result, `demonstration`, is the port of the Why3 lemma of the same name
(`proofs/sudoers.mlw`, module `Correctness`): for a table with unique names that has a
topologically sorted permutation in which every referenced alias is defined, deciding with
the precomputed table gives the same answer as deciding on the fully expanded list, and
`|table|` rounds of expansion remove every alias reference.
-/

namespace SudoersSpec

variable {α τ : Type}

/-! ## `get_aliases` -/

/-- One iteration of the loop of `get_aliases` (`mod.rs` lines 701-709). -/
def getAliasesStep (pred : α → Bool) (set : FoundAliases) (d : Def α) : FoundAliases :=
  if (findItem pred set (withUnit d.items)).isSome then set.insert d.name true
  else if (findItem pred set ((Qualified.allow Meta.all, ()) :: withUnit d.items)).isNone then
    set.insert d.name false
  else set

/-- `mod.rs` `get_aliases`; `table` is the `VecOrd` iteration order. -/
def getAliases (table : List (Def α)) (pred : α → Bool) : FoundAliases :=
  table.foldl (getAliasesStep pred) FoundAliases.empty

/-- The verdict an alias body gives under a table: `some true` affirmed, `some false`
explicitly excluded, `none` not mentioned. -/
def aliasValue (pred : α → Bool) (set : FoundAliases) (items : SpecList α) : Option Bool :=
  (lastMatch (matchedBy set pred) items).map fun s => (condition set (s, ())).isSome

theorem lastMatch_withUnit (p : Spec α → Bool) (items : SpecList α) :
    lastMatch (fun x : Spec α × Unit => p x.1) (withUnit items) =
      (lastMatch p items).map (·, ()) := by
  rw [withUnit, lastMatch_map]; rfl

theorem getAliasesStep_eq (pred : α → Bool) (G : FoundAliases) (d : Def α) :
    getAliasesStep pred G d =
      match aliasValue pred G d.items with
      | some b => G.insert d.name b
      | none => G := by
  have h1 : findItem pred G (withUnit d.items) =
      ((lastMatch (matchedBy G pred) d.items).map fun s => condition G (s, ())).getD none := by
    rw [findItem, foldl_findItemStep, lastMatch_withUnit, Option.map_map]; rfl
  have h2 : findItem pred G ((Qualified.allow Meta.all, ()) :: withUnit d.items) =
      ((lastMatch (matchedBy G pred) d.items).map fun s => condition G (s, ())).getD
        (some ()) := by
    rw [findItem, List.foldl_cons, foldl_findItemStep, lastMatch_withUnit, Option.map_map]; rfl
  simp only [getAliasesStep, aliasValue, h1, h2]
  cases lastMatch (matchedBy G pred) d.items with
  | none => simp
  | some s => cases hc : condition G (s, ()) <;> simp [hc]

theorem getAliasesStep_other (pred : α → Bool) (G : FoundAliases) (d : Def α) (k : String)
    (hk : k ≠ d.name) : getAliasesStep pred G d k = G k := by
  rw [getAliasesStep_eq]
  cases aliasValue pred G d.items <;> simp [FoundAliases.insert, hk]

theorem getAliasesStep_self (pred : α → Bool) (G : FoundAliases) (d : Def α)
    (h : G d.name = none) : getAliasesStep pred G d d.name = aliasValue pred G d.items := by
  rw [getAliasesStep_eq]
  cases aliasValue pred G d.items <;> simp [FoundAliases.insert, h]

/-- Names defined by a table. -/
def names (t : List (Def α)) : List String := t.map (·.name)

theorem foldl_getAliasesStep_other (pred : α → Bool) (l : List (Def α)) (G : FoundAliases)
    (k : String) (hk : k ∉ names l) : l.foldl (getAliasesStep pred) G k = G k := by
  induction l generalizing G with
  | nil => rfl
  | cons d l ih =>
    simp only [names, List.map_cons, List.mem_cons, not_or] at hk
    rw [List.foldl_cons, ih _ hk.2, getAliasesStep_other _ _ _ _ hk.1]

/-- An alias that the table does not define is never in the result. -/
theorem getAliases_undefined (pred : α → Bool) (t : List (Def α)) (k : String)
    (hk : k ∉ names t) : getAliases t pred k = none :=
  foldl_getAliasesStep_other pred t _ k hk

theorem aliasValue_congr (pred : α → Bool) {A B : FoundAliases} (items : SpecList α)
    (h : ∀ s ∈ items, ∀ k, s.who = .alias k → A k = B k) :
    aliasValue pred A items = aliasValue pred B items := by
  have hm : ∀ s ∈ items, matchedBy A pred s = matchedBy B pred s := by
    intro s hs
    unfold matchedBy
    cases hw : s.who with
    | alias k => simp [h s hs k hw]
    | _ => rfl
  have hc : ∀ s ∈ items, condition A (s, ()) = condition B (s, ()) := by
    intro s hs
    cases s <;> rename_i m <;> cases m <;> simp only [condition] <;>
      (rename_i k; rw [h _ hs k rfl])
  unfold aliasValue
  have hp : lastMatch (matchedBy A pred) items = lastMatch (matchedBy B pred) items := by
    unfold lastMatch; rw [List.filter_congr hm]
  rw [← hp]
  cases h1 : lastMatch (matchedBy A pred) items with
  | none => rfl
  | some s => simp [hc s (lastMatch_spec h1).1]

/-! ## Sortedness and the fixpoint property -/

/-- Every alias referenced by a definition is defined strictly earlier in the table
(topologically sorted, and every reference resolved). -/
def Sorted (t : List (Def α)) : Prop :=
  ∀ pre d post, t = pre ++ d :: post → ∀ s ∈ d.items, ∀ k, s.who = .alias k → k ∈ names pre

theorem names_append (a b : List (Def α)) : names (a ++ b) = names a ++ names b := by
  simp [names]

theorem names_cons (d : Def α) (a : List (Def α)) : names (d :: a) = d.name :: names a := rfl

theorem mem_names {t : List (Def α)} {d : Def α} (h : d ∈ t) : d.name ∈ names t :=
  List.mem_map_of_mem h

/-- The precomputed table is a fixpoint: every alias holds exactly the verdict of its own
body evaluated under the final table (Why3 postconditions of `get_aliases`). -/
theorem getAliases_fixpoint (pred : α → Bool) (t : List (Def α)) (hu : (names t).Nodup)
    (hs : Sorted t) (d : Def α) (hd : d ∈ t) :
    getAliases t pred d.name = aliasValue pred (getAliases t pred) d.items := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hd
  rw [names_append, names_cons, List.nodup_append, List.nodup_cons] at hu
  obtain ⟨-, ⟨hdpost, -⟩, hdisj⟩ := hu
  have hdpre : d.name ∉ names pre := fun h => hdisj _ h _ List.mem_cons_self rfl
  have hG : getAliases (pre ++ d :: post) pred =
      post.foldl (getAliasesStep pred)
        (getAliasesStep pred (pre.foldl (getAliasesStep pred) FoundAliases.empty) d) := by
    simp [getAliases, List.foldl_append]
  have hGpd : (pre.foldl (getAliasesStep pred) FoundAliases.empty) d.name = none :=
    foldl_getAliasesStep_other pred pre _ _ hdpre
  rw [hG, foldl_getAliasesStep_other pred post _ _ hdpost, getAliasesStep_self _ _ _ hGpd]
  apply aliasValue_congr
  intro s hsi k hk
  have hkpre := hs pre d post rfl s hsi k hk
  have hkpost : k ∉ names post := fun h => hdisj _ hkpre _ (List.mem_cons_of_mem _ h) rfl
  have hkd : k ≠ d.name := fun h => hdpre (h ▸ hkpre)
  rw [foldl_getAliasesStep_other pred post _ _ hkpost, getAliasesStep_other _ _ _ _ hkd]

/-! ## Full alias expansion (not present in the Rust code) -/

/-- The body of the first definition of `k`. -/
def lookupDef (t : List (Def α)) (k : String) : Option (SpecList α) :=
  (t.find? (·.name == k)).map (·.items)

/-- Substitute one entry: `A` becomes the body of `A` (carrying the entry's satellite data),
`!A` the body with every qualifier flipped; undefined aliases disappear. -/
def expandItem (t : List (Def α)) : Spec α × τ → List (Spec α × τ)
  | (.allow (.alias k), i) => ((lookupDef t k).getD []).map (·, i)
  | (.forbid (.alias k), i) => ((lookupDef t k).getD []).map fun s => (s.negate, i)
  | x => [x]

/-- One round of expansion (Why3 `expand_aliases`). -/
def expandStep (t : List (Def α)) (l : List (Spec α × τ)) : List (Spec α × τ) :=
  l.flatMap (expandItem t)

/-- `n` rounds of expansion. -/
def expandN (t : List (Def α)) : Nat → List (Spec α × τ) → List (Spec α × τ)
  | 0, l => l
  | n + 1, l => expandN t n (expandStep t l)

/-- Full expansion: one round per definition (Why3 `expand_all_aliases`). -/
def expandAll (t : List (Def α)) (l : List (Spec α × τ)) : List (Spec α × τ) :=
  expandN t t.length l

/-- No entry refers to an alias. -/
def AliasFree (l : List (Spec α × τ)) : Prop := ∀ x ∈ l, ∀ k, x.1.who ≠ .alias k

/-- Every alias referenced by the entries is defined in `P`. -/
def RefsIn (P : List (Def α)) (l : List (Spec α × τ)) : Prop :=
  ∀ x ∈ l, ∀ k, x.1.who = .alias k → k ∈ names P

theorem matchedBy_negate (G : FoundAliases) (pred : α → Bool) (s : Spec α) :
    matchedBy G pred s.negate = matchedBy G pred s := by
  cases s <;> rfl

theorem who_negate (s : Spec α) : s.negate.who = s.who := by
  cases s <;> rfl

theorem condition_info (G : FoundAliases) (s : Spec α) (i : τ) :
    condition G (s, i) = (condition G (s, ())).map fun _ => i := by
  cases s <;> rename_i m <;> cases m <;> simp only [condition] <;> (try split) <;> rfl

theorem condition_negate (G : FoundAliases) (s : Spec α) (i : τ) :
    condition G (s.negate, i) = if (condition G (s, ())).isSome then none else some i := by
  cases s <;> rename_i m <;> cases m <;> simp only [condition, Qualified.negate] <;>
    (try split) <;> simp_all

theorem lookupDef_some {t : List (Def α)} {k : String} {body : SpecList α}
    (h : lookupDef t k = some body) : ∃ d ∈ t, d.name = k ∧ d.items = body := by
  simp only [lookupDef, Option.map_eq_some_iff] at h
  obtain ⟨d, hd, rfl⟩ := h
  exact ⟨d, List.mem_of_find?_eq_some hd, by simpa using List.find?_some hd, rfl⟩

theorem lookupDef_none {t : List (Def α)} {k : String} (h : lookupDef t k = none) :
    k ∉ names t := by
  simp only [lookupDef, Option.map_eq_none_iff, List.find?_eq_none] at h
  intro hk
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hk
  exact h d hd (by simp)

/-- Expanding one entry does not change the decision, provided the alias table holds the
verdict of every body (the fixpoint property) and nothing for undefined aliases. -/
theorem foldl_expandItem (pred : α → Bool) (G : FoundAliases) (t : List (Def α))
    (hfix : ∀ k body, lookupDef t k = some body → G k = aliasValue pred G body)
    (hnone : ∀ k, lookupDef t k = none → G k = none) (r : Option τ) (x : Spec α × τ) :
    (expandItem t x).foldl (findItemStep pred G) r = findItemStep pred G r x := by
  obtain ⟨q, i⟩ := x
  cases q with
  | allow m =>
    cases m with
    | all => rfl
    | only _ => rfl
    | alias k =>
      cases hl : lookupDef t k with
      | none => simp [expandItem, hl, findItemStep, hnone k hl]
      | some body =>
        have hk := hfix k body hl
        simp only [expandItem, hl, Option.getD_some, foldl_findItemStep]
        rw [lastMatch_map]
        have hc : ((fun x : Spec α × τ => matchedBy G pred x.1) ∘ fun s => (s, i)) =
            matchedBy G pred := rfl
        rw [hc]
        simp only [aliasValue] at hk
        cases hm : lastMatch (matchedBy G pred) body with
        | none => simp [hm, findItemStep, hk]
        | some s =>
          rw [hm] at hk
          simp only [Option.map_some, Option.getD_some]
          rw [condition_info]
          cases hcs : condition G (s, ()) <;> simp_all [findItemStep, boolThen]
  | forbid m =>
    cases m with
    | all => rfl
    | only _ => rfl
    | alias k =>
      cases hl : lookupDef t k with
      | none => simp [expandItem, hl, findItemStep, hnone k hl]
      | some body =>
        have hk := hfix k body hl
        simp only [expandItem, hl, Option.getD_some, foldl_findItemStep]
        rw [lastMatch_map]
        have hc : ((fun x : Spec α × τ => matchedBy G pred x.1) ∘ fun s => (s.negate, i)) =
            matchedBy G pred := by
          funext s; exact matchedBy_negate G pred s
        rw [hc]
        simp only [aliasValue] at hk
        cases hm : lastMatch (matchedBy G pred) body with
        | none => simp [hm, findItemStep, hk]
        | some s =>
          rw [hm] at hk
          simp only [Option.map_some, Option.getD_some]
          rw [condition_negate]
          cases hcs : condition G (s, ()) <;> simp_all [findItemStep, boolThen]

theorem findItem_expandN (pred : α → Bool) (G : FoundAliases) (t : List (Def α))
    (hfix : ∀ k body, lookupDef t k = some body → G k = aliasValue pred G body)
    (hnone : ∀ k, lookupDef t k = none → G k = none) (n : Nat) (l : List (Spec α × τ)) :
    findItem pred G (expandN t n l) = findItem pred G l := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    rw [expandN, ih]
    simp only [findItem, expandStep, List.foldl_flatMap]
    congr 1
    funext acc x
    exact foldl_expandItem pred G t hfix hnone acc x

/-- One round of expansion lowers the rank of every reference by one. -/
theorem refsIn_expandStep (t sorted : List (Def α)) (hperm : t.Perm sorted)
    (hu : (names sorted).Nodup) (hs : Sorted sorted) (P rest : List (Def α)) (d' : Def α)
    (hsplit : sorted = P ++ d' :: rest) (l : List (Spec α × τ))
    (hl : RefsIn (P ++ [d']) l) : RefsIn P (expandStep t l) := by
  intro y hy k' hk'
  obtain ⟨x, hx, hyx⟩ := List.mem_flatMap.1 hy
  obtain ⟨q, i⟩ := x
  -- the definition an alias reference is replaced with, and where it sits in `sorted`
  have key : ∀ k body s, (q, i) = (q, i) → (Qualified.who q = .alias k) →
      lookupDef t k = some body → s ∈ body → s.who = .alias k' → k' ∈ names P := by
    intro k body s _ hq hb hs' hsk
    obtain ⟨d, hdt, hdk, rfl⟩ := lookupDef_some hb
    have hds : d ∈ sorted := hperm.mem_iff.1 hdt
    have hkP : k ∈ names (P ++ [d']) := hl _ hx k hq
    rw [hsplit, names_append, names_cons, List.nodup_append] at hu
    rw [hsplit] at hds
    rcases List.mem_append.1 hds with hdP | hdrest
    · obtain ⟨pre, post, rfl⟩ := List.append_of_mem hdP
      have := hs pre d (post ++ d' :: rest) (by rw [hsplit]; simp) s hs' k' hsk
      rw [names_append]; exact List.mem_append_left _ this
    · rcases List.mem_cons.1 hdrest with rfl | hdr
      · exact hs P d rest hsplit s hs' k' hsk
      · exfalso
        rw [names_append] at hkP
        rcases List.mem_append.1 hkP with h1 | h1
        · exact hu.2.2 _ h1 _ (List.mem_cons_of_mem _ (hdk ▸ mem_names hdr)) rfl
        · simp only [names, List.map_cons, List.map_nil, List.mem_singleton] at h1
          rw [List.nodup_cons] at hu
          exact hu.2.1.1 (h1 ▸ hdk ▸ mem_names hdr)
  cases q with
  | allow m =>
    cases m with
    | all => simp [expandItem] at hyx; subst hyx; cases hk'
    | only _ => simp [expandItem] at hyx; subst hyx; cases hk'
    | alias k =>
      cases hb : lookupDef t k with
      | none => simp [expandItem, hb] at hyx
      | some body =>
        simp only [expandItem, hb, Option.getD_some, List.mem_map] at hyx
        obtain ⟨s, hs', rfl⟩ := hyx
        exact key k body s rfl rfl hb hs' hk'
  | forbid m =>
    cases m with
    | all => simp [expandItem] at hyx; subst hyx; cases hk'
    | only _ => simp [expandItem] at hyx; subst hyx; cases hk'
    | alias k =>
      cases hb : lookupDef t k with
      | none => simp [expandItem, hb] at hyx
      | some body =>
        simp only [expandItem, hb, Option.getD_some, List.mem_map] at hyx
        obtain ⟨s, hs', rfl⟩ := hyx
        exact key k body s rfl rfl hb hs' (by rw [← who_negate]; exact hk')

theorem aliasFree_expandN (t sorted : List (Def α)) (hperm : t.Perm sorted)
    (hu : (names sorted).Nodup) (hs : Sorted sorted) (n : Nat) :
    ∀ (P : List (Def α)) (l : List (Spec α × τ)), (∃ rest, sorted = P ++ rest) →
      P.length = n → RefsIn P l → AliasFree (expandN t n l) := by
  induction n with
  | zero =>
    intro P l _ hP hl x hx k hk
    rw [List.length_eq_zero_iff] at hP
    subst hP
    simpa [names] using hl x hx k hk
  | succ n ih =>
    intro P l ⟨rest, hrest⟩ hP hl
    rcases List.eq_nil_or_concat P with rfl | ⟨P', d', rfl⟩
    · simp at hP
    · rw [List.concat_eq_append] at hrest hP hl
      simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hP
      have hsplit : sorted = P' ++ d' :: rest := by rw [hrest]; simp
      exact ih P' (expandStep t l) ⟨d' :: rest, hsplit⟩ hP
        (refsIn_expandStep t sorted hperm hu hs P' rest d' hsplit l hl)

/-- **Alias demonstration** (port of Why3 `Correctness.demonstration`). Let `t` be an alias
table in file order and `sorted` a permutation of it with unique names in which every alias
referenced by a definition is defined earlier (acyclic and fully defined). If every alias the
items refer to is defined, then full expansion removes all alias references, and deciding on
the expanded list (under any alias table `S`, which is no longer consulted) is the same as
deciding with the table `get_aliases` precomputes. -/
theorem demonstration (t sorted : List (Def α)) (pred : α → Bool)
    (items : List (Spec α × τ)) (S : FoundAliases)
    (hperm : t.Perm sorted) (hu : (names sorted).Nodup) (hs : Sorted sorted)
    (hdef : RefsIn sorted items) :
    AliasFree (expandAll t items) ∧
      findItem pred S (expandAll t items) = findItem pred (getAliases sorted pred) items := by
  have hfree : AliasFree (expandAll t items) :=
    aliasFree_expandN t sorted hperm hu hs t.length sorted items ⟨[], by simp⟩
      hperm.length_eq.symm hdef
  refine ⟨hfree, ?_⟩
  rw [findItem_congr pred _ (fun x hx k hk => absurd hk (hfree x hx k))
    (B := getAliases sorted pred)]
  apply findItem_expandN
  · intro k body hb
    obtain ⟨d, hdt, rfl, rfl⟩ := lookupDef_some hb
    exact getAliases_fixpoint pred sorted hu hs d (hperm.mem_iff.1 hdt)
  · intro k hk
    apply getAliases_undefined
    intro hks
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hks
    exact lookupDef_none hk (mem_names (hperm.mem_iff.2 hd))

end SudoersSpec
