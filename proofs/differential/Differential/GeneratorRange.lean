import Differential.Generate

open SudoersSpec

namespace Differential.GeneratorRange

open Differential.Generate

/-- Every initial generator state gives a value satisfying `P`. -/
def Produces (g : Gen α) (P : α → Prop) : Prop := ∀ seed, P ((g.run seed).1)

theorem ret (a : α) (P : α → Prop) (h : P a) : Produces (pure a) P := fun _ => h

theorem seq {g : Gen α} {k : α → Gen β} {P : α → Prop} {Q : β → Prop}
    (hg : Produces g P) (hk : ∀ a, P a → Produces (k a) Q) : Produces (g >>= k) Q :=
  fun seed => hk (g.run seed).1 (hg seed) (g.run seed).2

theorem mono {g : Gen α} {P Q : α → Prop} (h : Produces g P)
    (imp : ∀ a, P a → Q a) : Produces g Q := fun s => imp _ (h s)

private theorem below_lt (n : Nat) (h : 0 < n) : Produces (Gen.below n) (· < n) := by
  intro s
  change (if n = 0 then 0 else (s.next.1.toNat % n)) < n
  simp [Nat.ne_of_gt h, Nat.mod_lt _ h]

theorem pick_mem [Inhabited α] (xs : List α) (hx : xs ≠ []) :
    Produces (Gen.pick xs) (· ∈ xs) := by
  unfold Gen.pick
  refine seq (Q := fun x => x ∈ xs) (below_lt xs.length (List.length_pos_iff.mpr hx)) ?_
  intro i hi
  apply ret
  rw [getElem!_pos xs i hi]
  exact List.getElem_mem hi

/-- A generator list is a list with these cardinality bounds and a property on each item. -/
def ItemRange (lo hi : Nat) (P : α → Prop) (xs : List α) : Prop :=
  lo ≤ xs.length ∧ xs.length ≤ hi ∧ ∀ x ∈ xs, P x

private theorem array_push_all {P : α → Prop} {out : Array α} {x : α}
    (ho : ∀ a ∈ out.toList, P a) (hx : P x) :
    ∀ a ∈ (out.push x).toList, P a := by
  intro a ha
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at ha
  rcases ha with ha | rfl
  · exact ho a ha
  · exact hx

private theorem forDraws {P : α → Prop} {g : Gen α} (hg : Produces g P) :
    ∀ (ns : List Nat) (out : Array α), (∀ a ∈ out.toList, P a) →
      Produces (forIn ns out (fun _ out => do pure (.yield (out.push (← g)))))
        (fun a => a.size = out.size + ns.length ∧ ∀ x ∈ a.toList, P x) := by
  intro ns
  induction ns with
  | nil => intro out ho; simp only [List.forIn_nil]; exact ret _ _ ⟨by simp, ho⟩
  | cons j ns ih =>
    intro out ho
    rw [List.forIn_cons]
    intro s
    have hf := ih (out.push (g.run s).1) (array_push_all ho (hg s)) (g.run s).2
    constructor
    · change ((forIn ns (out.push (g.run s).1) (fun _ out => do pure (.yield (out.push (← g))))).run
        (g.run s).2).1.size = _
      rw [hf.1, Array.size_push, List.length_cons]
      omega
    · exact hf.2

theorem listOf_range {P : α → Prop} {g : Gen α} (hg : Produces g P)
    (lo hi : Nat) (hn : lo ≤ hi) : Produces (Gen.listOf lo hi g) (ItemRange lo hi P) := by
  unfold Gen.listOf
  refine seq (Q := ItemRange lo hi P) (below_lt (hi + 1 - lo) (by omega)) ?_
  intro n hd
  dsimp only
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  refine seq (Q := ItemRange lo hi P) (forDraws hg _ #[] (by simp)) ?_
  intro a ha
  apply ret
  obtain ⟨hl, hP⟩ := ha
  simp [Std.Legacy.Range.size] at hl
  change lo ≤ a.toList.length ∧ a.toList.length ≤ hi ∧ _
  rw [Array.length_toList, hl]
  exact ⟨by omega, by omega, hP⟩

def totalWeight (xs : List (Nat × α)) : Nat := (xs.map Prod.fst).sum

private theorem weightFold (xs : List (Nat × α)) (n : Nat) :
    xs.foldl (fun x y => x + y.1) n = n + totalWeight xs := by
  induction xs generalizing n with
  | nil => simp [totalWeight]
  | cons x xs ih => simp [totalWeight, ih, Nat.add_assoc]

private abbrev weightStep (x : Nat × α) (st : Option α × Nat) : Gen (ForInStep (Option α × Nat)) :=
  if st.2 < x.1 then pure (.done (some x.2, st.2)) else pure (.yield (none, st.2 - x.1))

private theorem weightLoop : ∀ (xs : List (Nat × α)) (i : Nat), i < totalWeight xs →
    Produces (forIn xs (none, i) weightStep) (fun out =>
      ∃ w x, (w, x) ∈ xs ∧ 0 < w ∧ out.1 = some x) := by
  intro xs
  induction xs with
  | nil => intro i h; simp [totalWeight] at h
  | cons a xs ih =>
    obtain ⟨w, x⟩ := a
    intro i h
    rw [List.forIn_cons]
    by_cases h' : i < w
    · intro seed
      refine ⟨w, x, by simp, by omega, ?_⟩
      simp only [weightStep, h', ite_true, pure_bind]
      rfl
    · intro seed
      have hb : i - w < totalWeight xs := by
        change i < w + totalWeight xs at h
        omega
      obtain ⟨w', x', hm, hw, ho⟩ := ih (i - w) hb seed
      exact ⟨w', x', List.mem_cons_of_mem _ hm, hw, by
        simpa only [weightStep, h', ite_false, pure_bind] using ho⟩

theorem weighted_mem [Inhabited α] (xs : List (Nat × α)) (h : 0 < totalWeight xs) :
    Produces (Gen.weighted xs) (fun a => ∃ w, (w, a) ∈ xs ∧ 0 < w) := by
  unfold Gen.weighted
  simp only [weightFold, Nat.zero_add]
  refine seq (Q := fun a => ∃ w, (w, a) ∈ xs ∧ 0 < w) (below_lt (totalWeight xs) h) ?_
  intro i hi
  refine seq (Q := fun a => ∃ w, (w, a) ∈ xs ∧ 0 < w) (weightLoop xs i hi) ?_
  rintro out ⟨w, x, hm, hw, he⟩
  rw [he]
  exact ret _ _ ⟨w, hm, hw⟩

def aliasPool (pfx : String) : List String :=
  (List.range 3).map (fun i => s!"{pfx}{i}")

private def ordinaryDefStep (pfx : String) (plain : Gen α) (i : Nat)
    (out : Array (Def α)) : Gen (ForInStep (Array (Def α))) := do
  let _ ← Gen.chance 1 2
  let refs ← pure ((List.range i).map (fun x => s!"{pfx}{x}"))
  let items ← Gen.listOf 1 3 (Generate.item plain refs [])
  pure (.yield (out.push ⟨s!"{pfx}{i}", items⟩))

private def defCount : Gen Nat := Gen.weighted [(3, 0), (3, 1), (2, 2), (1, 3)]

private def ordinaryDefs (pfx : String) (plain : Gen α) : Gen (List (Def α)) := do
  let n ← defCount
  let out ← forIn [:n] #[] (ordinaryDefStep pfx plain)
  let _ ← Gen.chance 1 2
  pure out.toList

private theorem ordinaryDefs_eq (pfx : String) (plain : Gen α) (caps : List String) :
    Generate.defs {} pfx plain caps = ordinaryDefs pfx plain := by
  simp only [Generate.defs, ordinaryDefs, defCount, Bool.false_and, Bool.false_eq_true, ite_false]
  rfl

private theorem defCount_bound : Produces defCount (· ≤ 3) := by
  refine mono (Q := (· ≤ 3)) (weighted_mem [(3, 0), (3, 1), (2, 2), (1, 3)] (by decide)) ?_
  rintro n ⟨w, hw, -⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hw
  rcases hw with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide

private theorem run_bind_gen (g : Gen α) (k : α → Gen β) (s : Rng) :
    (g >>= k).run s = (k (g.run s).1).run (g.run s).2 := rfl

private theorem run_draws (g : Gen α) (v : Gen β) (f : β → γ) (s : Rng) :
    (do let _ ← g; let b ← v; pure (f b) : Gen γ).run s =
      (f (v.run (g.run s).2).1, (v.run (g.run s).2).2) := rfl

private theorem defStep_run (pfx : String) (plain : Gen α) (i : Nat)
    (out : Array (Def α)) (s : Rng) :
    let r := (Gen.chance 1 2).run s |>.2
    let it := (Gen.listOf 1 3 (Generate.item plain ((List.range i).map (fun x => s!"{pfx}{x}")) [])).run r
    (ordinaryDefStep pfx plain i out).run s = (.yield (out.push ⟨s!"{pfx}{i}", it.1⟩), it.2) := by
  unfold ordinaryDefStep
  simp only [pure_bind]
  exact run_draws _ _ _ s

private theorem forIn_yield_run {step : γ → β → Gen (ForInStep β)} {i : γ} {is : List γ}
    {a b : β} {s t : Rng} (h : (step i a).run s = (.yield b, t)) :
    (forIn (i :: is) a step).run s = (forIn is b step).run t := by
  rw [List.forIn_cons, run_bind_gen, h]

private theorem defLoop_names (pfx : String) (plain : Gen α) :
    ∀ ns : List Nat, (∀ i ∈ ns, i < 3) → ∀ out : Array (Def α),
      (∀ d ∈ out.toList, d.name ∈ aliasPool pfx) →
      Produces (forIn ns out (ordinaryDefStep pfx plain)) (fun a => ∀ d ∈ a.toList, d.name ∈ aliasPool pfx) := by
  intro ns
  induction ns with
  | nil => intro _ out ho; rw [List.forIn_nil]; exact ret out _ ho
  | cons i is ih =>
    intro hI out ho
    unfold Produces
    intro s
    have hi := hI i (by simp)
    have hm : s!"{pfx}{i}" ∈ aliasPool pfx :=
      List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
    rw [forIn_yield_run (defStep_run pfx plain i out s)]
    exact ih (fun j hj => hI j (List.mem_cons_of_mem _ hj))
      _ (array_push_all ho hm) _

theorem defs_names (pfx : String) (plain : Gen α) (caps : List String) :
    Produces (Generate.defs {} pfx plain caps) (fun xs => ∀ d ∈ xs, d.name ∈ aliasPool pfx) := by
  rw [ordinaryDefs_eq]
  unfold ordinaryDefs
  refine seq (Q := fun (xs : List (Def α)) => ∀ d ∈ xs, d.name ∈ aliasPool pfx) defCount_bound ?_
  intro n hn
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  refine seq (Q := fun (xs : List (Def α)) => ∀ d ∈ xs, d.name ∈ aliasPool pfx)
    (defLoop_names pfx plain _ (fun i hi => ?_) #[] (by simp)) ?_
  · simp [Std.Legacy.Range.size] at hi
    omega
  · intro a ha
    exact seq (P := fun _ => True) (fun _ => trivial) (fun _ _ => ret a.toList _ ha)

theorem namesOf_range {t : List (Def α)} {pool : List String}
    (h : ∀ d ∈ t, d.name ∈ pool) : ∀ n ∈ Generate.namesOf t, n ∈ pool := by
  intro n hn
  simp only [Generate.namesOf, List.mem_eraseDups] at hn
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hn
  exact h d hd

end Differential.GeneratorRange
