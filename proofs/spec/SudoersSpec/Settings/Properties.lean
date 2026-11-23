import SudoersSpec.Settings.Model

/-!
# Properties of the settings model

* the list operations as set operations (`mem_applyList`), and their independence from the
  representation (`applyList_equiv`);
* the name table (`settingNamed_name`, `settingNamed_eq_some`);
* the ranges the integer checkers guarantee, and the invariant they give: every value reached
  from `Settings.default` by modifiers that `negate`, `set`, `checkInteger`, `checkText`,
  `buildList` produce has `passwd_tries ≤ 1000` and `umask ≤ u32::MAX` (`reachable_inRange`).
-/

namespace SudoersSpec.Settings

/-! ## Sets -/

theorem StrSet.mem_insert (s : StrSet) (x y : String) : x ∈ s.insert y ↔ x = y ∨ x ∈ s := by
  unfold StrSet.insert
  split
  · rename_i h
    have : y ∈ s := by simpa using h
    constructor
    · exact .inr
    · rintro (rfl | h) <;> assumption
  · exact List.mem_cons

theorem StrSet.mem_remove (s : StrSet) (x y : String) : x ∈ s.remove y ↔ x ∈ s ∧ x ≠ y := by
  simp [StrSet.remove]

theorem StrSet.mem_foldl_insert (items : List String) (s : StrSet) (x : String) :
    x ∈ items.foldl StrSet.insert s ↔ x ∈ s ∨ x ∈ items := by
  induction items generalizing s with
  | nil => simp
  | cons y rest ih =>
    simp only [List.foldl_cons, ih, StrSet.mem_insert, List.mem_cons]
    constructor
    · rintro ((h | h) | h) <;> simp_all
    · rintro (h | h | h) <;> simp_all

theorem StrSet.mem_foldl_remove (items : List String) (s : StrSet) (x : String) :
    x ∈ items.foldl StrSet.remove s ↔ x ∈ s ∧ x ∉ items := by
  induction items generalizing s with
  | nil => simp
  | cons y rest ih =>
    simp only [List.foldl_cons, ih, StrSet.mem_remove, List.mem_cons, not_or]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩

/-- **The list modes as set operations**: `=` gives exactly the items, `+=` adds them, `-=`
removes them. -/
theorem mem_applyList (s : StrSet) (mode : ListMode) (items : List String) (x : String) :
    x ∈ applyList s (mode, items) ↔
      match mode with
      | .Set => x ∈ items
      | .Add => x ∈ s ∨ x ∈ items
      | .Del => x ∈ s ∧ x ∉ items := by
  cases mode <;> simp [applyList, StrSet.mem_foldl_insert, StrSet.mem_foldl_remove]

/-- The result as a set depends only on the set the list started from. -/
theorem applyList_equiv {a b : StrSet} (h : StrSet.Equiv a b) (v : ListMode × List String) :
    StrSet.Equiv (applyList a v) (applyList b v) := by
  intro x
  rcases v with ⟨mode, items⟩
  rw [mem_applyList, mem_applyList]
  cases mode <;> simp only [h x]

/-! ## The name table -/

theorem settingNamed_name (s : Setting) : settingNamed s.name = some s := by
  cases s <;> rfl

theorem settingNamed_eq_some {n : String} {s : Setting} (h : settingNamed n = some s) :
    n = s.name := by
  unfold settingNamed at h
  have := List.find?_some h
  exact (beq_iff_eq.mp this).symm

theorem negate_isSome_set {n : String} {m : SettingsModifier} (h : negate n = some m) :
    (set n).isSome := by
  unfold negate at h; unfold set
  cases hs : settingNamed n <;> simp_all

/-! ## Ranges -/

theorem parseDigits_le (radix max : Nat) (l : List Nat) (acc v : Nat) (hacc : acc ≤ max)
    (h : parseDigits radix max l acc = .ok v) : v ≤ max := by
  induction l generalizing acc with
  | nil => simp only [parseDigits, Except.ok.injEq] at h; omega
  | cons b rest ih =>
    simp only [parseDigits] at h
    split at h
    · cases h
    · split at h
      · exact ih _ (by assumption) h
      · cases h

theorem fromStrRadix_le (max radix : Nat) (b : List Nat) (v : Nat)
    (h : fromStrRadix max radix b = .ok v) : v ≤ max := by
  obtain ⟨l, hl, -⟩ := fromStrRadix_digits _ _ _ _ h
  exact parseDigits_le _ _ _ _ _ (Nat.zero_le _) hl

theorem octalMode_le {t : String} {v : Nat} (h : octalMode t = some v) : v ≤ u32Max := by
  unfold octalMode at h
  split at h
  · split at h
    · rename_i hv; simp only [Option.some.injEq] at h; subst h
      exact fromStrRadix_le _ _ _ _ hv
    · cases h
  · cases h

theorem integerInRange_le {t : String} {r a b v : Nat} (h : integerInRange t r a b = some v) :
    v ≤ b := by
  unfold integerInRange at h
  split at h
  · split at h
    · simp only [Option.some.injEq] at h; omega
    · cases h
  · cases h

/-- The ranges `Judgement::authorization` needs: `passwd_tries` fits `u16` (here `≤ 1000`),
`umask` fits `u32` (`mode_t`). -/
structure InRange (s : Settings) : Prop where
  passwd_tries : s.passwd_tries ≤ 1000
  umask : s.umask ≤ u32Max

/-- The modifiers the `Defaults` parser can produce: those `negate`, `set`, `checkInteger`,
`checkText` and `buildList` return. -/
inductive Produced : SettingsModifier → Prop where
  | negate {n m} : negate n = some m → Produced m
  | flag {n m} : set n = some (.Flag m) → Produced m
  | integer {id t m} : checkInteger id t = some m → Produced m
  | text {id t m} : checkText id t = some m → Produced m
  | list {id mode items m} : buildList id mode items = m → Produced m

theorem produced_passwd_tries {v : Nat} (h : Produced (.passwd_tries v)) : v ≤ 1000 := by
  cases h with
  | negate h =>
    unfold negate at h
    rcases hs : settingNamed _ with _ | s <;> rw [hs] at h
    · cases h
    · cases s <;> simp [Setting.negation] at h
  | flag h =>
    unfold set at h
    rcases hs : settingNamed _ with _ | s <;> rw [hs] at h
    · cases h
    · cases s <;> simp [Setting.kind] at h
  | integer h =>
    rename_i id t
    cases id <;> simp only [checkInteger, Option.map_eq_some_iff] at h
    all_goals obtain ⟨w, hw, he⟩ := h
    all_goals (try cases he)
    exact integerInRange_le hw
  | text h =>
    rename_i id t
    cases id <;> simp only [checkText] at h
    all_goals (try split at h) <;> simp_all
  | list h => rename_i id _ _; cases id <;> simp [buildList] at h

theorem produced_umask {v : Nat} (h : Produced (.umask v)) : v ≤ u32Max := by
  cases h with
  | negate h =>
    unfold negate at h
    rcases hs : settingNamed _ with _ | s <;> rw [hs] at h
    · cases h
    · cases s <;> simp [Setting.negation] at h
      subst h; decide
  | flag h =>
    unfold set at h
    rcases hs : settingNamed _ with _ | s <;> rw [hs] at h
    · cases h
    · cases s <;> simp [Setting.kind] at h
  | integer h =>
    rename_i id t
    cases id <;> simp only [checkInteger, Option.map_eq_some_iff] at h
    all_goals obtain ⟨w, hw, he⟩ := h
    all_goals (try cases he)
    exact octalMode_le hw
  | text h =>
    rename_i id t
    cases id <;> simp only [checkText] at h
    all_goals (try split at h) <;> simp_all
  | list h => rename_i id _ _; cases id <;> simp [buildList] at h

theorem inRange_apply {s : Settings} {m : SettingsModifier} (hs : InRange s) (hm : Produced m) :
    InRange (m.apply s) := by
  cases m with
  | passwd_tries v => exact ⟨produced_passwd_tries hm, hs.umask⟩
  | umask v => exact ⟨hs.passwd_tries, produced_umask hm⟩
  | _ => exact ⟨hs.passwd_tries, hs.umask⟩

/-- The values a `Settings` takes: the defaults, then modifiers the parser can produce. -/
inductive Reachable : Settings → Prop where
  | default : Reachable Settings.default
  | apply {s m} : Reachable s → Produced m → Reachable (m.apply s)

/-- **Every reachable value is in range.** -/
theorem reachable_inRange {s : Settings} (h : Reachable s) : InRange s := by
  induction h with
  | default => exact ⟨by decide, by decide⟩
  | apply _ hm ih => exact inRange_apply ih hm

end SudoersSpec.Settings
