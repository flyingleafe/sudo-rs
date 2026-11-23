import SudoRsProofs.Defaults.Range
import SudoersSpec.Analysis.Collect

/-!
# `apply_settings` refines `SudoersSpec.Analysis.applyModifiers`

`src/sudoers/mod.rs`: `apply_settings` consumes a `Vec<SettingsModifier>` with an owning
`IntoIter` and folds `SettingsModifier::apply` over the current `Settings`. The reference is
`applyModifiers`, the left fold of the abstract `SettingsModifier.apply` over the abstracted
modifier list.

The lemmas also carry the authorization ranges (`SettingsInRange`) and the fact that every
consumed modifier is `Produced` — the two facts the decision needs. `Defaults.apply_eq` turns each
step into the abstract effect; `Defaults.settings_inRange_apply` keeps the ranges.
-/

open Aeneas Aeneas.Std Result
open sudo_rs
open SudoersSpec.Analysis (applyModifiers)

namespace SudoRsProofs.Parser.Scoping

/-! ## The abstract fold -/

@[simp] theorem applyModifiers_nil (s : SudoersSpec.Settings.Settings) :
    applyModifiers [] s = s := rfl

@[simp] theorem applyModifiers_cons (m : SudoersSpec.Settings.SettingsModifier)
    (ms : List SudoersSpec.Settings.SettingsModifier) (s : SudoersSpec.Settings.Settings) :
    applyModifiers (m :: ms) s = applyModifiers ms (m.apply s) := rfl

theorem applyModifiers_append (l₁ l₂ : List SudoersSpec.Settings.SettingsModifier)
    (s : SudoersSpec.Settings.Settings) :
    applyModifiers (l₁ ++ l₂) s = applyModifiers l₂ (applyModifiers l₁ s) := by
  induction l₁ generalizing s with
  | nil => rfl
  | cons m l₁ ih => simp only [List.cons_append, applyModifiers_cons, ih]

/-! ## `apply_settings_loop` -/

@[simp] theorem apply_settings_loop_false (settings : defaults.Settings)
    (modifiers : alloc.vec.into_iter.IntoIter defaults.SettingsModifier) :
    sudoers.apply_settings_loop settings modifiers false = ok settings := by
  rw [sudoers.apply_settings_loop]
  simp

/-- The `true` run of the loop, proved by induction on the abstract list (the model iterator is
a wrapper around it, so `Defaults.next_nil` / `Defaults.next_cons` expose each step). -/
theorem apply_settings_loop_true_eq (l : List defaults.SettingsModifier) :
    ∀ (modifiers : alloc.vec.into_iter.IntoIter defaults.SettingsModifier)
      (settings : defaults.Settings), modifiers.val = l →
      SettingsInRange settings → (∀ m ∈ l, Defaults.Produced m) →
      ∃ s', sudoers.apply_settings_loop settings modifiers true = ok s' ∧
        Defaults.absSettings s' =
          applyModifiers (l.map Defaults.absModifier) (Defaults.absSettings settings) ∧
        SettingsInRange s' := by
  induction l with
  | nil =>
    intro modifiers settings h hs hm
    have hstep : sudoers.apply_settings_loop settings modifiers true = ok settings := by
      rw [sudoers.apply_settings_loop]
      simp [Defaults.next_nil modifiers h]
    refine ⟨settings, hstep, ?_, hs⟩
    simp [applyModifiers]
  | cons m l ih =>
    intro modifiers settings h hs hm
    obtain ⟨settings1, happly, habs⟩ := Defaults.apply_eq m settings
    obtain ⟨modifiers', hval', hnext⟩ := Defaults.next_cons modifiers m l h
    have hstep : sudoers.apply_settings_loop settings modifiers true =
        sudoers.apply_settings_loop settings1 modifiers' true := by
      rw [sudoers.apply_settings_loop]
      simp only [if_true]
      simp [hnext, happly]
    have hrange1 : SettingsInRange settings1 :=
      Defaults.settings_inRange_apply hs (hm m (by simp)) happly
    obtain ⟨s', hloop, habs', hrange'⟩ :=
      ih modifiers' settings1 hval' hrange1 (fun x hx => hm x (List.mem_cons_of_mem _ hx))
    refine ⟨s', ?_, ?_, hrange'⟩
    · rw [hstep, hloop]
    · rw [habs', habs]
      simp [applyModifiers, List.foldl_cons]

/-- `apply_settings` is the `true` run of the loop on the same vector. -/
theorem apply_settings_unfold (modifiers : alloc.vec.Vec defaults.SettingsModifier)
    (settings : defaults.Settings) :
    sudoers.apply_settings modifiers settings =
      sudoers.apply_settings_loop settings modifiers true := by
  unfold sudoers.apply_settings
  simp only [alloc.vec.IntoIteratorVec.into_iter]
  exact bind_ok modifiers _

/-- **`apply_settings` is `applyModifiers`** on the abstracted modifiers, and the ranges survive
when every modifier is `Produced`. -/
theorem apply_settings_eq (modifiers : alloc.vec.Vec defaults.SettingsModifier)
    (settings : defaults.Settings) (hs : SettingsInRange settings)
    (hm : ∀ m ∈ modifiers.val, Defaults.Produced m) :
    ∃ s', sudoers.apply_settings modifiers settings = ok s' ∧
      Defaults.absSettings s' = applyModifiers (modifiers.val.map Defaults.absModifier)
        (Defaults.absSettings settings) ∧
      SettingsInRange s' := by
  obtain ⟨s', hloop, habs, hrange⟩ :=
    apply_settings_loop_true_eq modifiers.val modifiers settings rfl hs hm
  exact ⟨s', by rw [apply_settings_unfold]; exact hloop, habs, hrange⟩

end SudoRsProofs.Parser.Scoping
