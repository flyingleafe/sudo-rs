import SudoRsProofs.Defaults.Initial
import SudoRsProofs.Defaults.Integer
import SudoRsProofs.Defaults.Lookup
import SudoRsProofs.Defaults.Text

/-!
# The Defaults producers preserve the authorization ranges

A `Produced` modifier is an actual successful return from one of the five extracted
producers. This property does not require well-formed text or the timeout length bound:
regardless of whether a call can return, only the two integer constructors of interest could
violate the ranges. Their payloads are bounded by the range check and the `u32` parse.
-/

open Aeneas Aeneas.Std Result sudo_rs

namespace SudoRsProofs.Defaults

set_option allowUnsafeReducibility true in
attribute [local reducible] Str

/-- A modifier returned by the extracted settings constructors. -/
inductive Produced : sudo_rs.defaults.SettingsModifier → Prop where
  | flag {nm m} : defaults.set nm = ok (some (.Flag m)) → Produced m
  | negate {nm m} : defaults.negate nm = ok (some m) → Produced m
  | integer {id t m} : defaults.check_integer id t = ok (some m) → Produced m
  | text {id t m} : defaults.check_text id t = ok (some m) → Produced m
  | list {id mode items m} : defaults.build_list id mode items = ok m → Produced m

def ModifierInRange : defaults.SettingsModifier → Prop
  | .passwd_tries v => v.val ≤ U16.max
  | .umask v => v.val ≤ U32.max
  | _ => True

private theorem before_bind_ok {α β : Type} {a : Result α} {f : α → Result β} {r : β}
    (h : Aeneas.Std.bind a f = ok r) : ∃ x, a = ok x ∧ f x = ok r := by
  cases a with
  | ret x => exact ⟨x, rfl, by simpa using h⟩
  | vis _ _ => simp at h
  | div => simp at h

private theorem integer_in_range_le (t : Str) (radix : U32) (lo hi v : U64)
    (h : defaults.integer_in_range t radix lo hi = ok (some v)) : v.val ≤ hi.val := by
  unfold defaults.integer_in_range at h
  obtain ⟨ret, _, h⟩ := before_bind_ok h
  cases ret with
  | Err _ => simp at h
  | Ok w =>
    simp only at h
    split at h
    · split at h
      · have hw : w = v := by simpa only [Result.ok.injEq, Option.some.injEq] using h
        subst w
        exact (UScalar.le_equiv _ _).mp (by assumption)
      · simp at h
    · simp at h

private theorem octal_mode_le (t : Str) (v : U64)
    (h : defaults.octal_mode t = ok (some v)) : v.val ≤ U32.max := by
  unfold defaults.octal_mode at h
  simp only [core.str.Str.as_bytes, bind_ok, core.slice.Slice.is_empty] at h
  split at h
  · simp at h
  · obtain ⟨_, _, h⟩ := before_bind_ok h
    split at h
    · simp at h
    · obtain ⟨⟨_, digits⟩, _, h⟩ := before_bind_ok h
      obtain ⟨ret, _, h⟩ := before_bind_ok h
      cases ret with
      | Err _ => simp at h
      | Ok x =>
        simp only [lift, bind_ok, Result.ok.injEq, Option.some.injEq] at h
        rw [← h, core.convert.num.FromU64U32.from_val_eq]
        scalar_tac

theorem produced_inRange {m : defaults.SettingsModifier} (h : Produced m) : ModifierInRange m := by
  cases h with
  | flag h =>
    unfold defaults.set at h
    obtain ⟨o, _, h⟩ := before_bind_ok h
    cases o with
    | none => simp at h
    | some k => cases k <;> simp at h <;> subst m <;> trivial
  | negate h =>
    unfold defaults.negate at h
    obtain ⟨o, _, h⟩ := before_bind_ok h
    cases o with
    | none => simp at h
    | some k => cases k <;> simp at h <;> subst m <;> simp [ModifierInRange, U32.max_eq]
  | integer h =>
    rename_i id t
    cases id <;> simp only [defaults.check_integer] at h
    all_goals
      obtain ⟨o, ho, h⟩ := before_bind_ok h
      cases o with
      | none => simp at h
      | some v =>
        simp only [Result.ok.injEq, Option.some.injEq] at h
        subst m
        first
        | exact octal_mode_le t v ho
        | have hv := integer_in_range_le t 10#u32 0#u64 1000#u64 v ho
          simpa only [ModifierInRange, U16.max_eq] using (show v.val ≤ 65535 by scalar_tac)
        | trivial
  | text h =>
    rename_i id t
    cases id <;> simp only [defaults.check_text, Str.Insts.CoreCmpPartialEqStr.eq, bind_ok,
      core.convert.IntoFrom.into, BoxStr.Insts.CoreConvertFromShared0Str.from] at h
    all_goals try split_ifs at h
    all_goals (simp at h; subst m; trivial)
  | list h =>
    rename_i id mode items
    cases id <;> simp [defaults.build_list] at h <;> subst m <;> trivial

theorem settings_inRange_apply {s s' : defaults.Settings} {m : defaults.SettingsModifier}
    (hs : SettingsInRange s) (hm : Produced m)
    (h : defaults.SettingsModifier.apply m s = ok s') : SettingsInRange s' := by
  obtain ⟨out, ho, ha⟩ := apply_eq m s
  have e : out = s' := by simpa only [Result.ok.injEq] using ho.symm.trans h
  subst out
  have hmod := produced_inRange hm
  have hp := congrArg SudoersSpec.Settings.Settings.passwd_tries ha
  have hu := congrArg SudoersSpec.Settings.Settings.umask ha
  cases m <;> simp only [absSettings, absModifier, SudoersSpec.Settings.SettingsModifier.apply,
    ModifierInRange] at hp hu hmod <;>
    exact ⟨hp.symm ▸ (by first | exact hs.passwd_tries | exact hmod),
      hu.symm ▸ (by first | exact hs.umask | exact hmod)⟩

/-- The settings reached from a successful `Settings::default()` by applying produced
modifiers in sequence. -/
inductive Reachable : defaults.Settings → Prop where
  | default {s} : defaults.Settings.Insts.CoreDefaultDefault.default = ok s → Reachable s
  | apply {s s' m} : Reachable s → Produced m →
      defaults.SettingsModifier.apply m s = ok s' → Reachable s'

theorem reachable_inRange {s : defaults.Settings} (h : Reachable s) : SettingsInRange s := by
  induction h with
  | default h => exact default_inRange h
  | apply _ hm hstep ih => exact settings_inRange_apply ih hm hstep

/-- `authorization_eq` without a range premise, for settings built by the Defaults DSL. -/
theorem authorization_reachable_eq (j : sudoers.Judgement) (h : Reachable j.settings) :
    ∃ a, sudoers.policy.Judgement.authorization j = ok a ∧
      absAuthorization a =
        SudoersSpec.authorization (absSettings j.settings).toDefaults (j.flags.map absTag) := by
  simpa only [absDefaults_eq] using authorization_eq j (reachable_inRange h)

end SudoRsProofs.Defaults
