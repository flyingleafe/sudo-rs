import SudoRsProofs.Defaults.Apply

/-!
# `set` and `negate` refine the settings model

The name table (`setting_at`) and its lookup loop (`setting_named`) against `settingAt` and
`settingNamed`; then `set` and `negate`.

Hypothesis (the string model): the `&str` argument `nm` holds the UTF-8 bytes of the spec
text `n` (`nm.val = stringBytes n`), as every `&str` made from a Rust `String` does.
-/

open Aeneas Aeneas.Std Result
open sudo_rs
open SudoersSpec.Settings (Setting)

namespace SudoRsProofs.Defaults

/-- The table entry at a position: its name's bytes and the setting. -/
theorem setting_at_spec (k : Usize) :
    ∃ r, defaults.setting_at k = ok r ∧
      r.map (fun p => (p.1.val, p.2)) =
        (SudoersSpec.Settings.settingAt k.val).map
          (fun p => (sudo_rs.stringBytes p.1, concSetting p.2)) := by
  unfold defaults.setting_at
  generalize k.val = i
  iterate 35
    (rcases i with _ | i
     · exact ⟨_, rfl, by simp [SudoersSpec.Settings.settingAt, Setting.all, Setting.name,
         toStr_val, concSetting]⟩)
  refine ⟨none, ?_, ?_⟩
  · rfl
  · simp [SudoersSpec.Settings.settingAt, Setting.all]

theorem usize_succ (k : Usize) (hk : k.val ≤ 35) :
    ∃ k', k + 1#usize = ok k' ∧ k'.val = k.val + 1 := by
  have h := Usize.add_spec (x := k) (y := 1#usize) (by scalar_tac)
  obtain ⟨k', hk', hv⟩ := exists_eq_ok_of_spec h
  exact ⟨k', hk', by simpa using hv⟩

theorem loop_done (nm : Str) (found : Option defaults.Setting) (k : Usize) :
    defaults.setting_named_loop nm found k false = ok found := by
  unfold defaults.setting_named_loop
  rfl

theorem setting_named_loop_eq (nm : Str) (n : String) (h : nm.val = sudo_rs.stringBytes n) :
    ∀ (d : Nat) (k : Usize), Setting.all.length - k.val = d → k.val ≤ Setting.all.length →
      defaults.setting_named_loop nm none k true =
        ok (((Setting.all.drop k.val).find? (·.name == n)).map concSetting) := by
  intro d
  induction d with
  | zero =>
    intro k hd hk
    have hk35 : k.val = Setting.all.length := by omega
    obtain ⟨r, hr, hrel⟩ := setting_at_spec k
    have hnone : SudoersSpec.Settings.settingAt k.val = none := by
      simp [SudoersSpec.Settings.settingAt, hk35]
    rw [hnone] at hrel
    have : r = none := by cases r <;> simp_all
    subst this
    unfold defaults.setting_named_loop
    simp only [hr, bind_ok, ↓reduceIte, loop_done, hk35, List.drop_length,
      List.find?_nil, Option.map_none]
  | succ d ih =>
    intro k hd hk
    have hlt : k.val < Setting.all.length := by omega
    obtain ⟨r, hr, hrel⟩ := setting_at_spec k
    obtain ⟨k', hk', hk'v⟩ := usize_succ k (by simp [Setting.all] at hk; omega)
    have hget : SudoersSpec.Settings.settingAt k.val =
        some ((Setting.all[k.val]'hlt).name, Setting.all[k.val]'hlt) := by
      simp [SudoersSpec.Settings.settingAt, List.getElem?_eq_getElem hlt]
    rw [hget] at hrel
    rcases r with _ | ⟨key, setting⟩
    · simp at hrel
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hrel
    obtain ⟨hkey, rfl⟩ := hrel
    have hdrop : Setting.all.drop k.val =
        (Setting.all[k.val]'hlt) :: Setting.all.drop (k.val + 1) :=
      List.drop_eq_getElem_cons hlt
    have heq : decide (key.val = nm.val) = ((Setting.all[k.val]'hlt).name == n) := by
      rw [hkey, h]
      by_cases e : (Setting.all[k.val]'hlt).name = n
      · simp [e]
      · have : sudo_rs.stringBytes (Setting.all[k.val]'hlt).name ≠ sudo_rs.stringBytes n :=
          fun h' => e (stringBytes_inj.mp h')
        simp [this, e]
    unfold defaults.setting_named_loop
    simp only [hr, bind_ok, ↓reduceIte, Str.Insts.CoreCmpPartialEqStr.eq, hk', uncurry]
    rw [hdrop, List.find?_cons]
    by_cases e : ((Setting.all[k.val]'hlt).name == n) = true
    · have kv : key.val = nm.val := by rw [← heq] at e; simpa using e
      have : decide (key = nm) = true := by simp [Slice.ext key nm kv]
      simp only [this, ↓reduceIte, bind_ok, uncurry, loop_done, e, Option.map_some]
    · have kv : ¬ key.val = nm.val := by rw [← heq] at e; simpa using e
      have : decide (key = nm) = false := by
        simp only [decide_eq_false_iff_not]; intro c; exact kv (c ▸ rfl)
      simp only [this, Bool.false_eq_true, ↓reduceIte, bind_ok, uncurry]
      rw [ih k' (by omega) (by omega), hk'v]
      simp [e]

/-- **`setting_named` is `settingNamed`.** -/
theorem setting_named_eq (nm : Str) (n : String) (h : nm.val = sudo_rs.stringBytes n) :
    defaults.setting_named nm = ok ((SudoersSpec.Settings.settingNamed n).map concSetting) := by
  unfold defaults.setting_named
  rw [setting_named_loop_eq nm n h _ 0#usize rfl (by simp)]
  rfl

/-- **`set` refines `set`.** -/
theorem set_eq (nm : Str) (n : String) (h : nm.val = sudo_rs.stringBytes n) :
    ∃ r, defaults.set nm = ok r ∧ r.map absKind = SudoersSpec.Settings.set n := by
  unfold defaults.set SudoersSpec.Settings.set
  rw [setting_named_eq nm n h, bind_ok]
  rcases SudoersSpec.Settings.settingNamed n with _ | s
  · exact ⟨none, rfl, rfl⟩
  · cases s <;> exact ⟨_, rfl, rfl⟩

/-- **`negate` refines `negate`.** -/
theorem negate_eq (nm : Str) (n : String) (h : nm.val = sudo_rs.stringBytes n) :
    ∃ r, defaults.negate nm = ok r ∧ r.map absModifier = SudoersSpec.Settings.negate n := by
  unfold defaults.negate SudoersSpec.Settings.negate
  rw [setting_named_eq nm n h, bind_ok]
  rcases SudoersSpec.Settings.settingNamed n with _ | s
  · exact ⟨none, rfl, rfl⟩
  · cases s <;> exact ⟨_, rfl, rfl⟩

end SudoRsProofs.Defaults
