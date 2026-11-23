import SudoRsProofs.Defaults.Initial
import SudoersSpec.Analysis.Observations

/-! The extracted initializer and literal settings table agree on every operation relevant
to `check`, including after scoping. The three native hash sets are compared by membership.
No assumption on their iteration order or the initial hash seed is needed. -/

open Aeneas.Std Result sudo_rs

namespace SudoRsProofs.Defaults

theorem initialModel_equiv : SudoersSpec.Settings.Equiv initialModel SudoersSpec.Settings.Settings.default :=
  ⟨rfl, initialModel_sets.1, initialModel_sets.2.1, initialModel_sets.2.2⟩

theorem effective_authorization_of_initial {s : defaults.Settings}
    (init : defaults.Settings.Insts.CoreDefaultDefault.default = ok s)
    (O : SudoersSpec.Oracle U G) (aliases : SudoersSpec.AliasTable) (c : SudoersSpec.Analysis.Collected)
    (req : SudoersSpec.Request U G) (flags : Option SudoersSpec.Tag) :
    let effective := SudoersSpec.Analysis.settingsInForce O aliases c req
    SudoersSpec.Settings.observeAuthorization (SudoersSpec.authorization (effective (absSettings s)).toDefaults flags) =
      SudoersSpec.Settings.observeAuthorization (SudoersSpec.authorization
        (effective SudoersSpec.Settings.Settings.default).toDefaults flags) := by
  obtain ⟨s', e, v⟩ := default_eq
  rw [init] at e
  simp only [Result.ok.injEq] at e
  subst s'
  dsimp only
  rw [v]
  exact SudoersSpec.Settings.authorization_congr (initialModel_equiv.settingsInForce O aliases c req) flags

end SudoRsProofs.Defaults
