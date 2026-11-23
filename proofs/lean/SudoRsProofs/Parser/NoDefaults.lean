import SudoRsProofs.Parser.EndToEnd

/-! The P4 specialization makes its hypothesis on accepted source items, not on the two
analyzer outputs whose behavior it is supposed to verify. A diagnostic is not a Defaults item. -/

namespace SudoRsProofs.Parser

open Aeneas.Std
open SudoersSpec SudoersSpec.Analysis Syntax

private theorem localStep {acc next : Collected} {i : Parsed Sudo}
    (noDef : ∀ ms sc, i ≠ .ok (.decl (.defaults ms sc))) (step : collectItem acc i = some next) :
    next.nonCommand = acc.nonCommand ∧ next.command = acc.command := by
  cases i with
  | error e => cases e <;> cases step; exact ⟨rfl, rfl⟩
  | ok line => cases line with
    | decl d => cases d with
      | defaults ms sc => exact (noDef ms sc rfl).elim
      | _ => cases step; exact ⟨rfl, rfl⟩
    | «include» _ _ | includeDir _ _ => cases step
    | spec _ | lineComment => cases step; exact ⟨rfl, rfl⟩

private theorem localFold {acc out : Collected} {items : List (Parsed Sudo)}
    (absent : ∀ ms sc, .ok (.decl (.defaults ms sc)) ∉ items) (ran : collectFrom acc items = some out) :
    out.nonCommand = acc.nonCommand ∧ out.command = acc.command := by
  induction items generalizing acc with
  | nil => cases ran; exact ⟨rfl, rfl⟩
  | cons i rest ih =>
    cases hs : collectItem acc i with
    | none => simp [collectFrom, List.foldlM_cons, hs] at ran
    | some next =>
      have tail : collectFrom next rest = some out := by
        simpa [collectFrom, List.foldlM_cons, hs] using ran
      have a := localStep (fun ms sc he => absent ms sc (List.mem_cons.mpr (.inl he.symm))) hs
      have b := ih (fun ms sc hm => absent ms sc (List.mem_cons_of_mem i hm)) tail
      exact ⟨b.1.trans a.1, b.2.trans a.2⟩

/-- For texts with no accepted Defaults declaration, `check` uses the literal initial settings.
The associated decision, denial and terms are those of the same `text_to_authorization` run. -/
theorem TextAgreement.no_defaults {U G UG : Type} {A : GlobAbs} {E : Oracles} {O : Oracle U G}
    {ui : sudo_rs.system.interface.UnixUser U UG} {eqi : core.cmp.PartialEq U U}
    {gi : sudo_rs.system.interface.UnixGroup G} {path source src invoker host req} {x : FileRun}
    (h : TextAgreement A E O ui eqi gi path source src invoker host req x)
    (absent : ∀ ms sc, Except.ok (.decl (.defaults ms sc)) ∉ x.items) :
    Settings.Equiv (Defaults.absSettings x.judgement.settings) Settings.Settings.default := by
  obtain ⟨hn, hc⟩ := localFold absent h.collected
  simpa [settingsInForce, nonCommandModifiers, commandModifiers, applyModifiers, hn, hc] using h.effective

end SudoRsProofs.Parser
