import SudoRsProofs.Parser.DefaultsParse.Common

/-! Dependency-aware success inversion for the generated `?` binds. A success retains the
reference call equation (needed for bounds on token values); errors propagate unchanged. -/

open Aeneas Aeneas.Std Result SudoersSpec

namespace SudoRsProofs.Parser.DefaultsParse

/-- Split a refining parser call into a shared success or a related error. -/
theorem refines_cases {T α : Type} {f : T → α} {x : Result (RParsed T × CS)}
    {out : Syntax.Parsed α × Syntax.Stream} (h : Refines f x out) :
    (∃ v t, x = ok (.Ok v, t) ∧ out = (.ok (f v), absStream t) ∧ StreamOK t) ∨
    (∃ e e' t, x = ok (.Err e, t) ∧ out = (.error e', absStream t) ∧ StreamOK t ∧
      StatusRel e e') := by
  obtain ⟨r, t, he, hr, ht, ha⟩ := h
  obtain ⟨r', st⟩ := out
  change absStream t = st at ha
  subst st
  cases r with
  | Ok v =>
    cases r' with
    | error _ => cases hr
    | ok v' =>
      have hv : f v = v' := hr
      subst v'
      exact .inl ⟨v, t, he, rfl, ht⟩
  | Err e =>
    cases r' with
    | error e' => exact .inr ⟨e, e', t, he, rfl, ht, hr⟩
    | ok _ => cases hr

/-- Reduce a paired `?` / `Parser.bind` call, discharging the related error immediately.
The named outputs are the value, extracted cursor, cursor invariant and reference equation. -/
syntax "call_refinement " term " with " ident ident ident ident : tactic
macro_rules
  | `(tactic| call_refinement $proof with $v $t $ht $hp) => `(tactic| (
      obtain ⟨$v, $t, hRust, $hp, $ht⟩ | ⟨_, _, _, hRust, $hp, $ht, hRel⟩ :=
        refines_cases $proof
      all_goals
        simp only [hRust, bind_ok, uncurry_apply_pair, branch_Ok, branch_Err,
          from_residual_Err, Syntax.Parser.run_bind, ($hp), id_eq]
      all_goals try exact ⟨_, _, rfl, hRel, $ht, rfl⟩))

end SudoRsProofs.Parser.DefaultsParse
