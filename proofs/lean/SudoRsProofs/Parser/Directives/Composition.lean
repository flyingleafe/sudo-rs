import SudoRsProofs.Parser.Directives.Reference

/-! A paired case split for the extracted `Result::branch` and the reference bind. -/

open Aeneas Aeneas.Std Result SudoersSpec

namespace SudoRsProofs.Parser

/-- Eliminate a refinement by the inner Rust `Result`. The outer Aeneas computation has
already returned; the two branches agree on whether a value or a diagnostic was produced. -/
theorem Refines.elimCases {T α : Type} {f : T → α} {x : Result (RParsed T × CS)}
    {out : Syntax.Parsed α × Syntax.Stream} (h : Refines f x out) {P : Prop}
    (hOk : ∀ a t, x = ok (.Ok a, t) → out = (.ok (f a), absStream t) → StreamOK t → P)
    (hErr : ∀ e e' t, x = ok (.Err e, t) → out = (.error e', absStream t) →
      StreamOK t → StatusRel e e' → P) : P := by
  obtain ⟨r, t, hx, hr, ht, ha⟩ := h
  rcases out with ⟨r', out⟩
  change absStream t = out at ha
  subst out
  rcases r with a | e <;> rcases r' with e' | a' <;> simp only [ResultRel] at hr
  · subst a'; exact hOk _ _ hx rfl ht
  · exact hErr _ _ _ hx rfl ht hr

/-- A `make` leaf does not move the cursor. -/
theorem refines_value {T α : Type} {f : T → α} (a : T) {s : CS} (hs : StreamOK s) :
    Refines f (ok (.Ok a, s)) (.ok (f a), absStream s) :=
  ⟨_, _, rfl, rfl, hs, rfl⟩

/-- The value type changes across a `?` failure, but the diagnostic and cursor do not. -/
theorem refines_diagnostic {T α : Type} {f : T → α} {e : RStatus}
    {e' : Syntax.Status} {s : CS} (h : StatusRel e e') (hs : StreamOK s) :
    Refines f (ok (.Err e, s)) (.error e', absStream s) :=
  ⟨_, _, rfl, h, hs, rfl⟩

end SudoRsProofs.Parser
