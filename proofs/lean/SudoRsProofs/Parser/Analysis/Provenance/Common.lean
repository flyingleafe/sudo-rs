import SudoRsProofs.Defaults.Range
import SudoRsProofs.SanitizeAliases
import SudoRsProofs.Parser.Combinators

/-! Postconditions for successful returns of the raw parser, independent of the reference. -/

open Aeneas Aeneas.Std Result
open sudo_rs.sudoers

namespace SudoRsProofs.Parser.Analysis

/-- The inner Rust result only constrains actual AST nodes, not parser diagnostics. -/
def OkOn (good : T → Prop) : RParsed T → Prop
  | .Ok x => good x
  | .Err _ => True

/-- A vector whose entries all satisfy the postcondition. -/
def AllOn (good : T → Prop) (v : alloc.vec.Vec T) : Prop := ∀ x ∈ v.val, good x

theorem push_all_on {good : T → Prop} {v w : alloc.vec.Vec T} {x : T}
    (hv : AllOn good v) (hx : good x) (hp : alloc.vec.Vec.push v x = ok w) : AllOn good w := by
  unfold alloc.vec.Vec.push at hp
  dsimp only at hp
  split at hp
  · obtain rfl := Result.ok_injective hp
    intro y hy
    rcases (show y ∈ v.val ∨ y = x by simpa using hy) with hy | rfl
    · exact hv _ hy
    · exact hx
  · simp at hp

theorem try_nonterminal_on_return {P : basic_parser.Parse T} {good : T → Prop}
    (hP : ∀ s, OnReturn (P.parse s) (fun x => OkOn good x.1)) (s : CS) :
    OnReturn (basic_parser.try_nonterminal P s) (fun x => OkOn good x.1) := by
  unfold basic_parser.try_nonterminal
  apply OnReturn.bind
  rintro ⟨r, s'⟩ h
  have hr := hP _ _ h
  cases r with
  | Ok x =>
    simp only [uncurry_apply_pair, branch_Ok, bind_ok]
    apply OnReturn.bind
    rintro ⟨ws, t⟩ _
    simp only [uncurry_apply_pair]
    cases ws <;> simp only [branch_Ok, branch_Err, from_residual_Err, make_eq, bind_ok]
    · exact OnReturn.pure hr
    · exact OnReturn.pure True.intro
  | Err e =>
    simp only [uncurry_apply_pair, branch_Err, from_residual_Err, bind_ok]
    exact OnReturn.pure True.intro

theorem expect_nonterminal_on_return {P : basic_parser.Parse T}
    {UF : ast_names.UserFriendly T} {good : T → Prop}
    (hP : ∀ s, OnReturn (P.parse s) (fun x => OkOn good x.1)) (s : CS) :
    OnReturn (basic_parser.expect_nonterminal P UF s) (fun x => OkOn good x.1) := by
  unfold basic_parser.expect_nonterminal
  apply OnReturn.bind
  intro pos _
  apply OnReturn.bind
  rintro ⟨r, s'⟩ h
  have hr := try_nonterminal_on_return hP s _ h
  rcases r with _ | (_ | _)
  · exact OnReturn.pure hr
  · exact OnReturn.pure True.intro
  · apply OnReturn.bind
    intro d _
    simp only [fatal_from_eq, bind_ok]
    exact OnReturn.pure True.intro

theorem on_return_bind_pair {r : Result (α × β)} {k : α × β → Result γ} {good : γ → Prop}
    (h : ∀ a b, r = ok (a, b) → OnReturn (k (a, b)) good) :
    OnReturn (r >>= k) good :=
  OnReturn.bind fun (a, b) eq => h a b eq

/-- Invert one extracted monadic bind, preserving the equation for that successful call. -/
macro "provenance_bind " x:rcasesPat h:ident : tactic =>
  `(tactic| (apply OnReturn.bind; rintro $x:rcasesPat $h))

end SudoRsProofs.Parser.Analysis
