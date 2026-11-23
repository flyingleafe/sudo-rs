import SudoersSpec.Analysis.Collect
import SudoersSpec.Grammar.SudoFile

/-! A clean analysis cannot have discarded a parse diagnostic. This lets the clean-file
corollary use the diagnostics the caller actually received instead of silently assuming a
separate clean parse as a precondition. -/

namespace SudoersSpec.Analysis

open Syntax (Parsed Sudo)

private theorem collectItem_without_diagnostics {acc out : Collected} {i : Parsed Sudo}
    (h : collectItem acc i = some out) (clean : out.diagnostics = []) :
    acc.diagnostics = [] ∧ ∃ a, i = .ok a := by
  cases i with
  | error e => cases e with
    | reject => cases h
    | fatal sp kind => simp only [collectItem, Option.some.injEq] at h; subst out; simp at clean
  | ok a =>
    refine ⟨?_, ⟨a, rfl⟩⟩
    cases a with
    | «include» | includeDir => cases h
    | lineComment => cases h; exact clean
    | spec rule =>
      simp only [collectItem, Option.some.injEq] at h
      subst out
      exact (List.append_eq_nil_iff.mp clean).1
    | decl d => cases d with
      | defaults mods scope => cases scope <;> cases h <;> exact clean
      | _ => cases h; exact clean

/-- Fatal items append diagnostics. A clean successful collection thus has only successful
items, including any parsed comments, in exactly the original order. -/
theorem collectFrom_without_diagnostics {items : List (Parsed Sudo)} {acc out : Collected}
    (h : collectFrom acc items = some out) (clean : out.diagnostics = []) :
    acc.diagnostics = [] ∧ ∃ ast : List Sudo, items = ast.map Except.ok := by
  induction items generalizing acc with
  | nil => cases h; exact ⟨clean, [], rfl⟩
  | cons i is ih =>
    cases step : collectItem acc i with
    | none => simp [collectFrom, List.foldlM_cons, step] at h
    | some next =>
      have rest : collectFrom next is = some out := by simpa [collectFrom, List.foldlM_cons, step] using h
      obtain ⟨hs, ast, hast⟩ := ih rest
      obtain ⟨hacc, a, ha⟩ := collectItem_without_diagnostics step hs
      exact ⟨hacc, a :: ast, by simp [ha, hast]⟩

/-- If the local reports followed by the sanitizer reports are empty, the original file
has a grammar derivation for its accepted ASTs and the driver exhausted its characters.
No assumption of parser cleanliness, or of grammar unambiguity, appears in this theorem. -/
theorem cleanGrammar_of_collected {O : Syntax.Oracles} {src : List Char}
    {items : List (Parsed Sudo)} {c : Collected} {sanitizerReports : List String}
    (parse : Syntax.parseSudoers O src = .ok items) (collection : collect items = some c)
    (clean : c.diagnostics.map Prod.snd ++ sanitizerReports = []) :
    ∃ ast : List Sudo, items = ast.map Except.ok ∧ Syntax.Recovery.CleanFile (Grammar.SudoItemG O)
      (Syntax.Stream.new src) ast ((Syntax.Stream.new src).advance src.length) := by
  have localEmpty := List.map_eq_nil_iff.mp (List.append_eq_nil_iff.mp clean).1
  obtain ⟨_, ast, hi⟩ := collectFrom_without_diagnostics collection localEmpty
  exact ⟨ast, hi, Grammar.parseSudoersWith_clean_sound _ _ _ _ (hi ▸ parse)⟩

end SudoersSpec.Analysis
