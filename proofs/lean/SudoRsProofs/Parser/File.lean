import SudoRsProofs.Parser.Lines
import SudoRsProofs.Parser.PermissionLines.Common
import SudoersSpec.Syntax.PanicFree

/-!
# File result from item refinement

The reference file wrapper checks for a marker representing a failed Rust `unwrap`. A
refinement proof must establish the outer Aeneas `ok`, even when the Rust parser rejects the
syntax. An `ok` containing an ordinary diagnostic must not stand in for an Aeneas panic.
-/

open Aeneas Aeneas.Std Result
open SudoersSpec

namespace SudoRsProofs.Parser

/-- The panic marker is not an abstraction of any ordinary Rust parser diagnostic. -/
theorem KindRel.not_unwrap {k : RKind} : ¬KindRel k .unwrapNone := by
  intro h; cases h

private theorem related_not_unwrap {T α : Type} {f : T → α} {r : RParsed T} {sp : SudoersSpec.Span} :
    ¬ ResultRel f r (.error (.fatal sp .unwrapNone)) := by
  cases r with
  | Ok => exact id
  | Err e =>
    intro rel
    change StatusRel e (.fatal sp .unwrapNone) at rel
    cases rel with | fatal _ _ _ h => exact KindRel.not_unwrap h

private theorem no_marker_in_results {T α : Type} {f : T → α} {raw : List (RParsed T)}
    {items : List (Syntax.Parsed α)} (h : List.Forall₂ (ResultRel f) raw items) :
    items.any Syntax.markerItem = false := by
  induction h with
  | nil => rfl
  | @cons r item _ _ rel _ ih =>
    rw [List.any_cons, ih, Bool.or_false]
    rcases item with (⟨sp, k⟩ | _) | a
    · cases k <;> first | rfl | exact False.elim (related_not_unwrap rel)
    · rfl
    · rfl

/-- Composition rule, not a premise-free theorem about `Parse Sudo`: the production proof must
supply `item`. Once it does, the top-level wrapper returns the related items (not the panic
marker), the recovered list contains no `Reject`, and the Rust computation actually returns.
The single input bound pays for both nested quoted streams and the result vector. -/
theorem parseSudoersWith_of_refinement {T : Type} {P : sudo_rs.sudoers.basic_parser.Parse T}
    {UF : sudo_rs.sudoers.ast_names.UserFriendly T} {f : T → Syntax.Sudo}
    {D : Syntax.Descriptions} {O : Syntax.Oracles}
    (item : ParseRefinesOn QuoteRoom P f (Syntax.sudo O D)) (desc : DescRel UF D.sudo)
    (src : Slice Char) (room : 1 + 2 * src.val.length ≤ Usize.max) :
    ∃ raw stop items,
      sudo_rs.sudoers.basic_parser.parse_lines P UF ⟨src, 0#usize, 1#usize, 1#usize⟩ = ok (raw, stop) ∧
      Syntax.parseSudoersWith D O src.val = .ok items ∧ List.Forall₂ (ResultRel f) raw.val items ∧
      StreamOK stop ∧ ∀ r ∈ raw.val, r ≠ .Err .Reject := by
  obtain ⟨raw, stop, items, run, reference, rel, wf⟩ :=
    parse_lines_refines_on quoteRoom_stable item desc (StreamOK.initial src (by omega))
      (QuoteRoom.initial src room) (by simp; omega)
  change (Syntax.parseLines D.sudo (Syntax.sudo O D)).run (Syntax.Stream.new src.val) = _ at reference
  have file : Syntax.parseSudoersWith D O src.val = .ok items := by
    simp [Syntax.parseSudoersWith, reference]
    intro i hi
    have hnot := List.any_eq_false.mp (no_marker_in_results rel) i hi
    rcases i with (⟨sp, k⟩ | _) | a
    · cases k <;> first | rfl | exact False.elim (hnot rfl)
    · rfl
    · rfl
  refine ⟨raw, stop, items, run, file, rel, wf, ?_⟩
  intro r hr er
  obtain ⟨i, hi, related⟩ := forall₂_mem_left rel hr
  subst r
  have bad : i = .error .reject := by
    cases i with
    | ok => cases related
    | error e => change StatusRel .Reject e at related; cases related; rfl
  exact Syntax.parseSudoersWith_ne_reject D O src.val items file i hi bad

end SudoRsProofs.Parser
