import SudoRsProofs.Parser.Directives.Reference

/-! Cursor advance and checked column arithmetic for the saved `Defaults@` cursor. -/

open Aeneas Aeneas.Std Result SudoersSpec
open sudo_rs

namespace SudoRsProofs.Parser

private theorem pop_eq_self_of_peek_none {s : Syntax.Stream} (h : s.peek = none) : s.pop = s := by
  rcases s with ⟨_ | ⟨c, cs⟩, l, k⟩
  · rfl
  · cases h

private theorem advance_loop_eq (s : CS) (n i : Usize) (hs : StreamOK s) :
    ∃ t : CS,
      sudoers.char_stream.CharStream.advance_loop s.src s.pos s.line s.col n i =
        ok (t.src, t.pos, t.line, t.col) ∧ StreamOK t ∧
      absStream t = (absStream s).advance (n.val - i.val) := by
  rw [sudoers.char_stream.CharStream.advance_loop]
  split
  · rename_i hlt
    have hi : i.val < n.val := by scalar_tac
    have ham : i.val + (1#usize : Usize).val ≤ UScalar.max .Usize := by scalar_tac
    obtain ⟨j, hj, hjv⟩ := exists_eq_ok_of_spec
      (UScalar.add_spec (x := i) (y := 1#usize) ham)
    have hsucc : n.val - i.val = (n.val - j.val) + 1 := by simp at hjv; omega
    have hdec : n.val - j.val < n.val - i.val := by omega
    rw [hsucc, Syntax.Stream.advance_succ]
    have eta : (⟨s.src, s.pos, s.line, s.col⟩ : CS) = s := by cases s; rfl
    simp only [eta, peek_eq, bind_ok]
    cases hp : (absStream s).peek with
    | none =>
      obtain ⟨t, ht, hst, ha⟩ := advance_loop_eq s n j hs
      refine ⟨t, by simpa only [hp, bind_ok, uncurry_apply_pair, hj] using ht,
        hst, ?_⟩
      simpa only [pop_eq_self_of_peek_none hp] using ha
    | some c =>
      obtain ⟨s1, hb, hs1, ha1⟩ := bump_eq hs hp
      obtain ⟨t, ht, hst, ha⟩ := advance_loop_eq s1 n j hs1
      exact ⟨t, by simpa only [hp, hb, bind_ok, uncurry_apply_pair, hj] using ht,
        hst, ha.trans (congrArg (fun st => st.advance (n.val - j.val)) ha1)⟩
  · rename_i hge
    have hz : n.val - i.val = 0 := by
      have : ¬ i.val < n.val := by simpa only [← UScalar.lt_equiv] using hge
      omega
    exact ⟨s, rfl, hs, by rw [hz, Syntax.Stream.advance_zero]⟩
termination_by n.val - i.val

/-- `CharStream::advance` uses the same physical cursor bookkeeping as the reference;
advancing past end-of-input performs no further movement. -/
theorem advance_eq {s : CS} (hs : StreamOK s) (n : Usize) :
    ∃ t, sudoers.char_stream.CharStream.advance s n = ok t ∧ StreamOK t ∧
      absStream t = (absStream s).advance n.val := by
  obtain ⟨t, he, ht, ha⟩ := advance_loop_eq s n 0#usize hs
  refine ⟨t, ?_, ht, by simpa using ha⟩
  simp only [sudoers.char_stream.CharStream.advance, he, bind_ok, uncurry_apply_pair]

/-- Rust's checked `col - beginCol` in `defaults_scope` agrees with `Nat` subtraction.
The forward-reach premise is used only on the same-line branch, before any rewind. -/
theorem scope_adjacent_eq {beginState current : CS}
    (h : (absStream beginState).Reaches (absStream current)) :
    (if current.line = beginState.line then do
      let diff ← current.col - beginState.col
      ok (decide (diff = sudoers.ast.DEFAULTS_LEN))
    else ok false) =
      ok ((absStream current).line == (absStream beginState).line &&
        (absStream current).col - (absStream beginState).col == 8) := by
  by_cases he : current.line = beginState.line
  · have hl : (absStream current).line = (absStream beginState).line := by simp [he]
    have hc : beginState.col.val ≤ current.col.val := reaches_col_le_of_line_eq h hl
    obtain ⟨d, hd, hdv, _⟩ := exists_eq_ok_of_spec
      (UScalar.sub_spec (x := current.col) (y := beginState.col) (by scalar_tac))
    have de : decide (d = sudoers.ast.DEFAULTS_LEN) = (d.val == 8) := by
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, beq_iff_eq, sudoers.ast.DEFAULTS_LEN]
      exact ⟨fun h => by rw [h]; rfl, fun h => UScalar.eq_of_val_eq (by simpa using h)⟩
    simp only [he, ite_true, hd, bind_ok, hl, beq_self_eq_true, Bool.true_and, de, hdv,
      absStream_col]
  · have hl : current.line.val ≠ beginState.line.val := fun hv => he (UScalar.eq_of_val_eq hv)
    simp [he, hl]

end SudoRsProofs.Parser
