import SudoRsProofs.Parser.Ast
import SudoRsProofs.AbsMatch

/-! Shared parser refinement lemmas and the headroom needed by re-escaped quoted users. -/

open Aeneas Aeneas.Std Result SudoersSpec

namespace SudoRsProofs.Parser

/-- A cursor with room for a nested stream that quotes at most twice as many characters as
remain in the input. At a file start this needs `1 + 2 * src.val.length ≤ Usize.max`. The
`max 1` accounts for a newline resetting even a zero-valued initial column to one. -/
structure QuoteRoom (s : Syntax.Stream) : Prop where
  line_le : s.line + 2 * s.rest.length ≤ Usize.max
  col_le : max 1 s.col + 2 * s.rest.length ≤ Usize.max

theorem QuoteRoom.pop {s : Syntax.Stream} (h : QuoteRoom s) : QuoteRoom s.pop := by
  rcases s with ⟨_ | ⟨c, cs⟩, line, col⟩
  · exact h
  · obtain ⟨hl, hc⟩ := h
    simp only [List.length_cons] at hl hc
    by_cases hn : c = '\n'
    · subst c
      rw [Syntax.Stream.pop_newline]
      constructor <;> simp only [max_self] <;> omega
    · rw [Syntax.Stream.pop_other hn]
      exact ⟨by change line + 2 * cs.length ≤ Usize.max; omega,
        by change max 1 (col + 1) + 2 * cs.length ≤ Usize.max; omega⟩

theorem QuoteRoom.reaches {s s' : Syntax.Stream} (h : QuoteRoom s)
    (hr : s.Reaches s') : QuoteRoom s' := by
  obtain ⟨n, rfl⟩ := hr
  induction n generalizing s with
  | zero => simpa using h
  | succ n ih => rw [Syntax.Stream.advance_succ]; exact ih h.pop

theorem quoteRoom_stable : ForwardStable QuoteRoom := by
  intro s s' h hr
  exact h.reaches hr

theorem QuoteRoom.initial (src : Slice Char) (h : 1 + 2 * src.val.length ≤ Usize.max) :
    QuoteRoom (absStream ⟨src, 0#usize, 1#usize, 1#usize⟩) := by
  constructor <;> simpa using h

variable {T α : Type} {P : sudo_rs.sudoers.basic_parser.Parse T} {f : T → α}
  {p : Syntax.Parser α} {d : String}

/-- `Option<T>::parse` uses `maybe`, retaining the cursor at either kind of failure of `T`. -/
theorem option_parse_refines_at {s : CS} (hP : Refines f (P.parse s) (p.run (absStream s))) :
    Refines (Option.map f) ((sudo_rs.core.option.Option.Insts.Sudo_rsSudoersBasic_parserParse P).parse s)
      ((Syntax.parseOption p).run (absStream s)) := by
  obtain ⟨r, s', eq, hr, hs', ha⟩ := hP
  obtain ⟨m, hm, hmr⟩ := maybe_rel hr
  change Refines _ (sudo_rs.core.option.Option.Insts.Sudo_rsSudoersBasic_parserParse.parse P s) _
  unfold sudo_rs.core.option.Option.Insts.Sudo_rsSudoersBasic_parserParse.parse
  simp only [eq, bind_ok, uncurry_apply_pair, hm, refines_ok_iff]
  exact ⟨hmr, hs', ha⟩

theorem option_parse_refines (hP : ParseRefines P f p) :
    ParseRefines (sudo_rs.core.option.Option.Insts.Sudo_rsSudoersBasic_parserParse P) (Option.map f)
      (Syntax.parseOption p) :=
  ⟨fun s hs => option_parse_refines_at (hP.parse s hs)⟩

/-- `Vec<T>::DESCRIPTION` is `T::DESCRIPTION`. -/
theorem desc_vec {UF : sudo_rs.sudoers.ast_names.UserFriendly T} (hD : DescRel UF d) :
    DescRel (sudo_rs.alloc.vec.Vec.Insts.Sudo_rsSudoersAst_namesUserFriendly UF) d := by
  obtain ⟨s, hs, hv⟩ := hD
  exact ⟨s, by simp only [sudo_rs.alloc.vec.Vec.Insts.Sudo_rsSudoersAst_namesUserFriendly.DESCRIPTION,
    hs], hv⟩

/-- `Unquoted<T>::DESCRIPTION` is `T::DESCRIPTION`. -/
theorem desc_unquoted {UF : sudo_rs.sudoers.ast_names.UserFriendly T} (hD : DescRel UF d) :
    DescRel (sudo_rs.sudoers.tokens.Unquoted.Insts.Sudo_rsSudoersAst_namesUserFriendly UF) d := by
  obtain ⟨s, hs, hv⟩ := hD
  exact ⟨s, by simp only [sudo_rs.sudoers.tokens.Unquoted.Insts.Sudo_rsSudoersAst_namesUserFriendly.DESCRIPTION,
    hs], hv⟩

end SudoRsProofs.Parser
