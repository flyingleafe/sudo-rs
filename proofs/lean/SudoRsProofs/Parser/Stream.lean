import SudoRsProofs.Parser.Abs

/-!
# `char_stream.rs`: the cursor operations refine `SudoersSpec.Syntax.Stream`

Each lemma is total correctness on a representable cursor (`StreamOK`): the extracted function
returns `ok`, the output cursor is representable and abstracts to the reference result.
`bump` is the only place where machine arithmetic happens (`pos + 1`, `line + 1`, `col + 1`);
`StreamOK` is exactly what keeps it from overflowing.
-/

open Aeneas Aeneas.Std Result
open SudoersSpec.Syntax (Stream)

namespace SudoRsProofs.Parser

/-- A cursor from the fields of a tuple, the shape in which extracted loops return it. -/
abbrev mkCS (src : Slice Char) (pos line col : Usize) : CS := ⟨src, pos, line, col⟩

theorem pos_lt_of_peek {s : CS} {c : Char}
    (hc : (absStream s).peek = some c) :
    s.pos.val < s.src.val.length ∧ s.src.val[s.pos.val]? = some c := by
  simp only [Stream.peek, absStream_rest, List.head?_drop] at hc
  exact ⟨(List.getElem?_eq_some_iff.mp hc).1, hc⟩

theorem absStream_rest_cons {s : CS} {c : Char} (hc : (absStream s).peek = some c) :
    (absStream s).rest = c :: s.src.val.drop (s.pos.val + 1) := by
  simp only [Stream.peek, absStream_rest, List.head?_drop] at hc ⊢
  rw [List.drop_eq_getElem_cons (List.getElem?_eq_some_iff.mp hc).1]
  rw [List.getElem?_eq_some_iff] at hc
  obtain ⟨_, rfl⟩ := hc
  rfl

/-! ## `peek`, `get_pos` -/

theorem peek_eq (s : CS) :
    sudo_rs.sudoers.char_stream.CharStream.peek s = ok (absStream s).peek := by
  unfold sudo_rs.sudoers.char_stream.CharStream.peek
  dsimp only
  split
  · rename_i hlt
    have hi : s.pos.val < s.src.val.length := by scalar_tac
    obtain ⟨c, hc, hcv⟩ := exists_eq_ok_of_spec (Slice.index_usize_spec s.src s.pos hi)
    simp only [hc, bind_ok, Stream.peek, absStream_rest, List.head?_drop, ok.injEq]
    rw [List.getElem?_eq_getElem hi, hcv]
  · rename_i hge
    have : s.src.val.length ≤ s.pos.val := by scalar_tac
    simp [Stream.peek, List.drop_eq_nil_of_le this]

theorem get_pos_eq (s : CS) :
    sudo_rs.sudoers.char_stream.CharStream.get_pos s = ok (s.line, s.col) := rfl

/-! ## `bump` -/

/-- `bump(c)` after `peek` returned `c` is the reference `pop`. -/
theorem bump_eq {s : CS} (h : StreamOK s) {c : Char} (hc : (absStream s).peek = some c) :
    ∃ s', sudo_rs.sudoers.char_stream.CharStream.bump s c = ok s' ∧ StreamOK s' ∧
      absStream s' = (absStream s).pop := by
  obtain ⟨hlt, _⟩ := pos_lt_of_peek hc
  have hrest := absStream_rest_cons hc
  have hlen : s.src.val.length ≤ Usize.max := s.src.property
  have hpop : (absStream s).pop =
      ⟨s.src.val.drop (s.pos.val + 1), (SudoersSpec.Syntax.stepPos c (s.line.val, s.col.val)).1,
        (SudoersSpec.Syntax.stepPos c (s.line.val, s.col.val)).2⟩ := by
    have : absStream s = ⟨c :: s.src.val.drop (s.pos.val + 1), s.line.val, s.col.val⟩ := by
      rw [← hrest]; rfl
    rw [this]; rfl
  obtain ⟨i, hi, hiv⟩ := exists_eq_ok_of_spec
    (UScalar.add_spec (x := s.pos) (y := 1#usize) (by have := h.pos_le; scalar_tac))
  unfold sudo_rs.sudoers.char_stream.CharStream.bump
  simp only [hi, bind_ok]
  split
  · rename_i hn
    obtain ⟨l, hl, hlv⟩ := exists_eq_ok_of_spec
      (UScalar.add_spec (x := s.line) (y := 1#usize) (by have := h.line_le; scalar_tac))
    refine ⟨_, by rw [hl, bind_ok], ?_, ?_⟩
    · constructor <;> simp only [hiv, hlv] <;> simp <;> have := h.line_le <;> omega
    · rw [hpop]; simp [absStream, hiv, hlv, SudoersSpec.Syntax.stepPos, hn]
  · rename_i hn
    obtain ⟨k, hk, hkv⟩ := exists_eq_ok_of_spec
      (UScalar.add_spec (x := s.col) (y := 1#usize) (by have := h.col_le; scalar_tac))
    refine ⟨_, by rw [hk, bind_ok], ?_, ?_⟩
    · constructor <;> dsimp only <;> have := h.line_le <;> have := h.col_le <;> scalar_tac
    · rw [hpop]; simp [absStream, hiv, hkv, SudoersSpec.Syntax.stepPos, hn]

/-! ## `eat_char` -/

theorem eat_char_eq {s : CS} (h : StreamOK s) (c : Char) :
    ∃ s', sudo_rs.sudoers.char_stream.CharStream.eat_char s c =
        ok (((absStream s).eatChar c).1, s') ∧ StreamOK s' ∧
      absStream s' = ((absStream s).eatChar c).2 := by
  unfold sudo_rs.sudoers.char_stream.CharStream.eat_char
  rw [peek_eq, bind_ok, Stream.eatChar_eq]
  cases hp : (absStream s).peek with
  | none => exact ⟨s, by simp, h, by simp⟩
  | some d =>
    by_cases hd : d = c
    · subst hd
      obtain ⟨s', hb, h', ha⟩ := bump_eq h hp
      exact ⟨s', by simp [hb], h', by simp [ha]⟩
    · exact ⟨s, by simp [hd], h, by simp [hd]⟩

/-! ## `skip_to_newline` -/

@[simp] theorem skip_to_newline_loop_false (s : Slice Char) (i l k : Usize) :
    sudo_rs.sudoers.char_stream.CharStream.skip_to_newline_loop s i l k false =
      ok (s, i, l, k) := by
  rw [sudo_rs.sudoers.char_stream.CharStream.skip_to_newline_loop]; simp

theorem skip_to_newline_loop_eq (s : Slice Char) (i l k : Usize) (h : StreamOK (mkCS s i l k)) :
    ∃ s' : CS, sudo_rs.sudoers.char_stream.CharStream.skip_to_newline_loop s i l k true =
        ok (s'.src, s'.pos, s'.line, s'.col) ∧ StreamOK s' ∧
      absStream s' = (absStream (mkCS s i l k)).skipToNewline := by
  rw [sudo_rs.sudoers.char_stream.CharStream.skip_to_newline_loop]
  simp only [↓reduceIte]
  rw [peek_eq, bind_ok, Stream.skipToNewline, Stream.skipWhile_eq]
  cases hp : (absStream (mkCS s i l k)).peek with
  | none =>
    have hr : (absStream (mkCS s i l k)).rest = [] := by
      simpa [Stream.peek] using hp
    refine ⟨mkCS s i l k, by simp, h, ?_⟩
    rcases hs : absStream (mkCS s i l k) with ⟨r, a, b⟩
    rw [hs] at hr; subst hr; rfl
  | some c =>
    rw [Stream.nextIf_of_rest_cons (absStream_rest_cons hp)]
    by_cases hc : c = '\n'
    · subst hc
      exact ⟨mkCS s i l k, by simp, h, by simp⟩
    · obtain ⟨s1, hb, h1, ha1⟩ := bump_eq h hp
      have hlt : s1.src.val.length - s1.pos.val < s.val.length - i.val := by
        have e1 := congrArg (fun t => t.rest.length) ha1
        have e2 := Stream.pop_length_lt hp
        simp only [absStream_rest, List.length_drop, mkCS] at e1 e2
        omega
      obtain ⟨s', he, h', ha'⟩ := skip_to_newline_loop_eq s1.src s1.pos s1.line s1.col h1
      refine ⟨s', ?_, h', ?_⟩
      · simp only [hc, bne_iff_ne, ne_eq, not_false_eq_true, ↓reduceIte, hb, bind_ok]
        exact he
      · simp only [hc, bne_iff_ne, ne_eq, not_false_eq_true, ↓reduceIte, ← ha1]
        exact ha'
termination_by s.val.length - i.val

theorem skip_to_newline_eq {s : CS} (h : StreamOK s) :
    ∃ s', sudo_rs.sudoers.char_stream.CharStream.skip_to_newline s = ok s' ∧ StreamOK s' ∧
      absStream s' = (absStream s).skipToNewline := by
  obtain ⟨s', he, h', ha'⟩ := skip_to_newline_loop_eq s.src s.pos s.line s.col h
  exact ⟨s', by simp [sudo_rs.sudoers.char_stream.CharStream.skip_to_newline, he], h', ha'⟩

end SudoRsProofs.Parser
