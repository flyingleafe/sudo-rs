import SudoRsProofs.Parser.Combinators

/-!
# `impl<T: Token> Parse for T`: `accept_escaped` and the token loop

For any extracted `Token T` instance `Tk` that refines a reference `TokenSpec α`
(`TokenRefines Tk f T'`):

* `accept_escaped_refines`: `accept_escaped::<T>(first, ..)` refines
  `acceptEscaped T' (if first then T'.accept1st else T'.accept)`;
* `token_loop_eq`: the loop of the blanket `parse` (failure flag, `String` accumulator) refines
  `whileMaybe (acceptEscaped T' T'.accept) .. (tokenBody T')`, with the token text abstracted to
  its characters (`String.toList`); the text stays within `MAX_LEN + 4` bytes, so `String::len`
  never fails;
* `token_refines`: the blanket instance `Parse.Blanket Tk` refines `token T'`.
-/

open Aeneas Aeneas.Std Result
open SudoersSpec.Syntax (Stream ErrKind Parser Parsed TokenSpec)

namespace SudoRsProofs.Parser

variable {T α : Type} {Tk : sudo_rs.sudoers.basic_parser.Token T} {f : T → α} {T' : TokenSpec α}

theorem accepts_eq (hT : TokenRefines Tk f T') (first : Bool) (c : Char) :
    sudo_rs.sudoers.basic_parser.accepts Tk first c =
      ok ((if first then T'.accept1st else T'.accept) c) := by
  unfold sudo_rs.sudoers.basic_parser.accepts
  cases first <;> simp [hT.accept, hT.accept_1st]

theorem nextIf_of_peek_none {s : Stream} (h : s.peek = none) (p : Char → Bool) :
    s.nextIf p = (none, s) := by
  rcases s with ⟨_ | ⟨c, cs⟩, l, k⟩
  · rfl
  · simp [Stream.peek] at h

/-! ## `accept_escaped` -/

theorem accept_escaped_refines (hT : TokenRefines Tk f T') (first : Bool) {s : CS}
    (h : StreamOK s) :
    Refines id (sudo_rs.sudoers.basic_parser.accept_escaped Tk first s)
      ((SudoersSpec.Syntax.acceptEscaped T' (if first then T'.accept1st else T'.accept)).run
        (absStream s)) := by
  generalize hpred : (if first then T'.accept1st else T'.accept) = pred
  have hacc : ∀ c, sudo_rs.sudoers.basic_parser.accepts Tk first c = ok (pred c) := by
    intro c; rw [accepts_eq hT, hpred]
  unfold sudo_rs.sudoers.basic_parser.accept_escaped
  simp only [escape_char_eq, bind_ok, hT.allow_escape, SudoersSpec.Syntax.acceptEscaped,
    Parser.run_bind]
  cases hA : T'.allowEscape with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, Parser.run_pure, peek_eq, bind_ok, Parser.run_bind,
      Parser.run_nextIf]
    cases hp : (absStream s).peek with
    | none => simp [nextIf_of_peek_none hp, h]
    | some c =>
      rw [Stream.nextIf_of_rest_cons (absStream_rest_cons hp)]
      cases hc : pred c with
      | false => simp [hacc, hc, h]
      | true =>
        obtain ⟨s2, e2, h2, a2⟩ := bump_eq h hp
        simp [hacc, hc, e2, h2, a2]
  | true =>
    obtain ⟨s1, e1, h1, a1⟩ := eat_char_eq h '\\'
    simp only [↓reduceIte, e1, bind_ok, uncurry_apply_pair, Parser.run_eatChar, ← a1]
    cases hb : ((absStream s).eatChar '\\').1 with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, peek_eq, bind_ok, Parser.run_bind,
        Parser.run_nextIf]
      cases hp : (absStream s1).peek with
      | none => simp [nextIf_of_peek_none hp, h1]
      | some c =>
        rw [Stream.nextIf_of_rest_cons (absStream_rest_cons hp)]
        cases hc : pred c with
        | false => simp [hacc, hc, h1]
        | true =>
          obtain ⟨s2, e2, h2, a2⟩ := bump_eq h1 hp
          simp [hacc, hc, e2, h2, a2]
    | true =>
      simp only [↓reduceIte, peek_eq, bind_ok, Parser.run_bind, Parser.run_nextIf]
      -- after the backslash: an `escaped` character, else the backslash itself, else a line
      -- continuation, else an error
      have rest : ∀ (o : Option Char),
          (absStream s1).nextIf T'.escaped = (none, absStream s1) →
          Refines id
            (do
              let b3 ← sudo_rs.sudoers.basic_parser.accepts Tk first '\\'
              if b3 = true then ok (core.result.Result.Ok '\\', s1)
              else do
                let (b4, stream2) ← sudo_rs.sudoers.char_stream.CharStream.eat_char s1 '\n'
                if b4 = true then do
                  let b5 ← sudo_rs.sudoers.basic_parser.accepts Tk first ' '
                  if b5 = true then ok (core.result.Result.Ok ' ', stream2)
                  else do
                    let r ← sudo_rs.sudoers.basic_parser.reject Char
                    ok (r, stream2)
                else do
                  let r ← sudo_rs.sudoers.basic_parser.fatal_here Char stream2
                    sudo_rs.sudoers.basic_parser.ErrorKind.IllegalEscape
                  ok (r, stream2))
            ((if pred '\\' = true then pure '\\'
              else do
                if (← Parser.eatChar '\n') = true then
                  if pred ' ' = true then pure ' ' else Parser.reject
                else Parser.fatalHere ErrKind.illegalEscapeSequence : Parser Char).run
              (absStream s1)) := by
        intro _ _
        cases hq : pred '\\' with
        | true => simp [hacc, hq, h1]
        | false =>
          obtain ⟨s2, e2, h2, a2⟩ := eat_char_eq h1 '\n'
          simp only [hacc, hq, Bool.false_eq_true, ↓reduceIte, bind_ok, e2, uncurry_apply_pair,
            Parser.run_bind, Parser.run_eatChar, ← a2]
          cases hn : ((absStream s1).eatChar '\n').1 with
          | false => simp [h2, Parser.run_fatalHere]
          | true =>
            cases hsp : pred ' ' <;> simp [h2]
      cases hp : (absStream s1).peek with
      | none =>
        have hn := nextIf_of_peek_none hp T'.escaped
        simpa [hn] using rest none hn
      | some c =>
        rw [Stream.nextIf_of_rest_cons (absStream_rest_cons hp)]
        cases he : T'.escaped c with
        | true =>
          obtain ⟨s2, e2, h2, a2⟩ := bump_eq h1 hp
          simp [hT.escaped, he, e2, h2, a2]
        | false =>
          have hn : (absStream s1).nextIf T'.escaped = (none, absStream s1) := by
            rw [Stream.nextIf_of_rest_cons (absStream_rest_cons hp)]; simp [he]
          simpa [hT.escaped, he] using rest (some c) hn

/-! ## The token loop -/

theorem string_len_eq (s : String) (h : s.utf8ByteSize ≤ Usize.max) :
    ∃ n : Usize, alloc.string.String.len s = ok n ∧ n.val = s.utf8ByteSize := by
  have h' : s.utf8ByteSize < 2 ^ UScalarTy.Usize.numBits := by
    rw [Usize.max_def, Usize.numBits_def] at h
    have := Nat.one_le_two_pow (n := UScalarTy.Usize.numBits)
    omega
  have h'' : s.utf8ByteSize < 2 ^ System.Platform.numBits := by simpa using h'
  exact ⟨_, by simp [alloc.string.String.len, h''], Usize.ofNatCore_val_eq h'⟩

/-- The reference token loop from the characters `str` read so far. -/
abbrev refTokenLoop (T' : TokenSpec α) (str : List Char) : Parser (List Char) :=
  Parser.whileMaybe (SudoersSpec.Syntax.acceptEscaped T' T'.accept)
    (SudoersSpec.Syntax.acceptEscaped_consumes T' T'.accept) (SudoersSpec.Syntax.tokenBody T') id
    str

theorem token_loop_false (st : CS) (text : String) (failure : Option RStatus) :
    sudo_rs.sudoers.basic_parser.Parse.Blanket.parse_loop Tk st text failure false =
      ok (st.src, st.pos, st.line, st.col, text, failure) := by
  rw [sudo_rs.sudoers.basic_parser.Parse.Blanket.parse_loop]; simp

/-- The token loop: the text accumulated so far (`text`, of the characters `str`) stays within
`MAX_LEN + 4` bytes; the result is the text, or the status the loop stopped with. -/
theorem token_loop_eq (hT : TokenRefines Tk f T') (st : CS) (h : StreamOK st) (text : String)
    (str : List Char) (hstr : text.toList = str)
    (hlen : text.utf8ByteSize = SudoersSpec.Syntax.utf8Len str)
    (hbound : text.utf8ByteSize ≤ T'.maxLen + 4) :
    ∃ (s' : CS) (text' : String) (failure : Option RStatus),
      sudo_rs.sudoers.basic_parser.Parse.Blanket.parse_loop Tk st text none true =
        ok (s'.src, s'.pos, s'.line, s'.col, text', failure) ∧
      StreamOK s' ∧ text'.utf8ByteSize ≤ T'.maxLen + 4 ∧
      ResultRel String.toList (match failure with | none => .Ok text' | some e => .Err e)
        ((refTokenLoop T' str).run (absStream st)).1 ∧
      absStream s' = ((refTokenLoop T' str).run (absStream st)).2 := by
  obtain ⟨r, s1, e1, hr, h1, a1⟩ := accept_escaped_refines hT false h
  simp only [Bool.false_eq_true, ↓reduceIte] at hr a1
  rw [sudo_rs.sudoers.basic_parser.Parse.Blanket.parse_loop]
  simp only [↓reduceIte, e1, bind_ok, uncurry_apply_pair]
  unfold refTokenLoop Parser.whileMaybe
  rw [Parser.loop_run]
  simp only [Parser.whileMaybeBody, Parser.run_bind, Parser.run_maybe]
  rcases hR : (SudoersSpec.Syntax.acceptEscaped T' T'.accept).run (absStream st) with ⟨r', s''⟩
  rw [hR] at hr a1
  subst a1
  rcases r with c | (⟨sp, k⟩ | _) <;> rcases r' with (⟨sp', k'⟩ | _) | c' <;>
    simp only [ResultRel, StatusRel.fatal_reject, StatusRel.reject_fatal] at hr
  · -- a character: the length check, then the next iteration
    subst hr
    obtain ⟨n, hn, hnv⟩ := string_len_eq text (by have := hT.max_len_le; omega)
    obtain ⟨m, hm, hmv⟩ := hT.max_len
    simp only [SudoersSpec.Syntax.maybe, id, hn, hm, bind_ok, SudoersSpec.Syntax.tokenBody]
    by_cases hge : SudoersSpec.Syntax.utf8Len str ≥ T'.maxLen
    · have hge' : n ≥ m := by scalar_tac
      refine ⟨s1, text, some (.Fatal ⟨(s1.line, s1.col), (s1.line, s1.col)⟩ .TokenTooLong),
        ?_, h1, hbound, ?_, ?_⟩
      · simp [hge', token_loop_false]
      · simp [hge, Parser.run_fatalHere]
      · simp [hge, Parser.run_fatalHere]
    · have hge' : ¬ n ≥ m := by scalar_tac
      have hc := (SudoersSpec.Syntax.acceptEscaped_consumes T' T'.accept) _ _ _ hR
      have hlt : s1.src.val.length - s1.pos.val < st.src.val.length - st.pos.val := by
        simpa using hc
      have hcs : c.utf8Size ≤ 4 := Char.utf8Size_le_four c
      obtain ⟨s', text', failure, e', h', hb', hr', a'⟩ :=
        token_loop_eq hT s1 h1 (text.push c) (str ++ [c])
          (by rw [String.toList_push, hstr])
          (by simp [String.utf8ByteSize_push, hlen, SudoersSpec.Syntax.utf8Len])
          (by rw [String.utf8ByteSize_push]; omega)
      simp only [hge, hge', ↓reduceIte, alloc.string.String.push, bind_ok, Parser.run_pure]
      exact ⟨s', text', failure, e', h', hb', hr', a'⟩
  · -- a fatal error of `accept_escaped`
    simp only [SudoersSpec.Syntax.maybe]
    exact ⟨s1, text, some (.Fatal sp k), by simp [token_loop_false], h1, hbound, hr, rfl⟩
  · -- `Reject`: the token ends
    simp only [SudoersSpec.Syntax.maybe, Parser.run_pure]
    exact ⟨s1, text, none, by simp [token_loop_false], h1, hbound, hstr, rfl⟩
termination_by (absStream st).rest.length

/-- **`impl<T: Token> Parse for T` refines `token`.** -/
theorem token_refines (hT : TokenRefines Tk f T') :
    ParseRefines (sudo_rs.sudoers.basic_parser.Parse.Blanket Tk) f
      (SudoersSpec.Syntax.token T') := by
  constructor
  intro s h
  obtain ⟨r, s1, e1, hr, h1, a1⟩ := accept_escaped_refines hT true h
  simp only [↓reduceIte] at hr a1
  show Refines f (sudo_rs.sudoers.basic_parser.Parse.Blanket.parse Tk s) _
  unfold sudo_rs.sudoers.basic_parser.Parse.Blanket.parse
  simp only [get_pos_eq', bind_ok, e1, uncurry_apply_pair, SudoersSpec.Syntax.token,
    Parser.run_bind, Parser.run_getPos]
  rcases hR : (SudoersSpec.Syntax.acceptEscaped T' T'.accept1st).run (absStream s) with
    ⟨r', s''⟩
  rw [hR] at hr a1
  subst a1
  rcases r with c | st <;> rcases r' with e' | c' <;> simp only [ResultRel] at hr
  · subst hr
    have hcs : c.utf8Size ≤ 4 := Char.utf8Size_le_four c
    obtain ⟨s', text', failure, e2, h2, hb2, hr2, a2⟩ :=
      token_loop_eq hT s1 h1 ("".push c) [c] (by simp) (by simp [SudoersSpec.Syntax.utf8Len])
        (by simp; omega)
    simp only [branch_Ok, alloc.string.String.new, alloc.string.String.push, bind_ok, e2,
      uncurry_apply_pair, id]
    rcases hW : (refTokenLoop T' [c]).run (absStream s1) with ⟨w, s3⟩
    rw [hW] at hr2 a2
    simp only at a2
    subst a2
    rcases failure with _ | st <;> rcases w with e3 | str <;> simp only [ResultRel] at hr2
    · -- the loop ended normally: `construct`
      obtain ⟨rc, hc, hrc⟩ := hT.construct text' (by have := hT.max_len_le; omega)
      simp only [hc, bind_ok]
      rw [← hr2]
      rcases rc with x | k <;> rcases hC : T'.construct text'.toList with k' | a <;>
        simp only [ConstructRel, hC] at hrc
      · simp [h2, hrc]
      · simp [h2, hrc]
    · -- the loop stopped with an error
      simp [h2, hr2]
  · simp [hr, h1]

end SudoRsProofs.Parser
