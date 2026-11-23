import SudoRsProofs.Parser.Combinators

/-!
# `impl<T: Token> Parse for T`: `accept_escaped` and the token loop

For any extracted `Token T` instance `Tk` that refines a reference `TokenSpec α`, with
`construct` refined on the texts satisfying `Pre` (`TokenRefines Tk f T' Pre`):

* `accept_escaped_refines`: `accept_escaped::<T>(first, ..)` refines
  `acceptEscaped T' (if first then T'.accept1st else T'.accept)`; `acceptEscaped_produces`:
  what it returns is a character it `Produces`;
* `token_loop_eq`: the loop of the blanket `parse` (failure flag, `String` accumulator) refines
  `whileMaybe (acceptEscaped T' T'.accept) .. (tokenBody T')`, with the token text abstracted to
  its characters (`String.toList`); the text stays within `MAX_LEN + 4` bytes, so `String::len`
  never fails, and it stays a `TokenText T'` (non-empty, first character produced with
  `accept1st`, the others with `accept`);
* `token_refines`: the blanket instance `Parse.Blanket Tk` refines `token T'` provided
  `TokenText T' ⊆ Pre`.
-/

open Aeneas Aeneas.Std Result
open SudoersSpec.Syntax (Stream ErrKind Parser Parsed TokenSpec)

namespace SudoRsProofs.Parser

variable {T α : Type} {Tk : sudo_rs.sudoers.basic_parser.Token T} {f : T → α} {T' : TokenSpec α}
  {Pre : List Char → Prop}

theorem accepts_eq (hT : TokenRefines Tk f T' Pre) (first : Bool) (c : Char) :
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

theorem accept_escaped_refines (hT : TokenRefines Tk f T' Pre) (first : Bool) {s : CS}
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

/-- What `acceptEscaped T' pred` returns is a character it `Produces`. -/
theorem acceptEscaped_produces {pred : Char → Bool} {s s' : Stream} {c : Char}
    (h : (SudoersSpec.Syntax.acceptEscaped T' pred).run s = (.ok c, s')) : Produces T' pred c := by
  have hnext : ∀ (p : Char → Bool) (s₀ : Stream) (d : Char),
      (s₀.nextIf p).1 = some d → p d = true := by
    intro p s₀ d hd
    exact (Stream.nextIf_eq_some (s' := (s₀.nextIf p).2)).mp (by rw [← hd]) |>.2.1
  unfold SudoersSpec.Syntax.acceptEscaped at h
  simp only [Parser.run_bind] at h
  cases hA : T'.allowEscape
  · simp only [hA, Bool.false_eq_true, ↓reduceIte, Parser.run_pure, Parser.run_bind,
      Parser.run_nextIf] at h
    rcases hn : (s.nextIf pred).1 with _ | d <;> simp only [hn, Parser.run_reject,
      Parser.run_pure, Prod.mk.injEq, Except.ok.injEq, reduceCtorEq, false_and] at h
    exact Or.inl (h.1 ▸ hnext _ _ _ hn)
  · simp only [hA, ↓reduceIte, Parser.run_eatChar] at h
    cases hb : (s.eatChar '\\').1 <;>
      simp only [hb, Bool.false_eq_true, ↓reduceIte, Parser.run_bind, Parser.run_nextIf] at h
    · rcases hn : ((s.eatChar '\\').2.nextIf pred).1 with _ | d <;> simp only [hn,
        Parser.run_reject, Parser.run_pure, Prod.mk.injEq, Except.ok.injEq, reduceCtorEq,
        false_and] at h
      exact Or.inl (h.1 ▸ hnext _ _ _ hn)
    · rcases hn : ((s.eatChar '\\').2.nextIf T'.escaped).1 with _ | d <;> simp only [hn,
        Parser.run_pure, Prod.mk.injEq, Except.ok.injEq] at h
      · cases hq : pred '\\' <;> simp only [hq, Bool.false_eq_true, ↓reduceIte, Parser.run_pure,
          Prod.mk.injEq, Except.ok.injEq, Parser.run_bind, Parser.run_eatChar] at h
        · cases he : (((s.eatChar '\\').2.nextIf T'.escaped).2.eatChar '\n').1 <;>
            simp only [he, Bool.false_eq_true, ↓reduceIte, Parser.run_fatalHere, Prod.mk.injEq,
              reduceCtorEq, false_and] at h
          cases hsp : pred ' ' <;> simp only [hsp, Bool.false_eq_true, ↓reduceIte,
            Parser.run_pure, Parser.run_reject, Prod.mk.injEq, Except.ok.injEq, reduceCtorEq,
            false_and] at h
          exact Or.inl (h.1 ▸ hsp)
        · exact Or.inl (h.1 ▸ hq)
      · exact Or.inr ⟨hA, h.1 ▸ hnext _ _ _ hn⟩

theorem TokenText.snoc {str : List Char} {c : Char} (h : TokenText T' str)
    (hc : Produces T' T'.accept c) : TokenText T' (str ++ [c]) := by
  rcases str with _ | ⟨d, ds⟩
  · exact h.elim
  · refine ⟨h.1, fun e he => ?_⟩
    rcases List.mem_append.mp he with he | he
    · exact h.2 e he
    · rw [List.mem_singleton.mp he]; exact hc

/-- At a position already past trailing whitespace, an accepted first character is read
directly from the stream, rather than produced by an escape. -/
theorem acceptEscaped_at_noBlankNext {pred : Char → Bool} {s s' : Stream} {c : Char}
    (hs : NoBlankNext s)
    (h : (SudoersSpec.Syntax.acceptEscaped T' pred).run s = (.ok c, s')) :
    s.peek = some c ∧ pred c = true := by
  have he : s.eatChar '\\' = (false, s) := Stream.eatChar_false.mpr ⟨
    fun hp => (hs _ hp).2.2 rfl, rfl⟩
  simp only [SudoersSpec.Syntax.acceptEscaped, Parser.run_bind] at h
  have hn : (if T'.allowEscape then Parser.eatChar '\\' else pure false).run s =
      (.ok false, s) := by
    cases T'.allowEscape <;> simp [he]
  rw [hn] at h
  simp only [Bool.false_eq_true, ↓reduceIte, Parser.run_bind, Parser.run_nextIf] at h
  rcases hp : (s.nextIf pred).1 with _ | d <;> simp [hp] at h
  obtain ⟨hp', hd, _⟩ := Stream.nextIf_eq_some.mp
    (show s.nextIf pred = (some d, (s.nextIf pred).2) by rw [← hp])
  simpa [h.1] using And.intro hp' hd

/-- The token loop: the text accumulated so far (`text`, of the characters `str`) stays within
`MAX_LEN + 4` bytes and remains a `TokenText`; the result is the text, or the status the loop
stopped with. -/
theorem token_loop_eq (hT : TokenRefines Tk f T' Pre) (st : CS) (h : StreamOK st)
    (text : String) (str : List Char) (hstr : text.toList = str)
    (hlen : text.utf8ByteSize = SudoersSpec.Syntax.utf8Len str)
    (hbound : text.utf8ByteSize ≤ T'.maxLen + 4) (htt : TokenText T' str) :
    ∃ (s' : CS) (text' : String) (failure : Option RStatus),
      sudo_rs.sudoers.basic_parser.Parse.Blanket.parse_loop Tk st text none true =
        ok (s'.src, s'.pos, s'.line, s'.col, text', failure) ∧
      StreamOK s' ∧ text'.utf8ByteSize ≤ T'.maxLen + 4 ∧ TokenText T' text'.toList ∧
      text'.toList.head? = str.head? ∧
      ResultRel String.toList (match failure with | none => .Ok text' | some e => .Err e)
        ((refTokenLoop T' str).run (absStream st)).1 ∧
      absStream s' = ((refTokenLoop T' str).run (absStream st)).2 := by
  have htt' : TokenText T' text.toList := hstr ▸ htt
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
        ?_, h1, hbound, htt', congrArg List.head? hstr, ?_, ?_⟩
      · simp [hge', token_loop_false]
      · simp [hge, Parser.run_fatalHere]
      · simp [hge, Parser.run_fatalHere]
    · have hge' : ¬ n ≥ m := by scalar_tac
      have hc := (SudoersSpec.Syntax.acceptEscaped_consumes T' T'.accept) _ _ _ hR
      have hlt : s1.src.val.length - s1.pos.val < st.src.val.length - st.pos.val := by
        simpa using hc
      have hcs : c.utf8Size ≤ 4 := Char.utf8Size_le_four c
      obtain ⟨s', text', failure, e', h', hb', ht', hhead, hr', a'⟩ :=
        token_loop_eq hT s1 h1 (text.push c) (str ++ [c])
          (by rw [String.toList_push, hstr])
          (by simp [String.utf8ByteSize_push, hlen, SudoersSpec.Syntax.utf8Len])
          (by rw [String.utf8ByteSize_push]; omega)
          (htt.snoc (acceptEscaped_produces hR))
      simp only [hge, hge', ↓reduceIte, alloc.string.String.push, bind_ok, Parser.run_pure]
      have hh : (str ++ [c]).head? = str.head? := by cases str <;> simp_all [TokenText]
      exact ⟨s', text', failure, e', h', hb', ht', hhead.trans hh, hr', a'⟩
  · -- a fatal error of `accept_escaped`
    simp only [SudoersSpec.Syntax.maybe]
    exact ⟨s1, text, some (.Fatal sp k), by simp [token_loop_false], h1, hbound, htt',
      congrArg List.head? hstr, hr, rfl⟩
  · -- `Reject`: the token ends
    simp only [SudoersSpec.Syntax.maybe, Parser.run_pure]
    exact ⟨s1, text, none, by simp [token_loop_false], h1, hbound, htt',
      congrArg List.head? hstr, hstr, rfl⟩
termination_by (absStream st).rest.length

/-- Refine the blanket parser at this cursor when the domain of `construct` is known using
both the token text and the first-character parse. -/
theorem token_refines_at (hT : TokenRefines Tk f T' Pre) (s : CS) (h : StreamOK s)
    (hPre : ∀ cs c s1, cs.head? = some c →
      (SudoersSpec.Syntax.acceptEscaped T' T'.accept1st).run (absStream s) = (.ok c, s1) →
      TokenText T' cs → Pre cs) :
    Refines f ((sudo_rs.sudoers.basic_parser.Parse.Blanket Tk).parse s)
      ((SudoersSpec.Syntax.token T').run (absStream s)) := by
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
    obtain ⟨s', text', failure, e2, h2, hb2, ht2, hh2, hr2, a2⟩ :=
      token_loop_eq hT s1 h1 ("".push c) [c] (by simp) (by simp [SudoersSpec.Syntax.utf8Len])
        (by simp; omega) ⟨acceptEscaped_produces hR, by simp⟩
    simp only [branch_Ok, alloc.string.String.new, alloc.string.String.push, bind_ok, e2,
      uncurry_apply_pair, id]
    rcases hW : (refTokenLoop T' [c]).run (absStream s1) with ⟨w, s3⟩
    rw [hW] at hr2 a2
    simp only at a2
    subst a2
    rcases failure with _ | st <;> rcases w with e3 | str <;> simp only [ResultRel] at hr2
    · -- the loop ended normally: `construct`
      obtain ⟨rc, hc, hrc⟩ := hT.construct text' (by have := hT.max_len_le; omega)
        (hPre _ _ _ hh2 hR ht2)
      simp only [hc, bind_ok]
      rw [← hr2]
      rcases rc with x | k <;> rcases hC : T'.construct text'.toList with k' | a <;>
        simp only [ConstructRel, hC] at hrc
      · simp [h2, hrc]
      · simp [h2, hrc]
    · -- the loop stopped with an error
      simp [h2, hr2]
  · simp [hr, h1]

/-- **`impl<T: Token> Parse for T` refines `token`** when `construct` refines on every
text the token loop can build. -/
theorem token_refines (hT : TokenRefines Tk f T' Pre) (hPre : ∀ cs, TokenText T' cs → Pre cs) :
    ParseRefines (sudo_rs.sudoers.basic_parser.Parse.Blanket Tk) f
      (SudoersSpec.Syntax.token T') :=
  ⟨fun s h => token_refines_at hT s h (fun cs _ _ _ _ ht => hPre cs ht)⟩

end SudoRsProofs.Parser
