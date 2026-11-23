import SudoRsProofs.Parser.Stream

/-!
# `basic_parser.rs`: whitespace, comments, syntax characters, nonterminals

Refinement lemmas, total correctness, for `LeadingWhitespace`, `TrailingWhitespace`, `Comment`,
`skip_trailing_whitespace`, `try_syntax`, `expect_syntax`, `is_syntax`, `maybe`,
`try_nonterminal` and `expect_nonterminal` against `SudoersSpec.Syntax`.

The loops (`while more { … }` in Rust, `…_loop` with `partial_fixpoint` in Lean) are proved by
well-founded recursion on the number of characters left (`termination_by`), against the
unfolding equations of the reference loops (`Stream.skipWhile_eq`, `Parser.loop_run`).
-/

open Aeneas Aeneas.Std Result
open SudoersSpec.Syntax (Stream ErrKind Parser Parsed)

namespace SudoRsProofs.Parser

/-! ## Small extracted functions -/

@[simp] theorem make_eq {T : Type} (v : T) :
    sudo_rs.sudoers.basic_parser.make v = ok (.Ok v) := rfl

@[simp] theorem reject_eq (T : Type) :
    sudo_rs.sudoers.basic_parser.reject T = ok (.Err .Reject) := rfl

@[simp] theorem fatal_here_eq (T : Type) (s : CS) (k : RKind) :
    sudo_rs.sudoers.basic_parser.fatal_here T s k =
      ok (.Err (.Fatal ⟨(s.line, s.col), (s.line, s.col)⟩ k)) := by
  simp [sudo_rs.sudoers.basic_parser.fatal_here, sudo_rs.sudoers.char_stream.CharStream.get_pos]

@[simp] theorem fatal_from_eq (T : Type) (p : Usize × Usize) (s : CS) (k : RKind) :
    sudo_rs.sudoers.basic_parser.fatal_from T p s k =
      ok (.Err (.Fatal ⟨p, (s.line, s.col)⟩ k)) := by
  simp [sudo_rs.sudoers.basic_parser.fatal_from, sudo_rs.sudoers.char_stream.CharStream.get_pos]

@[simp] theorem get_pos_eq' (s : CS) :
    sudo_rs.sudoers.char_stream.CharStream.get_pos s = ok (s.line, s.col) := rfl

@[simp] theorem escape_char_eq : sudoers.basic_parser.escape_char = ok '\\' := rfl

/-- A fatal error at the current position (`fatal_here` / `Parser.fatalHere`). -/
theorem StatusRel.here {s : CS} {k : RKind} {k' : ErrKind} (hk : KindRel k k') :
    StatusRel (.Fatal ⟨(s.line, s.col), (s.line, s.col)⟩ k)
      (.fatal ⟨(absStream s).getPos, (absStream s).getPos⟩ k') :=
  .fatal _ _ _ hk

/-- A fatal error from a start position (`fatal_from` / `Parser.fatalFrom`). -/
theorem StatusRel.from {p : Usize × Usize} {s : CS} {k : RKind} {k' : ErrKind}
    (hk : KindRel k k') :
    StatusRel (.Fatal ⟨p, (s.line, s.col)⟩ k)
      (.fatal ⟨(p.1.val, p.2.val), (absStream s).getPos⟩ k') :=
  .fatal _ _ _ hk

/-! ## Closing refinement goals by `simp`

Proof pattern: rewrite the extracted side with the equations of the callee lemmas until it is
`ok (r, s')`, rewrite the reference side with `Parser.run_*` until it is a pair, then
`simp [refines_ok_iff, …]`. -/

@[simp] theorem refines_ok_iff {T α : Type} {f : T → α} {r : RParsed T} {s' : CS}
    {out : Parsed α × Stream} :
    Refines f (ok (r, s')) out ↔ ResultRel f r out.1 ∧ StreamOK s' ∧ absStream s' = out.2 := by
  constructor
  · rintro ⟨r', s'', e, h⟩
    simp only [ok.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact h
  · intro h; exact ⟨r, s', rfl, h⟩

@[simp] theorem absSpan_mk (a b c d : Usize) :
    absSpan ⟨(a, b), (c, d)⟩ = ⟨(a.val, b.val), (c.val, d.val)⟩ := rfl

@[simp] theorem StatusRel.fatal_iff {sp : sudo_rs.sudoers.basic_parser.Span} {k : RKind}
    {sp' : SudoersSpec.Span} {k' : ErrKind} :
    StatusRel (.Fatal sp k) (.fatal sp' k') ↔ absSpan sp = sp' ∧ KindRel k k' := by
  constructor
  · intro h; cases h; exact ⟨rfl, by assumption⟩
  · rintro ⟨rfl, h⟩; exact .fatal _ _ _ h

@[simp] theorem StatusRel.reject_iff : StatusRel .Reject .reject ↔ True :=
  ⟨fun _ => trivial, fun _ => .reject⟩

@[simp] theorem StatusRel.fatal_reject {sp : sudo_rs.sudoers.basic_parser.Span} {k : RKind} :
    ¬ StatusRel (.Fatal sp k) .reject := by
  intro h; cases h

@[simp] theorem StatusRel.reject_fatal {sp' : SudoersSpec.Span} {k' : ErrKind} :
    ¬ StatusRel .Reject (.fatal sp' k') := by
  intro h; cases h

@[simp] theorem KindRel.expected_iff {s : Str} {d : String} :
    KindRel (.Expected s) (.expected d) ↔ s.val = sudo_rs.stringBytes d :=
  ⟨fun h => by cases h; assumption, fun h => .expected _ _ h⟩

attribute [simp] KindRel.superfluousWhitespace KindRel.strayEscape KindRel.expecting
  KindRel.illegalEscape KindRel.tokenTooLong KindRel.tooManyItems KindRel.missingLineTerminator
  KindRel.garbageAtEndOfLine KindRel.hostIpv4

@[simp] theorem maybe_Ok {T : Type} (x : T) :
    sudo_rs.sudoers.basic_parser.maybe (.Ok x) = ok (.Ok (some x)) := rfl
@[simp] theorem maybe_Reject {T : Type} :
    sudo_rs.sudoers.basic_parser.maybe (T := T) (.Err .Reject) = ok (.Ok none) := rfl
@[simp] theorem maybe_Fatal {T : Type} (sp : sudo_rs.sudoers.basic_parser.Span) (k : RKind) :
    sudo_rs.sudoers.basic_parser.maybe (T := T) (.Err (.Fatal sp k)) =
      ok (.Err (.Fatal sp k)) := rfl

/-- `basic_parser::maybe` refines `Syntax.maybe`. -/
theorem maybe_rel {T α : Type} {f : T → α} {r : RParsed T} {r' : Parsed α}
    (h : ResultRel f r r') :
    ∃ m, sudo_rs.sudoers.basic_parser.maybe r = ok m ∧
      ResultRel (Option.map f) m (SudoersSpec.Syntax.maybe r') := by
  rcases r with x | (⟨sp, k⟩ | _) <;> rcases r' with (⟨sp', k'⟩ | _) | a <;>
    simp_all [ResultRel, SudoersSpec.Syntax.maybe]

/-! ## `LeadingWhitespace` -/

/-- The class of `LeadingWhitespace`: `'\t'` and `' '`. -/
abbrev isBlank (c : Char) : Bool := c == '\t' || c == ' '

theorem leading_ws_loop_eq (s : Slice Char) (i l k : Usize) (h : StreamOK (mkCS s i l k)) :
    ∃ s' : CS,
      sudo_rs.sudoers.basic_parser.LeadingWhitespace.Insts.Sudo_rsSudoersBasic_parserParse.parse_loop
          s i l k true = ok (s'.src, s'.pos, s'.line, s'.col) ∧ StreamOK s' ∧
      absStream s' = (absStream (mkCS s i l k)).skipWhile isBlank := by
  rw [sudo_rs.sudoers.basic_parser.LeadingWhitespace.Insts.Sudo_rsSudoersBasic_parserParse.parse_loop]
  simp only [↓reduceIte]
  rw [peek_eq, bind_ok, Stream.skipWhile_eq]
  have hfalse : ∀ (s : Slice Char) (i l k : Usize),
      sudo_rs.sudoers.basic_parser.LeadingWhitespace.Insts.Sudo_rsSudoersBasic_parserParse.parse_loop
        s i l k false = ok (s, i, l, k) := by
    intro s i l k
    rw [sudo_rs.sudoers.basic_parser.LeadingWhitespace.Insts.Sudo_rsSudoersBasic_parserParse.parse_loop]
    simp
  cases hp : (absStream (mkCS s i l k)).peek with
  | none =>
    have hr : (absStream (mkCS s i l k)).rest = [] := by
      simpa [Stream.peek] using hp
    refine ⟨mkCS s i l k, by simp [hfalse], h, ?_⟩
    rcases hs : absStream (mkCS s i l k) with ⟨r, a, b⟩
    rw [hs] at hr; subst hr; rfl
  | some c =>
    rw [Stream.nextIf_of_rest_cons (absStream_rest_cons hp)]
    by_cases hc : c = '\t' ∨ c = ' '
    · obtain ⟨s1, hb, h1, ha1⟩ := bump_eq h hp
      have hlt : s1.src.val.length - s1.pos.val < s.val.length - i.val := by
        have e1 := congrArg (fun t => t.rest.length) ha1
        have e2 := Stream.pop_length_lt hp
        simp only [absStream_rest, List.length_drop, mkCS] at e1 e2
        omega
      obtain ⟨s', he, h', ha'⟩ := leading_ws_loop_eq s1.src s1.pos s1.line s1.col h1
      have hcb : isBlank c = true := by rcases hc with rfl | rfl <;> rfl
      refine ⟨s', ?_, h', ?_⟩
      · rcases hc with rfl | rfl
        · simp only [↓reduceIte, hb, bind_ok]; exact he
        · simp only [show (' ' : Char) ≠ '\t' by decide, ↓reduceIte, hb, bind_ok]; exact he
      · simp only [hcb, ↓reduceIte, ← ha1]; exact ha'
    · have hcb : isBlank c = false := by
        simp only [isBlank, Bool.or_eq_false_iff, beq_eq_false_iff_ne]; tauto
      refine ⟨mkCS s i l k, ?_, h, by simp [hcb]⟩
      have h1 : c ≠ '\t' := fun e => hc (.inl e)
      have h2 : c ≠ ' ' := fun e => hc (.inr e)
      simp [h1, h2, hfalse]
termination_by s.val.length - i.val

theorem leading_ws_refines {s : CS} (h : StreamOK s) :
    Refines id
      (sudo_rs.sudoers.basic_parser.LeadingWhitespace.Insts.Sudo_rsSudoersBasic_parserParse.parse s)
      (SudoersSpec.Syntax.leadingWhitespace.run (absStream s)) := by
  rcases s with ⟨src, pos, line, col⟩
  obtain ⟨⟨src', pos', line', col'⟩, he, h', ha'⟩ := leading_ws_loop_eq src pos line col h
  rw [SudoersSpec.Syntax.leadingWhitespace_run]
  unfold sudo_rs.sudoers.basic_parser.LeadingWhitespace.Insts.Sudo_rsSudoersBasic_parserParse.parse
  dsimp only at he ⊢
  simp only [he, bind_ok, uncurry_apply_pair, peek_eq]
  rw [← ha']
  cases hp : (absStream ⟨src', pos', line', col'⟩).peek <;> simp [h']

/-! ## `TrailingWhitespace`, `skip_trailing_whitespace` -/

theorem trailing_ws_loop_false (st : CS) (stray : Bool) :
    sudo_rs.sudoers.basic_parser.TrailingWhitespace.Insts.Sudo_rsSudoersBasic_parserParse.parse_loop
      st stray false = ok (st.src, st.pos, st.line, st.col, stray) := by
  rw [sudo_rs.sudoers.basic_parser.TrailingWhitespace.Insts.Sudo_rsSudoersBasic_parserParse.parse_loop]
  simp

/-- The loop of `TrailingWhitespace::parse` (`stray` flag) against `trailingWhitespace`: the
reference result is the error `stray escape sequence` at the output position iff the flag is
set. -/
theorem trailing_ws_loop_eq (st : CS) (h : StreamOK st) :
    ∃ (s' : CS) (stray : Bool),
      sudo_rs.sudoers.basic_parser.TrailingWhitespace.Insts.Sudo_rsSudoersBasic_parserParse.parse_loop
          st false true = ok (s'.src, s'.pos, s'.line, s'.col, stray) ∧ StreamOK s' ∧
      SudoersSpec.Syntax.trailingWhitespace.run (absStream st) =
        (if stray then .error (.fatal ⟨(absStream s').getPos, (absStream s').getPos⟩
          .strayEscapeSequence) else .ok (), absStream s') := by
  obtain ⟨r1, s1, e1, -, h1, a1⟩ := leading_ws_refines h
  obtain ⟨s2, e2, h2, a2⟩ := eat_char_eq h1 '\\'
  rw [sudo_rs.sudoers.basic_parser.TrailingWhitespace.Insts.Sudo_rsSudoersBasic_parserParse.parse_loop]
  simp only [↓reduceIte, e1, bind_ok, uncurry_apply_pair, escape_char_eq, e2]
  rw [SudoersSpec.Syntax.trailingWhitespace, Parser.loop_run]
  simp only [SudoersSpec.Syntax.trailingWhitespaceBody, Parser.run_bind, Parser.run_observe,
    Parser.run_eatChar, ← a1, ← a2]
  cases hb : ((absStream s1).eatChar '\\').1 with
  | false =>
    refine ⟨s2, false, by simp [trailing_ws_loop_false], h2, ?_⟩
    simp [Parser.run_pure]
  | true =>
    obtain ⟨s3, e3, h3, a3⟩ := eat_char_eq h2 '\n'
    simp only [↓reduceIte, e3, bind_ok, uncurry_apply_pair, Parser.run_bind, Parser.run_eatChar,
      ← a3]
    cases hb' : ((absStream s2).eatChar '\n').1 with
    | false =>
      refine ⟨s3, true, by simp [trailing_ws_loop_false], h3, ?_⟩
      simp [Parser.run_fatalHere]
    | true =>
      have hlt : (absStream s3).rest.length < (absStream st).rest.length := by
        have l1 := SudoersSpec.Syntax.Parser.length_le SudoersSpec.Syntax.leadingWhitespace
          (absStream st)
        rw [← a1] at l1
        have l2 : (absStream s2).rest.length < (absStream s1).rest.length := by
          have := (Stream.eatChar_true (c := '\\') (s := absStream s1)
            (s' := ((absStream s1).eatChar '\\').2)).mp (by rw [← hb])
          rw [a2, this.2]; exact SudoersSpec.Syntax.Stream.pop_length_lt this.1
        have l3 : (absStream s3).rest.length ≤ (absStream s2).rest.length := by
          rw [a3]; exact (Stream.Reaches.eatChar _ _).length_le
        omega
      have hlt' : s3.src.val.length - s3.pos.val < st.src.val.length - st.pos.val := by
        simpa using hlt
      obtain ⟨s', stray, e', h', a'⟩ := trailing_ws_loop_eq s3 h3
      refine ⟨s', stray, by simpa using e', h', ?_⟩
      simp only [↓reduceIte, Parser.run_pure]
      exact a'
termination_by (absStream st).rest.length

theorem trailing_ws_refines {s : CS} (h : StreamOK s) :
    Refines id
      (sudo_rs.sudoers.basic_parser.TrailingWhitespace.Insts.Sudo_rsSudoersBasic_parserParse.parse s)
      (SudoersSpec.Syntax.trailingWhitespace.run (absStream s)) := by
  obtain ⟨s', stray, e, h', a⟩ := trailing_ws_loop_eq s h
  unfold sudo_rs.sudoers.basic_parser.TrailingWhitespace.Insts.Sudo_rsSudoersBasic_parserParse.parse
  rw [a]
  cases stray <;> simp [e, h']

theorem skip_trailing_whitespace_refines {s : CS} (h : StreamOK s) :
    Refines id (sudo_rs.sudoers.basic_parser.skip_trailing_whitespace s)
      (SudoersSpec.Syntax.skipTrailingWhitespace.run (absStream s)) := by
  obtain ⟨r, s', e, hr, h', a⟩ := trailing_ws_refines h
  unfold sudo_rs.sudoers.basic_parser.skip_trailing_whitespace
  simp only [SudoersSpec.Syntax.skipTrailingWhitespace, Parser.run_bind, e, bind_ok,
    uncurry_apply_pair]
  rcases hT : SudoersSpec.Syntax.trailingWhitespace.run (absStream s) with ⟨r', s''⟩
  rw [hT] at hr a
  rcases r with u | st <;> rcases r' with e' | u' <;> simp_all [Parser.run_pure]

/-! ## `Comment` -/

theorem comment_refines {s : CS} (h : StreamOK s) :
    Refines id (sudo_rs.sudoers.basic_parser.Comment.Insts.Sudo_rsSudoersBasic_parserParse.parse s)
      (SudoersSpec.Syntax.comment.run (absStream s)) := by
  obtain ⟨s1, e1, h1, a1⟩ := eat_char_eq h '#'
  unfold sudo_rs.sudoers.basic_parser.Comment.Insts.Sudo_rsSudoersBasic_parserParse.parse
  simp only [SudoersSpec.Syntax.comment, Parser.run_bind, Parser.run_eatChar, e1, bind_ok,
    uncurry_apply_pair, ← a1]
  cases hb : ((absStream s).eatChar '#').1 with
  | false => simp [h1]
  | true =>
    obtain ⟨s2, e2, h2, a2⟩ := skip_to_newline_eq h1
    simp [e2, h2, a2]

/-! ## Syntax characters -/

theorem try_syntax_refines {s : CS} (h : StreamOK s) (c : Char) :
    Refines id (sudo_rs.sudoers.basic_parser.try_syntax c s)
      ((SudoersSpec.Syntax.trySyntax c).run (absStream s)) := by
  obtain ⟨s1, e1, h1, a1⟩ := eat_char_eq h c
  unfold sudo_rs.sudoers.basic_parser.try_syntax
  simp only [SudoersSpec.Syntax.trySyntax, Parser.run_bind, Parser.run_eatChar, e1, bind_ok,
    uncurry_apply_pair, ← a1]
  cases hb : ((absStream s).eatChar c).1 with
  | false => simp [h1]
  | true =>
    obtain ⟨r, s2, e2, hr, h2, a2⟩ := skip_trailing_whitespace_refines h1
    simp only [↓reduceIte, Bool.not_true, Bool.false_eq_true, e2, bind_ok, uncurry_apply_pair]
    rcases r with ⟨⟩ | st <;> simp_all

theorem expect_syntax_refines {s : CS} (h : StreamOK s) (c : Char) :
    Refines id (sudo_rs.sudoers.basic_parser.expect_syntax c s)
      ((SudoersSpec.Syntax.expectSyntax c).run (absStream s)) := by
  obtain ⟨r, s1, e1, hr, h1, a1⟩ := try_syntax_refines h c
  unfold sudo_rs.sudoers.basic_parser.expect_syntax
  simp only [SudoersSpec.Syntax.expectSyntax, Parser.run_bind, Parser.run_observe, e1, bind_ok,
    uncurry_apply_pair, ← a1]
  rcases hT : (SudoersSpec.Syntax.trySyntax c).run (absStream s) with ⟨r', s''⟩
  rw [hT] at hr a1
  subst a1
  rcases r with ⟨⟩ | st <;> rcases r' with e' | ⟨⟩ <;>
    simp_all [peek_eq, Parser.run_bind, Parser.run_peek, Parser.run_fatalHere]

theorem is_syntax_refines {s : CS} (h : StreamOK s) (c : Char) :
    Refines id (sudo_rs.sudoers.basic_parser.is_syntax c s)
      ((SudoersSpec.Syntax.isSyntax c).run (absStream s)) := by
  obtain ⟨r, s1, e1, hr, h1, a1⟩ := try_syntax_refines h c
  unfold sudo_rs.sudoers.basic_parser.is_syntax
  simp only [SudoersSpec.Syntax.isSyntax, Parser.run_bind, Parser.run_maybe, e1, bind_ok,
    uncurry_apply_pair]
  rcases hT : (SudoersSpec.Syntax.trySyntax c).run (absStream s) with ⟨r', s''⟩
  rw [hT] at hr a1
  subst a1
  rcases r with ⟨⟩ | (⟨sp, k⟩ | _) <;> rcases r' with (⟨sp', k'⟩ | _) | ⟨⟩ <;>
    simp_all [SudoersSpec.Syntax.maybe]

/-! ## Nonterminals -/

theorem try_nonterminal_refines {T α : Type} {P : sudo_rs.sudoers.basic_parser.Parse T}
    {f : T → α} {p : Parser α} (hP : ParseRefines P f p) {s : CS} (h : StreamOK s) :
    Refines f (sudo_rs.sudoers.basic_parser.try_nonterminal P s)
      ((SudoersSpec.Syntax.tryNonterminal p).run (absStream s)) := by
  obtain ⟨r, s1, e1, hr, h1, a1⟩ := hP.parse s h
  unfold sudo_rs.sudoers.basic_parser.try_nonterminal
  simp only [SudoersSpec.Syntax.tryNonterminal, Parser.run_bind, e1, bind_ok, uncurry_apply_pair]
  rcases hT : p.run (absStream s) with ⟨r', s''⟩
  rw [hT] at hr a1
  subst a1
  rcases r with x | st <;> rcases r' with e' | a <;> simp only [ResultRel] at hr
  · obtain ⟨u, s2, e2, hu, h2, a2⟩ := skip_trailing_whitespace_refines h1
    simp only [e2, bind_ok, uncurry_apply_pair]
    rcases hT2 : SudoersSpec.Syntax.skipTrailingWhitespace.run (absStream s1) with ⟨u', s3⟩
    rw [hT2] at hu a2
    rcases u with ⟨⟩ | st <;> rcases u' with e' | ⟨⟩ <;> simp_all
  · simp [hr, h1]

theorem expect_nonterminal_refines {T α : Type} {P : sudo_rs.sudoers.basic_parser.Parse T}
    {UF : sudo_rs.sudoers.ast_names.UserFriendly T} {f : T → α} {p : Parser α} {d : String}
    (hP : ParseRefines P f p) (hD : DescRel UF d) {s : CS} (h : StreamOK s) :
    Refines f (sudo_rs.sudoers.basic_parser.expect_nonterminal P UF s)
      ((SudoersSpec.Syntax.expectNonterminal d p).run (absStream s)) := by
  obtain ⟨sd, hsd, hsdv⟩ := hD
  obtain ⟨r, s1, e1, hr, h1, a1⟩ := try_nonterminal_refines hP h
  unfold sudo_rs.sudoers.basic_parser.expect_nonterminal
  simp only [SudoersSpec.Syntax.expectNonterminal, Parser.run_bind, Parser.run_getPos,
    Parser.run_observe, get_pos_eq', e1, bind_ok, uncurry_apply_pair]
  rcases hT : (SudoersSpec.Syntax.tryNonterminal p).run (absStream s) with ⟨r', s''⟩
  rw [hT] at hr a1
  subst a1
  rcases r with x | (⟨sp, k⟩ | _) <;> rcases r' with (⟨sp', k'⟩ | _) | a <;>
    simp_all [Parser.run_lift, Parser.run_fatalFrom]

end SudoRsProofs.Parser
