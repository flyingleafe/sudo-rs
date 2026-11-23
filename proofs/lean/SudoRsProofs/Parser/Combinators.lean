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

/-- A condition on reference cursors preserved by every forward parse, including errors. -/
def ForwardStable (I : Stream → Prop) : Prop :=
  ∀ ⦃s s'⦄, I s → s.Reaches s' → I s'

/-- Refinement on representable cursors satisfying an additional reference-stream condition. -/
def ParseRefinesOn (I : Stream → Prop) {T α : Type}
    (P : sudo_rs.sudoers.basic_parser.Parse T) (f : T → α) (p : Parser α) : Prop :=
  ∀ s, StreamOK s → I (absStream s) → Refines f (P.parse s) (p.run (absStream s))

theorem ParseRefines.on {I : Stream → Prop} {T α : Type}
    {P : sudo_rs.sudoers.basic_parser.Parse T} {f : T → α} {p : Parser α}
    (hP : ParseRefines P f p) : ParseRefinesOn I P f p :=
  fun s hs _ => hP.parse s hs

theorem ForwardStable.after {I : Stream → Prop} (hI : ForwardStable I) {s s' : CS}
    (hi : I (absStream s)) {α : Type} (p : Parser α)
    (ha : absStream s' = (p.run (absStream s)).2) : I (absStream s') :=
  ha ▸ hI hi (p.reaches _)

theorem try_nonterminal_refines_at {T α : Type} {P : sudo_rs.sudoers.basic_parser.Parse T}
    {f : T → α} {p : Parser α} {s : CS}
    (hP : Refines f (P.parse s) (p.run (absStream s))) :
    Refines f (sudo_rs.sudoers.basic_parser.try_nonterminal P s)
      ((SudoersSpec.Syntax.tryNonterminal p).run (absStream s)) := by
  obtain ⟨r, s1, e1, hr, h1, a1⟩ := hP
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

theorem try_nonterminal_refines {T α : Type} {P : sudo_rs.sudoers.basic_parser.Parse T}
    {f : T → α} {p : Parser α} (hP : ParseRefines P f p) {s : CS} (h : StreamOK s) :
    Refines f (sudo_rs.sudoers.basic_parser.try_nonterminal P s)
      ((SudoersSpec.Syntax.tryNonterminal p).run (absStream s)) :=
  try_nonterminal_refines_at (hP.parse s h)

theorem expect_nonterminal_refines_at {T α : Type} {P : sudo_rs.sudoers.basic_parser.Parse T}
    {UF : sudo_rs.sudoers.ast_names.UserFriendly T} {f : T → α} {p : Parser α} {d : String}
    {s : CS} (hP : Refines f (P.parse s) (p.run (absStream s))) (hD : DescRel UF d) :
    Refines f (sudo_rs.sudoers.basic_parser.expect_nonterminal P UF s)
      ((SudoersSpec.Syntax.expectNonterminal d p).run (absStream s)) := by
  obtain ⟨sd, hsd, hsdv⟩ := hD
  obtain ⟨r, s1, e1, hr, h1, a1⟩ := try_nonterminal_refines_at hP
  unfold sudo_rs.sudoers.basic_parser.expect_nonterminal
  simp only [SudoersSpec.Syntax.expectNonterminal, Parser.run_bind, Parser.run_getPos,
    Parser.run_observe, get_pos_eq', e1, bind_ok, uncurry_apply_pair]
  rcases hT : (SudoersSpec.Syntax.tryNonterminal p).run (absStream s) with ⟨r', s''⟩
  rw [hT] at hr a1
  subst a1
  rcases r with x | (⟨sp, k⟩ | _) <;> rcases r' with (⟨sp', k'⟩ | _) | a <;>
    simp_all [Parser.run_lift, Parser.run_fatalFrom]

theorem expect_nonterminal_refines {T α : Type} {P : sudo_rs.sudoers.basic_parser.Parse T}
    {UF : sudo_rs.sudoers.ast_names.UserFriendly T} {f : T → α} {p : Parser α} {d : String}
    (hP : ParseRefines P f p) (hD : DescRel UF d) {s : CS} (h : StreamOK s) :
    Refines f (sudo_rs.sudoers.basic_parser.expect_nonterminal P UF s)
      ((SudoersSpec.Syntax.expectNonterminal d p).run (absStream s)) :=
  expect_nonterminal_refines_at (hP.parse s h) hD

/-! ## The character after trailing whitespace

After a successful `TrailingWhitespace` (so after `skip_trailing_whitespace`, `try_syntax`,
`try_nonterminal` and `expect_nonterminal`), the next character, if any, is neither a blank nor
the escape character: the loop ends only when `LeadingWhitespace` stopped at a non-blank and
`eat_char('\\')` failed. -/

/-- The property of the stream left by a successful `TrailingWhitespace`. -/
def NoBlankNext (s : Stream) : Prop :=
  ∀ c, s.peek = some c → c ≠ ' ' ∧ c ≠ '\t' ∧ c ≠ '\\'

theorem skipWhile_peek {f : Char → Bool} {s : Stream} {c : Char}
    (h : (s.skipWhile f).peek = some c) : f c = false := by
  rw [Stream.peek, Stream.skipWhile_rest] at h
  generalize s.rest = l at h
  induction l with
  | nil => cases h
  | cons a l ih =>
    by_cases ha : f a = true
    · rw [List.dropWhile_cons_of_pos ha] at h; exact ih h
    · rw [List.dropWhile_cons_of_neg ha] at h
      simp only [List.head?_cons, Option.some.injEq] at h
      subst h; simpa using ha

theorem leadingWhitespace_snd (s : Stream) :
    (SudoersSpec.Syntax.leadingWhitespace.run s).2 = s.skipWhile isBlank := by
  rw [SudoersSpec.Syntax.leadingWhitespace_run]; split <;> rfl

theorem trailingWhitespace_ok_next {s s' : Stream} {u : Unit}
    (h : SudoersSpec.Syntax.trailingWhitespace.run s = (.ok u, s')) : NoBlankNext s' := by
  have key := Parser.loop_invariant SudoersSpec.Syntax.trailingWhitespaceBody_progressive
    (fun _ => True) (fun r s' => r.isOk = true → NoBlankNext s')
    (fun _ _ _ _ _ _ => trivial) ?_ ?_ () s trivial
  · have h' : (Parser.loop SudoersSpec.Syntax.trailingWhitespaceBody
        SudoersSpec.Syntax.trailingWhitespaceBody_progressive ()).run s = (.ok u, s') := h
    rw [h'] at key
    exact key rfl
  · intro st s0 b s1 _ hb _
    simp only [SudoersSpec.Syntax.trailingWhitespaceBody, Parser.run_bind, Parser.run_observe,
      Parser.run_eatChar, leadingWhitespace_snd] at hb
    cases he : ((s0.skipWhile isBlank).eatChar '\\').1 with
    | true =>
      simp only [he, ↓reduceIte, Parser.run_bind, Parser.run_eatChar] at hb
      cases hn : (((s0.skipWhile isBlank).eatChar '\\').2.eatChar '\n').1 <;>
        simp [hn, Parser.run_fatalHere] at hb
    | false =>
      simp only [he, Bool.false_eq_true, ↓reduceIte, Parser.run_pure, Prod.mk.injEq] at hb
      have hs := (Stream.eatChar_false (c := '\\') (s := s0.skipWhile isBlank)
        (s' := ((s0.skipWhile isBlank).eatChar '\\').2)).mp (by rw [← he])
      rw [← hb.2, hs.2]
      intro c hc
      have hb' := skipWhile_peek hc
      simp only [isBlank, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hb'
      refine ⟨hb'.2, hb'.1, ?_⟩
      rintro rfl; exact hs.1 hc
  · intro _ _ _ _ _ _ hok; simp [Except.isOk, Except.toBool] at hok

theorem skipTrailingWhitespace_ok_next {s s' : Stream} {u : Unit}
    (h : SudoersSpec.Syntax.skipTrailingWhitespace.run s = (.ok u, s')) : NoBlankNext s' := by
  simp only [SudoersSpec.Syntax.skipTrailingWhitespace, Parser.run_bind] at h
  rcases hT : SudoersSpec.Syntax.trailingWhitespace.run s with ⟨r, s1⟩
  rw [hT] at h
  rcases r with e | v <;> simp [Parser.run_pure] at h
  rw [← h]; exact trailingWhitespace_ok_next hT

theorem trySyntax_ok_next {c : Char} {s s' : Stream} {u : Unit}
    (h : (SudoersSpec.Syntax.trySyntax c).run s = (.ok u, s')) : NoBlankNext s' := by
  obtain ⟨b, s1, -, h⟩ := Parser.run_bind_eq_ok.mp h
  cases b with
  | false => simp at h
  | true => simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
            exact skipTrailingWhitespace_ok_next h

theorem tryNonterminal_ok_next {α : Type} {p : Parser α} {s s' : Stream} {a : α}
    (h : (SudoersSpec.Syntax.tryNonterminal p).run s = (.ok a, s')) : NoBlankNext s' := by
  obtain ⟨x, s1, -, h⟩ := Parser.run_bind_eq_ok.mp h
  obtain ⟨u, s2, h2, h⟩ := Parser.run_bind_eq_ok.mp h
  simp only [Parser.run_pure, Prod.mk.injEq] at h
  rw [← h.2]; exact skipTrailingWhitespace_ok_next h2

theorem expectNonterminal_ok_next {α : Type} {p : Parser α} {d : String} {s s' : Stream}
    {a : α} (h : (SudoersSpec.Syntax.expectNonterminal d p).run s = (.ok a, s')) :
    NoBlankNext s' := by
  simp only [SudoersSpec.Syntax.expectNonterminal, Parser.run_bind, Parser.run_getPos,
    Parser.run_observe] at h
  rcases hT : (SudoersSpec.Syntax.tryNonterminal p).run s with ⟨r, s1⟩
  rw [hT] at h
  rcases r with (⟨sp, k⟩ | _) | x <;> simp [Parser.run_lift, Parser.run_fatalFrom] at h
  obtain ⟨rfl, rfl⟩ := h
  exact tryNonterminal_ok_next hT

/-- **The extracted `skip_trailing_whitespace`, on success, leaves a stream whose next
character is neither a blank nor `\`.** -/
theorem skip_trailing_whitespace_ok_next {s : CS} (h : StreamOK s) :
    ∃ r s', sudo_rs.sudoers.basic_parser.skip_trailing_whitespace s = ok (r, s') ∧
      StreamOK s' ∧ (r = .Ok () → NoBlankNext (absStream s')) := by
  obtain ⟨r, s', e, hr, h', a⟩ := skip_trailing_whitespace_refines h
  refine ⟨r, s', e, h', fun hr' => ?_⟩
  subst hr'
  rcases hT : SudoersSpec.Syntax.skipTrailingWhitespace.run (absStream s) with ⟨r', s''⟩
  rw [hT] at hr a
  rcases r' with e' | ⟨⟩ <;> simp only [ResultRel] at hr
  rw [a]; exact skipTrailingWhitespace_ok_next hT

end SudoRsProofs.Parser
