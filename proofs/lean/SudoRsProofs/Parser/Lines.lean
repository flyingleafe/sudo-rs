import SudoRsProofs.Parser.Combinators

/-!
# `basic_parser.rs`: `line_follows` and `parse_lines`

* `line_follows_eq`: `line_follows` returns whether `LeadingWhitespace::parse` succeeded, with
  the stream it left (`leadingWhitespace`).
* `parse_lines_item_eq`: the body of the loop of `parse_lines`, from the item to the stream
  before the next `line_follows`, refines `parseLinesItem`; it pushes at most two results.
* `parse_lines_loop_eq`: the loop refines `loop (parseLinesBody d p)`. The Rust loop calls
  `line_follows` before the loop and at the end of each iteration, the reference runs
  `leadingWhitespace` at the start of each iteration: the lemma starts from the stream before
  `line_follows`. Every iteration pushes at most two results and consumes a character, so
  `v.len + 2 * rest.length ≤ usize::MAX` is an invariant that keeps `Vec::push` from failing.
* `parse_lines_refines`: `parse_lines` refines `parseLines`.
-/

open Aeneas Aeneas.Std Result
open SudoersSpec.Syntax (Stream ErrKind Parser Parsed)

namespace SudoRsProofs.Parser

/-! ## `line_follows` -/

theorem line_follows_eq {s : CS} (h : StreamOK s) :
    ∃ s', sudo_rs.sudoers.basic_parser.line_follows s =
        ok ((SudoersSpec.Syntax.leadingWhitespace.run (absStream s)).1.isOk, s') ∧
      StreamOK s' ∧ absStream s' = (SudoersSpec.Syntax.leadingWhitespace.run (absStream s)).2 := by
  obtain ⟨r, s1, e1, hr, h1, a1⟩ := leading_ws_refines h
  unfold sudo_rs.sudoers.basic_parser.line_follows
  rw [e1, bind_ok, uncurry_apply_pair]
  rcases hL : SudoersSpec.Syntax.leadingWhitespace.run (absStream s) with ⟨r', s''⟩
  rw [hL] at hr a1
  rcases r with ⟨⟩ | st <;> rcases r' with e' | ⟨⟩ <;> simp only [ResultRel] at hr
  · exact ⟨s1, rfl, h1, a1⟩
  · exact ⟨s1, rfl, h1, a1⟩

/-! ## One line -/

variable {T α : Type} {P : sudo_rs.sudoers.basic_parser.Parse T}
  {UF : sudo_rs.sudoers.ast_names.UserFriendly T} {f : T → α} {p : Parser α} {d : String}

theorem parse_lines_item_eq (hP : ParseRefines P f p) (hD : DescRel UF d) (s1 : CS)
    (h1 : StreamOK s1) (v : alloc.vec.Vec (RParsed T)) (acc : List (Parsed α))
    (hacc : List.Forall₂ (ResultRel f) v.val acc) (hv : v.val.length + 2 ≤ Usize.max) :
    ∃ (st' : CS) (v' : alloc.vec.Vec (RParsed T)) (acc' : List (Parsed α)),
      (∀ more s5, sudo_rs.sudoers.basic_parser.line_follows st' = ok (more, s5) →
        sudo_rs.sudoers.basic_parser.parse_lines_loop P UF s1 v true =
          sudo_rs.sudoers.basic_parser.parse_lines_loop P UF s5 v' more) ∧
      (SudoersSpec.Syntax.parseLinesItem d p acc).run (absStream s1) = (.ok acc', absStream st') ∧
      List.Forall₂ (ResultRel f) v'.val acc' ∧ StreamOK st' ∧ v'.val.length ≤ v.val.length + 2 := by
  obtain ⟨item, s2, e2, hr2, h2, a2⟩ := expect_nonterminal_refines hP hD h1
  obtain ⟨v1, hv1, hv1v⟩ := exists_eq_ok_of_spec (alloc.vec.Vec.push_spec v item (by omega))
  obtain ⟨rc, s3, e3, hrc, h3, a3⟩ := comment_refines h2
  obtain ⟨m, hm, -⟩ := maybe_rel hrc
  obtain ⟨s4, e4, h4, a4⟩ := eat_char_eq h3 '\n'
  rcases hE : (SudoersSpec.Syntax.expectNonterminal d p).run (absStream s1) with ⟨item', sE⟩
  rw [hE] at hr2 a2
  simp only at a2
  subst a2
  have hF1 : List.Forall₂ (ResultRel f) v1.val (acc ++ [item']) := by
    rw [hv1v]; exact List.rel_append hacc (List.Forall₂.cons hr2 List.Forall₂.nil)
  have hunf : sudo_rs.sudoers.basic_parser.parse_lines_loop P UF s1 v true =
      sudo_rs.sudoers.basic_parser.parse_lines_loop P UF s1 v true := rfl
  conv at hunf => rhs; rw [sudo_rs.sudoers.basic_parser.parse_lines_loop]
  simp only [↓reduceIte, e2, bind_ok, uncurry_apply_pair, hv1, e3, hm, e4] at hunf
  simp only [SudoersSpec.Syntax.parseLinesItem, Parser.run_bind, Parser.run_observe, hE,
    Parser.run_maybe, Parser.run_eatChar, ← a3, ← a4]
  cases hb : (Stream.eatChar '\n' (absStream s3)).1 with
  | true =>
    refine ⟨s4, v1, acc ++ [item'], ?_, rfl, hF1, h4, by rw [hv1v]; simp⟩
    intro more s5 hl
    rw [hunf, hb]
    cases item <;> simp only [↓reduceIte, bind_ok, uncurry_apply_pair, hl]
  | false =>
    obtain ⟨s5, e5, h5, a5⟩ := skip_to_newline_eq h4
    rcases item with x | st <;> rcases item' with e' | a <;> simp only [ResultRel] at hr2
    · -- a successful item without a line end: the error, then the rest of the line
      have hpk := peek_eq s4
      let msg : ErrKind := if (absStream s4).peek.isNone then .missingLineTerminator
        else .garbageAtEndOfLine
      let kind : RKind := if (absStream s4).peek.isNone then .MissingLineTerminator
        else .GarbageAtEndOfLine
      have hk : KindRel kind msg := by
        cases hp : (absStream s4).peek <;> simp [msg, kind, hp]
      obtain ⟨v2, hv2, hv2v⟩ := exists_eq_ok_of_spec (alloc.vec.Vec.push_spec v1
        (.Err (.Fatal ⟨(s4.line, s4.col), (s4.line, s4.col)⟩ kind)) (by rw [hv1v]; simp; omega))
      refine ⟨s5, v2, acc ++ [.ok a] ++
        [.error (.fatal ⟨(absStream s4).getPos, (absStream s4).getPos⟩ msg)], ?_, ?_, ?_, h5, ?_⟩
      · intro more s6 hl
        rw [hunf, hb]
        simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, hpk, fatal_here_eq]
        split <;> rename_i hp <;> simp only [kind, hp, Option.isNone_none, Option.isNone_some,
          ↓reduceIte, Bool.false_eq_true] at hv2 <;>
          simp only [bind_ok, hv2, e5, uncurry_apply_pair, hl]
      · simp [a5, msg, Except.isOk, Except.toBool, Parser.run_bind]
      · rw [hv2v]
        exact List.rel_append hF1 (List.Forall₂.cons (StatusRel.here hk) List.Forall₂.nil)
      · rw [hv2v, hv1v]; simp
    · -- a failed item: only the rest of the line is skipped
      refine ⟨s5, v1, acc ++ [.error e'], ?_, ?_, hF1, h5, by rw [hv1v]; simp⟩
      · intro more s6 hl
        rw [hunf, hb]
        simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, uncurry_apply_pair, e5, hl]
      · simp [a5, Except.isOk, Except.toBool, Parser.run_bind]

/-! ## The loop -/

/-- The reference loop of `parseLines` from the results `acc` collected so far. -/
abbrev refLinesLoop (d : String) (p : Parser α) (acc : List (Parsed α)) :
    Parser (List (Parsed α)) :=
  SudoersSpec.Syntax.Parser.loop (SudoersSpec.Syntax.parseLinesBody d p)
    (SudoersSpec.Syntax.parseLinesBody_progressive d p) acc

theorem parse_lines_loop_false (s : CS) (v : alloc.vec.Vec (RParsed T)) :
    sudo_rs.sudoers.basic_parser.parse_lines_loop P UF s v false =
      ok (s.src, s.pos, s.line, s.col, v) := by
  rw [sudo_rs.sudoers.basic_parser.parse_lines_loop]; simp

/-- The loop of `parse_lines`, from the stream `st` before `line_follows`: `line_follows st`
returned `(more, s1)`, the loop runs on `s1`. -/
theorem parse_lines_loop_eq (hP : ParseRefines P f p) (hD : DescRel UF d) (st : CS)
    (h : StreamOK st) (v : alloc.vec.Vec (RParsed T)) (acc : List (Parsed α))
    (hacc : List.Forall₂ (ResultRel f) v.val acc)
    (hb : v.val.length + 2 * (absStream st).rest.length ≤ Usize.max) (more : Bool) (s1 : CS)
    (hl : sudo_rs.sudoers.basic_parser.line_follows st = ok (more, s1)) :
    ∃ (v' : alloc.vec.Vec (RParsed T)) (s' : CS) (items : List (Parsed α)),
      sudo_rs.sudoers.basic_parser.parse_lines_loop P UF s1 v more =
        ok (s'.src, s'.pos, s'.line, s'.col, v') ∧
      (refLinesLoop d p acc).run (absStream st) = (.ok items, absStream s') ∧
      List.Forall₂ (ResultRel f) v'.val items ∧ StreamOK s' := by
  obtain ⟨s1', e1, h1, a1⟩ := line_follows_eq h
  rw [hl] at e1
  simp only [ok.injEq, Prod.mk.injEq] at e1
  obtain ⟨rfl, rfl⟩ := e1
  rw [SudoersSpec.Syntax.Parser.loop_run]
  simp only [SudoersSpec.Syntax.parseLinesBody, Parser.run_bind, Parser.run_observe]
  rcases hL : SudoersSpec.Syntax.leadingWhitespace.run (absStream st) with ⟨r, sl⟩
  rw [hL] at a1
  simp only at a1
  subst a1
  cases r with
  | error e =>
    exact ⟨v, s1, acc, parse_lines_loop_false s1 v, by simp, hacc, h1⟩
  | ok u =>
    have hne : (absStream s1).rest ≠ [] := SudoersSpec.Syntax.leadingWhitespace_ok hL
    have hlw : (absStream s1).rest.length ≤ (absStream st).rest.length := by
      have := SudoersSpec.Syntax.Parser.length_le SudoersSpec.Syntax.leadingWhitespace
        (absStream st)
      rwa [hL] at this
    have hpos : 0 < (absStream s1).rest.length := List.length_pos_iff.2 hne
    obtain ⟨st', v1, acc1, hrust, hitem, hF, h', hlen⟩ :=
      parse_lines_item_eq hP hD s1 h1 v acc hacc (by omega)
    have hlt := SudoersSpec.Syntax.parseLinesItem_lt hne hitem
    obtain ⟨s5, e5, -, -⟩ := line_follows_eq h'
    obtain ⟨v', s', items, eL, eR, hF', hS⟩ :=
      parse_lines_loop_eq hP hD st' h' v1 acc1 hF (by omega) _ s5 e5
    refine ⟨v', s', items, ?_, ?_, hF', hS⟩
    · show sudo_rs.sudoers.basic_parser.parse_lines_loop P UF s1 v true = _
      rw [hrust _ _ e5]; exact eL
    · simp only [Parser.run_bind, hitem, Parser.run_pure]
      exact eR
termination_by (absStream st).rest.length
decreasing_by omega

/-! ## `parse_lines` -/

/-- **`parse_lines` refines `parseLines`**: one result per line, the stream after the last line;
`hbound` keeps the `Vec::push`es (at most two per line, at least one character per line) within
`usize`. -/
theorem parse_lines_refines (hP : ParseRefines P f p) (hD : DescRel UF d) {s : CS}
    (h : StreamOK s) (hbound : 2 * (s.src.val.length - s.pos.val) ≤ Usize.max) :
    ∃ (v : alloc.vec.Vec (RParsed T)) (s' : CS) (items : List (Parsed α)),
      sudo_rs.sudoers.basic_parser.parse_lines P UF s = ok (v, s') ∧
      (SudoersSpec.Syntax.parseLines d p).run (absStream s) = (.ok items, absStream s') ∧
      List.Forall₂ (ResultRel f) v.val items ∧ StreamOK s' := by
  obtain ⟨s1, e1, -, -⟩ := line_follows_eq h
  obtain ⟨v', s', items, eL, eR, hF, hS⟩ :=
    parse_lines_loop_eq hP hD s h (alloc.vec.Vec.new _) [] (by simp) (by simpa using hbound) _ s1
      e1
  refine ⟨v', s', items, ?_, eR, hF, hS⟩
  unfold sudo_rs.sudoers.basic_parser.parse_lines
  rw [e1, bind_ok, uncurry_apply_pair, eL]
  simp only [bind_ok, uncurry_apply_pair]

/-- `parse_lines` on a whole input `src` (cursor at position 0, line 1, column 1): the only
precondition is the input length, `2 * len ≤ usize::MAX`. -/
theorem parse_lines_refines_text (hP : ParseRefines P f p) (hD : DescRel UF d)
    (src : Slice Char) (hlen : 2 * src.val.length ≤ Usize.max) :
    ∃ (v : alloc.vec.Vec (RParsed T)) (s' : CS) (items : List (Parsed α)),
      sudo_rs.sudoers.basic_parser.parse_lines P UF ⟨src, 0#usize, 1#usize, 1#usize⟩ =
        ok (v, s') ∧
      (SudoersSpec.Syntax.parseLines d p).run (Stream.new src.val) = (.ok items, absStream s') ∧
      List.Forall₂ (ResultRel f) v.val items ∧ StreamOK s' := by
  have hmax : 1 ≤ Usize.max := by scalar_tac
  exact parse_lines_refines hP hD (StreamOK.initial src (by omega)) (by simpa using hlen)

theorem forall₂_mem_left {β γ : Type} {R : β → γ → Prop} {l : List β} {l' : List γ}
    (h : List.Forall₂ R l l') {r : β} (hr : r ∈ l) : ∃ r' ∈ l', R r r' := by
  induction h with
  | nil => cases hr
  | cons hab _ ih =>
    rcases List.mem_cons.mp hr with rfl | hm
    · exact ⟨_, List.mem_cons_self .., hab⟩
    · obtain ⟨r', h1, h2⟩ := ih hm
      exact ⟨r', List.mem_cons_of_mem _ h1, h2⟩

/-- Results related elementwise to reference results contain no `ErrorKind::Message`. -/
theorem forall₂_not_message {l : List (RParsed T)} {l' : List (Parsed α)}
    (h : List.Forall₂ (ResultRel f) l l') :
    ∀ r ∈ l, ∀ sp m, r ≠ .Err (.Fatal sp (.Message m)) := by
  induction h with
  | nil => simp
  | cons hr _ ih =>
    intro r hmem
    rcases List.mem_cons.mp hmem with rfl | hm
    · exact hr.not_message
    · exact ih r hm

/-- **`parse_lines` yields no `Err(Reject)` and no `ErrorKind::Message`** (on every
representable stream within the bound): the first part transfers `parseLines_ok` of the
reference, so `panic!("internal parser error")` in `Sudoers::process` is unreachable for any
item production that refines a reference production. -/
theorem parse_lines_no_reject_no_message (hP : ParseRefines P f p) (hD : DescRel UF d) {s : CS}
    (h : StreamOK s) (hbound : 2 * (s.src.val.length - s.pos.val) ≤ Usize.max) :
    ∃ v s', sudo_rs.sudoers.basic_parser.parse_lines P UF s = ok (v, s') ∧
      ∀ r ∈ v.val, r ≠ .Err .Reject ∧ ∀ sp m, r ≠ .Err (.Fatal sp (.Message m)) := by
  obtain ⟨v, s', items, e, hrun, hF, -⟩ := parse_lines_refines (d := d) hP hD h hbound
  obtain ⟨items', hok, hne⟩ := SudoersSpec.Syntax.parseLines_ok d p (absStream s)
  rw [hrun] at hok
  simp only [Except.ok.injEq] at hok
  subst hok
  refine ⟨v, s', e, fun r hr => ⟨?_, forall₂_not_message hF r hr⟩⟩
  rintro rfl
  obtain ⟨r', hr', hrel⟩ := forall₂_mem_left hF hr
  rcases r' with (⟨sp', k'⟩ | _) | a <;> simp [ResultRel] at hrel
  exact hne _ hr' rfl

end SudoRsProofs.Parser
