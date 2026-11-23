import SudoRsProofs.Parser.PermissionLines.Common

/-! Command tags, qualification, and the extracted `CommandSpec` parser. -/

open Aeneas Aeneas.Std Result
open SudoersSpec
open SudoersSpec.Syntax (Stream Parser)

namespace SudoRsProofs.Parser

private theorem isSyntax_ok_next {c : Char} {s s' : Stream} {b : Bool}
    (hs : NoBlankNext s) (h : (Syntax.isSyntax c).run s = (.ok b, s')) : NoBlankNext s' := by
  simp only [Syntax.isSyntax, Parser.run_bind, Parser.run_maybe] at h
  rcases hT : (Syntax.trySyntax c).run s with ⟨r, s1⟩
  rw [hT] at h
  rcases r with (⟨sp, k⟩ | _) | ⟨⟩
  · simp [Syntax.maybe] at h
  · simp only [Syntax.maybe_reject, Parser.run_pure, Prod.mk.injEq] at h
    exact h.2 ▸ (Syntax.trySyntax_reject hT ▸ hs)
  · simp only [Syntax.maybe_ok, Parser.run_pure, Prod.mk.injEq] at h
    exact h.2 ▸ trySyntax_ok_next hT

private theorem refBangLoop_ok_next (neg : Bool) (s : Stream) (hs : NoBlankNext s)
    {neg' : Bool} {s' : Stream} (h : (refBangLoop neg).run s = (.ok neg', s')) :
    NoBlankNext s' := by
  unfold refBangLoop Parser.whileMaybe at h
  rw [Parser.loop_run] at h
  simp only [Parser.whileMaybeBody, Parser.run_bind, Parser.run_maybe] at h
  rcases hT : (Syntax.trySyntax '!').run s with ⟨r, s1⟩
  rw [hT] at h
  rcases r with (⟨sp, k⟩ | _) | ⟨⟩
  · simp [Syntax.maybe] at h
  · simp only [Syntax.maybe_reject, Parser.run_pure, Prod.mk.injEq] at h
    exact h.2 ▸ (Syntax.trySyntax_reject hT ▸ hs)
  · have hlt := Syntax.trySyntax_consumes '!' _ _ _ hT
    simp only [Syntax.maybe_ok, Parser.run_pure] at h
    exact refBangLoop_ok_next (!neg) s1 (trySyntax_ok_next hT) h
termination_by s.rest.length
decreasing_by simpa using hlt

/-- `Qualified<T>` preserves the leaf's input domain: either there is no `!` (no cursor
movement), or each successfully parsed `!` skips its trailing whitespace. -/
theorem qualified_refines_at {T α : Type} {P : sudo_rs.sudoers.basic_parser.Parse T}
    {UF : sudo_rs.sudoers.ast_names.UserFriendly T} {f : T → α} {p : Parser α} {d : String}
    (hP : ∀ s, StreamOK s → NoBlankNext (absStream s) →
      Refines f (P.parse s) (p.run (absStream s))) (hD : DescRel UF d)
    (s : CS) (hs : StreamOK s) (hn : NoBlankNext (absStream s)) :
    Refines (absQualified f)
      ((sudo_rs.sudoers.ast.Qualified.Insts.Sudo_rsSudoersBasic_parserParse P UF).parse s)
      ((Syntax.qualified d p).run (absStream s)) := by
  obtain ⟨r, s1, e1, hr, h1, a1⟩ := is_syntax_refines hs '!'
  change Refines _ (sudo_rs.sudoers.ast.Qualified.Insts.Sudo_rsSudoersBasic_parserParse.parse
    P UF s) _
  unfold sudo_rs.sudoers.ast.Qualified.Insts.Sudo_rsSudoersBasic_parserParse.parse
  simp only [Syntax.qualified, Parser.run_bind, e1, bind_ok, uncurry_apply_pair]
  rcases hR : (Syntax.isSyntax '!').run (absStream s) with ⟨r', s''⟩
  rw [hR] at hr a1
  subst a1
  rcases r with b | st <;> rcases r' with e' | b' <;> simp only [ResultRel] at hr
  · subst hr
    have hn1 := isSyntax_ok_next hn hR
    cases b with
    | true =>
      simp only [id_eq, ↓reduceIte, Parser.run_bind]
      obtain ⟨s2, neg, failure, e2, h2, hr2, a2⟩ := qualified_loop_eq s1 h1 true
      simp only [branch_Ok, ↓reduceIte, e2, bind_ok, uncurry_apply_pair]
      rcases hW : (refBangLoop true).run (absStream s1) with ⟨w, s3⟩
      rw [hW] at hr2 a2
      simp only at a2
      subst a2
      rcases failure with _ | st <;> rcases w with e3 | neg' <;> simp only [ResultRel] at hr2
      · subst hr2
        have hn2 := refBangLoop_ok_next true (absStream s1) hn1 hW
        obtain ⟨r4, s4, e4, hr4, h4, a4⟩ :=
          expect_nonterminal_refines_at (P := P) (p := p) (hP s2 h2 hn2) hD
        simp only [e4, bind_ok, uncurry_apply_pair]
        rcases hE : (Syntax.expectNonterminal d p).run (absStream s2) with ⟨r5, s5⟩
        rw [hE] at hr4 a4
        simp only at a4
        subst a4
        rcases r4 with x | st4 <;> rcases r5 with e5 | a <;> simp only [ResultRel] at hr4
        · cases neg <;> simp [h4, hr4, absQualified]
        · simp [h4, hr4]
      · simp [h2, hr2]
    | false =>
      simp only [id_eq, Bool.false_eq_true, ↓reduceIte, Parser.run_bind]
      obtain ⟨r4, s4, e4, hr4, h4, a4⟩ :=
        try_nonterminal_refines_at (P := P) (p := p) (hP s1 h1 hn1)
      simp only [branch_Ok, Bool.false_eq_true, ↓reduceIte, e4, bind_ok, uncurry_apply_pair]
      rcases hE : (Syntax.tryNonterminal p).run (absStream s1) with ⟨r5, s5⟩
      rw [hE] at hr4 a4
      subst a4
      rcases r4 with x | st4 <;> rcases r5 with e5 | a <;> simp only [ResultRel] at hr4
      · simp [h4, hr4, absQualified]
      · simp [h4, hr4]
  · simp [hr, h1]

/-! ## The tag loop -/

private abbrev refCommandTagInput (O : Syntax.Oracles) (D : Syntax.Descriptions) :=
  Syntax.tryNonterminal (Syntax.parseOption (Syntax.metaOrTag O D))

private theorem refCommandTagInput_consumes (O : Syntax.Oracles) (D : Syntax.Descriptions) :
    (refCommandTagInput O D).ConsumesSome :=
  Syntax.tryNonterminal_parseOption_consumesSome (Syntax.metaOrTag_consumes O D)

private abbrev refCommandTagStep (O : Syntax.Oracles) (D : Syntax.Descriptions) :=
  Parser.whileSomeBody (refCommandTagInput O D) Syntax.commandSpecBody Sum.inl

private abbrev refCommandTagLoop (O : Syntax.Oracles) (D : Syntax.Descriptions) :=
  Parser.whileSome (refCommandTagInput O D) (refCommandTagInput_consumes O D)
    Syntax.commandSpecBody Sum.inl

private abbrev RTags := alloc.vec.Vec sudo_rs.sudoers.ast.Modifier
private abbrev RMetaCommand := sudo_rs.sudoers.tokens.Meta RCommand
private abbrev CommandTagDone := List SudoersSpec.Modifier ⊕ SudoersSpec.CommandSpec

/-- Read the Rust `found` flag at loop exit: `none` triggers the fallback command parser;
`some` is a command completed by the tag parser (`ALL` or an alias). -/
private def absCommandTagDone (fc : RCommand → SudoersSpec.Command) (tags : RTags) :
    Option RMetaCommand → CommandTagDone
  | none => .inl (absVec absModifier tags)
  | some cmd => .inr (absCommandSpec fc (tags, .Allow cmd))

/-- The outer option encodes whether to run another tag iteration. -/
private def absCommandTagStep (fc : RCommand → SudoersSpec.Command) (tags : RTags) :
    Option (Option RMetaCommand) → Parser.Step (List SudoersSpec.Modifier) CommandTagDone
  | none => .next (absVec absModifier tags)
  | some cmd => .done (absCommandTagDone fc tags cmd)

private abbrev commandTagLimit :=
  sudo_rs.sudoers.basic_parser.Many.LIMIT.default sudo_rs.sudoers.ast.Identifier

private theorem commandTagLimit_val : commandTagLimit.val = Syntax.identifierMany.limit := by
  simp [commandTagLimit, sudo_rs.sudoers.basic_parser.Many.LIMIT.default, Syntax.identifierMany]

variable {O : Syntax.Oracles} {D : Syntax.Descriptions} {fc : RCommand → SudoersSpec.Command}

/-- One extracted iteration refines the reference tag-loop body. A continuing iteration
consumed input and stays within the tag bound. A fallback (`some none`) is only reached
through a successful optional nonterminal, which has already skipped trailing whitespace. -/
theorem command_tag_step_refines
    (hTag : ParseRefines sudo_rs.sudoers.ast.MetaOrTag.Insts.Sudo_rsSudoersBasic_parserParse
      (absMeta absModifier) (Syntax.metaOrTag O D))
    (hTooMany : KindRel .TooManyTags .tooManyTags)
    (s : CS) (hs : StreamOK s) (tags : RTags) (hcap : tags.val.length ≤ Syntax.identifierMany.limit) :
    ∃ (r : RParsed (Option (Option RMetaCommand))) (s' : CS) (tags' : RTags),
      sudo_rs.sudoers.ast.command_tag_step s tags = ok (r, s', tags') ∧ StreamOK s' ∧
      ResultRel (absCommandTagStep fc tags') r
        ((refCommandTagStep O D (absVec absModifier tags)).run (absStream s)).1 ∧
      absStream s' = ((refCommandTagStep O D (absVec absModifier tags)).run (absStream s)).2 ∧
      (r = .Ok none → tags'.val.length ≤ Syntax.identifierMany.limit ∧
        (absStream s').rest.length < (absStream s).rest.length) ∧
      (r = .Ok (some none) → NoBlankNext (absStream s')) := by
  obtain ⟨r, s1, e1, hr, h1, a1⟩ := try_nonterminal_refines (option_parse_refines hTag) hs
  unfold sudo_rs.sudoers.ast.command_tag_step refCommandTagStep Parser.whileSomeBody
  simp only [e1, bind_ok, uncurry_apply_pair, Parser.run_bind]
  rcases hR : (refCommandTagInput O D).run (absStream s) with ⟨r', s''⟩
  rw [hR] at hr a1
  subst a1
  rcases r with o | e <;> rcases r' with e' | o' <;> simp only [ResultRel] at hr
  · subst o'
    rcases o with _ | kw
    · refine ⟨.Ok (some none), s1, tags, by simp, h1, rfl, rfl, by simp, ?_⟩
      intro _
      exact tryNonterminal_ok_next hR
    · change sudo_rs.sudoers.tokens.Meta sudo_rs.sudoers.ast.Modifier at kw
      cases kw with
      | All =>
        exact ⟨.Ok (some (some .All)), s1, tags, by simp, h1, rfl, rfl, by simp, by simp⟩
      | Alias aliasName =>
        exact ⟨.Ok (some (some (.Alias aliasName))), s1, tags, by simp, h1, rfl, rfl,
          by simp, by simp⟩
      | Only m =>
        have hlim : Syntax.identifierMany.limit < Usize.max := by
          change 127 < Usize.max
          scalar_tac
        obtain ⟨tags1, hpush, hpv⟩ := exists_eq_ok_of_spec
          (alloc.vec.Vec.push_spec tags m (Nat.lt_of_le_of_lt hcap hlim))
        have habs : absVec absModifier tags1 = absVec absModifier tags ++ [absModifier m] := by
          simp [absVec, hpv]
        have hgt : alloc.vec.Vec.len tags1 > commandTagLimit ↔
            (absVec absModifier tags ++ [absModifier m]).length > Syntax.identifierMany.limit := by
          rw [← habs]
          change commandTagLimit < alloc.vec.Vec.len tags1 ↔
            Syntax.identifierMany.limit < (absVec absModifier tags1).length
          rw [UScalar.lt_equiv]
          simp only [commandTagLimit_val, alloc.vec.Vec.len_val, absVec, List.length_map, iff_self]
        by_cases hfull : (absVec absModifier tags ++ [absModifier m]).length >
            Syntax.identifierMany.limit
        · have hrust := hgt.mpr hfull
          refine ⟨.Err (.Fatal ⟨(s1.line, s1.col), (s1.line, s1.col)⟩ .TooManyTags),
            s1, tags1, ?_, h1, ?_, ?_, by simp, by simp⟩
          · simp only [branch_Ok, bind_ok, hpush, hrust, ↓reduceIte, fatal_here_eq]
          · simp only [Option.map_some, absMeta, Syntax.commandSpecBody, hfull, ↓reduceIte,
              Parser.run_fatalHere, ResultRel]
            exact StatusRel.here (s := s1) hTooMany
          · simp only [Option.map_some, absMeta, Syntax.commandSpecBody, hfull, ↓reduceIte,
              Parser.run_fatalHere]
        · have hrust : ¬ alloc.vec.Vec.len tags1 > commandTagLimit := fun h => hfull (hgt.mp h)
          have hbound : tags1.val.length ≤ Syntax.identifierMany.limit := by
            rw [← habs, absVec, List.length_map] at hfull
            exact Nat.le_of_not_gt hfull
          have hlt := refCommandTagInput_consumes O D _ _ _ hR
          refine ⟨.Ok none, s1, tags1, ?_, h1, ?_, ?_, fun _ => ⟨hbound, hlt⟩, by simp⟩
          · simp only [branch_Ok, bind_ok, hpush, hrust, ↓reduceIte, make_eq]
          · simp only [Option.map_some, absMeta, Syntax.commandSpecBody, hfull, ↓reduceIte,
              Parser.run_pure, ResultRel, absCommandTagStep, habs]
          · simp only [Option.map_some, absMeta, Syntax.commandSpecBody, hfull, ↓reduceIte,
              Parser.run_pure]
  · exact ⟨.Err e, s1, tags, by simp, h1, hr, rfl, by simp, by simp⟩

private theorem command_spec_loop_false (s : CS) (tags : RTags) (failure : Option RStatus)
    (found : Option RMetaCommand) :
    sudo_rs.sudoers.ast.CommandSpec.Insts.Sudo_rsSudoersBasic_parserParse.parse_loop
      s tags failure found false = ok (s.src, s.pos, s.line, s.col, tags, failure, found) := by
  rw [sudo_rs.sudoers.ast.CommandSpec.Insts.Sudo_rsSudoersBasic_parserParse.parse_loop]
  simp

/-- The generated flag-based loop and `whileSome` agree on the final tags, command or error,
and cursor. If the loop requests a fallback, the next command starts at a clean cursor. -/
theorem command_spec_loop_eq
    (hTag : ParseRefines sudo_rs.sudoers.ast.MetaOrTag.Insts.Sudo_rsSudoersBasic_parserParse
      (absMeta absModifier) (Syntax.metaOrTag O D))
    (hTooMany : KindRel .TooManyTags .tooManyTags)
    (s : CS) (hs : StreamOK s) (tags : RTags) (hcap : tags.val.length ≤ Syntax.identifierMany.limit) :
    ∃ (s' : CS) (tags' : RTags) (failure : Option RStatus) (found : Option RMetaCommand),
      sudo_rs.sudoers.ast.CommandSpec.Insts.Sudo_rsSudoersBasic_parserParse.parse_loop
        s tags none none true = ok (s'.src, s'.pos, s'.line, s'.col, tags', failure, found) ∧
      StreamOK s' ∧
      ResultRel (absCommandTagDone fc tags') (match failure with
        | none => .Ok found
        | some err => .Err err) ((refCommandTagLoop O D (absVec absModifier tags)).run (absStream s)).1 ∧
      absStream s' = ((refCommandTagLoop O D (absVec absModifier tags)).run (absStream s)).2 ∧
      (failure = none → found = none → NoBlankNext (absStream s')) := by
  obtain ⟨r, s1, tags1, e1, h1, hr, a1, hnext, hblank⟩ :=
    command_tag_step_refines (fc := fc) hTag hTooMany s hs tags hcap
  rw [sudo_rs.sudoers.ast.CommandSpec.Insts.Sudo_rsSudoersBasic_parserParse.parse_loop]
  simp only [↓reduceIte, e1, bind_ok, uncurry_apply_pair]
  unfold refCommandTagLoop Parser.whileSome
  rw [Parser.loop_run]
  rcases hR : (refCommandTagStep O D (absVec absModifier tags)).run (absStream s) with ⟨r', s''⟩
  rw [hR] at hr a1
  subst a1
  rcases r with o | e <;> rcases r' with e' | step <;> simp only [ResultRel] at hr
  · subst step
    rcases o with _ | cmd
    · obtain ⟨hcap1, hlt⟩ := hnext rfl
      exact command_spec_loop_eq hTag hTooMany s1 h1 tags1 hcap1
    · refine ⟨s1, tags1, none, cmd, by simp [command_spec_loop_false], h1, rfl, rfl, ?_⟩
      rintro _ rfl
      exact hblank rfl
  · refine ⟨s1, tags1, some e, none, by simp [command_spec_loop_false], h1, hr, rfl, by simp⟩
termination_by (absStream s).rest.length
decreasing_by simpa using hlt

/-! ## The command fallback and `CommandSpec::parse` -/

/-- The exact `Meta<Command>` instance used by the fallback. -/
abbrev metaCommandParseInst : sudo_rs.sudoers.basic_parser.Parse
    (sudo_rs.sudoers.tokens.Meta RCommand) :=
  sudo_rs.sudoers.basic_parser.Parse.Blanket
    (sudo_rs.sudoers.tokens.Meta.Insts.Sudo_rsSudoersBasic_parserToken
      sudo_rs.PairPatternArgs.Insts.Sudo_rsSudoersBasic_parserToken)

private abbrev metaCommandDescription :=
  sudo_rs.sudoers.tokens.Meta.Insts.Sudo_rsSudoersAst_namesUserFriendly
    sudo_rs.PairPatternArgs.Insts.Sudo_rsSudoersAst_namesUserFriendly

private abbrev specCommandParseInst :=
  sudo_rs.sudoers.ast.Qualified.Insts.Sudo_rsSudoersBasic_parserParse
    metaCommandParseInst metaCommandDescription

theorem command_description :
    DescRel sudo_rs.PairPatternArgs.Insts.Sudo_rsSudoersAst_namesUserFriendly
      Syntax.Descriptions.release.command :=
  ⟨_, rfl, by
    simp only [sudo_rs.PairPatternArgs.Insts.Sudo_rsSudoersAst_namesUserFriendly.DESCRIPTION]
    exact toStr_val _ _⟩

/-- The complete extracted `CommandSpec::parse` refines the reference on every `StreamOK`
cursor. Only the `Meta<Command>` leaf requires `NoBlankNext`: the tag loop supplies it on
fallback and `Qualified` maintains it until the leaf is called. -/
theorem command_spec_refines
    (hTag : ParseRefines sudo_rs.sudoers.ast.MetaOrTag.Insts.Sudo_rsSudoersBasic_parserParse
      (absMeta absModifier) (Syntax.metaOrTag O D))
    (hCmd : ∀ s, StreamOK s → NoBlankNext (absStream s) →
      Refines (absMeta fc) (metaCommandParseInst.parse s)
        ((Syntax.token (Syntax.metaToken O.char (Syntax.commandToken O))).run (absStream s)))
    (hD : DescRel sudo_rs.PairPatternArgs.Insts.Sudo_rsSudoersAst_namesUserFriendly D.command)
    (hTooMany : KindRel .TooManyTags .tooManyTags) :
    ParseRefines sudo_rs.sudoers.ast.CommandSpec.Insts.Sudo_rsSudoersBasic_parserParse
      (absCommandSpec fc) (Syntax.commandSpec O D) := by
  constructor
  intro s hs
  obtain ⟨s1, tags, failure, found, he, h1, hr, a1, hBlank⟩ :=
    command_spec_loop_eq (fc := fc) hTag hTooMany s hs (alloc.vec.Vec.new _) (by simp)
  change Refines _ (sudo_rs.sudoers.ast.CommandSpec.Insts.Sudo_rsSudoersBasic_parserParse.parse s) _
  unfold sudo_rs.sudoers.ast.CommandSpec.Insts.Sudo_rsSudoersBasic_parserParse.parse
  simp only [he, bind_ok, uncurry_apply_pair, Syntax.commandSpec, Parser.run_bind]
  have hNil : absVec absModifier (alloc.vec.Vec.new _) = [] := rfl
  rw [hNil] at hr a1
  rcases hW : (refCommandTagLoop O D []).run (absStream s) with ⟨w, s'⟩
  rw [hW] at hr a1
  subst a1
  rcases failure with _ | e <;> rcases w with e' | cmd <;> simp only [ResultRel] at hr
  · subst cmd
    rcases found with _ | cmd
    · simp only [absCommandTagDone, Parser.run_bind]
      have hSpec : Refines (absSpec fc) (specCommandParseInst.parse s1)
          ((Syntax.specCommand O D).run (absStream s1)) :=
        qualified_refines_at hCmd (desc_meta hD) s1 h1 (hBlank rfl rfl)
      obtain ⟨r2, s2, e2, hr2, h2, a2⟩ :=
        expect_nonterminal_refines_at (P := specCommandParseInst)
          (p := Syntax.specCommand O D) hSpec (desc_qualified (desc_meta hD))
      simp only [e2, bind_ok, uncurry_apply_pair]
      rcases hE : (Syntax.expectNonterminal D.command (Syntax.specCommand O D)).run
          (absStream s1) with ⟨r2', s3⟩
      rw [hE] at hr2 a2
      simp only at a2
      subst a2
      rcases r2 with x | err <;> rcases r2' with err' | a <;> simp only [ResultRel] at hr2
      · refine ⟨.Ok (tags, x), s2, ?_, ?_, h2, rfl⟩
        · simp only [branch_Ok, bind_ok, make_eq]; rfl
        · change absCommandSpec fc (tags, x) = ⟨absVec absModifier tags, a⟩
          exact congrArg (SudoersSpec.CommandSpec.mk (absVec absModifier tags)) hr2
      · simp [h2, hr2]
    · refine ⟨.Ok (tags, .Allow cmd), s1, ?_, rfl, h1, rfl⟩
      simp only [make_eq, bind_ok]; rfl
  · simp [h1, hr]

end SudoRsProofs.Parser
