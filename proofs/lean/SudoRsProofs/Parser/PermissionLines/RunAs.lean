import SudoRsProofs.Parser.PermissionLines.Users

/-!
# `RunAs`: the group list (`SpecList<Identifier>`) and the composition

`RunAs::parse` reads an optional `(`, a user list whose every error is discarded, an optional
`: group list`, and `)`. The user list needs `QuoteRoom` (a quoted user is re-parsed on a
temporary stream, `user_list_refines_of_meta`); the group list is `SpecList<Identifier>` and
needs nothing beyond `StreamOK`.

* `spec_list_identifier_refines` is the P1 `Qualified`/`Vec` composition for
  `Vec<Qualified<Meta<Identifier>>>`;
* `group_list_refines` wraps it in `try_nonterminal`;
* `run_as_refines_of_lists` composes a caller-supplied per-cursor user-list refinement
  (`absSpecList absUserSpecifier` of the `Vec`) with the group list and `expectSyntax ')'`.
  A discarded fatal user error leaves the cursor where the user list stopped, as in the
  extracted `unwrap_or_default`; a group `Reject` keeps the cursor after `:` and yields an
  empty group list, which is the reference `maybe`'s `none`.
-/

open Aeneas Aeneas.Std Result SudoersSpec

namespace SudoRsProofs.Parser

/-! ## The group list -/

/-- The exact `Parse` instance of `Meta<Identifier>` used by the group list. -/
abbrev metaIdentifierInst : sudo_rs.sudoers.basic_parser.Parse
    (sudo_rs.sudoers.tokens.Meta sudo_rs.sudoers.ast.Identifier) :=
  sudo_rs.sudoers.tokens.MetaIdentifier.Insts.Sudo_rsSudoersBasic_parserParse

/-- The exact `Parse` instance of `SpecList<Identifier> = Vec<Qualified<Meta<Identifier>>>`. -/
abbrev specListIdentifierInst :
    sudo_rs.sudoers.basic_parser.Parse
      (alloc.vec.Vec (RSpec sudo_rs.sudoers.ast.Identifier)) :=
  sudo_rs.alloc.vec.Vec.Insts.Sudo_rsSudoersBasic_parserParse
    (sudo_rs.sudoers.ast.Qualified.Insts.Sudo_rsSudoersBasic_parserParse
      sudo_rs.sudoers.tokens.MetaIdentifier.Insts.Sudo_rsSudoersBasic_parserParse
      (sudo_rs.sudoers.tokens.Meta.Insts.Sudo_rsSudoersAst_namesUserFriendly
        sudo_rs.sudoers.ast.Identifier.Insts.Sudo_rsSudoersAst_namesUserFriendly))
    (sudo_rs.sudoers.ast.Qualified.Insts.Sudo_rsSudoersBasic_parserMany
      (sudo_rs.sudoers.tokens.Meta.Insts.Sudo_rsSudoersBasic_parserMany
        sudo_rs.sudoers.ast.Identifier.Insts.Sudo_rsSudoersBasic_parserMany))
    (sudo_rs.sudoers.ast.Qualified.Insts.Sudo_rsSudoersAst_namesUserFriendly
      (sudo_rs.sudoers.tokens.Meta.Insts.Sudo_rsSudoersAst_namesUserFriendly
        sudo_rs.sudoers.ast.Identifier.Insts.Sudo_rsSudoersAst_namesUserFriendly))

/-- The extracted `RunAs` instance. -/
abbrev runAsInst : sudo_rs.sudoers.basic_parser.Parse sudo_rs.sudoers.ast.RunAs :=
  sudo_rs.sudoers.ast.RunAs.Insts.Sudo_rsSudoersBasic_parserParse

private abbrev emptyUsersVec : alloc.vec.Vec (RSpec sudo_rs.sudoers.ast.UserSpecifier) :=
  alloc.vec.Vec.new (RSpec sudo_rs.sudoers.ast.UserSpecifier)

private abbrev emptyGroupsVec : alloc.vec.Vec (RSpec sudo_rs.sudoers.ast.Identifier) :=
  alloc.vec.Vec.new (RSpec sudo_rs.sudoers.ast.Identifier)

private theorem absSpecList_emptyUsersVec :
    absSpecList absUserSpecifier emptyUsersVec.val = [] := rfl

/-- `impl Many for Identifier` has the default separator and limit. -/
theorem identifier_many :
    ManyRefines sudo_rs.sudoers.ast.Identifier.Insts.Sudo_rsSudoersBasic_parserMany
      Syntax.identifierMany :=
  ⟨by simp [sudo_rs.sudoers.basic_parser.Many.SEP.default, Syntax.identifierMany],
    ⟨_, rfl, by
      simp [sudo_rs.sudoers.basic_parser.Many.LIMIT.default, Syntax.identifierMany]⟩⟩

/-- **`SpecList<Identifier>` refines `specListIdentifier`** from a refining
`Meta<Identifier>`. No `QuoteRoom` is needed: no quoted token enters the group list. -/
theorem spec_list_identifier_refines {O : Syntax.Oracles}
    (hMeta : ParseRefines metaIdentifierInst (absMeta absIdentifier)
      (Syntax.metaIdentifier O Syntax.Descriptions.release)) :
    ParseRefines specListIdentifierInst
      (fun v : alloc.vec.Vec (RSpec sudo_rs.sudoers.ast.Identifier) =>
        absSpecList absIdentifier v.val)
      (Syntax.specListIdentifier O Syntax.Descriptions.release) :=
  vec_refines
    (qualified_refines hMeta (desc_meta identifier_description))
    (many_qualified (many_meta identifier_many))
    (desc_qualified (desc_meta identifier_description))

/-- The group list behind its `try_nonterminal`. -/
theorem group_list_refines {O : Syntax.Oracles}
    (hMeta : ParseRefines metaIdentifierInst (absMeta absIdentifier)
      (Syntax.metaIdentifier O Syntax.Descriptions.release)) {s : CS} (hs : StreamOK s) :
    Refines (fun v : alloc.vec.Vec (RSpec sudo_rs.sudoers.ast.Identifier) =>
        absSpecList absIdentifier v.val)
      (sudo_rs.sudoers.basic_parser.try_nonterminal specListIdentifierInst s)
      ((Syntax.tryNonterminal (Syntax.specListIdentifier O Syntax.Descriptions.release)).run
        (absStream s)) :=
  try_nonterminal_refines (spec_list_identifier_refines hMeta) hs

/-! ## The part after the user list -/

/-- `RunAs::parse` after the user list: the optional `: group list` and the closing `')'`.
This is the generated body from the `try_syntax ':'` down, with `users` fixed. -/
private def runAsTail (users : alloc.vec.Vec (RSpec sudo_rs.sudoers.ast.UserSpecifier))
    (s : CS) : Result (RParsed sudo_rs.sudoers.ast.RunAs × CS) := do
  let (r2, stream3) ← sudo_rs.sudoers.basic_parser.try_syntax ':' s
  match r2 with
  | core.result.Result.Ok _ =>
    let (r3, stream4) ←
      sudo_rs.sudoers.basic_parser.try_nonterminal specListIdentifierInst stream3
    match r3 with
    | core.result.Result.Ok groups =>
      let (r4, stream5) ← sudo_rs.sudoers.basic_parser.expect_syntax ')' stream4
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r4
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let r5 ← sudo_rs.sudoers.basic_parser.make
          ({ users, groups } : sudo_rs.sudoers.ast.RunAs)
        ok (r5, stream5)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r5 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            sudo_rs.sudoers.ast.RunAs
            (core.convert.FromSame sudo_rs.sudoers.basic_parser.Status) residual
        ok (r5, stream5)
    | core.result.Result.Err err =>
      match err with
      | sudo_rs.sudoers.basic_parser.Status.Fatal _ _ =>
        ok (core.result.Result.Err err, stream4)
      | sudo_rs.sudoers.basic_parser.Status.Reject =>
        let (r4, stream5) ← sudo_rs.sudoers.basic_parser.expect_syntax ')' stream4
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r4
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          let r5 ← sudo_rs.sudoers.basic_parser.make
            ({ users, groups := emptyGroupsVec } : sudo_rs.sudoers.ast.RunAs)
          ok (r5, stream5)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r5 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              sudo_rs.sudoers.ast.RunAs
              (core.convert.FromSame sudo_rs.sudoers.basic_parser.Status) residual
          ok (r5, stream5)
  | core.result.Result.Err err =>
    match err with
    | sudo_rs.sudoers.basic_parser.Status.Fatal _ _ =>
      ok (core.result.Result.Err err, stream3)
    | sudo_rs.sudoers.basic_parser.Status.Reject =>
      let (r3, stream4) ← sudo_rs.sudoers.basic_parser.expect_syntax ')' stream3
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r3
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let r4 ← sudo_rs.sudoers.basic_parser.make
          ({ users, groups := emptyGroupsVec } : sudo_rs.sudoers.ast.RunAs)
        ok (r4, stream4)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r4 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            sudo_rs.sudoers.ast.RunAs
            (core.convert.FromSame sudo_rs.sudoers.basic_parser.Status) residual
        ok (r4, stream4)

/-- The reference tail after the user list, for the abstracted users `usersAbs`. -/
private def refRunAsTail (O : Syntax.Oracles) (usersAbs : SpecList UserSpecifier) :
    Syntax.Parser RunAs := do
  let groups ← Syntax.Parser.maybe (do
    Syntax.trySyntax ':'
    Syntax.tryNonterminal (Syntax.specListIdentifier O Syntax.Descriptions.release))
  Syntax.expectSyntax ')'
  pure ⟨usersAbs, groups.getD []⟩

set_option maxHeartbeats 1000000 in
/-- **The tail refines.** The `:` and the group list are exact; a fatal group error ends the
parse at the cursor after the group attempt, a rejected group list is `none` and keeps that
cursor for the closing `)`, and the two extracted `)` failures become the reference's error. -/
private theorem runAsTail_refines {O : Syntax.Oracles}
    (hMeta : ParseRefines metaIdentifierInst (absMeta absIdentifier)
      (Syntax.metaIdentifier O Syntax.Descriptions.release))
    (users : alloc.vec.Vec (RSpec sudo_rs.sudoers.ast.UserSpecifier))
    (usersAbs : SpecList UserSpecifier)
    (hAbsUsers : absSpecList absUserSpecifier users.val = usersAbs)
    {s : CS} (hs : StreamOK s) :
    Refines absRunAs (runAsTail users s) ((refRunAsTail O usersAbs).run (absStream s)) := by
  obtain ⟨r2, s3, e3, hrel2, h3, a3⟩ := try_syntax_refines hs ':'
  rcases hC : (Syntax.trySyntax ':').run (absStream s) with ⟨r2', t3⟩
  rw [hC] at hrel2 a3
  simp only at a3
  subst t3
  simp only [runAsTail, refRunAsTail, Syntax.Parser.run_bind, Syntax.Parser.run_maybe,
    e3, hC, bind_ok, uncurry_apply_pair]
  rcases r2 with u2 | (⟨sp2, k2⟩ | _) <;> rcases r2' with e2' | ⟨⟩ <;>
    simp only [ResultRel] at hrel2
  · -- the colon was consumed
    simp only []
    obtain ⟨r3, s4, e4, hrel3, h4, a4⟩ := group_list_refines hMeta h3
    rcases hG : (Syntax.tryNonterminal (Syntax.specListIdentifier O Syntax.Descriptions.release)).run
      (absStream s3) with ⟨r3', t4⟩
    rw [hG] at hrel3 a4
    simp only at a4
    subst t4
    simp only [e4, bind_ok, uncurry_apply_pair]
    rcases r3 with vg | (⟨sp3, k3⟩ | _) <;> rcases r3' with e3' | lg <;>
      simp only [ResultRel] at hrel3
    · -- the group list was read
      simp only [Syntax.maybe_ok]
      obtain ⟨r4, s5, e5, hrel4, h5, a5⟩ := expect_syntax_refines h4 ')'
      rcases hE : (Syntax.expectSyntax ')').run (absStream s4) with ⟨r4', t5⟩
      rw [hE] at hrel4 a5
      simp only at a5
      subst t5
      simp only [e5, bind_ok, uncurry_apply_pair]
      rcases r4 with u4 | (⟨sp4, k4⟩ | _) <;> rcases r4' with e4' | ⟨⟩ <;>
        simp only [ResultRel] at hrel4
      · simp only [branch_Ok, bind_ok, make_eq]
        simp [refines_ok_iff, ResultRel, absRunAs, hAbsUsers, hrel3, h5]
      · simp only [branch_Err, from_residual_Err, bind_ok]
        simp [refines_ok_iff, ResultRel, hrel4, h5]
      · simp only [branch_Err, from_residual_Err, bind_ok]
        simp [refines_ok_iff, ResultRel, hrel4, h5]
    · -- a fatal error of the group list ends the parse there
      rcases e3' with ⟨sp', k'⟩ | _
      · simp [refines_ok_iff, ResultRel, Syntax.maybe_fatal, hrel3, h4]
      · cases hrel3
    · -- a rejected group list is `none`; the closing `)` follows at the same cursor
      cases hrel3
      obtain ⟨r4, s5, e5, hrel4, h5, a5⟩ := expect_syntax_refines h4 ')'
      rcases hE : (Syntax.expectSyntax ')').run (absStream s4) with ⟨r4', t5⟩
      rw [hE] at hrel4 a5
      simp only at a5
      subst t5
      simp only [e5, hE, Syntax.maybe_reject, bind_ok,
        uncurry_apply_pair]
      rcases r4 with u4 | (⟨sp4, k4⟩ | _) <;> rcases r4' with e4' | ⟨⟩ <;>
        simp only [ResultRel] at hrel4
      · simp only [branch_Ok, bind_ok, make_eq]
        simp [refines_ok_iff, ResultRel, absRunAs, hAbsUsers, h5]
      · simp only [branch_Err, from_residual_Err, bind_ok]
        simp [refines_ok_iff, ResultRel, hrel4, h5]
      · simp only [branch_Err, from_residual_Err, bind_ok]
        simp [refines_ok_iff, ResultRel, hrel4, h5]
  · -- a fatal error of `:` ends the parse there
    rcases e2' with ⟨sp', k'⟩ | _
    · simp [refines_ok_iff, ResultRel, Syntax.maybe_fatal, hrel2, h3]
    · cases hrel2
  · -- `:` rejected: the closing `)` follows at the same cursor and there are no groups
    cases hrel2
    obtain ⟨r4, s4, e4, hrel4, h4, a4⟩ := expect_syntax_refines h3 ')'
    rcases hE : (Syntax.expectSyntax ')').run (absStream s3) with ⟨r4', t4⟩
    rw [hE] at hrel4 a4
    simp only at a4
    subst t4
    simp only [e4, hE, Syntax.maybe_reject, bind_ok,
      uncurry_apply_pair]
    rcases r4 with u4 | (⟨sp4, k4⟩ | _) <;> rcases r4' with e4' | ⟨⟩ <;>
      simp only [ResultRel] at hrel4
    · simp only [branch_Ok, bind_ok, make_eq]
      simp [refines_ok_iff, ResultRel, absRunAs, hAbsUsers, h4]
    · simp only [branch_Err, from_residual_Err, bind_ok]
      simp [refines_ok_iff, ResultRel, hrel4, h4]
    · simp only [branch_Err, from_residual_Err, bind_ok]
      simp [refines_ok_iff, ResultRel, hrel4, h4]

/-! ## `RunAs` -/

set_option maxHeartbeats 1000000 in
/-- **`RunAs::parse` refines `runAs`** for any per-cursor refinement of the user list (with
`QuoteRoom`, the side condition of the quoted-user case) and a refining `Meta<Identifier>`.
The default user vector after a discarded error is `[]`, and a fatal user error still leaves
the cursor at the user list's stop, matching `observe`. -/
theorem run_as_refines_of_lists {O : Syntax.Oracles}
    (hUsers : ∀ s, StreamOK s → QuoteRoom (absStream s) →
      Refines (fun v : alloc.vec.Vec (RSpec sudo_rs.sudoers.ast.UserSpecifier) =>
          absSpecList absUserSpecifier v.val)
        (sudo_rs.sudoers.ast.user_list s)
        ((Syntax.tryNonterminal (Syntax.specListUserSpecifier O Syntax.Descriptions.release)).run
          (absStream s)))
    (hMeta : ParseRefines metaIdentifierInst (absMeta absIdentifier)
      (Syntax.metaIdentifier O Syntax.Descriptions.release)) :
    ParseRefinesOn QuoteRoom runAsInst absRunAs
      (Syntax.runAs O Syntax.Descriptions.release) := by
  intro s hs hq
  obtain ⟨r, s1, e1, hrel, h1, a1⟩ := try_syntax_refines hs '('
  have hq1 := quoteRoom_stable.after hq (Syntax.trySyntax '(') a1
  obtain ⟨ru, s2, e2, hrelu, h2, a2⟩ := hUsers s1 h1 hq1
  rcases hR : (Syntax.trySyntax '(').run (absStream s) with ⟨r', t1⟩
  rw [hR] at hrel a1
  simp only at a1
  subst t1
  rcases hU : (Syntax.tryNonterminal
      (Syntax.specListUserSpecifier O Syntax.Descriptions.release)).run (absStream s1)
    with ⟨r1', t2⟩
  rw [hU] at hrelu a2
  simp only at a2
  subst t2
  change Refines absRunAs
    (sudo_rs.sudoers.ast.RunAs.Insts.Sudo_rsSudoersBasic_parserParse.parse s) _
  simp only [sudo_rs.sudoers.ast.RunAs.Insts.Sudo_rsSudoersBasic_parserParse.parse,
    Syntax.runAs, Syntax.Parser.run_bind, e1, hR, bind_ok, uncurry_apply_pair]
  rcases r with u | (⟨sp, k⟩ | _) <;> rcases r' with e' | ⟨⟩ <;>
    simp only [ResultRel] at hrel
  · -- `(` accepted: reduce the observed user list now that the branch is selected
    simp only [branch_Ok, bind_ok, uncurry_apply_pair,
      Syntax.Parser.run_observe, e2, hU]
    rcases ru with uu | (⟨spu, ku⟩ | _) <;> rcases r1' with eu | lu <;>
      simp only [ResultRel] at hrelu
    · simp only [bind_ok]
      exact runAsTail_refines hMeta uu lu hrelu h2
    · simp only [bind_ok]
      exact runAsTail_refines hMeta emptyUsersVec [] absSpecList_emptyUsersVec h2
    · simp only [bind_ok]
      exact runAsTail_refines hMeta emptyUsersVec [] absSpecList_emptyUsersVec h2
  · -- a fatal error of `(`
    simp only [branch_Err, from_residual_Err, bind_ok]
    simp [refines_ok_iff, ResultRel, hrel, h1]
  · -- a rejected `(`: the reference propagates the same `Reject`
    simp only [branch_Err, from_residual_Err, bind_ok]
    simp [refines_ok_iff, ResultRel, hrel, h1]

end SudoRsProofs.Parser
