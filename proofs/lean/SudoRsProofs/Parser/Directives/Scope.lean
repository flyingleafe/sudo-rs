import SudoRsProofs.Parser.Directives.Cursor
import SudoRsProofs.Parser.Directives.Keywords
import SudoRsProofs.Parser.Directives.Composition
import SudoRsProofs.Parser.PermissionLines.UserLists

/-! Stable `defaults_scope`. A host scope restores the saved stream before advancing; the
other scope markers use the current stream. Command scopes use the existing path and glob oracles. -/

open Aeneas Aeneas.Std Result SudoersSpec
open sudo_rs
open sudo_rs.sudoers.ast (ConfigScope Qualified)
open Aeneas.Std.alloc.vec (Vec)

noncomputable section

namespace SudoRsProofs.Parser

private abbrev D := Syntax.Descriptions.release
private abbrev scopeUserUF := alloc.vec.Vec.Insts.Sudo_rsSudoersAst_namesUserFriendly
  (Qualified.Insts.Sudo_rsSudoersAst_namesUserFriendly
    (sudoers.tokens.Meta.Insts.Sudo_rsSudoersAst_namesUserFriendly userSpecifierUF))
private abbrev scopeHostUF := alloc.vec.Vec.Insts.Sudo_rsSudoersAst_namesUserFriendly
  (Qualified.Insts.Sudo_rsSudoersAst_namesUserFriendly
    (sudoers.tokens.Meta.Insts.Sudo_rsSudoersAst_namesUserFriendly
      sudoers.tokens.Hostname.Insts.Sudo_rsSudoersAst_namesUserFriendly))
private abbrev globUF := sudo_rs.glob.Pattern.Insts.Sudo_rsSudoersAst_namesUserFriendly
private abbrev metaGlobUF := sudoers.tokens.Meta.Insts.Sudo_rsSudoersAst_namesUserFriendly globUF
private abbrev qualGlobUF := Qualified.Insts.Sudo_rsSudoersAst_namesUserFriendly metaGlobUF
private abbrev globListUF := alloc.vec.Vec.Insts.Sudo_rsSudoersAst_namesUserFriendly qualGlobUF
private abbrev globMany := sudo_rs.glob.Pattern.Insts.Sudo_rsSudoersBasic_parserMany
private abbrev metaGlobParse := sudoers.basic_parser.Parse.Blanket
  (sudoers.tokens.Meta.Insts.Sudo_rsSudoersBasic_parserToken
    sudo_rs.glob.Pattern.Insts.Sudo_rsSudoersBasic_parserToken)
private abbrev globListParse := alloc.vec.Vec.Insts.Sudo_rsSudoersBasic_parserParse
  (Qualified.Insts.Sudo_rsSudoersBasic_parserParse metaGlobParse metaGlobUF)
  (Qualified.Insts.Sudo_rsSudoersBasic_parserMany
    (sudoers.tokens.Meta.Insts.Sudo_rsSudoersBasic_parserMany globMany)) qualGlobUF

private theorem glob_description : DescRel globUF D.simpleCommand :=
  ⟨_, rfl, by
    simp only [sudo_rs.glob.Pattern.Insts.Sudo_rsSudoersAst_namesUserFriendly.DESCRIPTION]
    exact toStr_val _ _⟩

private theorem glob_many : ManyRefines globMany {} :=
  ⟨by simp [sudoers.basic_parser.Many.SEP.default],
    ⟨_, rfl, by simp [sudoers.basic_parser.Many.LIMIT.default]⟩⟩

private theorem glob_token_eq :
    sudo_rs.glob.Pattern.Insts.Sudo_rsSudoersBasic_parserToken = simpleCommandInstance := by
  unfold sudo_rs.glob.Pattern.Insts.Sudo_rsSudoersBasic_parserToken simpleCommandInstance
  rw [sudo_rs.glob.Pattern.Insts.Sudo_rsSudoersBasic_parserToken.MAX_LEN]

/-- The list in a command-scoped Defaults uses `SimpleCommand`, not `Command`. -/
theorem simple_command_list_refines {A : GlobAbs} {O : Syntax.Oracles} (hO : P2Oracle A O) :
    ParseRefines globListParse (absVec (absQualified (absMeta A.pat)))
      (Syntax.specListSimpleCommand O D) := by
  have ht := token_refines (meta_token_refines hO.chars.unicode (simple_command_token_refines hO))
    (fun _ _ => trivial)
  rw [← glob_token_eq] at ht
  exact vec_refines (qualified_refines ht (desc_meta glob_description))
    (many_qualified (many_meta glob_many)) (desc_qualified (desc_meta glob_description))

private theorem scope_at_eq (v : Vec Char) :
    (if v.len > sudoers.ast.DEFAULTS_LEN then do
      let c ← Vec.index (core.slice.index.SliceIndexUsizeSlice Char) v sudoers.ast.DEFAULTS_LEN
      ok (decide (c = '@'))
    else ok false) = ok ((v.val.drop 8).head? == some '@') := by
  have e : sudoers.ast.DEFAULTS_LEN.val = 8 := by simp [sudoers.ast.DEFAULTS_LEN]
  by_cases h : 8 < v.val.length
  · have hl : sudoers.ast.DEFAULTS_LEN.val < v.val.length := by simpa only [e] using h
    have hi := eq_ok_of_spec (Vec.index_usize_spec v sudoers.ast.DEFAULTS_LEN hl)
    have hp : sudoers.ast.DEFAULTS_LEN < v.len := by
      simpa only [UScalar.lt_equiv, Vec.len_val, Vec.length, e] using h
    simp only [hp, ite_true, Vec.index_slice_index, hi, bind_ok, List.head?_drop, ← e,
      List.getElem?_eq_getElem hl, beq_iff_eq, Option.some.injEq, decide_eq_true_eq]
    rfl
  · have hn : ¬sudoers.ast.DEFAULTS_LEN < v.len := by
      simpa only [UScalar.lt_equiv, Vec.len_val, Vec.length, e] using h
    have hd := List.drop_eq_nil_of_le (Nat.le_of_not_lt h)
    simp [hn, hd]

/-- The scope part of the body of `Syntax.getDirective`, including its positional guard. -/
abbrev defaultsScopeRun (O : Syntax.Oracles) (kw : String)
    (saved current : Syntax.Stream) : Syntax.Parsed Syntax.ConfigScope × Syntax.Stream :=
  if (kw.toList.drop 8).head? == some '@' ||
      (current.line == saved.line && current.col - saved.col == 8) then
    (Syntax.defaultsScope O D (kw.toList.drop 8) saved).run current
  else (.ok .generic, current)

set_option maxHeartbeats 800000 in
/-- Refinement of `defaults_scope` at the cursor after the tried user list. The saved cursor
provides the actual rewind position, not an oracle. -/
theorem defaults_scope_refines_of_users {A : GlobAbs} {O : Syntax.Oracles}
    (hO : P2Oracle A O)
    (hUser : ParseRefinesOn QuoteRoom specListUserInst absUserList (Syntax.specListUserSpecifier O D))
    (kw : String) (hkw : kw.utf8ByteSize ≤ Usize.max) {saved s : CS}
    (hb : StreamOK saved) (hs : StreamOK s) (hq : QuoteRoom (absStream saved))
    (hr : (absStream saved).Reaches (absStream s)) :
    Refines (Analysis.absConfigScope A)
      (sudoers.ast.defaults_scope kw s saved (saved.line, saved.col))
      (defaultsScopeRun O kw (absStream saved) (absStream s)) := by
  obtain ⟨v, ev, av⟩ := chars_of_eq kw hkw
  have vv : v.val = kw.toList := by simpa only [SudoRsProofs.Vec.deref_val] using av
  unfold sudoers.ast.defaults_scope
  simp only [ev, bind_ok, scope_at_eq, vv, get_pos_eq, uncurry_apply_pair]
  rw [scope_adjacent_eq hr]
  simp only [bind_ok]
  have hUsr := fun s hs hq => expect_nonterminal_refines_at
    (hUser s hs hq) (UF := scopeUserUF) (desc_vec (desc_qualified (desc_meta user_specifier_description)))
  have hHost := fun s hs => expect_nonterminal_refines
    (spec_list_hostname_refines hO.chars.unicode D rfl) (UF := scopeHostUF)
    (desc_vec (desc_qualified (desc_meta hostname_description))) (s := s) hs
  have hCommand := fun s hs => expect_nonterminal_refines (simple_command_list_refines hO)
    (UF := globListUF) (desc_vec (desc_qualified (desc_meta glob_description))) (s := s) hs
  by_cases atScope : ((kw.toList.drop 8).head? == some '@') = true
  · simp only [defaultsScopeRun, atScope, Bool.true_or, ite_true, Syntax.defaultsScope,
      Syntax.AParser.run_bind, Syntax.AParser.run_lift, Syntax.AParser.run_restore]
    have add9 : sudoers.ast.DEFAULTS_LEN + 1#usize = ok 9#usize := by
      rw [sudoers.ast.DEFAULTS_LEN]
      obtain ⟨x, hx, hv⟩ := exists_eq_ok_of_spec
        (UScalar.add_spec (x := 8#usize) (y := 1#usize) (by scalar_tac))
      rw [hx, show x = 9#usize from UScalar.eq_of_val_eq (by simpa using hv)]
    obtain ⟨s1, e1, hs1, a1⟩ := advance_eq hb 9#usize
    have a1' : absStream s1 = (absStream saved).advance 9 := by simpa using a1
    simp only [add9, bind_ok, e1, Syntax.Parser.run_advance, uncurry_apply_pair]
    rw [← a1']
    apply (skip_trailing_whitespace_refines hs1).elimCases
    · intro u s2 e2 a2 hs2
      simp only [e2, a2, bind_ok, uncurry_apply_pair, branch_Ok]
      apply (hHost s2 hs2).elimCases
      · intro xs t ex ax ht
        simp only [ex, ax, bind_ok, uncurry_apply_pair, branch_Ok, make_eq, Syntax.AParser.run_pure]
        exact refines_value (ConfigScope.Host xs) ht
      · intro e e' t ex ax ht rel
        simp only [ex, ax, bind_ok, uncurry_apply_pair, branch_Err, from_residual_Err]
        exact refines_diagnostic rel ht
    · intro e e' t ex ax ht rel
      simp only [ex, ax, bind_ok, uncurry_apply_pair, branch_Err, from_residual_Err]
      exact refines_diagnostic rel ht
  · have atFalse : ((kw.toList.drop 8).head? == some '@') = false := by simpa using atScope
    by_cases adjacent : ((absStream s).line == (absStream saved).line &&
        (absStream s).col - (absStream saved).col == 8) = true
    · simp only [defaultsScopeRun, atFalse, Bool.false_or, adjacent, Bool.false_eq_true,
        ite_false, ite_true, Syntax.defaultsScope, Syntax.AParser.run_bind, Syntax.AParser.run_lift]
      apply (is_syntax_refines hs ':').elimCases
      · intro colon s1 e1 a1 hs1
        have q1 := quoteRoom_stable.after (hq.reaches hr) (Syntax.isSyntax ':') (congrArg Prod.snd a1).symm
        cases colon
        · simp only [e1, a1, bind_ok, uncurry_apply_pair, branch_Ok, id_eq, Bool.false_eq_true, ite_false,
            Syntax.AParser.run_bind, Syntax.AParser.run_lift]
          apply (is_syntax_refines hs1 '!').elimCases
          · intro bang s2 e2 a2 hs2
            have q2 := quoteRoom_stable.after q1 (Syntax.isSyntax '!') (congrArg Prod.snd a2).symm
            cases bang
            · simp only [e2, a2, bind_ok, uncurry_apply_pair, branch_Ok, id_eq, Bool.false_eq_true,
                ite_false, Syntax.AParser.run_bind, Syntax.AParser.run_lift]
              apply (is_syntax_refines hs2 '>').elimCases
              · intro gt s3 e3 a3 hs3
                have q3 := quoteRoom_stable.after q2 (Syntax.isSyntax '>') (congrArg Prod.snd a3).symm
                cases gt
                · simp only [e3, a3, bind_ok, uncurry_apply_pair, branch_Ok, id_eq, Bool.false_eq_true,
                    ite_false, make_eq, Syntax.AParser.run_pure]
                  exact refines_value ConfigScope.Generic hs3
                · simp only [e3, a3, bind_ok, uncurry_apply_pair, branch_Ok, id_eq, ite_true,
                    Syntax.AParser.run_bind, Syntax.AParser.run_lift]
                  apply (hUsr s3 hs3 q3).elimCases
                  · intro xs t ex ax ht
                    simp only [ex, ax, bind_ok, uncurry_apply_pair, branch_Ok, make_eq,
                      Syntax.AParser.run_pure]
                    exact refines_value (ConfigScope.RunAs xs) ht
                  · intro e e' t ex ax ht rel
                    simp only [ex, ax, bind_ok, uncurry_apply_pair, branch_Err, from_residual_Err]
                    exact refines_diagnostic rel ht
              · intro e e' t ex ax ht rel
                simp only [ex, ax, bind_ok, uncurry_apply_pair, branch_Err, from_residual_Err]
                exact refines_diagnostic rel ht
            · simp only [e2, a2, bind_ok, uncurry_apply_pair, branch_Ok, id_eq, ite_true,
                Syntax.AParser.run_bind, Syntax.AParser.run_lift]
              apply (hCommand s2 hs2).elimCases
              · intro xs t ex ax ht
                simp only [ex, ax, bind_ok, uncurry_apply_pair, branch_Ok, make_eq,
                  Syntax.AParser.run_pure]
                exact refines_value (ConfigScope.Command xs) ht
              · intro e e' t ex ax ht rel
                simp only [ex, ax, bind_ok, uncurry_apply_pair, branch_Err, from_residual_Err]
                exact refines_diagnostic rel ht
          · intro e e' t ex ax ht rel
            simp only [ex, ax, bind_ok, uncurry_apply_pair, branch_Err, from_residual_Err]
            exact refines_diagnostic rel ht
        · simp only [e1, a1, bind_ok, uncurry_apply_pair, branch_Ok, id_eq, ite_true,
            Syntax.AParser.run_bind, Syntax.AParser.run_lift]
          apply (hUsr s1 hs1 q1).elimCases
          · intro xs t ex ax ht
            simp only [ex, ax, bind_ok, uncurry_apply_pair, branch_Ok, make_eq, Syntax.AParser.run_pure]
            exact refines_value (ConfigScope.User xs) ht
          · intro e e' t ex ax ht rel
            simp only [ex, ax, bind_ok, uncurry_apply_pair, branch_Err, from_residual_Err]
            exact refines_diagnostic rel ht
      · intro e e' t ex ax ht rel
        simp only [ex, ax, bind_ok, uncurry_apply_pair, branch_Err, from_residual_Err]
        exact refines_diagnostic rel ht
    · simp only [defaultsScopeRun, atFalse, Bool.false_or, Bool.false_eq_true, ite_false,
        adjacent, make_eq, bind_ok]
      exact refines_value ConfigScope.Generic hs

end SudoRsProofs.Parser
