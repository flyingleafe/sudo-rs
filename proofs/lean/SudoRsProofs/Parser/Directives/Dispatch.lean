import SudoRsProofs.Parser.Directives.Scope
import SudoRsProofs.Parser.Directives.Domain

/-! Stable `get_directive` consumes the alias or Defaults body only after classifying the first
user. The refinements taken here are the leaf alias-list and settings productions. -/

open Aeneas Aeneas.Std Result SudoersSpec
open sudo_rs
open sudo_rs.sudoers.ast (Directive)

noncomputable section

namespace SudoRsProofs.Parser

private abbrev D := Syntax.Descriptions.release
private abbrev defsParse {T} (uf : sudoers.ast_names.UserFriendly T)
    (p : sudoers.basic_parser.Parse (sudoers.tokens.Meta T))
    (m : sudoers.basic_parser.Many T) :=
  alloc.vec.Vec.Insts.Sudo_rsSudoersBasic_parserParse
    (sudoers.ast.Def.Insts.Sudo_rsSudoersBasic_parserParse uf p
      (sudoers.tokens.Meta.Insts.Sudo_rsSudoersBasic_parserMany m))
    (sudoers.ast.Def.Insts.Sudo_rsSudoersBasic_parserMany T)
    (sudoers.ast.Def.Insts.Sudo_rsSudoersAst_namesUserFriendly T)
private abbrev defsUF (T : Type) := alloc.vec.Vec.Insts.Sudo_rsSudoersAst_namesUserFriendly
  (sudoers.ast.Def.Insts.Sudo_rsSudoersAst_namesUserFriendly T)
private abbrev userDefsParse := defsParse userSpecifierUF
  sudoers.tokens.MetaUserSpecifier.Insts.Sudo_rsSudoersBasic_parserParse
  sudoers.ast.UserSpecifier.Insts.Sudo_rsSudoersBasic_parserMany
private abbrev hostDefsParse := defsParse
  sudoers.tokens.Hostname.Insts.Sudo_rsSudoersAst_namesUserFriendly
  (sudoers.basic_parser.Parse.Blanket (sudoers.tokens.Meta.Insts.Sudo_rsSudoersBasic_parserToken
    sudoers.tokens.Hostname.Insts.Sudo_rsSudoersBasic_parserToken))
  sudoers.tokens.Hostname.Insts.Sudo_rsSudoersBasic_parserMany
private abbrev commandDefsParse := defsParse PairPatternArgs.Insts.Sudo_rsSudoersAst_namesUserFriendly
  (sudoers.basic_parser.Parse.Blanket (sudoers.tokens.Meta.Insts.Sudo_rsSudoersBasic_parserToken
    PairPatternArgs.Insts.Sudo_rsSudoersBasic_parserToken))
  PairPatternArgs.Insts.Sudo_rsSudoersBasic_parserMany
private abbrev modUF := defaults.SettingsModifier.Insts.Sudo_rsSudoersAst_namesUserFriendly
private abbrev modsUF := alloc.vec.Vec.Insts.Sudo_rsSudoersAst_namesUserFriendly modUF
private abbrev modsParse := alloc.vec.Vec.Insts.Sudo_rsSudoersBasic_parserParse
  defaults.SettingsModifier.Insts.Sudo_rsSudoersBasic_parserParse
  defaults.SettingsModifier.Insts.Sudo_rsSudoersBasic_parserMany modUF

/-- The immediate expected alias-list and settings-list calls in `get_directive`.
These are discharged by the concrete leaf proofs in the integrated wrapper. -/
structure DirectiveLeaves (A : GlobAbs) (O : Syntax.Oracles) : Prop where
  users : ∀ s, StreamOK s → QuoteRoom (absStream s) →
    Refines (absVec (absDef absUserSpecifier))
      (sudoers.basic_parser.expect_nonterminal userDefsParse (defsUF sudoers.ast.UserSpecifier) s)
      ((Syntax.expectNonterminal D.def_
        (Syntax.defs D Syntax.userSpecifierMany D.userSpecifier (Syntax.metaUserSpecifier O D))).run
        (absStream s))
  hosts : ∀ s, StreamOK s →
    Refines (absVec (absDef id))
      (sudoers.basic_parser.expect_nonterminal hostDefsParse (defsUF sudoers.tokens.Hostname) s)
      ((Syntax.expectNonterminal D.def_
        (Syntax.defs D Syntax.hostnameMany D.hostname (Syntax.metaHostname O.char))).run (absStream s))
  commands : ∀ s, StreamOK s →
    Refines (absVec (absDef (absCommand A)))
      (sudoers.basic_parser.expect_nonterminal commandDefsParse (defsUF RCommand) s)
      ((Syntax.expectNonterminal D.def_ (Syntax.defs D {} D.command
        (Syntax.token (Syntax.metaToken O.char (Syntax.commandToken O))))).run (absStream s))
  settings : ∀ s, StreamOK s →
    Refines (absVec Defaults.absModifier)
      (sudoers.basic_parser.expect_nonterminal modsParse modsUF s)
      ((Syntax.expectNonterminal D.settingsModifier (Syntax.parseVec Syntax.settingsModifierMany
        D.settingsModifier (Syntax.settingsModifier O D))).run (absStream s))

/-- The test used after a provisional user list has more than one entry. -/
theorem could_be_username_eq (A : GlobAbs) (d : Directive) :
    Directive.could_be_username d = ok ((Analysis.absDirective A d).couldBeUsername) := by
  cases d with
  | Defaults _ cs => cases cs <;> rfl
  | _ => rfl

private abbrev expectedMods (O : Syntax.Oracles) :=
  Syntax.expectNonterminal D.settingsModifier
    (Syntax.parseVec Syntax.settingsModifierMany D.settingsModifier (Syntax.settingsModifier O D))

-- The do elaborator distributes the settings continuation into both branches of the
-- scope guard. Factor it out again so one scope refinement handles both branches.
private theorem defaults_part_run (O : Syntax.Oracles) (kw : String) (saved s : Syntax.Stream) :
    ((do
      let pos ← (Syntax.Parser.getPos : Syntax.Parser _)
      let scope ← if (kw.toList.drop 8).head? == some '@' ||
          (pos.1 == saved.getPos.1 && pos.2 - saved.getPos.2 == 8) then
        Syntax.defaultsScope O D (kw.toList.drop 8) saved
      else pure .generic
      let mods ← (expectedMods O : Syntax.Parser _)
      pure (.defaults mods scope) : Syntax.AParser saved Syntax.Directive).run s) =
    (match defaultsScopeRun O kw saved s with
    | (.ok scope, t) =>
      match (expectedMods O).run t with
      | (.ok mods, st) => (.ok (.defaults mods scope), st)
      | (.error e, st) => (.error e, st)
    | (.error e, t) => (.error e, t)) := by
  let guard := (kw.toList.drop 8).head? == some '@' ||
    (s.line == saved.line && s.col - saved.col == 8)
  let finish (scope : Syntax.ConfigScope) : Syntax.AParser saved Syntax.Directive := do
    let mods ← (expectedMods O : Syntax.Parser _)
    pure (.defaults mods scope)
  change ((if guard then
      Syntax.defaultsScope O D (kw.toList.drop 8) saved >>= finish
    else pure .generic >>= finish).run s) =
    (match (if guard then (Syntax.defaultsScope O D (kw.toList.drop 8) saved).run s
      else (.ok .generic, s)) with
    | (.ok scope, t) =>
      match (expectedMods O).run t with
      | (.ok mods, st) => (.ok (.defaults mods scope), st)
      | (.error e, st) => (.error e, st)
    | (.error e, t) => (.error e, t))
  by_cases h : guard = true
  · simp only [h, ite_true, Syntax.AParser.run_bind, finish, Syntax.AParser.run_lift,
      Syntax.AParser.run_pure]
    rcases (Syntax.defaultsScope O D (kw.toList.drop 8) saved).run s with ⟨r, t⟩
    cases r with
    | error _ => rfl
    | ok scope =>
      rcases hmods : (expectedMods O).run t with ⟨r, t'⟩
      cases r <;> simp [hmods]
  · simp only [h, Bool.false_eq_true, ite_false, Syntax.AParser.run_bind, finish,
      Syntax.AParser.run_lift, Syntax.AParser.run_pure]
    rcases (expectedMods O).run s with ⟨r, t⟩
    cases r <;> rfl

private theorem get_directive_name_refines {A : GlobAbs} {O : Syntax.Oracles}
    (hO : P2Oracle A O) (hL : DirectiveLeaves A O)
    (hUser : ParseRefinesOn QuoteRoom specListUserInst absUserList (Syntax.specListUserSpecifier O D))
    (nm : common.string.SudoString) (hw : nm.str.utf8ByteSize ≤ Usize.max)
    {saved s : CS} (hb : StreamOK saved) (hs : StreamOK s) (hq : QuoteRoom (absStream saved))
    (hr : (absStream saved).Reaches (absStream s)) :
    Refines (Analysis.absDirective A)
      (sudoers.ast.get_directive (.Allow (.Only (.User (.Name nm)))) s saved)
      ((Syntax.getDirective O D (.allow (.only (.user (.name nm.str)))) (absStream saved)).run (absStream s)) := by
  have eu := equals_keyword_eq nm.str "User_Alias" sudoers.ast.ALIAS_KW_USER alias_kw_user_val hw
  have eh := equals_keyword_eq nm.str "Host_Alias" sudoers.ast.ALIAS_KW_HOST alias_kw_host_val hw
  have ec := equals_keyword_eq nm.str "Cmnd_Alias" sudoers.ast.ALIAS_KW_CMND alias_kw_cmnd_val hw
  have ecd := equals_keyword_eq nm.str "Cmd_Alias" sudoers.ast.ALIAS_KW_CMD alias_kw_cmd_val hw
  have er := equals_keyword_eq nm.str "Runas_Alias" sudoers.ast.ALIAS_KW_RUNAS alias_kw_runas_val hw
  have ed := starts_with_str_eq nm.str sudoers.ast.DEFAULTS hw
  rw [defaults_val] at ed
  simp only [Syntax.getDirective]
  split
  all_goals
    simp only [sudoers.ast.get_directive, sudoers.tokens.sudo_string_text, get_pos_eq, bind_ok,
      eu, eh, ec, ecd, er, ed]
  · rename_i hu
    simp [hu, Syntax.AParser.run_bind, Syntax.AParser.run_lift]
    apply (hL.users s hs (hq.reaches hr)).elimCases
    · intro a t ex ax ht
      simp only [ex, ax, bind_ok, uncurry_apply_pair, branch_Ok, make_eq, Syntax.AParser.run_pure]
      exact refines_value (Directive.UserAlias a) ht
    · intro e e' t ex ax ht rel
      simp only [ex, ax, bind_ok, uncurry_apply_pair, branch_Err, from_residual_Err]
      exact refines_diagnostic rel ht
  · rename_i hh
    simp [hh, Syntax.AParser.run_bind, Syntax.AParser.run_lift]
    apply (hL.hosts s hs).elimCases
    · intro a t ex ax ht
      simp only [ex, ax, bind_ok, uncurry_apply_pair, branch_Ok, make_eq, Syntax.AParser.run_pure]
      exact refines_value (Directive.HostAlias a) ht
    · intro e e' t ex ax ht rel
      simp only [ex, ax, bind_ok, uncurry_apply_pair, branch_Err, from_residual_Err]
      exact refines_diagnostic rel ht
  · rename_i hc
    simp [hc, Syntax.AParser.run_bind, Syntax.AParser.run_lift]
    apply (hL.commands s hs).elimCases
    · intro a t ex ax ht
      simp only [ex, ax, bind_ok, uncurry_apply_pair, branch_Ok, make_eq, Syntax.AParser.run_pure]
      exact refines_value (Directive.CmndAlias a) ht
    · intro e e' t ex ax ht rel
      simp only [ex, ax, bind_ok, uncurry_apply_pair, branch_Err, from_residual_Err]
      exact refines_diagnostic rel ht
  · rename_i hc
    simp [hc, Syntax.AParser.run_bind, Syntax.AParser.run_lift]
    apply (hL.commands s hs).elimCases
    · intro a t ex ax ht
      simp only [ex, ax, bind_ok, uncurry_apply_pair, branch_Ok, make_eq, Syntax.AParser.run_pure]
      exact refines_value (Directive.CmndAlias a) ht
    · intro e e' t ex ax ht rel
      simp only [ex, ax, bind_ok, uncurry_apply_pair, branch_Err, from_residual_Err]
      exact refines_diagnostic rel ht
  · rename_i hu
    simp [hu, Syntax.AParser.run_bind, Syntax.AParser.run_lift]
    apply (hL.users s hs (hq.reaches hr)).elimCases
    · intro a t ex ax ht
      simp only [ex, ax, bind_ok, uncurry_apply_pair, branch_Ok, make_eq, Syntax.AParser.run_pure]
      exact refines_value (Directive.RunasAlias a) ht
    · intro e e' t ex ax ht rel
      simp only [ex, ax, bind_ok, uncurry_apply_pair, branch_Err, from_residual_Err]
      exact refines_diagnostic rel ht
  · rename_i hu hh hc hcd hr'
    have hu' : (nm.str == "User_Alias") = false := by simpa using hu
    have hh' : (nm.str == "Host_Alias") = false := by simpa using hh
    have hc' : (nm.str == "Cmnd_Alias") = false := by simpa using hc
    have hcd' : (nm.str == "Cmd_Alias") = false := by simpa using hcd
    have hrun' : (nm.str == "Runas_Alias") = false := by simpa using hr'
    simp only [hu', hh', hc', hcd', hrun', Bool.false_eq_true, ite_false]
    by_cases hdefault : "Defaults".toList.isPrefixOf nm.str.toList = true
    · simp only [hdefault, ite_true]
      rw [defaults_part_run]
      apply (defaults_scope_refines_of_users hO hUser nm.str hw hb hs hq hr).elimCases
      · intro cs s1 ex ax hs1
        simp only [ex, bind_ok, uncurry_apply_pair, branch_Ok]
        rw [ax]
        apply (hL.settings s1 hs1).elimCases
        · intro a t ex ax ht
          simp only [ex, ax, bind_ok, uncurry_apply_pair, branch_Ok, make_eq, Syntax.AParser.run_pure]
          exact refines_value (Directive.Defaults a cs) ht
        · intro e e' t ex ax ht rel
          simp only [ex, ax, bind_ok, uncurry_apply_pair, branch_Err, from_residual_Err]
          exact refines_diagnostic rel ht
      · intro e e' s1 ex ax hs1 rel
        simp only [ex, bind_ok, uncurry_apply_pair, branch_Err, from_residual_Err]
        rw [ax]
        exact refines_diagnostic rel hs1
    · simp only [hdefault, ite_false, reject_eq, bind_ok, Syntax.AParser.run_lift,
        Syntax.Parser.run_reject]
      exact refines_diagnostic .reject hs

/-- A non-name key rejects unchanged. A name key is classified on its actual Unicode text. -/
theorem get_directive_refines_of_parts {A : GlobAbs} {O : Syntax.Oracles}
    (hO : P2Oracle A O) (hL : DirectiveLeaves A O)
    (hUser : ParseRefinesOn QuoteRoom specListUserInst absUserList (Syntax.specListUserSpecifier O D))
    (key : RSpec sudoers.ast.UserSpecifier) (hk : DirectiveKeyFits (absQualified (absMeta absUserSpecifier) key))
    {saved s : CS} (hb : StreamOK saved) (hs : StreamOK s) (hq : QuoteRoom (absStream saved))
    (hr : (absStream saved).Reaches (absStream s)) :
    Refines (Analysis.absDirective A) (sudoers.ast.get_directive key s saved)
      ((Syntax.getDirective O D (absQualified (absMeta absUserSpecifier) key) (absStream saved)).run
        (absStream s)) := by
  rcases key with (⟨⟩ | ⟨⟨nm | id⟩ | _ | _⟩ | _) | _ <;>
    first
    | exact get_directive_name_refines hO hL hUser nm hk hb hs hq hr
    | simpa only [sudoers.ast.get_directive, Syntax.getDirective, absQualified, absMeta,
        absIdentifier, absUserSpecifier, reject_eq, bind_ok, Syntax.AParser.run_lift,
        Syntax.Parser.run_reject] using (refines_diagnostic (f := Analysis.absDirective A) .reject hs)

end SudoRsProofs.Parser
