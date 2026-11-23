import SudoRsProofs.Parser.PermissionLines.Users

/-! The release user-list instances and their named tried and expected entries. -/

open Aeneas Aeneas.Std Result SudoersSpec
open sudo_rs.sudoers.ast (Qualified)
open sudo_rs.sudoers

namespace SudoRsProofs.Parser

private abbrev D := Syntax.Descriptions.release
private abbrev metaUserInst := tokens.MetaUserSpecifier.Insts.Sudo_rsSudoersBasic_parserParse
private abbrev metaUserUF := tokens.Meta.Insts.Sudo_rsSudoersAst_namesUserFriendly userSpecifierUF
private abbrev specUserUF := Qualified.Insts.Sudo_rsSudoersAst_namesUserFriendly metaUserUF
private abbrev userMany := ast.UserSpecifier.Insts.Sudo_rsSudoersBasic_parserMany

abbrev specListUserInst :=
  sudo_rs.alloc.vec.Vec.Insts.Sudo_rsSudoersBasic_parserParse
    (Qualified.Insts.Sudo_rsSudoersBasic_parserParse metaUserInst metaUserUF)
    (Qualified.Insts.Sudo_rsSudoersBasic_parserMany
      (tokens.Meta.Insts.Sudo_rsSudoersBasic_parserMany userMany)) specUserUF

abbrev absUserList (v : alloc.vec.Vec (RSpec ast.UserSpecifier)) : SpecList UserSpecifier :=
  absSpecList absUserSpecifier v.val

private theorem user_specifier_many : ManyRefines userMany Syntax.userSpecifierMany :=
  ⟨by simp [sudo_rs.sudoers.basic_parser.Many.SEP.default, Syntax.userSpecifierMany],
    ⟨_, rfl, by simp [sudo_rs.sudoers.basic_parser.Many.LIMIT.default, Syntax.userSpecifierMany]⟩⟩

theorem spec_list_user_refines_of_meta {O : Syntax.Oracles}
    (hMeta : ParseRefinesOn QuoteRoom metaUserInst (absMeta absUserSpecifier)
      (Syntax.metaUserSpecifier O D)) :
    ParseRefinesOn QuoteRoom specListUserInst absUserList (Syntax.specListUserSpecifier O D) :=
  vec_refines_on quoteRoom_stable
    (qualified_refines_on quoteRoom_stable hMeta (desc_meta user_specifier_description))
    (many_qualified (many_meta user_specifier_many))
    (desc_qualified (desc_meta user_specifier_description))

theorem user_list_refines_of_meta {O : Syntax.Oracles}
    (hMeta : ParseRefinesOn QuoteRoom metaUserInst (absMeta absUserSpecifier)
      (Syntax.metaUserSpecifier O D)) {s : CS} (hs : StreamOK s) (hq : QuoteRoom (absStream s)) :
    Refines absUserList (sudo_rs.sudoers.ast.user_list s)
      ((Syntax.tryNonterminal (Syntax.specListUserSpecifier O D)).run (absStream s)) :=
  try_nonterminal_refines_at (spec_list_user_refines_of_meta hMeta s hs hq)

theorem expect_user_list_refines_of_meta {O : Syntax.Oracles}
    (hMeta : ParseRefinesOn QuoteRoom metaUserInst (absMeta absUserSpecifier)
      (Syntax.metaUserSpecifier O D)) {s : CS} (hs : StreamOK s) (hq : QuoteRoom (absStream s)) :
    Refines absUserList (sudo_rs.sudoers.ast.expect_user_list s)
      ((Syntax.expectNonterminal D.userSpecifier (Syntax.specListUserSpecifier O D)).run
        (absStream s)) :=
  expect_nonterminal_refines_at (spec_list_user_refines_of_meta hMeta s hs hq)
    (desc_vec (desc_qualified (desc_meta user_specifier_description)))

end SudoRsProofs.Parser
