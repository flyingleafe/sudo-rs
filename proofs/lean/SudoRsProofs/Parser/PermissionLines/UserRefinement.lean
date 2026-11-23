import SudoRsProofs.Parser.PermissionLines.UserLists
import SudoRsProofs.Parser.PermissionLines.RunAs
import SudoRsProofs.Parser.Username
import SudoRsProofs.Parser.Digits
import SudoRsProofs.Parser.Parameters

/-! Release user productions instantiated with the concrete extracted tokens. -/

open Aeneas Aeneas.Std SudoersSpec

namespace SudoRsProofs.Parser

private abbrev D := Syntax.Descriptions.release

variable {O : Syntax.Oracles}

theorem identifier_refines (hO : P2CharOracle O.char) :
    ParseRefines identifierInst absIdentifier (Syntax.identifier O D) :=
  identifier_refines_of_tokens digits_u32_parse_refines (username_parse_refines hO)

theorem meta_identifier_refines (hO : P2CharOracle O.char) :
    ParseRefines sudo_rs.sudoers.tokens.MetaIdentifier.Insts.Sudo_rsSudoersBasic_parserParse
      (absMeta absIdentifier) (Syntax.metaIdentifier O D) :=
  meta_identifier_refines_of_tokens (identifier_refines hO) (meta_username_parse_refines hO)

theorem user_specifier_refines (hO : P2CharOracle O.char) :
    ParseRefinesOn QuoteRoom userSpecifierInst absUserSpecifier (Syntax.userSpecifier O D) :=
  user_specifier_refines_of_tokens (identifier_refines hO) .netgroupsNotSupported
    (unquoted_parse_refines hO (username_token_refines hO))

theorem meta_user_specifier_refines (hO : P2CharOracle O.char) :
    ParseRefinesOn QuoteRoom sudo_rs.sudoers.tokens.MetaUserSpecifier.Insts.Sudo_rsSudoersBasic_parserParse
      (absMeta absUserSpecifier) (Syntax.metaUserSpecifier O D) :=
  meta_user_specifier_refines_of_tokens (user_specifier_refines hO) (meta_username_parse_refines hO)

theorem spec_list_user_refines (hO : P2CharOracle O.char) :
    ParseRefinesOn QuoteRoom specListUserInst absUserList (Syntax.specListUserSpecifier O D) :=
  spec_list_user_refines_of_meta (meta_user_specifier_refines hO)

theorem user_list_refines (hO : P2CharOracle O.char) {s : CS} (hs : StreamOK s)
    (hq : QuoteRoom (absStream s)) :
    Refines absUserList (sudo_rs.sudoers.ast.user_list s)
      ((Syntax.tryNonterminal (Syntax.specListUserSpecifier O D)).run (absStream s)) :=
  user_list_refines_of_meta (meta_user_specifier_refines hO) hs hq

theorem expect_user_list_refines (hO : P2CharOracle O.char) {s : CS} (hs : StreamOK s)
    (hq : QuoteRoom (absStream s)) :
    Refines absUserList (sudo_rs.sudoers.ast.expect_user_list s)
      ((Syntax.expectNonterminal D.userSpecifier (Syntax.specListUserSpecifier O D)).run (absStream s)) :=
  expect_user_list_refines_of_meta (meta_user_specifier_refines hO) hs hq

theorem run_as_refines (hO : P2CharOracle O.char) :
    ParseRefinesOn QuoteRoom runAsInst absRunAs (Syntax.runAs O D) :=
  run_as_refines_of_lists (fun _ hs hq => user_list_refines hO hs hq) (meta_identifier_refines hO)

/-- P2 user-list entry from an original input at position `(1,1)`. -/
theorem user_list_refines_text (hO : P2CharOracle O.char) (src : Slice Char)
    (hlen : 1 + 2 * src.val.length ≤ Usize.max) :
    Refines absUserList (sudo_rs.sudoers.ast.user_list ⟨src, 0#usize, 1#usize, 1#usize⟩)
      ((Syntax.tryNonterminal (Syntax.specListUserSpecifier O D)).run (Syntax.Stream.new src.val)) :=
  user_list_refines hO (StreamOK.initial src (by omega)) (QuoteRoom.initial src hlen)

theorem expect_user_list_refines_text (hO : P2CharOracle O.char) (src : Slice Char)
    (hlen : 1 + 2 * src.val.length ≤ Usize.max) :
    Refines absUserList (sudo_rs.sudoers.ast.expect_user_list ⟨src, 0#usize, 1#usize, 1#usize⟩)
      ((Syntax.expectNonterminal D.userSpecifier (Syntax.specListUserSpecifier O D)).run
        (Syntax.Stream.new src.val)) :=
  expect_user_list_refines hO (StreamOK.initial src (by omega)) (QuoteRoom.initial src hlen)

end SudoRsProofs.Parser
