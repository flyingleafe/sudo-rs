import SudoRsProofs.Parser.Ast

open Aeneas Aeneas.Std Result

namespace SudoRsProofs.Parser

/-- The P2 `AliasName` instance reuses the two P1 class lemmas. The constructor keeps the
string unchanged. -/
theorem alias_name_token_refines :
    TokenRefines sudo_rs.sudoers.tokens.AliasName.Insts.Sudo_rsSudoersBasic_parserToken id
      SudoersSpec.Syntax.aliasNameToken (fun _ => True) where
  max_len := ⟨_, rfl, by
    simp [sudo_rs.sudoers.basic_parser.Token.MAX_LEN.default, SudoersSpec.Syntax.aliasNameToken]⟩
  max_len_le := by
    simp only [SudoersSpec.Syntax.aliasNameToken]
    scalar_tac
  allow_escape := by
    simp [sudo_rs.sudoers.basic_parser.Token.ALLOW_ESCAPE.default, SudoersSpec.Syntax.aliasNameToken]
  accept := aliasName_accept_eq
  accept_1st := aliasName_accept_1st_eq
  escaped _ := rfl
  construct s _ _ := ⟨.Ok s, rfl, String.ofList_toList.symm⟩

theorem alias_name_parse_refines :
    ParseRefines
      (sudo_rs.sudoers.basic_parser.Parse.Blanket
        sudo_rs.sudoers.tokens.AliasName.Insts.Sudo_rsSudoersBasic_parserToken)
      id (SudoersSpec.Syntax.token SudoersSpec.Syntax.aliasNameToken) :=
  token_refines alias_name_token_refines (fun _ _ => trivial)

end SudoRsProofs.Parser
