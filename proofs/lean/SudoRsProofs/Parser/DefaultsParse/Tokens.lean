import SudoRsProofs.Parser.DefaultsParse.Common
import SudoRsProofs.Parser.P2Oracle
import SudoRsProofs.Parser.PermissionLines.Common

/-! The four Defaults-only tokens preserve their text. Their lexical classes use only the
existing P2 character agreements (the numeric and option-name classes are ASCII). -/

open Aeneas Aeneas.Std Result sudo_rs
open SudoersSpec

namespace SudoRsProofs.Parser.DefaultsParse

open Syntax

private theorem ascii_hex_eq (c : Char) :
    core.char.methods.Char.is_ascii_hexdigit c = ok (isAsciiHexdigit c) := by
  rfl

private theorem ascii_alphanum_eq (c : Char) :
    core.char.methods.Char.is_ascii_alphanumeric c = ok (isAsciiAlphanumeric c) := by
  simp [core.char.methods.Char.is_ascii_alphanumeric, Char.isAlphanum, Char.isAlpha,
    isAsciiAlphanumeric, isAsciiDigit, isAsciiUppercase, isAsciiLowercase,
    Char.isDigit, Char.isUpper, Char.isLower, Char.le_def, Bool.or_assoc,
    Bool.or_left_comm, Bool.or_comm]

private theorem numeric_accept (c : Char) :
    sudoers.tokens.Numeric.Insts.Sudo_rsSudoersBasic_parserToken.accept c =
      ok (numericToken.accept c) := by
  simp only [sudoers.tokens.Numeric.Insts.Sudo_rsSudoersBasic_parserToken.accept,
    ascii_hex_eq, bind_ok, numericToken]
  cases isAsciiHexdigit c <;> simp [Sanitize.decide_eq_beq]

private theorem defaultName_accept (c : Char) :
    sudoers.tokens.DefaultName.Insts.Sudo_rsSudoersBasic_parserToken.accept c =
      ok (defaultNameToken.accept c) := by
  simp only [sudoers.tokens.DefaultName.Insts.Sudo_rsSudoersBasic_parserToken.accept,
    ascii_alphanum_eq, bind_ok, defaultNameToken]
  cases isAsciiAlphanumeric c <;> simp [Sanitize.decide_eq_beq]

private theorem envVar_escaped (c : Char) :
    sudoers.tokens.EnvVar.Insts.Sudo_rsSudoersBasic_parserToken.escaped c =
      ok (Syntax.EnvVar.escaped c) := by
  simp only [sudoers.tokens.EnvVar.Insts.Sudo_rsSudoersBasic_parserToken.escaped,
    escape_char_eq, bind_ok, Syntax.EnvVar.escaped]
  split_ifs <;> simp_all [Sanitize.decide_eq_beq]

private theorem envVar_accept {O : CharOracle} (hO : P2CharOracle O) (c : Char) :
    sudoers.tokens.EnvVar.Insts.Sudo_rsSudoersBasic_parserToken.accept c =
      ok ((envVarToken O).accept c) := by
  simp only [sudoers.tokens.EnvVar.Insts.Sudo_rsSudoersBasic_parserToken.accept,
    hO.is_control, hO.is_whitespace, envVar_escaped, bind_ok, envVarToken]
  cases O.isControl c <;> cases O.isWhitespace c <;> simp

private theorem quoted_escaped {O : CharOracle} (hO : P2CharOracle O) (c : Char) :
    sudoers.tokens.QuotedStringParameter.Insts.Sudo_rsSudoersBasic_parserToken.escaped c =
      ok (Syntax.QuotedStringParameter.escaped O c) := by
  simp only [sudoers.tokens.QuotedStringParameter.Insts.Sudo_rsSudoersBasic_parserToken.escaped,
    escape_char_eq, hO.is_control, bind_ok, Syntax.QuotedStringParameter.escaped]
  split_ifs <;> simp_all

private theorem quoted_accept {O : CharOracle} (hO : P2CharOracle O) (c : Char) :
    sudoers.tokens.QuotedStringParameter.Insts.Sudo_rsSudoersBasic_parserToken.accept c =
      ok ((quotedStringParameterToken O).accept c) := by
  simp [sudoers.tokens.QuotedStringParameter.Insts.Sudo_rsSudoersBasic_parserToken.accept,
    quoted_escaped hO, quotedStringParameterToken]

theorem numeric_token_refines :
    TokenRefines sudoers.tokens.Numeric.Insts.Sudo_rsSudoersBasic_parserToken id
      numericToken (fun _ => True) where
  max_len := ⟨_, rfl, by
    simp [sudoers.tokens.Numeric.Insts.Sudo_rsSudoersBasic_parserToken.MAX_LEN, numericToken]⟩
  max_len_le := by simp only [numericToken]; scalar_tac
  allow_escape := by simp [sudoers.basic_parser.Token.ALLOW_ESCAPE.default, numericToken]
  accept := numeric_accept
  accept_1st := numeric_accept
  escaped := fun _ => rfl
  construct s _ _ := ⟨_, rfl, by simp [ConstructRel, numericToken, String.ofList_toList]⟩

theorem defaultName_token_refines :
    TokenRefines sudoers.tokens.DefaultName.Insts.Sudo_rsSudoersBasic_parserToken id
      defaultNameToken (fun _ => True) where
  max_len := ⟨_, rfl, by simp [sudoers.basic_parser.Token.MAX_LEN.default, defaultNameToken]⟩
  max_len_le := by simp only [defaultNameToken]; scalar_tac
  allow_escape := by simp [sudoers.basic_parser.Token.ALLOW_ESCAPE.default, defaultNameToken]
  accept := defaultName_accept
  accept_1st := defaultName_accept
  escaped := fun _ => rfl
  construct s _ _ := ⟨_, rfl, by simp [ConstructRel, defaultNameToken, String.ofList_toList]⟩

theorem envVar_token_refines {O : CharOracle} (hO : P2CharOracle O) :
    TokenRefines sudoers.tokens.EnvVar.Insts.Sudo_rsSudoersBasic_parserToken id
      (envVarToken O) (fun _ => True) where
  max_len := ⟨_, rfl, by simp [sudoers.basic_parser.Token.MAX_LEN.default, envVarToken]⟩
  max_len_le := by simp only [envVarToken]; scalar_tac
  allow_escape := by simp [sudoers.tokens.EnvVar.Insts.Sudo_rsSudoersBasic_parserToken.ALLOW_ESCAPE,
    envVarToken]
  accept := envVar_accept hO
  accept_1st := envVar_accept hO
  escaped := envVar_escaped
  construct s _ _ := ⟨_, rfl, by simp [ConstructRel, envVarToken, String.ofList_toList]⟩

theorem quotedStringParameter_token_refines {O : CharOracle} (hO : P2CharOracle O) :
    TokenRefines sudoers.tokens.QuotedStringParameter.Insts.Sudo_rsSudoersBasic_parserToken id
      (quotedStringParameterToken O) (fun _ => True) where
  max_len := ⟨_, rfl, by
    simp [sudoers.tokens.QuotedStringParameter.Insts.Sudo_rsSudoersBasic_parserToken.MAX_LEN,
      quotedStringParameterToken]⟩
  max_len_le := by simp only [quotedStringParameterToken]; scalar_tac
  allow_escape := by
    simp [sudoers.tokens.QuotedStringParameter.Insts.Sudo_rsSudoersBasic_parserToken.ALLOW_ESCAPE,
      quotedStringParameterToken]
  accept := quoted_accept hO
  accept_1st := quoted_accept hO
  escaped := quoted_escaped hO
  construct s _ _ := ⟨_, rfl, by simp [ConstructRel, quotedStringParameterToken, String.ofList_toList]⟩

theorem numeric_parse_refines :
    ParseRefines (sudoers.basic_parser.Parse.Blanket
      sudoers.tokens.Numeric.Insts.Sudo_rsSudoersBasic_parserToken) id (token numericToken) :=
  token_refines numeric_token_refines (by intros; trivial)

theorem defaultName_parse_refines :
    ParseRefines (sudoers.basic_parser.Parse.Blanket
      sudoers.tokens.DefaultName.Insts.Sudo_rsSudoersBasic_parserToken) id
      (token defaultNameToken) :=
  token_refines defaultName_token_refines (by intros; trivial)

theorem envVar_parse_refines {O : CharOracle} (hO : P2CharOracle O) :
    ParseRefines (sudoers.basic_parser.Parse.Blanket
      sudoers.tokens.EnvVar.Insts.Sudo_rsSudoersBasic_parserToken) id (token (envVarToken O)) :=
  token_refines (envVar_token_refines hO) (by intros; trivial)

theorem quotedStringParameter_parse_refines {O : CharOracle} (hO : P2CharOracle O) :
    ParseRefines (sudoers.basic_parser.Parse.Blanket
      sudoers.tokens.QuotedStringParameter.Insts.Sudo_rsSudoersBasic_parserToken) id
      (token (quotedStringParameterToken O)) :=
  token_refines (quotedStringParameter_token_refines hO) (by intros; trivial)

theorem numeric_description :
    DescRel sudoers.tokens.Numeric.Insts.Sudo_rsSudoersAst_namesUserFriendly
      Descriptions.release.numeric := by
  refine ⟨_, rfl, ?_⟩
  simp only [sudoers.tokens.Numeric.Insts.Sudo_rsSudoersAst_namesUserFriendly.DESCRIPTION]
  exact Defaults.toStr_val _ _

theorem defaultName_description :
    DescRel sudoers.tokens.DefaultName.Insts.Sudo_rsSudoersAst_namesUserFriendly
      Descriptions.release.defaultName := by
  refine ⟨_, rfl, ?_⟩
  simp only [sudoers.tokens.DefaultName.Insts.Sudo_rsSudoersAst_namesUserFriendly.DESCRIPTION]
  exact Defaults.toStr_val _ _

theorem envVar_description :
    DescRel sudoers.tokens.EnvVar.Insts.Sudo_rsSudoersAst_namesUserFriendly
      Descriptions.release.envVar := by
  refine ⟨_, rfl, ?_⟩
  simp only [sudoers.tokens.EnvVar.Insts.Sudo_rsSudoersAst_namesUserFriendly.DESCRIPTION]
  exact Defaults.toStr_val _ _

theorem quotedStringParameter_description :
    DescRel sudoers.tokens.QuotedStringParameter.Insts.Sudo_rsSudoersAst_namesUserFriendly
      Descriptions.release.quotedStringParameter := by
  refine ⟨_, rfl, ?_⟩
  simp only [sudoers.tokens.QuotedStringParameter.Insts.Sudo_rsSudoersAst_namesUserFriendly.DESCRIPTION]
  exact Defaults.toStr_val _ _

end SudoRsProofs.Parser.DefaultsParse
