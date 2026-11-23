import SudoRsProofs.Parser.P2Oracle
import SudoRsProofs.Parser.Command
import SudoRsProofs.Parser.Username
import SudoersSpec.Grammar.Token

/-! Include-path tokens and the byte bounds used before comparing a parsed keyword. -/

open Aeneas Aeneas.Std Result
open SudoersSpec.Syntax (CharOracle Descriptions Oracles Parser Stream TokenSpec utf8Len)

namespace SudoRsProofs.Parser

open sudo_rs.sudoers

private theorem include_escaped_eq (c : Char) :
    tokens.IncludePath.Insts.Sudo_rsSudoersBasic_parserToken.escaped c =
      ok (SudoersSpec.Syntax.IncludePath.escaped c) := by
  have hc (x y : Char) : (x == y) = decide (x = y) := rfl
  simp only [tokens.IncludePath.Insts.Sudo_rsSudoersBasic_parserToken.escaped,
    escape_char_eq, bind_ok, SudoersSpec.Syntax.IncludePath.escaped, hc]
  split_ifs <;> simp_all

private theorem include_accept_eq {O : CharOracle} (hO : P2CharOracle O) (c : Char) :
    tokens.IncludePath.Insts.Sudo_rsSudoersBasic_parserToken.accept c =
      ok ((SudoersSpec.Syntax.includePathToken O).accept c) := by
  cases hc : O.isControl c <;>
    simp [tokens.IncludePath.Insts.Sudo_rsSudoersBasic_parserToken.accept, hO.is_control,
      hc, include_escaped_eq, SudoersSpec.Syntax.includePathToken]

private theorem quoted_include_escaped_eq {O : CharOracle} (hO : P2CharOracle O) (c : Char) :
    tokens.QuotedIncludePath.Insts.Sudo_rsSudoersBasic_parserToken.escaped c =
      ok (SudoersSpec.Syntax.QuotedIncludePath.escaped O c) := by
  have hc (x y : Char) : (x == y) = decide (x = y) := rfl
  by_cases h : c = '"' <;>
    simp [tokens.QuotedIncludePath.Insts.Sudo_rsSudoersBasic_parserToken.escaped,
      SudoersSpec.Syntax.QuotedIncludePath.escaped, hc, h, hO.is_control]

private theorem quoted_include_accept_eq {O : CharOracle} (hO : P2CharOracle O) (c : Char) :
    tokens.QuotedIncludePath.Insts.Sudo_rsSudoersBasic_parserToken.accept c =
      ok ((SudoersSpec.Syntax.quotedIncludePathToken O).accept c) := by
  simp [tokens.QuotedIncludePath.Insts.Sudo_rsSudoersBasic_parserToken.accept,
    quoted_include_escaped_eq hO, SudoersSpec.Syntax.quotedIncludePathToken, Bool.not_eq_true]

theorem include_path_token_refines {O : CharOracle} (hO : P2CharOracle O) :
    TokenRefines tokens.IncludePath.Insts.Sudo_rsSudoersBasic_parserToken id
      (SudoersSpec.Syntax.includePathToken O) (fun _ => True) where
  max_len := ⟨_, rfl, by simp [tokens.IncludePath.Insts.Sudo_rsSudoersBasic_parserToken.MAX_LEN,
    SudoersSpec.Syntax.includePathToken]⟩
  max_len_le := by simp only [SudoersSpec.Syntax.includePathToken]; scalar_tac
  allow_escape := by simp [tokens.IncludePath.Insts.Sudo_rsSudoersBasic_parserToken.ALLOW_ESCAPE,
    SudoersSpec.Syntax.includePathToken]
  accept := include_accept_eq hO
  accept_1st := include_accept_eq hO
  escaped := include_escaped_eq
  construct s _ _ := ⟨.Ok s, rfl, String.ofList_toList.symm⟩

theorem quoted_include_path_token_refines {O : CharOracle} (hO : P2CharOracle O) :
    TokenRefines tokens.QuotedIncludePath.Insts.Sudo_rsSudoersBasic_parserToken id
      (SudoersSpec.Syntax.quotedIncludePathToken O) (fun _ => True) where
  max_len := ⟨_, rfl, by simp [tokens.QuotedIncludePath.Insts.Sudo_rsSudoersBasic_parserToken.MAX_LEN,
    SudoersSpec.Syntax.quotedIncludePathToken]⟩
  max_len_le := by simp only [SudoersSpec.Syntax.quotedIncludePathToken]; scalar_tac
  allow_escape := by simp [tokens.QuotedIncludePath.Insts.Sudo_rsSudoersBasic_parserToken.ALLOW_ESCAPE,
    SudoersSpec.Syntax.quotedIncludePathToken]
  accept := quoted_include_accept_eq hO
  accept_1st := quoted_include_accept_eq hO
  escaped := quoted_include_escaped_eq hO
  construct s _ _ := ⟨.Ok s, rfl, String.ofList_toList.symm⟩

theorem include_path_parse_refines {O : CharOracle} (hO : P2CharOracle O) :
    ParseRefines (basic_parser.Parse.Blanket tokens.IncludePath.Insts.Sudo_rsSudoersBasic_parserToken)
      id (SudoersSpec.Syntax.token (SudoersSpec.Syntax.includePathToken O)) :=
  token_refines (include_path_token_refines hO) (fun _ _ => trivial)

theorem quoted_include_path_parse_refines {O : CharOracle} (hO : P2CharOracle O) :
    ParseRefines
      (basic_parser.Parse.Blanket tokens.QuotedIncludePath.Insts.Sudo_rsSudoersBasic_parserToken)
      id (SudoersSpec.Syntax.token (SudoersSpec.Syntax.quotedIncludePathToken O)) :=
  token_refines (quoted_include_path_token_refines hO) (fun _ _ => trivial)

theorem include_path_description :
    DescRel tokens.IncludePath.Insts.Sudo_rsSudoersAst_namesUserFriendly
      Descriptions.release.includePath :=
  ⟨_, rfl, by
    simp only [tokens.IncludePath.Insts.Sudo_rsSudoersAst_namesUserFriendly.DESCRIPTION]
    exact toStr_val _ _⟩

theorem quoted_include_path_description :
    DescRel tokens.QuotedIncludePath.Insts.Sudo_rsSudoersAst_namesUserFriendly
      Descriptions.release.quotedIncludePath :=
  ⟨_, rfl, by
    simp only [tokens.QuotedIncludePath.Insts.Sudo_rsSudoersAst_namesUserFriendly.DESCRIPTION]
    exact toStr_val _ _⟩

private theorem lenOK_utf8 {m : Nat} (cs acc : List Char) (hp : utf8Len acc ≤ m + 4)
    (h : SudoersSpec.Grammar.LenOK m acc cs) : utf8Len (acc ++ cs) ≤ m + 4 := by
  induction cs generalizing acc with
  | nil => simpa using hp
  | cons c cs ih =>
    change utf8Len acc < m ∧ SudoersSpec.Grammar.LenOK m (acc ++ [c]) cs at h
    have hc := Char.utf8Size_le_four c
    have hpush : utf8Len (acc ++ [c]) ≤ m + 4 := by
      rw [utf8Len_append]
      simp only [utf8Len_cons, utf8Len_nil, Nat.add_zero]
      have := h.1
      omega
    simpa only [List.append_assoc, List.singleton_append] using ih (acc ++ [c]) hpush h.2

/-- The constructor receives the bounded token text witnessed by the reference grammar. -/
theorem token_construct_text {α : Type} {t : TokenSpec α} {s s' : Stream} {v : α}
    (h : (SudoersSpec.Syntax.token t).run s = (.ok v, s')) :
    ∃ cs, t.construct cs = .ok v ∧ utf8Len cs ≤ t.maxLen + 4 := by
  obtain ⟨_, _, hg⟩ := SudoersSpec.Grammar.token_sound t s v s' h
  cases hg with
  | mk _ _ hlen hc =>
    refine ⟨_, hc, ?_⟩
    have hx (x : Char) : utf8Len [x] ≤ t.maxLen + 4 := by
      simp only [utf8Len_cons, utf8Len_nil, Nat.add_zero]
      have := Char.utf8Size_le_four x
      omega
    simpa only [List.singleton_append] using lenOK_utf8 _ _ (hx _) hlen

private theorem username_construct_value {O : Oracles} {cs : List Char} {kw : String}
    (h : SudoersSpec.Syntax.Username.construct O cs = .ok kw) : kw = String.ofList cs := by
  have he (xs : List Char) :
      (if xs.contains '$' then Except.error .embeddedDollarInUsername
        else SudoersSpec.Syntax.sudoStringNew O cs) = Except.ok kw →
        kw = String.ofList cs := by
    by_cases hd : xs.contains '$' = true
    · simp only [hd, ↓reduceIte, reduceCtorEq, false_implies]
    · intro hh
      have hs : SudoersSpec.Syntax.sudoStringNew O cs = .ok kw := by
        simpa only [hd, Bool.false_eq_true, ↓reduceIte] using hh
      unfold SudoersSpec.Syntax.sudoStringNew at hs
      split at hs
      · cases hs
      · exact (Except.ok.inj hs).symm
  unfold SudoersSpec.Syntax.Username.construct at h
  exact he _ h

theorem username_token_value_bound {O : Oracles} {s s' : Stream} {kw : String}
    (h : (SudoersSpec.Syntax.token (SudoersSpec.Syntax.usernameToken O)).run s = (.ok kw, s')) :
    kw.utf8ByteSize ≤ Usize.max := by
  obtain ⟨cs, hc, hl⟩ := token_construct_text h
  have he := username_construct_value (O := O) hc
  rw [he, utf8Len_toList, String.toList_ofList]
  have hm : (SudoersSpec.Syntax.usernameToken O).maxLen = 255 := rfl
  rw [hm] at hl
  exact hl.trans (by scalar_tac)

theorem alias_name_token_value_bound {s s' : Stream} {kw : String}
    (h : (SudoersSpec.Syntax.token SudoersSpec.Syntax.aliasNameToken).run s = (.ok kw, s')) :
    kw.utf8ByteSize ≤ Usize.max := by
  obtain ⟨cs, hc, hl⟩ := token_construct_text h
  change Except.ok (String.ofList cs) = Except.ok kw at hc
  rw [← Except.ok.inj hc, utf8Len_toList, String.toList_ofList]
  have hm : SudoersSpec.Syntax.aliasNameToken.maxLen = 255 := rfl
  rw [hm] at hl
  exact hl.trans (by scalar_tac)

theorem meta_username_only_value_bound {O : Oracles} {s s' : Stream} {kw : String}
    (h : (SudoersSpec.Syntax.token (SudoersSpec.Syntax.metaToken O.char
      (SudoersSpec.Syntax.usernameToken O))).run s = (.ok (.only kw), s')) :
    kw.utf8ByteSize ≤ Usize.max := by
  obtain ⟨cs, hc, hl⟩ := token_construct_text h
  have hm : (SudoersSpec.Syntax.metaToken O.char (SudoersSpec.Syntax.usernameToken O)).maxLen = 255 := rfl
  rw [hm] at hl
  change SudoersSpec.Syntax.Meta.construct O.char (SudoersSpec.Syntax.usernameToken O) cs =
    .ok (.only kw) at hc
  unfold SudoersSpec.Syntax.Meta.construct at hc
  dsimp only at hc
  split at hc
  · cases hc
  split at hc
  · cases hc
  simp only [SudoersSpec.Syntax.usernameToken] at hc
  split at hc
  · rename_i parsed he
    obtain rfl : parsed = kw := by simpa using hc
    rw [username_construct_value he, utf8Len_toList, String.toList_ofList]
    exact hl.trans (by scalar_tac)
  · cases hc

end SudoRsProofs.Parser
