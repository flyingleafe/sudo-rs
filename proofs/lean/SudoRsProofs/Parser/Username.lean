import SudoRsProofs.Parser.Ast
import SudoRsProofs.Parser.P2Oracle

/-!
# Username tokens

The scanner cannot hand a NUL to `Username::construct`, even through an escape or the
widened `Meta<Username>` classes. For direct constructor calls outside that domain, the
Rust diagnostic retains the original text, and the reference formats that same text.

`sudo_string_nul_diagnostic` and `sudo_string_ok_of_no_nul` state the two outcomes of
`SudoString::new` (`NulInString` / `Ok`) and their reference counterparts: validation
succeeds exactly on texts without NUL. `username_nul_diagnostic` pairs the same outcomes
for `Username::construct` once the embedded-dollar check has passed, using
`validationDiagnostic` (not `KindRel`) to render the raw payload through `O.fmt.debugStr`.
-/

open Aeneas Aeneas.Std Result
open SudoersSpec
open sudo_rs

namespace SudoRsProofs.Parser

private theorem char_beq (c d : Char) : (c == d) = decide (c = d) := rfl

private theorem char_beq_comm (a b : Char) : (a == b) = (b == a) := by
  rw [char_beq, char_beq]
  by_cases h : a = b
  · simp [h]
  · have h' : ¬ b = a := fun e => h e.symm
    simp [h, h']

private theorem username_accept_eq {O : Syntax.CharOracle} (hO : P2CharOracle O) (c : Char) :
    sudoers.tokens.Username.Insts.Sudo_rsSudoersBasic_parserToken.accept c =
      ok (Syntax.Username.accept O c) := by
  simp only [sudoers.tokens.Username.Insts.Sudo_rsSudoersBasic_parserToken.accept,
    hO.is_alphanumeric, bind_ok, Syntax.Username.accept]
  cases O.isAlphanumeric c
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_or]
    split_ifs <;> simp_all [char_beq]
  · rfl

private theorem username_accept_1st_eq {O : Syntax.CharOracle} (hO : P2CharOracle O) (c : Char) :
    sudoers.tokens.Username.Insts.Sudo_rsSudoersBasic_parserToken.accept_1st c =
      ok (Syntax.Username.accept1st O c) := by
  cases hb : (c == '@') <;>
    simp [sudoers.tokens.Username.Insts.Sudo_rsSudoersBasic_parserToken.accept_1st,
      Syntax.Username.accept1st, hb, bne, username_accept_eq hO]

private theorem username_escaped_eq (c : Char) :
    sudoers.tokens.Username.Insts.Sudo_rsSudoersBasic_parserToken.escaped c =
      ok (Syntax.Username.escaped c) := by
  simp only [sudoers.tokens.Username.Insts.Sudo_rsSudoersBasic_parserToken.escaped,
    sudoers.basic_parser.escape_char, bind_ok, Syntax.Username.escaped]
  split_ifs <;> simp_all [char_beq]

/-! ## Constructor checks -/

private theorem contains_char_loop_eq (text : Slice Char) (len : Usize) (c : Char)
    (found : Bool) (i : Usize) (hlen : len.val ≤ text.val.length) :
    sudoers.tokens.contains_char_loop text len c found i =
      ok (found || ((text.val.take len.val).drop i.val).contains c) := by
  cases found with
  | true => rw [sudoers.tokens.contains_char_loop]; rfl
  | false =>
    rw [sudoers.tokens.contains_char_loop]
    simp only [Bool.false_eq_true, Bool.false_or, ↓reduceIte]
    split
    · rename_i hlt
      have hi : i.val < len.val := by scalar_tac
      have hit : i.val < text.val.length := lt_of_lt_of_le hi hlen
      obtain ⟨j, hj, hjv⟩ := exists_eq_ok_of_spec
        (UScalar.add_spec (x := i) (y := 1#usize) (by scalar_tac))
      have hidx : Slice.index_usize text i = ok text.val[i.val] :=
        eq_ok_of_spec (Slice.index_usize_spec text i hit)
      rw [hidx, bind_ok, hj, bind_ok, contains_char_loop_eq text len c _ j hlen]
      have hcut : i.val < (text.val.take len.val).length := by
        simp [List.length_take, Nat.min_eq_left hlen, hi]
      have htail : (text.val.take len.val).drop i.val =
          text.val[i.val] :: (text.val.take len.val).drop j.val := by
        rw [List.drop_eq_getElem_cons hcut]
        have hgi : (text.val.take len.val)[i.val] = text.val[i.val] := by
          rw [List.getElem_take]
        rw [hgi, hjv]
        congr 1
      rw [htail, List.contains_cons, ← char_beq, char_beq_comm]
    · have hge : len.val ≤ i.val := by scalar_tac
      have hdrop : (text.val.take len.val).drop i.val = [] :=
        List.drop_eq_nil_of_le (by simp [List.length_take, Nat.min_eq_left hlen, hge])
      rw [hdrop]; rfl
termination_by len.val - i.val
decreasing_by simp at hjv; omega

private theorem contains_char_eq (text : Slice Char) (len : Usize) (c : Char)
    (hlen : len.val ≤ text.val.length) :
    sudoers.tokens.contains_char text len c = ok ((text.val.take len.val).contains c) := by
  unfold sudoers.tokens.contains_char
  simpa using contains_char_loop_eq text len c false 0#usize hlen

private theorem embedded_dollar_eq (text : Slice Char) :
    sudoers.tokens.embedded_dollar text = ok
      ((if text.val.getLast? == some '$' then text.val.dropLast else text.val).contains '$') := by
  by_cases hn : 0 < text.val.length
  · have hpos : 0#usize < Slice.len text := by simpa using hn
    obtain ⟨i, hi, hiv, _⟩ := exists_eq_ok_of_spec
      (UScalar.sub_spec (x := Slice.len text) (y := 1#usize) (by scalar_tac))
    have hiv' : i.val = text.val.length - 1 := by simpa using hiv
    have hlt : i.val < text.val.length := by omega
    have hidx : Slice.index_usize text i = ok text.val[i.val] :=
      eq_ok_of_spec (Slice.index_usize_spec text i hlt)
    have hlast : text.val.getLast? = some text.val[i.val] := by
      rw [List.getLast?_eq_getElem?, ← hiv', List.getElem?_eq_getElem hlt]
    simp only [sudoers.tokens.embedded_dollar, hpos, ↓reduceIte, hi, hidx, bind_ok, hlast]
    split
    · rename_i hd
      have hb : (some text.val[i.val] == some '$') = true := by simp [hd]
      simp only [hb, ↓reduceIte, bind_ok]
      rw [contains_char_eq text i '$' hlt.le, List.dropLast_eq_take]
      congr 1
      rw [hiv']
    · rename_i hd
      have hb : (some text.val[i.val] == some '$') = false := by
        simpa using hd
      simp only [hb, Bool.false_eq_true, ↓reduceIte, bind_ok]
      rw [contains_char_eq text (Slice.len text) '$' (by simp)]
      simp
  · have hn' : text.val.length = 0 := by omega
    have hpos : ¬ 0#usize < Slice.len text := by simpa using hn
    have hz : text.val = [] := List.length_eq_zero_iff.mp hn'
    simp only [sudoers.tokens.embedded_dollar, hpos, ↓reduceIte, bind_ok]
    rw [contains_char_eq text (Slice.len text) '$' (by simp), hz]
    simp

/-- The embedded-dollar test of `Username::construct`. -/
private def usernameDollar (s : String) : Bool :=
  (if s.toList.getLast? == some '$' then s.toList.dropLast else s.toList).contains '$'

private theorem username_construct_eq (s : String) (hs : s.utf8ByteSize ≤ Usize.max) :
    sudoers.tokens.Username.Insts.Sudo_rsSudoersBasic_parserToken.construct s =
      ok (if usernameDollar s then core.result.Result.Err (.EmbeddedDollar : RKind)
          else if s.toList.contains (Char.ofNat 0) = true then
            core.result.Result.Err (.NulInString s)
          else core.result.Result.Ok ⟨s⟩) := by
  obtain ⟨v, hv, hval⟩ := chars_of_eq s hs
  simp only [sudoers.tokens.Username.Insts.Sudo_rsSudoersBasic_parserToken.construct, hv,
    bind_ok, hval, embedded_dollar_eq, sudoers.tokens.sudo_string]
  by_cases hd : (if s.toList.getLast? == some '$' then s.toList.dropLast
      else s.toList).contains '$' = true
  · have hdU : usernameDollar s = true := hd
    simp only [ite_eq_left hd, ite_eq_left hdU]
  · have hdU : ¬ (usernameDollar s = true) := hd
    simp only [ite_eq_right hd, ite_eq_right hdU]
    by_cases hc : s.toList.contains (Char.ofNat 0) = true
    · simp only [ite_eq_left hc, bind_ok]
    · have hc' : ¬ (s.toList.contains (Char.ofNat 0) = true) := hc
      simp only [ite_eq_right hc', bind_ok]

/-- `SudoString::new` returns the same NUL diagnostic, with the Rust model retaining the
raw text and the reference applying the formatting oracle to it. -/
private theorem sudo_string_nul_diagnostic (O : Syntax.Oracles) (s : String)
    (hNul : '\x00' ∈ s.toList) :
    sudoers.tokens.sudo_string s = ok (.Err (.NulInString s)) ∧
      ∃ k, validationDiagnostic O.fmt (.NulInString s) = some k ∧
        Syntax.sudoStringNew O s.toList = .error k := by
  have hc : s.toList.contains '\x00' = true := by
    rw [List.contains_eq_mem, decide_eq_true_eq]
    exact hNul
  have hr : s.toList.contains (Char.ofNat 0) = true := hc
  refine ⟨?_, ?_⟩
  · simp only [sudoers.tokens.sudo_string, hr, ↓reduceIte]
  · simp only [Syntax.sudoStringNew, hc, ↓reduceIte, String.ofList_toList,
      validationDiagnostic]
    exact ⟨_, rfl, rfl⟩

/-- `SudoString::new` accepts exactly the texts without NUL. -/
theorem sudo_string_ok_of_no_nul (O : Syntax.Oracles) (s : String)
    (hNul : '\x00' ∉ s.toList) :
    sudoers.tokens.sudo_string s = ok (.Ok ⟨s⟩) ∧
      Syntax.sudoStringNew O s.toList = .ok (String.ofList s.toList) := by
  have hc : s.toList.contains '\x00' = false := by
    rw [List.contains_eq_mem]
    simp [hNul]
  have hr : s.toList.contains (Char.ofNat 0) = false := hc
  refine ⟨?_, ?_⟩
  · simp only [sudoers.tokens.sudo_string, hr, Bool.false_eq_true, ↓reduceIte]
  · simp only [Syntax.sudoStringNew, hc, Bool.false_eq_true, ↓reduceIte]

/-- The two possible outcomes of `SudoString::new`, hence its exact domain: NUL is the only
input on which validation fails, and it fails on every such input. -/
theorem sudo_string_domain (O : Syntax.Oracles) (s : String) :
    ('\x00' ∈ s.toList →
        sudoers.tokens.sudo_string s = ok (.Err (.NulInString s)) ∧
          ∃ k, validationDiagnostic O.fmt (.NulInString s) = some k ∧
            Syntax.sudoStringNew O s.toList = .error k) ∧
    ('\x00' ∉ s.toList →
        sudoers.tokens.sudo_string s = ok (.Ok ⟨s⟩) ∧
          Syntax.sudoStringNew O s.toList = .ok (String.ofList s.toList)) :=
  ⟨sudo_string_nul_diagnostic O s, sudo_string_ok_of_no_nul O s⟩

/-- The embedded-dollar check precedes validation. If it passes and there is a NUL, the
constructor's raw error payload renders to the reference error using `O.fmt.debugStr`. -/
theorem username_nul_diagnostic (O : Syntax.Oracles) (s : String) (hs : s.utf8ByteSize ≤ Usize.max)
    (hDollar : (if s.toList.getLast? == some '$' then s.toList.dropLast
      else s.toList).contains '$' = false)
    (hNul : '\x00' ∈ s.toList) :
    sudoers.tokens.Username.Insts.Sudo_rsSudoersBasic_parserToken.construct s =
        ok (.Err (.NulInString s)) ∧
      ∃ k, validationDiagnostic O.fmt (.NulInString s) = some k ∧
        Syntax.Username.construct O s.toList = .error k := by
  obtain ⟨h1, h2⟩ := sudo_string_nul_diagnostic O s hNul
  have hnul : s.toList.contains (Char.ofNat 0) = true := by
    rw [List.contains_eq_mem, decide_eq_true_eq]
    exact hNul
  have hd : ¬ ((if s.toList.getLast? == some '$' then s.toList.dropLast
      else s.toList).contains '$' = true) := by
    rw [Bool.eq_false_iff] at hDollar
    exact hDollar
  have hd' : (if s.toList.getLast? == some '$' then s.toList.dropLast
      else s.toList).contains '$' = false := hDollar
  have hc : Syntax.Username.construct O s.toList = Syntax.sudoStringNew O s.toList := by
    simp only [Syntax.Username.construct, hd', Bool.false_eq_true, ↓reduceIte]
  refine ⟨?_, ?_⟩
  · have hdU : ¬ (usernameDollar s = true) := hd
    simp only [username_construct_eq s hs, ite_eq_right hdU, ite_eq_left hnul]
  · rw [hc]
    exact h2

/-! ## Scanner domain and refinement -/

theorem username_nul_not_accepted {O : Syntax.CharOracle} (hO : P2CharOracle O) :
    Syntax.Username.accept O '\x00' = false := by
  simp only [Syntax.Username.accept, hO.nul_not_alphanumeric, Bool.false_or]
  decide

theorem username_nul_not_accepted_1st {O : Syntax.CharOracle} (hO : P2CharOracle O) :
    Syntax.Username.accept1st O '\x00' = false := by
  simp only [Syntax.Username.accept1st, username_nul_not_accepted hO, bne]
  decide

theorem username_nul_not_escaped : Syntax.Username.escaped '\x00' = false := by
  decide

private theorem tokenText_excludes {α : Type} {T : Syntax.TokenSpec α} {c : Char}
    (hFirst : T.accept1st c = false) (hRest : T.accept c = false) (hEscape : T.escaped c = false)
    (cs : List Char) (hText : TokenText T cs) : c ∉ cs := by
  cases cs with
  | nil => simp
  | cons d ds =>
    change Produces T T.accept1st d ∧ ∀ a ∈ ds, Produces T T.accept a at hText
    intro hm
    rcases List.mem_cons.mp hm with rfl | hm
    · simpa [Produces, hFirst, hEscape] using hText.1
    · simpa [Produces, hRest, hEscape] using hText.2 c hm

/-- Neither ordinary nor escaped username characters can add a NUL to the token text. -/
theorem username_text_no_nul {O : Syntax.Oracles} (hO : P2CharOracle O.char)
    (cs : List Char) (hText : TokenText (Syntax.usernameToken O) cs) : '\x00' ∉ cs :=
  tokenText_excludes (T := Syntax.usernameToken O)
    (by simp [Syntax.usernameToken, username_nul_not_accepted_1st hO])
    (by simp [Syntax.usernameToken, username_nul_not_accepted hO])
    (by simp [Syntax.usernameToken, username_nul_not_escaped]) cs hText

/-- `Username` refines the reference token on texts without NUL. -/
theorem username_token_refines {O : Syntax.Oracles} (hO : P2CharOracle O.char) :
    TokenRefines sudoers.tokens.Username.Insts.Sudo_rsSudoersBasic_parserToken
      common.string.SudoString.str (Syntax.usernameToken O) (fun cs => '\x00' ∉ cs) where
  max_len := ⟨_, rfl, by
    simp [sudoers.basic_parser.Token.MAX_LEN.default, Syntax.usernameToken]⟩
  max_len_le := by
    simp only [Syntax.usernameToken]
    scalar_tac
  allow_escape := by
    simp [sudoers.tokens.Username.Insts.Sudo_rsSudoersBasic_parserToken.ALLOW_ESCAPE,
      Syntax.usernameToken]
  accept c := username_accept_eq hO c
  accept_1st c := username_accept_1st_eq hO c
  escaped c := username_escaped_eq c
  construct s hs hNul := by
    have hc : s.toList.contains '\x00' = false := by
      rw [List.contains_eq_mem]
      simp [hNul]
    have hr : s.toList.contains (Char.ofNat 0) = false := hc
    simp only [username_construct_eq s hs]
    refine ⟨_, rfl, ?_⟩
    by_cases hd : (if s.toList.getLast? == some '$' then s.toList.dropLast
        else s.toList).contains '$' = true
    · have hdU : usernameDollar s = true := hd
      simp only [ite_eq_left hdU]
      simp only [Syntax.usernameToken, Syntax.Username.construct, ite_eq_left hd]
      exact KindRel.embeddedDollar
    · have hdU : ¬ (usernameDollar s = true) := hd
      simp only [ite_eq_right hdU]
      have hd' : ¬ ((if s.toList.getLast? == some '$' then s.toList.dropLast
          else s.toList).contains '$' = true) := hd
      have hd'' : (if s.toList.getLast? == some '$' then s.toList.dropLast
          else s.toList).contains '$' = false := by
        rw [Bool.eq_false_iff]
        exact hd'
      simp only [Syntax.usernameToken, Syntax.Username.construct, hd'', Bool.false_eq_true,
        ↓reduceIte, Syntax.sudoStringNew, hr, String.ofList_toList]
      rfl

/-- The blanket username parser needs no NUL restriction on its input stream. -/
theorem username_parse_refines {O : Syntax.Oracles} (hO : P2CharOracle O.char) :
    ParseRefines
      (sudoers.basic_parser.Parse.Blanket
        sudoers.tokens.Username.Insts.Sudo_rsSudoersBasic_parserToken)
      common.string.SudoString.str (Syntax.token (Syntax.usernameToken O)) :=
  token_refines (username_token_refines hO) (username_text_no_nul hO)

/-- The initial token in `parse_meta`: uppercasing widens the classes but still excludes NUL. -/
theorem meta_username_parse_refines {O : Syntax.Oracles} (hO : P2CharOracle O.char) :
    ParseRefines
      (sudoers.basic_parser.Parse.Blanket
        (sudoers.tokens.Meta.Insts.Sudo_rsSudoersBasic_parserToken
          sudoers.tokens.Username.Insts.Sudo_rsSudoersBasic_parserToken))
      (SudoRsProofs.absMeta common.string.SudoString.str)
      (Syntax.token (Syntax.metaToken O.char (Syntax.usernameToken O))) := by
  apply token_refines (meta_token_refines hO.unicode (username_token_refines hO))
  intro cs hcs
  exact tokenText_excludes (T := Syntax.metaToken O.char (Syntax.usernameToken O))
    (by simp [Syntax.metaToken, Syntax.usernameToken, hO.nul_not_uppercase,
      username_nul_not_accepted_1st hO])
    (by simp [Syntax.metaToken, Syntax.usernameToken, hO.nul_not_uppercase,
      username_nul_not_accepted hO])
    (by simp [Syntax.metaToken, Syntax.usernameToken, username_nul_not_escaped]) cs hcs

/-- The extracted release description is `Descriptions.release.username`. -/
theorem username_description :
    DescRel sudoers.tokens.Username.Insts.Sudo_rsSudoersAst_namesUserFriendly
      Syntax.Descriptions.release.username := by
  refine ⟨_, rfl, ?_⟩
  simp only [sudoers.tokens.Username.Insts.Sudo_rsSudoersAst_namesUserFriendly.DESCRIPTION]
  exact toStr_val _ _

end SudoRsProofs.Parser
