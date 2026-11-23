import SudoRsProofs.Parser.Ast

open Aeneas Aeneas.Std Result
open SudoersSpec.Syntax (Descriptions ErrKind Oracles Parser aliasNameToken chDirToken
  expectNonterminal expectSyntax isSyntax stringParameterToken token tryNonterminal utf8Len)

namespace SudoRsProofs.Parser

open sudo_rs.sudoers

private abbrev TagMeta := SudoersSpec.Meta SudoersSpec.Modifier

private theorem chdir_description :
    DescRel tokens.ChDir.Insts.Sudo_rsSudoersAst_namesUserFriendly Descriptions.release.chDir :=
  ⟨_, rfl, by
    simp only [tokens.ChDir.Insts.Sudo_rsSudoersAst_namesUserFriendly.DESCRIPTION]
    exact toStr_val _ _⟩

private theorem string_parameter_description :
    DescRel tokens.StringParameter.Insts.Sudo_rsSudoersAst_namesUserFriendly
      Descriptions.release.stringParameter :=
  ⟨_, rfl, by
    simp only [tokens.StringParameter.Insts.Sudo_rsSudoersAst_namesUserFriendly.DESCRIPTION,
      tokens.QuotedStringParameter.Insts.Sudo_rsSudoersAst_namesUserFriendly.DESCRIPTION]
    exact toStr_val _ _⟩

/-- The token length check precedes each append, allowing up to four bytes for that character. -/
private theorem token_length_bound (m : Nat) (cs acc : List Char) (hacc : utf8Len acc ≤ m + 4)
    (h : SudoersSpec.Grammar.LenOK m acc cs) : utf8Len (acc ++ cs) ≤ m + 4 := by
  induction cs generalizing acc with
  | nil => simpa using hacc
  | cons c cs ih =>
    change utf8Len acc < m ∧ SudoersSpec.Grammar.LenOK m (acc ++ [c]) cs at h
    have hc := Char.utf8Size_le_four c
    have hpush : utf8Len (acc ++ [c]) ≤ m + 4 := by
      rw [utf8Len_append]
      simp only [utf8Len_cons, utf8Len_nil, Nat.add_zero]
      have := h.1
      omega
    simpa only [List.append_assoc, List.singleton_append] using ih (acc ++ [c]) hpush h.2

private theorem ofList_bytes (cs : List Char) : (String.ofList cs).utf8ByteSize = utf8Len cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    change (String.ofList ([c] ++ cs)).utf8ByteSize = utf8Len ([c] ++ cs)
    simp only [String.ofList_append, String.utf8ByteSize_append, ← String.singleton_eq_ofList,
      String.utf8ByteSize_singleton, ih, utf8Len_append, utf8Len_cons, utf8Len_nil, Nat.add_zero]

private theorem alias_text_fits {c : Char} {cs : List Char}
    (h : SudoersSpec.Grammar.LenOK 255 [c] cs) : Fits (String.ofList (c :: cs)) := by
  simp only [Fits, sudo_rs.stringBytes, List.length_map, Array.length_toList]
  change (String.ofList (c :: cs)).utf8ByteSize ≤ Usize.max
  rw [ofList_bytes]
  have hc := Char.utf8Size_le_four c
  have hfirst : utf8Len [c] ≤ 255 + 4 := by
    simp only [utf8Len_cons, utf8Len_nil, Nat.add_zero]
    omega
  exact (token_length_bound 255 cs [c] hfirst h).trans (by scalar_tac)

/-- `String::as_str` is total on every keyword returned by the alias-name token. -/
private theorem keyword_fits {s s' : SudoersSpec.Syntax.Stream} {kw : String}
    (h : (tryNonterminal (token aliasNameToken)).run s = (.ok kw, s')) : Fits kw := by
  obtain ⟨kw₀, s₁, hn, hrest⟩ := Parser.run_bind_eq_ok.mp h
  obtain ⟨_, _, _, hpure⟩ := Parser.run_bind_eq_ok.mp hrest
  simp only [Parser.run_pure, Prod.mk.injEq, Except.ok.injEq] at hpure
  rw [← hpure.1]
  obtain ⟨_, _, hg⟩ := SudoersSpec.Grammar.token_sound aliasNameToken s kw₀ s₁ hn
  cases hg with
  | mk _ _ hlen hconstruct =>
    simp only [aliasNameToken, Except.ok.injEq] at hconstruct
    rw [← hconstruct]
    exact alias_text_fits hlen

private theorem keyword_eq (kw lit : String) (hkw : Fits kw) (hlit : lit.toByteArray.size ≤ U32.max) :
    Str.Insts.CoreCmpPartialEqStr.eq (strOf kw hkw) (toStr lit hlit) = ok (decide (kw = lit)) := by
  rw [eq_ok_of_spec (Str.eq_spec _ _)]
  simp only [strOf_val, toStr_val, stringBytes_inj]

/-- Reduce a generated comparison and select its continuation without visiting the unused arm. -/
private theorem keyword_case_yes {α : Type} {kw lit : String} {hkw : Fits kw}
    {hlit : lit.toByteArray.size ≤ U32.max} (yes no : Result α) (h : kw = lit) :
    (do
      let b ← Str.Insts.CoreCmpPartialEqStr.eq (strOf kw hkw) (toStr lit hlit)
      if b then yes else no) = yes := by
  simp only [keyword_eq, bind_ok, decide_eq_true_eq, ite_eq_left h]

private theorem keyword_case_no {α : Type} {kw lit : String} {hkw : Fits kw}
    {hlit : lit.toByteArray.size ≤ U32.max} (yes no : Result α) (h : kw ≠ lit) :
    (do
      let b ← Str.Insts.CoreCmpPartialEqStr.eq (strOf kw hkw) (toStr lit hlit)
      if b then yes else no) = no := by
  simp only [keyword_eq, bind_ok, decide_eq_true_eq, ite_eq_right h]

/-- Apply one callee's refinement directly to an extracted `?` and retain its successful
cursor and value for the next call. The error branch is finished at the callee's cursor. -/
local macro "tag_step " hp:term "," spec:term " with " x:ident t:ident ht:ident : tactic =>
  `(tactic| (
    obtain ⟨r, $t, er, hrel, $ht, ha⟩ := $hp
    rcases hq : $spec with ⟨r', t'⟩
    rw [hq] at hrel ha
    subst ha
    rw [er]
    simp only [bind_ok, uncurry_apply_pair, Parser.run_bind, hq]
    rcases r with $x | e <;> rcases r' with e' | x' <;> simp only [ResultRel] at hrel
    swap
    · simp [hrel, ($ht)]
    try subst x'
    simp only [branch_Ok, bind_ok]))

private theorem fatal_arm (p : Usize × Usize) {k : RKind} {kind : ErrKind}
    (hk : KindRel k kind) {s : CS} (h : StreamOK s) :
    Refines (absMeta absModifier)
      (do let r ← basic_parser.fatal_from ast.MetaOrTag p s k; ok (r, s))
      ((Parser.fatalFrom (p.1.val, p.2.val) kind : Parser TagMeta).run (absStream s)) := by
  simp only [fatal_from_eq, bind_ok, Parser.run_fatalFrom, refines_ok_iff, ResultRel]
  exact ⟨StatusRel.from hk, h, trivial⟩

private theorem all_arm {s : CS} (h : StreamOK s) :
    Refines (absMeta absModifier) (do let r ← basic_parser.make .All; ok (r, s))
      ((pure .all : Parser TagMeta).run (absStream s)) := by
  simp [absMeta, h]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2048 in
/-- The extracted `MetaOrTag::parse` refines the release parser, including positions captured
before consuming an ignored tag's colon and the cursor after an unsupported modifier's `=`. -/
theorem meta_or_tag_refines (O : Oracles)
    (hAlias : ParseRefines (basic_parser.Parse.Blanket
      tokens.AliasName.Insts.Sudo_rsSudoersBasic_parserToken) id (token aliasNameToken))
    (hCwd : ParseRefines (basic_parser.Parse.Blanket
      tokens.ChDir.Insts.Sudo_rsSudoersBasic_parserToken) absChDir (token (chDirToken O)))
    (hProfile : ParseRefines (basic_parser.Parse.Blanket
      tokens.StringParameter.Insts.Sudo_rsSudoersBasic_parserToken) id
      (token (stringParameterToken O.char))) :
    ParseRefines ast.MetaOrTag.Insts.Sudo_rsSudoersBasic_parserParse (absMeta absModifier)
      (SudoersSpec.Syntax.metaOrTag O .release) := by
  constructor
  intro s hs
  obtain ⟨r, s₁, er, hrel, hs₁, ha⟩ := try_nonterminal_refines hAlias hs
  rcases he : (tryNonterminal (token aliasNameToken)).run (absStream s) with ⟨r', s₂⟩
  rw [he] at hrel ha
  subst ha
  show Refines (absMeta absModifier) (ast.MetaOrTag.Insts.Sudo_rsSudoersBasic_parserParse.parse s) _
  conv =>
    arg 3
    simp only [SudoersSpec.Syntax.metaOrTag, Parser.run_bind, Parser.run_getPos, he]
  rcases r with kw | st <;> rcases r' with st' | kw' <;> simp only [ResultRel] at hrel
  · change kw = kw' at hrel
    subst kw'
    conv =>
      arg 3
      simp only
    have hkw := keyword_fits he
    have hstr : alloc.string.String.as_str kw = ok (strOf kw hkw) := strOfString_eq hkw
    -- Split only the reference match. Open the large extracted body afterward, and
    -- prune each comparison before the simplifier descends into its continuations.
    split
    all_goals
      conv =>
        arg 2
        delta ast.MetaOrTag.Insts.Sudo_rsSudoersBasic_parserParse.parse
        rw [get_pos_eq', bind_ok, er, bind_ok, uncurry_apply_pair, branch_Ok, bind_ok]
        change (Aeneas.Std.bind (alloc.string.String.as_str _) _)
        rw [hstr, bind_ok]
        tactic =>
          repeat
            first
            | rewrite (occs := .pos [1]) [keyword_case_yes]
              swap
              decide
            | rewrite (occs := .pos [1]) [keyword_case_no]
              swap
              first | assumption | decide
    all_goals
      first
      | exact fatal_arm _ (KindRel.tagNotSupported _) hs₁
      | exact fatal_arm _ KindRel.selinuxNotSupported hs₁
      | exact all_arm hs₁
      | unfold ast.switch
        tag_step (expect_syntax_refines hs₁ ':'),
          ((expectSyntax ':').run (absStream s₁)) with u t ht
        simp [absMeta, absModifier, ht]
      | rw [get_pos_eq', bind_ok]
        simp only [Parser.run_bind, Parser.run_getPos]
        tag_step (expect_syntax_refines hs₁ ':'),
          ((expectSyntax ':').run (absStream s₁)) with u t ht
        simp [absMeta, absModifier, absSpan, ht]
      | tag_step (expect_syntax_refines hs₁ '='),
          ((expectSyntax '=').run (absStream s₁)) with u t ht
        first
        | tag_step (expect_nonterminal_refines hCwd chdir_description ht),
            ((expectNonterminal Descriptions.release.chDir (token (chDirToken O))).run
              (absStream t)) with x t' ht'
          simp [absMeta, absModifier, ht']
        | tag_step (expect_nonterminal_refines hProfile string_parameter_description ht),
            ((expectNonterminal Descriptions.release.stringParameter
              (token (stringParameterToken O.char))).run (absStream t)) with x t' ht'
          simp [absMeta, absModifier, ht']
      | tag_step (is_syntax_refines hs₁ '='),
          ((isSyntax '=').run (absStream s₁)) with eq t ht
        cases eq
        · simp [absMeta, ht]
        · simpa only [id_eq, ↓reduceIte, absStream_getPos] using
            fatal_arm (s.line, s.col) (KindRel.unsupportedModifier _) ht
  · delta ast.MetaOrTag.Insts.Sudo_rsSudoersBasic_parserParse.parse
    simp only [↓get_pos_eq', ↓er, ↓bind_ok, ↓uncurry_apply_pair, ↓branch_Err, from_residual_Err]
    exact ⟨_, _, rfl, hrel, hs₁, rfl⟩

end SudoRsProofs.Parser
