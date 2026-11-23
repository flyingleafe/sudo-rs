import SudoRsProofs.Parser.Token
import SudoRsProofs.Parser.List
import SudoRsProofs.Parser.Tokens

/-!
# `Qualified<T>`, the descriptions, and `SpecList<Hostname>` (`host_list`)

* `qualified_refines`: `impl Parse for Qualified<T>` refines `qualified` for any refining `T`;
* `DescRel` for the `UserFriendly` instances: `toStr` literals are the UTF-8 bytes of the
  reference strings (`toStr_val`); `Hostname::DESCRIPTION` is
  `Descriptions.release.hostname` (`hostname_description`), and `Meta<T>`, `Qualified<T>`
  delegate to `T` (`desc_meta`, `desc_qualified`). The extraction is a release build
  (`#[cfg(not(test))]`), so the release table is the one that applies;
* `ManyRefines` for `Hostname`, `Meta<T>`, `Qualified<T>`;
* **the P1 theorems** `spec_list_hostname_refines` (the `Vec<Qualified<Meta<Hostname>>>`
  instance refines `specListHostname O D`) and `host_list_refines` (`host_list`, i.e.
  `try_nonterminal::<SpecList<Hostname>>`, refines `tryNonterminal (specListHostname O D)`),
  for every representable stream; `host_list_refines_text` states it on a whole input, with a
  precondition on the input length only.
-/

open Aeneas Aeneas.Std Result
open SudoersSpec.Syntax (Stream ErrKind Parser Parsed TokenSpec CharOracle)

namespace SudoRsProofs.Parser

/-! ## `Qualified<T>` -/

/-- The reference loop `while is_syntax('!')? { neg = !neg }` of `qualified`. -/
abbrev refBangLoop (neg : Bool) : Parser Bool :=
  Parser.whileMaybe (SudoersSpec.Syntax.trySyntax '!') (SudoersSpec.Syntax.trySyntax_consumes '!')
    (fun neg _ => pure (.next !neg)) id neg

theorem qualified_loop_false (st : CS) (neg : Bool) (failure : Option RStatus) :
    sudo_rs.sudoers.ast.Qualified.Insts.Sudo_rsSudoersBasic_parserParse.parse_loop st neg failure
      false = ok (st.src, st.pos, st.line, st.col, neg, failure) := by
  rw [sudo_rs.sudoers.ast.Qualified.Insts.Sudo_rsSudoersBasic_parserParse.parse_loop]; simp

theorem qualified_loop_eq (st : CS) (h : StreamOK st) (neg : Bool) :
    ∃ (s' : CS) (neg' : Bool) (failure : Option RStatus),
      sudo_rs.sudoers.ast.Qualified.Insts.Sudo_rsSudoersBasic_parserParse.parse_loop st neg none
          true = ok (s'.src, s'.pos, s'.line, s'.col, neg', failure) ∧ StreamOK s' ∧
      ResultRel id (match failure with | none => .Ok neg' | some e => .Err e)
        ((refBangLoop neg).run (absStream st)).1 ∧
      absStream s' = ((refBangLoop neg).run (absStream st)).2 := by
  obtain ⟨r, s1, e1, hr, h1, a1⟩ := is_syntax_refines h '!'
  rw [sudo_rs.sudoers.ast.Qualified.Insts.Sudo_rsSudoersBasic_parserParse.parse_loop]
  simp only [↓reduceIte, e1, bind_ok, uncurry_apply_pair]
  unfold refBangLoop Parser.whileMaybe
  rw [Parser.loop_run]
  simp only [Parser.whileMaybeBody, Parser.run_bind, Parser.run_maybe]
  simp only [SudoersSpec.Syntax.isSyntax, Parser.run_bind, Parser.run_maybe] at hr a1
  rcases hR : (SudoersSpec.Syntax.trySyntax '!').run (absStream st) with ⟨r', s''⟩
  rw [hR] at hr a1
  rcases r with b | st' <;> rcases r' with (⟨sp', k'⟩ | _) | ⟨⟩ <;>
    simp [SudoersSpec.Syntax.maybe] at hr a1 <;> subst a1
  · -- `Reject`: no more `!`
    subst hr
    refine ⟨s1, neg, none, by simp [qualified_loop_false], h1, ?_, ?_⟩ <;>
      simp [SudoersSpec.Syntax.maybe, Parser.run_pure]
  · -- one more `!`
    subst hr
    have hc := (SudoersSpec.Syntax.trySyntax_consumes '!') _ _ _ hR
    have hlt : s1.src.val.length - s1.pos.val < st.src.val.length - st.pos.val := by
      simpa using hc
    obtain ⟨s', neg', failure, e', h', hr', a'⟩ := qualified_loop_eq s1 h1 (!neg)
    have hneg : (decide ¬ neg = true) = !neg := by cases neg <;> rfl
    simp only [SudoersSpec.Syntax.maybe, ↓reduceIte, hneg, Parser.run_pure]
    exact ⟨s', neg', failure, e', h', hr', a'⟩
  · -- a fatal error
    refine ⟨s1, neg, some st', by simp [qualified_loop_false], h1, ?_, ?_⟩ <;>
      simp [SudoersSpec.Syntax.maybe, hr]
termination_by (absStream st).rest.length

/-- **`impl Parse for Qualified<T>` refines `qualified`.** -/
theorem qualified_refines {T α : Type} {P : sudo_rs.sudoers.basic_parser.Parse T}
    {UF : sudo_rs.sudoers.ast_names.UserFriendly T} {f : T → α} {p : Parser α} {d : String}
    (hP : ParseRefines P f p) (hD : DescRel UF d) :
    ParseRefines (sudo_rs.sudoers.ast.Qualified.Insts.Sudo_rsSudoersBasic_parserParse P UF)
      (absQualified f) (SudoersSpec.Syntax.qualified d p) := by
  constructor
  intro s h
  obtain ⟨r, s1, e1, hr, h1, a1⟩ := is_syntax_refines h '!'
  show Refines (absQualified f)
    (sudo_rs.sudoers.ast.Qualified.Insts.Sudo_rsSudoersBasic_parserParse.parse P UF s) _
  unfold sudo_rs.sudoers.ast.Qualified.Insts.Sudo_rsSudoersBasic_parserParse.parse
  simp only [SudoersSpec.Syntax.qualified, Parser.run_bind, e1, bind_ok, uncurry_apply_pair]
  rcases hR : (SudoersSpec.Syntax.isSyntax '!').run (absStream s) with ⟨r', s''⟩
  rw [hR] at hr a1
  subst a1
  rcases r with b | st <;> rcases r' with e' | b' <;> simp only [ResultRel] at hr
  · subst hr
    cases b with
    | true =>
      simp only [id_eq, ↓reduceIte, Parser.run_bind]
      obtain ⟨s2, neg, failure, e2, h2, hr2, a2⟩ := qualified_loop_eq s1 h1 true
      simp only [branch_Ok, ↓reduceIte, e2, bind_ok, uncurry_apply_pair]
      rcases hW : (refBangLoop true).run (absStream s1) with ⟨w, s3⟩
      rw [hW] at hr2 a2
      simp only at a2
      subst a2
      rcases failure with _ | st <;> rcases w with e3 | neg' <;> simp only [ResultRel] at hr2
      · subst hr2
        obtain ⟨r4, s4, e4, hr4, h4, a4⟩ := expect_nonterminal_refines hP hD h2
        simp only [e4, bind_ok, uncurry_apply_pair]
        rcases hE : (SudoersSpec.Syntax.expectNonterminal d p).run (absStream s2) with ⟨r5, s5⟩
        rw [hE] at hr4 a4
        simp only at a4
        subst a4
        rcases r4 with x | st4 <;> rcases r5 with e5 | a <;> simp only [ResultRel] at hr4
        · cases neg <;> simp [h4, hr4, absQualified]
        · simp [h4, hr4]
      · simp [h2, hr2]
    | false =>
      simp only [id_eq, Bool.false_eq_true, ↓reduceIte, Parser.run_bind]
      obtain ⟨r4, s4, e4, hr4, h4, a4⟩ := try_nonterminal_refines hP h1
      simp only [branch_Ok, Bool.false_eq_true, ↓reduceIte, e4, bind_ok, uncurry_apply_pair]
      rcases hE : (SudoersSpec.Syntax.tryNonterminal p).run (absStream s1) with ⟨r5, s5⟩
      rw [hE] at hr4 a4
      simp only at a4
      subst a4
      rcases r4 with x | st4 <;> rcases r5 with e5 | a <;> simp only [ResultRel] at hr4
      · simp [h4, hr4, absQualified]
      · simp [h4, hr4]
  · simp [hr, h1]

/-! ## Descriptions -/

theorem byteArray_toList_eq (bs : ByteArray) : bs.toList = bs.data.toList := by
  have key : ∀ i r, i ≤ bs.size →
      ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
    intro i r hi
    fun_induction ByteArray.toList.loop bs i r with
    | case1 i r h ih =>
      rw [ih (by omega)]
      have hi' : i < bs.data.toList.length := by simpa using h
      rw [List.drop_eq_getElem_cons hi']
      simp [ByteArray.get!, h]
    | case2 i r h =>
      have : bs.data.toList.length ≤ i := by simp; omega
      simp [List.drop_eq_nil_of_le this]
  simpa [ByteArray.toList] using key 0 [] (Nat.zero_le _)

/-- A Rust string literal (`toStr`) is the UTF-8 encoding of the Lean string. -/
theorem toStr_val (s : String) (h : s.toByteArray.size ≤ U32.max) :
    (toStr s h).val = sudo_rs.stringBytes s := by
  simp only [toStr, sudo_rs.stringBytes, byteArray_toList_eq, Slice.from_val]
  apply List.map_congr_left
  intro x _
  rfl

/-- `Hostname::DESCRIPTION` (release build) is the reference `Descriptions.release.hostname`. -/
theorem hostname_description :
    DescRel sudo_rs.sudoers.tokens.Hostname.Insts.Sudo_rsSudoersAst_namesUserFriendly
      SudoersSpec.Syntax.Descriptions.release.hostname :=
  ⟨_, rfl, by
    simp only [sudo_rs.sudoers.tokens.Hostname.Insts.Sudo_rsSudoersAst_namesUserFriendly.DESCRIPTION]
    exact toStr_val _ _⟩

/-- `Meta<T>::DESCRIPTION` is `T::DESCRIPTION`. -/
theorem desc_meta {T : Type} {UF : sudo_rs.sudoers.ast_names.UserFriendly T} {d : String}
    (hD : DescRel UF d) :
    DescRel (sudo_rs.sudoers.tokens.Meta.Insts.Sudo_rsSudoersAst_namesUserFriendly UF) d := by
  obtain ⟨s, hs, hv⟩ := hD
  exact ⟨s, by
    simp only [sudo_rs.sudoers.tokens.Meta.Insts.Sudo_rsSudoersAst_namesUserFriendly.DESCRIPTION,
      hs], hv⟩

/-- `Qualified<T>::DESCRIPTION` is `T::DESCRIPTION`. -/
theorem desc_qualified {T : Type} {UF : sudo_rs.sudoers.ast_names.UserFriendly T} {d : String}
    (hD : DescRel UF d) :
    DescRel (sudo_rs.sudoers.ast.Qualified.Insts.Sudo_rsSudoersAst_namesUserFriendly UF) d := by
  obtain ⟨s, hs, hv⟩ := hD
  exact ⟨s, by
    simp only [sudo_rs.sudoers.ast.Qualified.Insts.Sudo_rsSudoersAst_namesUserFriendly.DESCRIPTION,
      hs], hv⟩

/-! ## `Many` -/

theorem hostname_many :
    ManyRefines sudo_rs.sudoers.tokens.Hostname.Insts.Sudo_rsSudoersBasic_parserMany
      SudoersSpec.Syntax.hostnameMany :=
  ⟨by simp [sudo_rs.sudoers.basic_parser.Many.SEP.default, SudoersSpec.Syntax.hostnameMany],
   ⟨_, rfl, by
     simp [sudo_rs.sudoers.basic_parser.Many.LIMIT.default, SudoersSpec.Syntax.hostnameMany]⟩⟩

theorem many_meta {T : Type} {M : sudo_rs.sudoers.basic_parser.Many T}
    {m : SudoersSpec.Syntax.Many} (hM : ManyRefines M m) :
    ManyRefines (sudo_rs.sudoers.tokens.Meta.Insts.Sudo_rsSudoersBasic_parserMany M)
      (SudoersSpec.Syntax.metaMany m) := by
  obtain ⟨hs, n, hn, hv⟩ := hM
  exact ⟨by simp [sudo_rs.sudoers.tokens.Meta.Insts.Sudo_rsSudoersBasic_parserMany.SEP, hs,
      SudoersSpec.Syntax.metaMany],
    ⟨n, by simp [sudo_rs.sudoers.tokens.Meta.Insts.Sudo_rsSudoersBasic_parserMany.LIMIT, hn],
      by simp [hv, SudoersSpec.Syntax.metaMany]⟩⟩

theorem many_qualified {T : Type} {M : sudo_rs.sudoers.basic_parser.Many T}
    {m : SudoersSpec.Syntax.Many} (hM : ManyRefines M m) :
    ManyRefines (sudo_rs.sudoers.ast.Qualified.Insts.Sudo_rsSudoersBasic_parserMany M)
      (SudoersSpec.Syntax.qualifiedMany m) := by
  obtain ⟨hs, n, hn, hv⟩ := hM
  exact ⟨by simp [sudo_rs.sudoers.ast.Qualified.Insts.Sudo_rsSudoersBasic_parserMany.SEP, hs,
      SudoersSpec.Syntax.qualifiedMany],
    ⟨n, by simp [sudo_rs.sudoers.ast.Qualified.Insts.Sudo_rsSudoersBasic_parserMany.LIMIT, hn],
      by simp [hv, SudoersSpec.Syntax.qualifiedMany]⟩⟩

/-! ## `SpecList<Hostname>` -/

/-- The extracted `Parse` instance of `SpecList<Hostname> = Vec<Qualified<Meta<Hostname>>>`, as
`host_list` builds it. -/
abbrev specListHostnameInst :
    sudo_rs.sudoers.basic_parser.Parse
      (alloc.vec.Vec (sudo_rs.sudoers.ast.Qualified (sudo_rs.sudoers.tokens.Meta
        sudo_rs.sudoers.tokens.Hostname))) :=
  sudo_rs.alloc.vec.Vec.Insts.Sudo_rsSudoersBasic_parserParse
    (sudo_rs.sudoers.ast.Qualified.Insts.Sudo_rsSudoersBasic_parserParse
      (sudo_rs.sudoers.basic_parser.Parse.Blanket
        (sudo_rs.sudoers.tokens.Meta.Insts.Sudo_rsSudoersBasic_parserToken
          sudo_rs.sudoers.tokens.Hostname.Insts.Sudo_rsSudoersBasic_parserToken))
      (sudo_rs.sudoers.tokens.Meta.Insts.Sudo_rsSudoersAst_namesUserFriendly
        sudo_rs.sudoers.tokens.Hostname.Insts.Sudo_rsSudoersAst_namesUserFriendly))
    (sudo_rs.sudoers.ast.Qualified.Insts.Sudo_rsSudoersBasic_parserMany
      (sudo_rs.sudoers.tokens.Meta.Insts.Sudo_rsSudoersBasic_parserMany
        sudo_rs.sudoers.tokens.Hostname.Insts.Sudo_rsSudoersBasic_parserMany))
    (sudo_rs.sudoers.ast.Qualified.Insts.Sudo_rsSudoersAst_namesUserFriendly
      (sudo_rs.sudoers.tokens.Meta.Insts.Sudo_rsSudoersAst_namesUserFriendly
        sudo_rs.sudoers.tokens.Hostname.Insts.Sudo_rsSudoersAst_namesUserFriendly))

/-- A host list as the reference `SpecList Hostname`. -/
def absHostList
    (v : alloc.vec.Vec (sudo_rs.sudoers.ast.Qualified (sudo_rs.sudoers.tokens.Meta
      sudo_rs.sudoers.tokens.Hostname))) : SudoersSpec.SpecList SudoersSpec.Hostname :=
  absSpecList id v.val

/-- **P1: the extracted `SpecList<Hostname>` parser refines `specListHostname`** for every
character oracle that the Unicode predicates agree with, and every description table whose
`hostname` entry is the release one. -/
theorem spec_list_hostname_refines {O : CharOracle} (hO : UnicodeOracle O)
    (D : SudoersSpec.Syntax.Descriptions)
    (hD : D.hostname = SudoersSpec.Syntax.Descriptions.release.hostname) :
    ParseRefines specListHostnameInst absHostList (SudoersSpec.Syntax.specListHostname O D) := by
  have hDesc : DescRel sudo_rs.sudoers.tokens.Hostname.Insts.Sudo_rsSudoersAst_namesUserFriendly
      D.hostname := hD ▸ hostname_description
  have hTok := token_refines (meta_token_refines hO (hostname_token_refines hO))
  have hQ := qualified_refines hTok (desc_meta hDesc)
  have hV := vec_refines hQ (many_qualified (many_meta hostname_many))
    (desc_qualified (desc_meta hDesc))
  exact hV

/-- **P1: `host_list` (`try_nonterminal::<SpecList<Hostname>>`) refines
`tryNonterminal (specListHostname O D)`**, total correctness, on every representable stream. -/
theorem host_list_refines {O : CharOracle} (hO : UnicodeOracle O)
    (D : SudoersSpec.Syntax.Descriptions)
    (hD : D.hostname = SudoersSpec.Syntax.Descriptions.release.hostname) {s : CS}
    (h : StreamOK s) :
    Refines absHostList (sudo_rs.sudoers.ast.host_list s)
      ((SudoersSpec.Syntax.tryNonterminal (SudoersSpec.Syntax.specListHostname O D)).run
        (absStream s)) :=
  try_nonterminal_refines (spec_list_hostname_refines hO D hD) h

/-- `host_list` on a whole input `src` (a cursor at position 0, line 1, column 1): the only
precondition is the input length. -/
theorem host_list_refines_text {O : CharOracle} (hO : UnicodeOracle O) (src : Slice Char)
    (hlen : src.val.length < Usize.max) :
    Refines absHostList (sudo_rs.sudoers.ast.host_list ⟨src, 0#usize, 1#usize, 1#usize⟩)
      ((SudoersSpec.Syntax.tryNonterminal
          (SudoersSpec.Syntax.specListHostname O SudoersSpec.Syntax.Descriptions.release)).run
        (Stream.new src.val)) :=
  host_list_refines hO _ rfl (StreamOK.initial src hlen)

end SudoRsProofs.Parser
