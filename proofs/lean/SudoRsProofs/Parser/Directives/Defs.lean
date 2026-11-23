import SudoRsProofs.Parser.Directives.IncludeTokens
import SudoRsProofs.Parser.Directives.Keywords
import SudoRsProofs.Parser.AliasName
import SudoRsProofs.Parser.PermissionLines.UserLists
import SudoRsProofs.Parser.PermissionLines.Commands
import SudoersSpec.Syntax.Sudo
import SudoRsProofs.Parser.Digits
import SudoRsProofs.Parser.Parameters

/-! Alias definitions and their `:`-separated lists. `=` and list separators establish the
command leaf's `NoBlankNext` condition before a `Qualified<Meta<Command>>` is called. The
user alias case instead carries the forward-stable quoted-stream size budget. -/

open Aeneas Aeneas.Std Result SudoersSpec
open SudoersSpec.Syntax (Parser Stream Descriptions Oracles Many)

namespace SudoRsProofs.Parser

open sudo_rs sudo_rs.sudoers

private abbrev D := Descriptions.release

/-- A successful expected delimiter has the same trailing-whitespace behavior as its tried form. -/
theorem expectSyntax_ok_next {c : Char} {s s' : Stream} {v : Unit}
    (h : (Syntax.expectSyntax c).run s = (.ok v, s')) : NoBlankNext s' := by
  unfold Syntax.expectSyntax at h
  simp only [Parser.run_bind, Parser.run_observe] at h
  rcases he : (Syntax.trySyntax c).run s with ⟨r, s1⟩
  rw [he] at h
  rcases r with e | ⟨⟩
  · simp [Parser.run_bind, Parser.run_peek] at h
  · simp only [Parser.run_pure, Prod.mk.injEq] at h
    exact h.2 ▸ trySyntax_ok_next he

/-! ## Lists whose item starts require a whitespace boundary -/

section BoundaryList

variable {T α : Type} {P : basic_parser.Parse T} {UF : ast_names.UserFriendly T}
  {f : T → α} {p : Parser α} {d : String}

/-- Unlike a forward-stable input invariant, `NoBlankNext` need not hold at every intermediate
cursor. A continuing list iteration establishes it at the next item through `trySyntax`. -/
private theorem boundary_list_loop_eq
    (hP : ParseRefinesOn NoBlankNext P f p) (hD : DescRel UF d) (sep : Char)
    (max : Usize) (st : CS) (h : StreamOK st) (elems : alloc.vec.Vec T) :
    ∃ (s' : CS) (elems' : alloc.vec.Vec T) (failure : Option RStatus),
      basic_parser.parse_list_loop P UF sep max st elems none true =
        ok (s'.src, s'.pos, s'.line, s'.col, elems', failure) ∧ StreamOK s' ∧
      ResultRel (absVec f) (match failure with | none => .Ok elems' | some e => .Err e)
        ((refListLoop sep max.val d p (absVec f elems)).run (absStream st)).1 ∧
      absStream s' = ((refListLoop sep max.val d p (absVec f elems)).run (absStream st)).2 := by
  obtain ⟨r, s1, e1, hr, h1, a1⟩ := try_syntax_refines h sep
  rw [basic_parser.parse_list_loop]
  simp only [↓reduceIte, e1, bind_ok, uncurry_apply_pair]
  unfold refListLoop Parser.whileMaybe
  rw [Parser.loop_run]
  simp only [Parser.whileMaybeBody, Parser.run_bind, Parser.run_maybe]
  rcases hR : (Syntax.trySyntax sep).run (absStream st) with ⟨r', s''⟩
  rw [hR] at hr a1
  subst a1
  rcases r with ⟨⟩ | (⟨sp, k⟩ | _) <;> rcases r' with (⟨sp', k'⟩ | _) | ⟨⟩ <;>
    simp only [ResultRel, StatusRel.fatal_reject, StatusRel.reject_fatal] at hr
  · simp only [Syntax.maybe, Syntax.parseListBody]
    by_cases hge : (absVec f elems).length ≥ max.val
    · have hge' : alloc.vec.Vec.len elems ≥ max := by
        simp only [absVec, List.length_map] at hge; scalar_tac
      refine ⟨s1, elems, some (.Fatal ⟨(s1.line, s1.col), (s1.line, s1.col)⟩ .TooManyItems),
        ?_, h1, ?_, ?_⟩
      · simp [hge', parse_list_loop_false]
      · simp [hge, Parser.run_fatalHere]
      · simp [hge, Parser.run_fatalHere]
    · have hge' : ¬ alloc.vec.Vec.len elems ≥ max := by
        simp only [absVec, List.length_map] at hge; scalar_tac
      obtain ⟨r2, s2, e2, hr2, h2, a2⟩ :=
        expect_nonterminal_refines_at (hP s1 h1 (trySyntax_ok_next hR)) hD
      simp only [hge, hge', ↓reduceIte, e2, bind_ok, uncurry_apply_pair, Parser.run_bind]
      rcases hE : (Syntax.expectNonterminal d p).run (absStream s1) with ⟨r2', s3⟩
      rw [hE] at hr2 a2
      subst a2
      rcases r2 with x | st2 <;> rcases r2' with e2' | a <;> simp only [ResultRel] at hr2
      · have hlen : elems.val.length < Usize.max := by
          simp only [absVec, List.length_map] at hge; scalar_tac
        obtain ⟨elems1, hpush, hpv⟩ := exists_eq_ok_of_spec (alloc.vec.Vec.push_spec elems x hlen)
        have hc := (Syntax.trySyntax_consumes sep) _ _ _ hR
        have hl2 := Parser.length_le_of_run hE
        have hlt : s2.src.val.length - s2.pos.val < st.src.val.length - st.pos.val := by
          simp only [absStream_rest, List.length_drop] at hc hl2; omega
        obtain ⟨s', elems', failure, e', h', hr', a'⟩ :=
          boundary_list_loop_eq hP hD sep max s2 h2 elems1
        have habs : absVec f elems1 = absVec f elems ++ [a] := by simp [absVec, hpv, hr2]
        simp only [hpush, bind_ok, Parser.run_pure]
        rw [habs] at hr' a'
        exact ⟨s', elems', failure, e', h', hr', a'⟩
      · refine ⟨s2, elems, some st2, by simp [parse_list_loop_false], h2, ?_, ?_⟩ <;> simp [hr2]
  · refine ⟨s1, elems, some (.Fatal sp k), by simp [parse_list_loop_false], h1, ?_, ?_⟩ <;>
      simp [Syntax.maybe, hr]
  · refine ⟨s1, elems, none, by simp [parse_list_loop_false], h1, ?_, ?_⟩ <;>
      simp [Syntax.maybe, Parser.run_pure]
termination_by (absStream st).rest.length

private theorem boundary_parse_list_refines (hP : ParseRefinesOn NoBlankNext P f p)
    (hD : DescRel UF d) (sep : Char) (max : Usize) (s : CS) (h : StreamOK s)
    (hn : NoBlankNext (absStream s)) :
    Refines (absVec f) (basic_parser.parse_list P UF sep max s)
      ((Syntax.parseList sep max.val d p).run (absStream s)) := by
  obtain ⟨r, s1, e1, hr, h1, a1⟩ := try_nonterminal_refines_at (hP s h hn)
  unfold basic_parser.parse_list
  simp only [Syntax.parseList, Parser.run_bind, e1, bind_ok, uncurry_apply_pair]
  rcases hR : (Syntax.tryNonterminal p).run (absStream s) with ⟨r', s''⟩
  rw [hR] at hr a1
  subst a1
  rcases r with x | st <;> rcases r' with e' | a <;> simp only [ResultRel] at hr
  · obtain ⟨elems, hpush, hpv⟩ := exists_eq_ok_of_spec
      (alloc.vec.Vec.push_spec (alloc.vec.Vec.new T) x (by simp; scalar_tac))
    obtain ⟨s', elems', failure, e', h', hr', a'⟩ := boundary_list_loop_eq hP hD sep max s1 h1 elems
    have habs : absVec f elems = [a] := by simp [absVec, hpv, hr]
    rw [habs] at hr' a'
    simp only [branch_Ok, hpush, bind_ok, e', uncurry_apply_pair]
    rcases hW : (refListLoop sep max.val d p [a]).run (absStream s1) with ⟨w, s3⟩
    rw [hW] at hr' a'
    simp only at a'
    subst a'
    rcases failure with _ | st <;> rcases w with e3 | l <;> simp only [ResultRel] at hr' <;>
      simp [h', hr']
  · simp [hr, h1]

private theorem boundary_vec_refines {M : basic_parser.Many T} {m : Syntax.Many}
    (hP : ParseRefinesOn NoBlankNext P f p) (hM : ManyRefines M m) (hD : DescRel UF d) :
    ParseRefinesOn NoBlankNext (sudo_rs.alloc.vec.Vec.Insts.Sudo_rsSudoersBasic_parserParse P M UF)
      (absVec f) (Syntax.parseVec m d p) := by
  intro s h hn
  obtain ⟨n, hn', hnv⟩ := hM.limit
  change Refines _ (sudo_rs.alloc.vec.Vec.Insts.Sudo_rsSudoersBasic_parserParse.parse P M UF s) _
  unfold sudo_rs.alloc.vec.Vec.Insts.Sudo_rsSudoersBasic_parserParse.parse
  simp only [hM.sep, hn', bind_ok, Syntax.parseVec]
  rw [← hnv]
  exact boundary_parse_list_refines hP hD m.sep n s h hn

end BoundaryList

/-! ## Alias definitions -/

abbrev aliasItemsUF {T : Type} (UF : ast_names.UserFriendly T) :=
  ast.Qualified.Insts.Sudo_rsSudoersAst_namesUserFriendly
    (tokens.Meta.Insts.Sudo_rsSudoersAst_namesUserFriendly UF)

abbrev aliasItemsInst {T : Type} (UF : ast_names.UserFriendly T)
    (P : basic_parser.Parse (tokens.Meta T)) (M : basic_parser.Many (tokens.Meta T)) :=
  sudo_rs.alloc.vec.Vec.Insts.Sudo_rsSudoersBasic_parserParse
    (ast.Qualified.Insts.Sudo_rsSudoersBasic_parserParse P
      (tokens.Meta.Insts.Sudo_rsSudoersAst_namesUserFriendly UF))
    (ast.Qualified.Insts.Sudo_rsSudoersBasic_parserMany M) (aliasItemsUF UF)

abbrev defsInst {T : Type} (UF : ast_names.UserFriendly T)
    (P : basic_parser.Parse (tokens.Meta T)) (M : basic_parser.Many (tokens.Meta T)) :=
  sudo_rs.alloc.vec.Vec.Insts.Sudo_rsSudoersBasic_parserParse
    (ast.Def.Insts.Sudo_rsSudoersBasic_parserParse UF P M)
    (ast.Def.Insts.Sudo_rsSudoersBasic_parserMany T)
    (ast.Def.Insts.Sudo_rsSudoersAst_namesUserFriendly T)

theorem def_description (T : Type) :
    DescRel (ast.Def.Insts.Sudo_rsSudoersAst_namesUserFriendly T) D.def_ :=
  ⟨_, rfl, by
    simp only [ast.Def.Insts.Sudo_rsSudoersAst_namesUserFriendly.DESCRIPTION]
    exact toStr_val _ _⟩

theorem def_many (T : Type) : ManyRefines (ast.Def.Insts.Sudo_rsSudoersBasic_parserMany T) Syntax.defMany :=
  ⟨by simp [ast.Def.Insts.Sudo_rsSudoersBasic_parserMany.SEP, Syntax.defMany],
    ⟨_, rfl, by simp [basic_parser.Many.LIMIT.default, Syntax.defMany]⟩⟩

private theorem alias_keyword_bound {s s' : Stream} {kw : String}
    (h : (Syntax.tryNonterminal (Syntax.token Syntax.aliasNameToken)).run s = (.ok kw, s')) :
    kw.utf8ByteSize ≤ Usize.max := by
  obtain ⟨x, t, hx, htail⟩ := Parser.run_bind_eq_ok.mp h
  obtain ⟨_, _, _, hpure⟩ := Parser.run_bind_eq_ok.mp htail
  simp only [Parser.run_pure, Prod.mk.injEq, Except.ok.injEq] at hpure
  exact hpure.1 ▸ alias_name_token_value_bound hx

/-- A `Def` needs the item list only after a successful `=`. The contract therefore makes no
blank-skip assumption on the definition's own input. -/
theorem def_refines_on {I : Stream → Prop} (hI : ForwardStable I) {T α : Type}
    {UF : ast_names.UserFriendly T} {P : basic_parser.Parse (tokens.Meta T)}
    {M : basic_parser.Many (tokens.Meta T)} {f : T → α} {m : Syntax.Many}
    {p : Parser (Meta α)} {d : String}
    (hItems : ∀ s, StreamOK s → I (absStream s) → NoBlankNext (absStream s) →
      Refines (fun v => absSpecList f v.val) ((aliasItemsInst UF P M).parse s)
        ((Syntax.specList m d p).run (absStream s))) (hD : DescRel UF d) :
    ParseRefinesOn I (ast.Def.Insts.Sudo_rsSudoersBasic_parserParse UF P M)
      (absDef f) (Syntax.defParser m d p) := by
  intro s hs hi
  obtain ⟨r, s1, er, hr, h1, a1⟩ := try_nonterminal_refines alias_name_parse_refines hs
  change Refines _ (ast.Def.Insts.Sudo_rsSudoersBasic_parserParse.parse UF P M s) _
  unfold ast.Def.Insts.Sudo_rsSudoersBasic_parserParse.parse
  simp only [Syntax.defParser, get_pos_eq', bind_ok, er, uncurry_apply_pair, Parser.run_bind,
    Parser.run_getPos]
  rcases hk : (Syntax.tryNonterminal (Syntax.token Syntax.aliasNameToken)).run (absStream s) with
    ⟨kr, kstream⟩
  rw [hk] at hr a1
  subst a1
  rcases r with key | e <;> rcases kr with ek | key' <;> simp only [ResultRel] at hr
  · subst key'
    have hsize := alias_keyword_bound hk
    simp only [id_eq] at hk ⊢
    simp only [branch_Ok, bind_ok, is_reserved_alias_eq key hsize]
    by_cases hres : Syntax.isReservedAlias key = true
    · simp only [hres, ↓reduceIte, fatal_from_eq, bind_ok, Parser.run_fatalFrom]
      exact (refines_ok_iff.mpr ⟨StatusRel.from (.reservedAlias _), h1, rfl⟩)
    · simp only [hres]
      obtain ⟨r2, s2, e2, rel2, h2, a2⟩ := expect_syntax_refines h1 '='
      simp only [e2, bind_ok, uncurry_apply_pair]
      rcases he : (Syntax.expectSyntax '=').run (absStream s1) with ⟨eqr, eqs⟩
      rw [he] at rel2 a2
      subst a2
      rcases r2 with ⟨⟩ | e <;> rcases eqr with ee | ⟨⟩ <;> simp only [ResultRel] at rel2
      · have hi1 := hI hi (Parser.reaches_of_run hk)
        have hi2 := hI hi1 (Parser.reaches_of_run he)
        obtain ⟨r3, s3, e3, rel3, h3, a3⟩ := expect_nonterminal_refines_at
          (hItems s2 h2 hi2 (expectSyntax_ok_next he)) (desc_vec (desc_qualified (desc_meta hD)))
        change basic_parser.expect_nonterminal (aliasItemsInst UF P M)
          (sudo_rs.alloc.vec.Vec.Insts.Sudo_rsSudoersAst_namesUserFriendly (aliasItemsUF UF)) s2 = _ at e3
        simp only [branch_Ok, bind_ok, e3, uncurry_apply_pair]
        rcases hiR : (Syntax.expectNonterminal d (Syntax.specList m d p)).run (absStream s2) with
          ⟨ir, istream⟩
        rw [hiR] at rel3 a3
        subst a3
        rcases r3 with xs | e <;> rcases ir with ei | ys <;> simp only [ResultRel] at rel3
        · simp [Parser.run_bind, he, hiR]
          refine ⟨.Ok (key, xs), s3, rfl, ?_, h3, rfl⟩
          change (⟨key, absSpecList f xs.val⟩ : SudoersSpec.Def α) = ⟨key, ys⟩
          rw [rel3]
        · simp [Parser.run_bind, he, hiR, rel3, h3]
      · simp [Parser.run_bind, he, rel2, h2]
  · simp [hr, h1]

/-- Generic `:` list of alias definitions, with the same forward-stable input invariant. -/
theorem defs_refines_on {I : Stream → Prop} (hI : ForwardStable I) {T α : Type}
    {UF : ast_names.UserFriendly T} {P : basic_parser.Parse (tokens.Meta T)}
    {M : basic_parser.Many (tokens.Meta T)} {f : T → α} {m : Syntax.Many}
    {p : Parser (Meta α)} {d : String}
    (hItems : ∀ s, StreamOK s → I (absStream s) → NoBlankNext (absStream s) →
      Refines (fun v => absSpecList f v.val) ((aliasItemsInst UF P M).parse s)
        ((Syntax.specList m d p).run (absStream s))) (hD : DescRel UF d) :
    ParseRefinesOn I (defsInst UF P M) (absVec (absDef f)) (Syntax.defs D m d p) :=
  vec_refines_on hI (def_refines_on hI hItems hD) (def_many T) (def_description T)

/-! ## The real alias-list instances used by the directive dispatcher -/

private abbrev userMetaInst := tokens.MetaUserSpecifier.Insts.Sudo_rsSudoersBasic_parserParse
private abbrev userMetaMany := tokens.Meta.Insts.Sudo_rsSudoersBasic_parserMany
  ast.UserSpecifier.Insts.Sudo_rsSudoersBasic_parserMany
private abbrev hostUF := tokens.Hostname.Insts.Sudo_rsSudoersAst_namesUserFriendly
private abbrev hostMetaInst := basic_parser.Parse.Blanket
  (tokens.Meta.Insts.Sudo_rsSudoersBasic_parserToken
    tokens.Hostname.Insts.Sudo_rsSudoersBasic_parserToken)
private abbrev hostMetaMany := tokens.Meta.Insts.Sudo_rsSudoersBasic_parserMany
  tokens.Hostname.Insts.Sudo_rsSudoersBasic_parserMany
private abbrev cmdUF := PairPatternArgs.Insts.Sudo_rsSudoersAst_namesUserFriendly
private abbrev cmdMetaInst := basic_parser.Parse.Blanket
  (tokens.Meta.Insts.Sudo_rsSudoersBasic_parserToken commandTokenInst)
private abbrev cmdMetaMany := tokens.Meta.Insts.Sudo_rsSudoersBasic_parserMany
  PairPatternArgs.Insts.Sudo_rsSudoersBasic_parserMany

abbrev userDefsInst := defsInst userSpecifierUF userMetaInst userMetaMany
abbrev hostDefsInst := defsInst hostUF hostMetaInst hostMetaMany
abbrev commandDefsInst := defsInst cmdUF cmdMetaInst cmdMetaMany

abbrev defsUF (T : Type) := sudo_rs.alloc.vec.Vec.Insts.Sudo_rsSudoersAst_namesUserFriendly
  (ast.Def.Insts.Sudo_rsSudoersAst_namesUserFriendly T)

theorem user_defs_refines {O : Oracles} (hO : P2CharOracle O.char) :
    ParseRefinesOn QuoteRoom userDefsInst (absVec (absDef absUserSpecifier))
      (Syntax.defs D Syntax.userSpecifierMany D.userSpecifier (Syntax.metaUserSpecifier O D)) := by
  have hId := identifier_refines_of_tokens digits_u32_parse_refines (username_parse_refines hO)
  have hUser := user_specifier_refines_of_tokens hId KindRel.netgroupsNotSupported
    (unquoted_parse_refines hO (username_token_refines hO))
  have hMeta := meta_user_specifier_refines_of_tokens hUser (meta_username_parse_refines hO)
  exact defs_refines_on quoteRoom_stable
    (fun s hs hi _ => spec_list_user_refines_of_meta hMeta s hs hi) user_specifier_description

theorem host_defs_refines {O : Oracles} (hO : UnicodeOracle O.char) :
    ParseRefines hostDefsInst (absVec (absDef id))
      (Syntax.defs D Syntax.hostnameMany D.hostname (Syntax.metaHostname O.char)) := by
  constructor
  intro s hs
  exact defs_refines_on (I := fun _ => True) (by intro; intros; trivial)
    (fun st h _ _ => (spec_list_hostname_refines hO D rfl).parse st h)
    hostname_description s hs trivial

theorem command_defs_refines {A : GlobAbs} {O : Oracles} (hO : P2Oracle A O) :
    ParseRefines commandDefsInst (absVec (absDef (absCommand A)))
      (Syntax.defs D {} D.command
        (Syntax.token (Syntax.metaToken O.char (Syntax.commandToken O)))) := by
  have hMany : ManyRefines PairPatternArgs.Insts.Sudo_rsSudoersBasic_parserMany
      ({} : Syntax.Many) :=
    ⟨by simp [basic_parser.Many.SEP.default],
      ⟨_, rfl, by simp [basic_parser.Many.LIMIT.default]⟩⟩
  have hQual := qualified_refines_at (meta_command_parse_refines_at hO)
    (desc_meta command_description)
  have hList := boundary_vec_refines hQual (many_qualified (many_meta hMany))
    (desc_qualified (desc_meta command_description))
  constructor
  intro s hs
  exact defs_refines_on (I := fun _ => True) (by intro; intros; trivial)
    (fun st ht _ hn => hList st ht hn) command_description s hs trivial

/-- The dispatcher uses this instance for both `User_Alias` and `Runas_Alias`. -/
theorem expect_user_defs_refines {O : Oracles} (hO : P2CharOracle O.char) {s : CS}
    (hs : StreamOK s) (hq : QuoteRoom (absStream s)) :
    Refines (absVec (absDef absUserSpecifier))
      (basic_parser.expect_nonterminal userDefsInst (defsUF ast.UserSpecifier) s)
      ((Syntax.expectNonterminal D.def_
        (Syntax.defs D Syntax.userSpecifierMany D.userSpecifier (Syntax.metaUserSpecifier O D))).run
          (absStream s)) :=
  expect_nonterminal_refines_at (user_defs_refines hO s hs hq) (desc_vec (def_description _))

theorem expect_host_defs_refines {O : Oracles} (hO : UnicodeOracle O.char) {s : CS}
    (hs : StreamOK s) :
    Refines (absVec (absDef id))
      (basic_parser.expect_nonterminal hostDefsInst (defsUF tokens.Hostname) s)
      ((Syntax.expectNonterminal D.def_
        (Syntax.defs D Syntax.hostnameMany D.hostname (Syntax.metaHostname O.char))).run
          (absStream s)) :=
  expect_nonterminal_refines (host_defs_refines hO) (desc_vec (def_description _)) hs

theorem expect_command_defs_refines {A : GlobAbs} {O : Oracles} (hO : P2Oracle A O)
    {s : CS} (hs : StreamOK s) :
    Refines (absVec (absDef (absCommand A)))
      (basic_parser.expect_nonterminal commandDefsInst (defsUF RCommand) s)
      ((Syntax.expectNonterminal D.def_
        (Syntax.defs D {} D.command
          (Syntax.token (Syntax.metaToken O.char (Syntax.commandToken O))))).run (absStream s)) :=
  expect_nonterminal_refines (command_defs_refines hO) (desc_vec (def_description _)) hs

end SudoRsProofs.Parser
