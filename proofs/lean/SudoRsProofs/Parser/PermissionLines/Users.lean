import SudoRsProofs.Parser.PermissionLines.Common

/-! Identifiers, user specifiers, and their user-name/alias prefix production. -/

open Aeneas Aeneas.Std Result SudoersSpec
open Syntax.Parser

namespace SudoRsProofs.Parser

open sudo_rs.sudoers.ast (Identifier UserSpecifier)
open sudo_rs.sudoers
open sudo_rs.sudoers.basic_parser (Parse)

private abbrev digitTk := tokens.DigitsU32.Insts.Sudo_rsSudoersBasic_parserToken
private abbrev usernameTk := tokens.Username.Insts.Sudo_rsSudoersBasic_parserToken
private abbrev usernameMetaTk := tokens.Meta.Insts.Sudo_rsSudoersBasic_parserToken usernameTk
private abbrev unquotedUserTk := tokens.Unquoted.Insts.Sudo_rsSudoersBasic_parserToken usernameTk
private abbrev D := Syntax.Descriptions.release

abbrev identifierInst := Identifier.Insts.Sudo_rsSudoersBasic_parserParse
abbrev userSpecifierInst := UserSpecifier.Insts.Sudo_rsSudoersBasic_parserParse
abbrev identifierUF := Identifier.Insts.Sudo_rsSudoersAst_namesUserFriendly
abbrev userSpecifierUF := UserSpecifier.Insts.Sudo_rsSudoersAst_namesUserFriendly

private theorem digits_description_local :
    DescRel tokens.DigitsU32.Insts.Sudo_rsSudoersAst_namesUserFriendly D.digitsU32 :=
  ⟨_, rfl, by
    simp only [tokens.DigitsU32.Insts.Sudo_rsSudoersAst_namesUserFriendly.DESCRIPTION]
    exact toStr_val _ _⟩

private theorem username_description_local :
    DescRel tokens.Username.Insts.Sudo_rsSudoersAst_namesUserFriendly D.username :=
  ⟨_, rfl, by
    simp only [tokens.Username.Insts.Sudo_rsSudoersAst_namesUserFriendly.DESCRIPTION]
    exact toStr_val _ _⟩

theorem identifier_description : DescRel identifierUF D.identifier :=
  ⟨_, rfl, by
    simp only [Identifier.Insts.Sudo_rsSudoersAst_namesUserFriendly.DESCRIPTION]
    exact toStr_val _ _⟩

theorem user_specifier_description : DescRel userSpecifierUF D.userSpecifier :=
  ⟨_, rfl, by
    simp only [UserSpecifier.Insts.Sudo_rsSudoersAst_namesUserFriendly.DESCRIPTION]
    exact toStr_val _ _⟩

theorem identifier_refines_of_tokens {O : Syntax.Oracles}
    (hDigit : ParseRefines (Parse.Blanket digitTk) (fun n : U32 => n.val)
      (Syntax.token Syntax.digitsU32Token))
    (hName : ParseRefines (Parse.Blanket usernameTk) common.string.SudoString.str
      (Syntax.token (Syntax.usernameToken O))) :
    ParseRefines identifierInst absIdentifier (Syntax.identifier O D) := by
  constructor
  intro s hs
  obtain ⟨s1, e1, h1, a1⟩ := eat_char_eq hs '#'
  change Refines _ (Identifier.Insts.Sudo_rsSudoersBasic_parserParse.parse s) _
  simp only [Identifier.Insts.Sudo_rsSudoersBasic_parserParse.parse, Syntax.identifier,
    run_bind, run_eatChar, e1, bind_ok, uncurry_apply_pair, ← a1]
  generalize ((absStream s).eatChar '#').1 = b
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, run_bind]
    obtain ⟨r, s2, e2, hr, h2, a2⟩ := try_nonterminal_refines hName h1
    rcases he : (Syntax.tryNonterminal (Syntax.token (Syntax.usernameToken O))).run (absStream s1)
      with ⟨r', t⟩
    rw [he] at hr a2
    cases r <;> cases r' <;> simp_all [absIdentifier]
  · simp only [↓reduceIte, run_bind]
    obtain ⟨r, s2, e2, hr, h2, a2⟩ :=
      expect_nonterminal_refines hDigit digits_description_local h1
    rcases he : (Syntax.expectNonterminal D.digitsU32 (Syntax.token Syntax.digitsU32Token)).run
      (absStream s1) with ⟨r', t⟩
    rw [he] at hr a2
    cases r <;> cases r' <;> simp_all [absIdentifier]

/-- `parse_meta` first runs an optional Meta<Username>; if absent, the fallback starts at the
same cursor as the reference, without any additional whitespace pass. -/
theorem parse_meta_refines_at {O : Syntax.Oracles} {T α : Type} {f : T → α}
    {P : Parse T} {p : Syntax.Parser α} {F : sudo_rs.sudoers.ast.FromUsername T}
    {embed : String → α} {s : CS} (hs : StreamOK s)
    (hName : ParseRefines (Parse.Blanket usernameMetaTk)
      (absMeta common.string.SudoString.str)
      (Syntax.token (Syntax.metaToken O.char (Syntax.usernameToken O))))
    (hF : ∀ u, ∃ t, F.from_username u = ok t ∧ f t = embed u.str)
    (hP : ∀ st, StreamOK st → (absStream s).Reaches (absStream st) →
      Refines f (P.parse st) (p.run (absStream st))) :
    Refines (absMeta f) (sudo_rs.sudoers.ast.parse_meta P F s)
      ((Syntax.parseMeta O p embed).run (absStream s)) := by
  obtain ⟨r, s1, e1, hr, h1, a1⟩ := try_nonterminal_refines (option_parse_refines hName) hs
  simp only [sudo_rs.sudoers.ast.parse_meta, Syntax.parseMeta, run_bind, e1, bind_ok,
    uncurry_apply_pair]
  rcases he : (Syntax.tryNonterminal (Syntax.parseOption
    (Syntax.token (Syntax.metaToken O.char (Syntax.usernameToken O))))).run (absStream s)
    with ⟨r', t⟩
  have hreach := (Syntax.tryNonterminal (Syntax.parseOption
    (Syntax.token (Syntax.metaToken O.char (Syntax.usernameToken O))))).reaches (absStream s)
  rw [he] at hr a1
  rw [he] at hreach
  simp only at a1 hreach
  subst t
  rcases r with (_ | m) | st <;> rcases r' with st' | (_ | m') <;>
    simp only [ResultRel, Option.map_none, Option.map_some, Option.some.injEq,
      reduceCtorEq] at hr
  · obtain ⟨r2, s2, e2, hr2, h2, a2⟩ := hP s1 h1 hreach
    rcases he2 : p.run (absStream s1) with ⟨r2', t2⟩
    rw [he2] at hr2 a2
    cases r2 <;> cases r2' <;> simp_all [absMeta, run_bind]
  · subst m'
    cases m with
    | All => simp [absMeta, h1]
    | Alias n => simp [absMeta, h1]
    | Only u =>
      obtain ⟨t, et, ht⟩ := hF u
      simp [absMeta, h1, et, ht]
  · simp [hr, h1]

theorem meta_identifier_refines_of_tokens {O : Syntax.Oracles}
    (hId : ParseRefines identifierInst absIdentifier (Syntax.identifier O D))
    (hName : ParseRefines (Parse.Blanket usernameMetaTk)
      (absMeta common.string.SudoString.str)
      (Syntax.token (Syntax.metaToken O.char (Syntax.usernameToken O)))) :
    ParseRefines tokens.MetaIdentifier.Insts.Sudo_rsSudoersBasic_parserParse (absMeta absIdentifier)
      (Syntax.metaIdentifier O D) :=
  ⟨fun s hs => parse_meta_refines_at (s := s) hs hName (fun _ => ⟨_, rfl, rfl⟩)
    (fun st ht _ => hId.parse st ht)⟩

/-- The production inside a quoted user and the unquoted branch of `UserSpecifier`. -/
theorem parse_user_refines_of_tokens {O : Syntax.Oracles}
    (hId : ParseRefines identifierInst absIdentifier (Syntax.identifier O D))
    (hNetgroups : KindRel .NetgroupsNotSupported .netgroupsNotSupported) {s : CS} (hs : StreamOK s) :
    Refines absUserSpecifier (sudo_rs.sudoers.ast.ParseUserSpecifier.parse.parse_user s)
      ((Syntax.parseUser O D).run (absStream s)) := by
  obtain ⟨s1, e1, h1, a1⟩ := eat_char_eq hs '%'
  simp only [sudo_rs.sudoers.ast.ParseUserSpecifier.parse.parse_user, Syntax.parseUser,
    run_bind, run_eatChar, e1, bind_ok, uncurry_apply_pair, ← a1]
  generalize ((absStream s).eatChar '%').1 = b
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, run_bind, run_eatChar]
    obtain ⟨s2, e2, h2, a2⟩ := eat_char_eq h1 '+'
    simp only [e2, bind_ok, uncurry_apply_pair, ← a2]
    generalize ((absStream s1).eatChar '+').1 = plus
    cases plus
    · obtain ⟨r, s3, e3, hr, h3, a3⟩ := try_nonterminal_refines hId h2
      rcases he : (Syntax.tryNonterminal (Syntax.identifier O D)).run (absStream s2) with ⟨r', t⟩
      rw [he] at hr a3
      cases r <;> cases r' <;> simp_all [run_bind, absUserSpecifier]
    · simpa [run_fatalHere, h2] using (StatusRel.here (s := s2) hNetgroups)
  · simp only [↓reduceIte, run_bind, run_eatChar]
    obtain ⟨s2, e2, h2, a2⟩ := eat_char_eq h1 ':'
    simp only [e2, bind_ok, uncurry_apply_pair, ← a2]
    obtain ⟨r, s3, e3, hr, h3, a3⟩ := expect_nonterminal_refines hId identifier_description h2
    rcases he : (Syntax.expectNonterminal D.identifier (Syntax.identifier O D)).run
      (absStream s2) with ⟨r', t⟩
    rw [he] at hr a3
    generalize ((absStream s1).eatChar ':').1 = nonunix
    cases r <;> cases r' <;> cases nonunix <;> simp_all [absUserSpecifier]

private theorem tokenLoop_length {α : Type} (tk : Syntax.TokenSpec α) (st : List Char)
    (s : Syntax.Stream) {out : List Char} {s' : Syntax.Stream}
    (h : (refTokenLoop tk st).run s = (.ok out, s')) : out.length ≤ st.length + s.rest.length := by
  unfold refTokenLoop Syntax.Parser.whileMaybe at h
  rw [Syntax.Parser.loop_run] at h
  simp only [Syntax.Parser.whileMaybeBody, run_bind, run_maybe] at h
  rcases hc : (Syntax.acceptEscaped tk tk.accept).run s with ⟨r, t⟩
  rw [hc] at h
  rcases r with (⟨sp, k⟩ | _) | c
  · simp [Syntax.maybe] at h
  · simp only [Syntax.maybe, run_pure, Prod.mk.injEq, Except.ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    change st.length ≤ st.length + s.rest.length
    omega
  · have ht := Syntax.acceptEscaped_consumes tk tk.accept _ _ _ hc
    simp only [Syntax.maybe, Syntax.tokenBody] at h
    by_cases hlim : Syntax.utf8Len st ≥ tk.maxLen
    · simp [hlim, run_fatalHere] at h
    · simp only [hlim, ↓reduceIte, run_pure] at h
      have hl := tokenLoop_length tk (st ++ [c]) t h
      simp only [List.length_append, List.length_singleton] at hl
      omega
termination_by s.rest.length

private theorem reescape_length {α : Type} (tk : Syntax.TokenSpec α) (cs : List Char) :
    (cs.flatMap fun c => if tk.escaped c then ['\\', c] else [c]).length ≤ 2 * cs.length := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    have hc : (if tk.escaped c then ['\\', c] else [c]).length ≤ 2 := by split <;> simp
    omega

private theorem unquoted_length {O : Syntax.Oracles} {s s' : Syntax.Stream} {text : String}
    (h : (Syntax.expectNonterminal D.username
      (Syntax.token (Syntax.unquotedToken O.char (Syntax.usernameToken O)))).run s = (.ok text, s')) :
    text.toList.length ≤ 2 * s.rest.length := by
  let tk := Syntax.unquotedToken O.char (Syntax.usernameToken O)
  change (Syntax.expectNonterminal D.username (Syntax.token tk)).run s = _ at h
  rcases ht : (Syntax.token tk).run s with ⟨r, t⟩
  rcases r with (⟨sp, k⟩ | _) | str
  · simp [Syntax.expectNonterminal, Syntax.tryNonterminal, run_bind, ht] at h
  · simp [Syntax.expectNonterminal, Syntax.tryNonterminal, run_bind, run_fatalFrom, ht] at h
  · have he : text = str := by
      simp only [Syntax.expectNonterminal, Syntax.tryNonterminal, run_bind, run_getPos, run_observe,
        ht] at h
      rcases hw : Syntax.skipTrailingWhitespace.run t with ⟨w, u⟩
      rcases w with (⟨sp, k⟩ | _) | ⟨⟩ <;> simp_all [run_lift, run_fatalFrom]
    rw [he]
    unfold Syntax.token at ht
    obtain ⟨pos, t0, h0, ht⟩ := run_bind_eq_ok.mp ht
    simp only [run_getPos, Prod.mk.injEq] at h0
    obtain ⟨_, rfl⟩ := h0
    obtain ⟨c, t1, h1, ht⟩ := run_bind_eq_ok.mp ht
    obtain ⟨cs, t2, h2, ht⟩ := run_bind_eq_ok.mp ht
    have hl := Syntax.acceptEscaped_consumes tk tk.accept1st _ _ _ h1
    have hcs := tokenLoop_length tk [c] t1 h2
    have hm := reescape_length (Syntax.usernameToken O) cs
    simp only [tk, Syntax.unquotedToken, Syntax.Unquoted.construct, run_pure, Prod.mk.injEq,
      Except.ok.injEq] at ht
    obtain ⟨rfl, -⟩ := ht
    simp only [String.toList_ofList]
    simp only [List.length_singleton] at hcs
    omega

private theorem nested_user_stream {s : CS} (hq : QuoteRoom (absStream s))
    (text : String) (ht : text.toList.length ≤ 2 * (absStream s).rest.length) :
    ∃ v : alloc.vec.Vec Char, sudoers.char_stream.chars_of text = ok v ∧
      StreamOK ⟨alloc.vec.Vec.deref v, 0#usize, s.line, s.col⟩ ∧
      absStream ⟨alloc.vec.Vec.deref v, 0#usize, s.line, s.col⟩ =
        Syntax.Stream.newWithPos text.toList (absStream s).getPos := by
  have hline := hq.line_le
  have hcol := hq.col_le
  have hlen : text.toList.length ≤ Usize.max := by omega
  let v : alloc.vec.Vec Char := ⟨Slice.from text.toList hlen⟩
  have hv : (alloc.vec.Vec.deref v).val = text.toList := by
    rw [Vec.deref_val]
    exact Slice.from_val _ _
  refine ⟨v, by simp [sudoers.char_stream.chars_of, hlen, v], ?_, ?_⟩
  · constructor <;> simp [hv] at * <;> omega
  · simp [absStream, Syntax.Stream.newWithPos, hv]

/-- On a quote, refine `parse_user` on the re-escaped text at the saved start position.
Its result (including a `Reject` or an inner fatal span) is taken as-is, and the outer
cursor stays after the token until the closing quote is expected on success. -/
theorem user_specifier_refines_of_tokens {O : Syntax.Oracles}
    (hId : ParseRefines identifierInst absIdentifier (Syntax.identifier O D))
    (hNetgroups : KindRel .NetgroupsNotSupported .netgroupsNotSupported)
    (hText : ParseRefines (Parse.Blanket unquotedUserTk)
      (fun u : tokens.Unquoted tokens.Username => u.1)
      (Syntax.token (Syntax.unquotedToken O.char (Syntax.usernameToken O)))) :
    ParseRefinesOn QuoteRoom userSpecifierInst absUserSpecifier (Syntax.userSpecifier O D) := by
  intro s hs hq
  obtain ⟨s1, e1, h1, a1⟩ := eat_char_eq hs '"'
  have hq1 := hq.reaches (a1 ▸ Syntax.Stream.Reaches.eatChar '"' (absStream s))
  change Refines _ (UserSpecifier.Insts.Sudo_rsSudoersBasic_parserParse.parse s) _
  simp only [UserSpecifier.Insts.Sudo_rsSudoersBasic_parserParse.parse, Syntax.userSpecifier,
    run_bind, run_eatChar, e1, bind_ok, uncurry_apply_pair, ← a1]
  generalize ((absStream s).eatChar '"').1 = b
  cases b
  · simpa using parse_user_refines_of_tokens hId hNetgroups h1
  · simp only [↓reduceIte, run_bind, run_getPos, get_pos_eq', bind_ok]
    obtain ⟨r, s2, e2, hr, h2, a2⟩ :=
      expect_nonterminal_refines hText (desc_unquoted username_description_local) h1
    rcases he : (Syntax.expectNonterminal D.username
      (Syntax.token (Syntax.unquotedToken O.char (Syntax.usernameToken O)))).run (absStream s1)
      with ⟨r', t⟩
    simp only [e2, bind_ok, uncurry_apply_pair]
    rw [he] at hr a2
    simp only at a2
    subst t
    rcases r with u | st <;> rcases r' with st' | text <;> simp only [ResultRel] at hr
    · rcases u with ⟨raw, phantom⟩
      change raw = text at hr
      subst raw
      obtain ⟨v, ev, hv, av⟩ := nested_user_stream hq1 text (unquoted_length he)
      let nestedCursor : CS := ⟨alloc.vec.Vec.deref v, 0#usize, s1.line, s1.col⟩
      obtain ⟨rn, sn, en, hrn, -, -⟩ := parse_user_refines_of_tokens hId hNetgroups hv
      change sudo_rs.sudoers.ast.ParseUserSpecifier.parse.parse_user nestedCursor = _ at en
      simp only [core.result.Result.Insts.CoreOpsTry.branch, ev, bind_ok,
        sudo_rs.sudoers.char_stream.CharStream.new_with_pos, uncurry_apply_pair, run_nested, ← av,
        show ast.ParseUserSpecifier.parse.parse_user
          ⟨alloc.vec.Vec.deref v, 0#usize, s1.line, s1.col⟩ = _ from en]
      rcases hn : (Syntax.parseUser O D).run (absStream nestedCursor) with ⟨r'n, t'n⟩
      rw [hn] at hrn
      rcases rn with value | st <;> rcases r'n with st' | value' <;> simp only [ResultRel] at hrn
      · obtain ⟨rq, sq, eq, hrel, hsq, aq⟩ := expect_syntax_refines h2 '"'
        rcases hclose : (Syntax.expectSyntax '"').run (absStream s2) with ⟨rq', tq⟩
        rw [hclose] at hrel aq
        rcases rq with ⟨⟩ | st <;> rcases rq' with st' | ⟨⟩ <;>
          simp_all [run_lift]
      · simpa [run_lift, h2] using hrn
    · simp [h2, hr]

theorem meta_user_specifier_refines_of_tokens {O : Syntax.Oracles}
    (hUser : ParseRefinesOn QuoteRoom userSpecifierInst absUserSpecifier (Syntax.userSpecifier O D))
    (hName : ParseRefines (Parse.Blanket usernameMetaTk)
      (absMeta common.string.SudoString.str)
      (Syntax.token (Syntax.metaToken O.char (Syntax.usernameToken O)))) :
    ParseRefinesOn QuoteRoom sudo_rs.sudoers.tokens.MetaUserSpecifier.Insts.Sudo_rsSudoersBasic_parserParse
      (absMeta absUserSpecifier) (Syntax.metaUserSpecifier O D) :=
  fun s hs hq => parse_meta_refines_at (s := s) hs hName (fun _ => ⟨_, rfl, rfl⟩)
    (fun st ht hr => hUser st ht (hq.reaches hr))

end SudoRsProofs.Parser
