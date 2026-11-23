import SudoRsProofs.Parser.Directives.Dispatch
import SudoRsProofs.Parser.PermissionLines.Tuples
import SudoRsProofs.Parser.File

/-! Outer item dispatch for the stable `Sudo` instance. Include paths are parsed as text:
this is not the analysis pass that opens included files. The extraction has the
feature-disabled `parse_remote` body, which reports an unknown directive. -/

open Aeneas Aeneas.Std Result SudoersSpec
open sudo_rs
open Aeneas.Std.alloc.vec (Vec)
open sudo_rs.sudoers.ast (Sudo)

noncomputable section

namespace SudoRsProofs.Parser

private abbrev D := Syntax.Descriptions.release
abbrev sudoParseInst := Sudo.Insts.Sudo_rsSudoersBasic_parserParse
abbrev sudoUF := Sudo.Insts.Sudo_rsSudoersAst_namesUserFriendly

/-- Immediate non-directive productions, and the user-list success invariant used by
`users[0]` and by the `#id` prepend. This record does not assume correctness of the item or
file parser. -/
structure SudoLeaves (A : GlobAbs) (O : Syntax.Oracles) : Prop where
  identifier : ParseRefines identifierInst absIdentifier (Syntax.identifier O D)
  users : ParseRefinesOn QuoteRoom specListUserInst absUserList (Syntax.specListUserSpecifier O D)
  userDomain : ∀ s xs t, (Syntax.specListUserSpecifier O D).run s = (.ok xs, t) →
    xs ≠ [] ∧ xs.length ≤ 127 ∧ ∀ key ∈ xs, DirectiveKeyFits key
  permissions : ∀ s, StreamOK s → QuoteRoom (absStream s) →
    Refines (absVec (absSeg A)) (sudoers.ast.permissions s)
      ((Syntax.expectNonterminal D.hostsRunasCommands (Syntax.permissions O D)).run (absStream s))
  includes : ∀ s, StreamOK s → Refines (Analysis.absSudo A) (sudoers.ast.parse_include s)
    ((Syntax.parseInclude O D).run (absStream s))
  directives : DirectiveLeaves A O

private theorem char_option_eq (o : Option Char) (c : Char) :
    core.option.Option.Insts.CoreCmpPartialEqOption.eq Char.Insts.CoreCmpPartialEqChar o (some c) =
      ok (o == some c) := by
  cases o with
  | none => rfl
  | some x => rfl

private theorem clone_cursor_eq (s : CS) :
    sudoers.char_stream.CharStream.Insts.CoreCloneClone.clone s = ok s := by
  simp [sudoers.char_stream.CharStream.Insts.CoreCloneClone.clone,
    core.clone.impls.CloneShared.clone, core.clone.impls.CloneUsize.clone, lift]

private abbrev rawFirstUser (i : sudoers.ast.Identifier) : RSpec sudoers.ast.UserSpecifier :=
  .Allow (.Only (.User i))

private theorem prepend_id_eq (users : Vec (RSpec sudoers.ast.UserSpecifier))
    (hn : absUserList users ≠ []) (hlen : (absUserList users).length ≤ 127)
    (i : sudoers.ast.Identifier) :
    ∃ ys, Vec.insert users 0#usize (rawFirstUser i) = ok ys ∧
      absUserList ys = .allow (.only (.user (absIdentifier i))) :: absUserList users := by
  have h0 : 0 < users.val.length := by
    cases h : users.val with
    | nil => exact False.elim (hn (by simp [absUserList, absSpecList, h]))
    | cons a tail => simp
  have h1 : users.val.length < Usize.max := by
    have hle : users.val.length ≤ 127 := by simpa [absUserList, absSpecList] using hlen
    have hm : 127 < Usize.max := by scalar_tac
    exact lt_of_le_of_lt hle hm
  obtain ⟨ys, hy, hv⟩ := exists_eq_ok_of_spec
    (Vec.insert_spec users 0#usize (rawFirstUser i) (by simpa using h0) h1)
  refine ⟨ys, hy, ?_⟩
  simp [absSpecList, hv, absSpec, absQualified, absMeta, absUserSpecifier]

private theorem user_head_eq (users : Vec (RSpec sudoers.ast.UserSpecifier))
    (hn : absUserList users ≠ []) :
    ∃ key, Vec.index (core.slice.index.SliceIndexUsizeSlice (RSpec sudoers.ast.UserSpecifier))
        users 0#usize = ok key ∧
      (absUserList users).headD (.allow .all) = absSpec absUserSpecifier key ∧
      absSpec absUserSpecifier key ∈ absUserList users := by
  cases hv : users.val with
  | nil => exact False.elim (hn (by simp [absUserList, absSpecList, hv]))
  | cons k ks =>
    have hb : (0#usize : Usize).val < users.val.length := by simp [hv]
    have hi := eq_ok_of_spec (Vec.index_usize_spec users 0#usize hb)
    refine ⟨k, ?_, ?_, ?_⟩
    · rw [Vec.index_slice_index, hi]; simp [hv]
    · simp [absUserList, absSpecList, hv]
    · simp [absUserList, absSpecList, hv]

private theorem user_list_tried {A : GlobAbs} {O : Syntax.Oracles} (hL : SudoLeaves A O)
    {s : CS} (hs : StreamOK s) (hq : QuoteRoom (absStream s)) :
    Refines absUserList (sudoers.ast.user_list s)
      ((Syntax.tryNonterminal (Syntax.specListUserSpecifier O D)).run (absStream s)) :=
  try_nonterminal_refines_at (hL.users s hs hq)

private theorem user_list_expected {A : GlobAbs} {O : Syntax.Oracles} (hL : SudoLeaves A O)
    {s : CS} (hs : StreamOK s) (hq : QuoteRoom (absStream s)) :
    Refines absUserList (sudoers.ast.expect_user_list s)
      ((Syntax.expectNonterminal D.userSpecifier (Syntax.specListUserSpecifier O D)).run
        (absStream s)) :=
  expect_nonterminal_refines_at (hL.users s hs hq)
    (desc_vec (desc_qualified (desc_meta user_specifier_description)))

set_option maxHeartbeats 1000000 in
/-- Stable `impl Parse for Sudo`, including numeric-ID/comment fallback, required quoted
user lists and ambiguous directive dispatch. -/
theorem sudo_refines_of_parts {A : GlobAbs} {O : Syntax.Oracles}
    (hO : P2Oracle A O) (hL : SudoLeaves A O) :
    ParseRefinesOn QuoteRoom sudoParseInst (Analysis.absSudo A) (Syntax.sudo O D) := by
  intro s hs hq
  obtain ⟨s1, ea, hs1, aa⟩ := eat_char_eq hs '@'
  have q1 : QuoteRoom (absStream s1) := aa ▸ hq.reaches (Syntax.Stream.Reaches.eatChar '@' _)
  change Refines _ (Sudo.Insts.Sudo_rsSudoersBasic_parserParse.parse s) _
  simp only [Sudo.Insts.Sudo_rsSudoersBasic_parserParse.parse, Syntax.sudo,
    Syntax.Parser.run_bind, Syntax.Parser.run_eatChar, ea, bind_ok, uncurry_apply_pair, ← aa]
  generalize ((absStream s).eatChar '@').1 = at_
  cases at_
  · simp only [Bool.false_eq_true, ite_false, peek_eq, char_option_eq, bind_ok,
      Syntax.Parser.run_bind, Syntax.Parser.run_peek]
    by_cases hHash : ((absStream s1).peek == some '#') = true
    · simp only [hHash, ite_true, Syntax.sudoHash, Syntax.Parser.run_bind, Syntax.Parser.run_observe]
      apply (try_nonterminal_refines hL.identifier hs1).elimCases
      · intro i s2 ei ai hs2
        have q2 := quoteRoom_stable.after q1 (Syntax.tryNonterminal (Syntax.identifier O D))
          (congrArg Prod.snd ai).symm
        simp only [ei, ai, bind_ok, uncurry_apply_pair, Syntax.Parser.run_bind]
        apply (is_syntax_refines hs2 ',').elimCases
        · intro comma s3 ec ac hs3
          have q3 := quoteRoom_stable.after q2 (Syntax.isSyntax ',') (congrArg Prod.snd ac).symm
          cases comma
          · simp only [ec, ac, bind_ok, uncurry_apply_pair, branch_Ok, id_eq, Bool.false_eq_true,
              ite_false, Syntax.Parser.run_bind, Syntax.Parser.run_pure]
            apply (hL.permissions s3 hs3 q3).elimCases
            · intro entries t ex ax ht
              simp only [ex, ax, lift, bind_ok, uncurry_apply_pair, branch_Ok, make_eq]
              exact refines_value (f := Analysis.absSudo A) (Sudo.Spec
                { users := alloc.slice.Slice.into_vec
                    (Array.make 1#usize [rawFirstUser i]).to_slice, permissions := entries }) ht
            · intro e e' t ex ax ht rel
              simp only [ex, ax, lift, bind_ok, uncurry_apply_pair, branch_Err, from_residual_Err]
              exact refines_diagnostic rel ht
          · simp only [ec, ac, bind_ok, uncurry_apply_pair, branch_Ok, id_eq, ite_true,
              Syntax.Parser.run_bind]
            apply (user_list_expected hL hs3 q3).elimCases
            · intro users s4 eu au hs4
              have q4 := quoteRoom_stable.after q3
                (Syntax.expectNonterminal D.userSpecifier (Syntax.specListUserSpecifier O D))
                (congrArg Prod.snd au).symm
              obtain ⟨hn, hlen, _⟩ := expectNonterminal_value hL.userDomain au
              obtain ⟨ys, ey, ay⟩ := prepend_id_eq users hn hlen i
              simp only [eu, au, ey, bind_ok, uncurry_apply_pair, branch_Ok,
                Syntax.Parser.run_pure]
              apply (hL.permissions s4 hs4 q4).elimCases
              · intro entries t ex ax ht
                simp only [ex, ax, bind_ok, uncurry_apply_pair, branch_Ok, make_eq]
                simpa only [Analysis.absSudo, absPermissionSpec, ay, absVec] using
                  (refines_value (f := Analysis.absSudo A) (Sudo.Spec { users := ys, permissions := entries }) ht)
              · intro e e' t ex ax ht rel
                simp only [ex, ax, bind_ok, uncurry_apply_pair, branch_Err, from_residual_Err]
                exact refines_diagnostic rel ht
            · intro e e' t ex ax ht rel
              simp only [ex, ax, bind_ok, uncurry_apply_pair, branch_Err, from_residual_Err]
              exact refines_diagnostic rel ht
        · intro e e' t ex ax ht rel
          simp only [ex, ax, bind_ok, uncurry_apply_pair, branch_Err, from_residual_Err]
          exact refines_diagnostic rel ht
      · intro e e' s2 ei ai hs2 _
        simp only [ei, ai, bind_ok, uncurry_apply_pair, Syntax.Parser.run_bind, Syntax.Parser.run_observe]
        apply (hL.includes s2 hs2).elimCases
        · intro item t ex ax ht
          simp only [ex, ax, bind_ok, uncurry_apply_pair, make_eq, Syntax.Parser.run_pure]
          exact refines_value item ht
        · intro _ _ s3 ex ax hs3 _
          obtain ⟨t, et, ht, aT⟩ := skip_to_newline_eq hs3
          simp only [ex, ax, et, bind_ok, uncurry_apply_pair, make_eq, Syntax.Parser.run_bind,
            Syntax.Parser.run_skipToNewline, ← aT, Syntax.Parser.run_pure]
          exact refines_value Sudo.LineComment ht
    · have hx : ((absStream s1).peek == some '#') = false := by simpa using hHash
      simp only [hx, Bool.false_eq_true, ite_false, clone_cursor_eq, bind_ok,
        Syntax.Parser.run_anchored, Syntax.sudoMain, Syntax.AParser.run_bind,
        Syntax.AParser.run_lift, Syntax.Parser.run_peek]
      by_cases hQuote : ((absStream s1).peek == some '"') = true
      · simp only [hQuote, ite_true, Syntax.AParser.run_bind, Syntax.AParser.run_lift]
        apply (user_list_expected hL hs1 q1).elimCases
        · intro users s2 eu au hs2
          have q2 := quoteRoom_stable.after q1
            (Syntax.expectNonterminal D.userSpecifier (Syntax.specListUserSpecifier O D))
            (congrArg Prod.snd au).symm
          simp only [eu, au, bind_ok, uncurry_apply_pair, branch_Ok]
          apply (hL.permissions s2 hs2 q2).elimCases
          · intro entries t ex ax ht
            simp only [ex, ax, bind_ok, uncurry_apply_pair, branch_Ok, make_eq, Syntax.AParser.run_pure]
            exact refines_value (Sudo.Spec { users, permissions := entries }) ht
          · intro e e' t ex ax ht rel
            simp only [ex, ax, bind_ok, uncurry_apply_pair, branch_Err, from_residual_Err]
            exact refines_diagnostic rel ht
        · intro e e' t ex ax ht rel
          simp only [ex, ax, bind_ok, uncurry_apply_pair, branch_Err, from_residual_Err]
          exact refines_diagnostic rel ht
      · have hqf : ((absStream s1).peek == some '"') = false := by simpa using hQuote
        simp only [hqf, Bool.false_eq_true, ite_false, Syntax.AParser.run_bind, Syntax.AParser.run_lift,
          Syntax.Parser.run_maybe]
        apply (user_list_tried hL hs1 q1).elimCases
        · intro users s2 eu au hs2
          have reaches : (absStream s1).Reaches (absStream s2) := by
            have ht := (Syntax.tryNonterminal (Syntax.specListUserSpecifier O D)).reaches (absStream s1)
            rwa [au] at ht
          obtain ⟨hn, _, hfit⟩ := tryNonterminal_value hL.userDomain au
          obtain ⟨key, ek, ak, hk⟩ := user_head_eq users hn
          simp only [eu, au, bind_ok, uncurry_apply_pair, maybe_Ok, branch_Ok, Syntax.maybe_ok,
            ek, ak, get_pos_eq, Syntax.AParser.run_bind, Syntax.AParser.run_maybe]
          apply (get_directive_refines_of_parts hO hL.directives hL.users key (hfit _ hk)
            hs1 hs2 q1 reaches).elimCases
          · intro d t ed ad ht
            have ar : (Syntax.getDirective O D (absSpec absUserSpecifier key)
                (absStream s1)).run (absStream s2) = (.ok (Analysis.absDirective A d), absStream t) := ad
            simp only [ed, ar, maybe_Ok, branch_Ok, bind_ok, uncurry_apply_pair, Syntax.maybe_ok]
            by_cases hl : users.val.length = 1
            · simp [absUserList, absSpecList, hl, Syntax.AParser.run_pure]
              exact ⟨rfl, ht⟩
            · have he : users.len ≠ 1#usize := by
                intro he
                apply hl
                have hv := congrArg UScalar.val he
                change users.val.length = 1 at hv
                exact hv
              have hne : (users.len != 1#usize) = true := bne_iff_ne.mpr he
              have hlen : (users.val.length != 1) = true := bne_iff_ne.mpr hl
              simp only [hne, ite_true, could_be_username_eq A d, bind_ok,
                absUserList, absSpecList, List.length_map]
              by_cases hu : (Analysis.absDirective A d).couldBeUsername = true
              · simp only [hlen, hu, Bool.true_and, ite_true, fatal_from_eq, bind_ok, Syntax.AParser.run_lift,
                  Syntax.Parser.run_fatalFrom, absStream_getPos]
                exact refines_diagnostic (StatusRel.from KindRel.ambiguousSyntax) ht
              · have hf : (Analysis.absDirective A d).couldBeUsername = false := by simpa using hu
                simp only [hf, Bool.and_false, Bool.false_eq_true, ite_false, make_eq, bind_ok,
                  Syntax.AParser.run_pure]
                exact refines_value (Sudo.Decl d) ht
          · intro e e' t ed ad ht rel
            cases rel with
            | reject =>
              have ar : (Syntax.getDirective O D (absSpec absUserSpecifier key)
                  (absStream s1)).run (absStream s2) = (.error .reject, absStream t) := ad
              simp only [ed, ar, bind_ok, uncurry_apply_pair, maybe_Reject, branch_Ok,
                Syntax.maybe_reject, Syntax.AParser.run_bind, Syntax.AParser.run_lift]
              have hq' : QuoteRoom (absStream t) := by
                have hh := (Syntax.getDirective O D (absSpec absUserSpecifier key) (absStream s1)).reaches
                  (absStream s2) reaches
                rw [ar] at hh
                exact q1.reaches hh
              apply (hL.permissions t ht hq').elimCases
              · intro entries stop ex ax hstop
                simp only [ex, ax, bind_ok, uncurry_apply_pair, branch_Ok, make_eq, Syntax.AParser.run_pure]
                exact refines_value (Sudo.Spec { users, permissions := entries }) hstop
              · intro err err' stop ex ax hstop rel
                simp only [ex, ax, bind_ok, uncurry_apply_pair, branch_Err, from_residual_Err]
                exact refines_diagnostic rel hstop
            | fatal sp k k' hk =>
              have ar : (Syntax.getDirective O D (absSpec absUserSpecifier key)
                  (absStream s1)).run (absStream s2) =
                    (.error (.fatal (absSpan sp) k'), absStream t) := ad
              simp only [ed, ar, bind_ok, uncurry_apply_pair, maybe_Fatal, branch_Err,
                from_residual_Err, Syntax.maybe_fatal]
              exact refines_diagnostic (.fatal _ _ _ hk) ht
        · intro e e' s2 eu au hs2 rel
          cases rel with
          | reject =>
            simp only [eu, au, bind_ok, uncurry_apply_pair, maybe_Reject, branch_Ok, make_eq,
              Syntax.maybe_reject, Syntax.AParser.run_pure]
            exact refines_value Sudo.LineComment hs2
          | fatal sp k k' hk =>
            simp only [eu, au, bind_ok, uncurry_apply_pair, maybe_Fatal, branch_Err,
              from_residual_Err, Syntax.maybe_fatal]
            exact refines_diagnostic (.fatal _ _ _ hk) hs2
  · simp only [ite_true]
    exact hL.includes s1 hs1

/-- Stable binary (`cfg(not(test))`) description for the monomorphic file entry. -/
theorem sudo_description : DescRel sudoUF D.sudo :=
  ⟨_, rfl, by
    simp only [Sudo.Insts.Sudo_rsSudoersAst_namesUserFriendly.DESCRIPTION]
    exact toStr_val _ _⟩

private theorem from_chars_eq (src : Slice Char) :
    sudoers.char_stream.CharStream.from_chars src = ok (⟨src, 0#usize, 1#usize, 1#usize⟩ : CS) := rfl

/-- Lifts item refinement to the actual two monomorphic Rust entry points. `parse_sudoers`
discards the cloned final cursor, so its equality is paired with the cursor-returning
`parse_sudo_lines`. The lemma retains the reference line-parser result and final cursor. -/
theorem parse_sudoers_refines_of_item {A : GlobAbs} {O : Syntax.Oracles}
    (hItem : ParseRefinesOn QuoteRoom sudoParseInst (Analysis.absSudo A) (Syntax.sudo O D))
    (src : Slice Char) (room : 1 + 2 * src.val.length ≤ Usize.max) :
    ∃ raw stop items,
      sudoers.parse_sudoers src = ok raw ∧
      sudoers.ast.parse_sudo_lines ⟨src, 0#usize, 1#usize, 1#usize⟩ = ok (raw, stop) ∧
      Syntax.parseSudoersWith D O src.val = .ok items ∧
      (Syntax.parseLines D.sudo (Syntax.sudo O D)).run (Syntax.Stream.new src.val) =
        (.ok items, absStream stop) ∧
      List.Forall₂ (ResultRel (Analysis.absSudo A)) raw.val items ∧
      StreamOK stop ∧ ∀ r ∈ raw.val, r ≠ .Err .Reject := by
  obtain ⟨raw, stop, items, hx, hs, hr, hw, hn⟩ :=
    parseSudoersWith_of_refinement hItem sudo_description src room
  obtain ⟨raw', stop', items', hx', hp, _, _⟩ := parse_lines_refines_on quoteRoom_stable
    hItem sudo_description (StreamOK.initial src (by omega)) (QuoteRoom.initial src room)
    (by simp; omega)
  simp only [hx, ok.injEq, Prod.mk.injEq] at hx'
  obtain ⟨rfl, rfl⟩ := hx'
  change (Syntax.parseLines D.sudo (Syntax.sudo O D)).run (Syntax.Stream.new src.val) = _ at hp
  have hei : items' = items := by
    simp only [Syntax.parseSudoersWith, hp] at hs
    split at hs
    · cases hs
    · exact Except.ok.inj hs
  subst items'
  refine ⟨raw, stop, items, ?_, ?_, hs, hp, hr, hw, hn⟩
  · simp only [sudoers.parse_sudoers, from_chars_eq, sudoers.ast.parse_sudo_lines,
      hx, bind_ok, uncurry_apply_pair]
  · exact hx

end SudoRsProofs.Parser
