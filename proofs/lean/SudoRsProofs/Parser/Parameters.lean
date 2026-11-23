import SudoRsProofs.Parser.P2Oracle

/-! Refinement of `StringParameter`, `Unquoted<T>`, and `ChDir`. -/

open Aeneas Aeneas.Std Result
open sudo_rs
open SudoersSpec.Syntax (CharOracle Oracles TokenSpec chDirToken stringParameterToken unquotedToken)

namespace SudoRsProofs.Parser

private theorem char_beq (c d : Char) : (c == d) = decide (c = d) := rfl

private theorem string_parameter_escaped_eq (c : Char) :
    sudoers.tokens.StringParameter.Insts.Sudo_rsSudoersBasic_parserToken.escaped c =
      ok (SudoersSpec.Syntax.StringParameter.escaped c) := by
  simp only [sudoers.tokens.StringParameter.Insts.Sudo_rsSudoersBasic_parserToken.escaped,
    escape_char_eq, bind_ok, SudoersSpec.Syntax.StringParameter.escaped, char_beq]
  split_ifs <;> simp_all

private theorem string_parameter_accept_eq {O : CharOracle} (hO : P2CharOracle O) (c : Char) :
    sudoers.tokens.StringParameter.Insts.Sudo_rsSudoersBasic_parserToken.accept c =
      ok ((stringParameterToken O).accept c) := by
  cases hc : O.isControl c <;>
    simp [sudoers.tokens.StringParameter.Insts.Sudo_rsSudoersBasic_parserToken.accept,
      hO.is_control, hc, string_parameter_escaped_eq, stringParameterToken]

theorem string_parameter_token_refines {O : CharOracle} (hO : P2CharOracle O) :
    TokenRefines sudoers.tokens.StringParameter.Insts.Sudo_rsSudoersBasic_parserToken id
      (stringParameterToken O) (fun _ => True) where
  max_len := ⟨_, rfl, by
    simp [sudoers.tokens.StringParameter.Insts.Sudo_rsSudoersBasic_parserToken.MAX_LEN,
      sudoers.tokens.QuotedStringParameter.Insts.Sudo_rsSudoersBasic_parserToken.MAX_LEN,
      stringParameterToken]⟩
  max_len_le := by simp only [stringParameterToken]; scalar_tac
  allow_escape := by
    change ok sudoers.tokens.StringParameter.Insts.Sudo_rsSudoersBasic_parserToken.ALLOW_ESCAPE =
      ok true
    rw [sudoers.tokens.StringParameter.Insts.Sudo_rsSudoersBasic_parserToken.ALLOW_ESCAPE]
  accept c := string_parameter_accept_eq hO c
  accept_1st c := string_parameter_accept_eq hO c
  escaped c := string_parameter_escaped_eq c
  construct s _ _ := ⟨.Ok s, rfl, (String.ofList_toList (s := s)).symm⟩

/-- The `impl Parse` instance of `StringParameter` refines `token`; `construct` is total. -/
theorem string_parameter_parse_refines {O : CharOracle} (hO : P2CharOracle O) :
    ParseRefines
      (sudoers.basic_parser.Parse.Blanket
        sudoers.tokens.StringParameter.Insts.Sudo_rsSudoersBasic_parserToken) id
      (SudoersSpec.Syntax.token (stringParameterToken O)) :=
  token_refines (string_parameter_token_refines hO) (fun _ _ => trivial)

section Unquoted

variable {T α : Type} {Tk : sudoers.basic_parser.Token T} {T' : TokenSpec α}

private theorem unquoted_construct_loop_aux (he : ∀ c, Tk.escaped c = ok (T'.escaped c))
    (chars : alloc.vec.Vec Char) :
    ∀ (n : Nat) (quoted : String) (i : Usize), chars.val.length - i.val ≤ n →
      sudoers.tokens.Unquoted.Insts.Sudo_rsSudoersBasic_parserToken.construct_loop Tk chars quoted i =
        ok (String.ofList (quoted.toList ++ (chars.val.drop i.val).flatMap
          fun c => if T'.escaped c then ['\\', c] else [c])) := by
  intro n
  induction n with
  | zero =>
    intro quoted i hi
    have hif : ¬ i.val < chars.val.length := by omega
    have hge : chars.val.length ≤ i.val := by omega
    unfold sudoers.tokens.Unquoted.Insts.Sudo_rsSudoersBasic_parserToken.construct_loop
    have hcond : ¬ (i < alloc.vec.Vec.len chars) := by
      simpa [alloc.vec.Vec.len] using hif
    rw [ite_eq_right hcond]
    simp [List.drop_eq_nil_of_le hge]
  | succ n ih =>
    intro quoted i hi
    by_cases hif : i.val < chars.val.length
    · have hi' : i.val < chars.val.length := hif
      have hindex : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Char) chars i =
          ok chars.val[i.val] := by
        rw [alloc.vec.Vec.index_slice_index]
        exact eq_ok_of_spec (alloc.vec.Vec.index_usize_spec chars i hi')
      obtain ⟨j, hj, hjv'⟩ := exists_eq_ok_of_spec
        (UScalar.add_spec (x := i) (y := 1#usize) (by have := chars.property; scalar_tac))
      have hjv : j.val = i.val + 1 := by simpa using hjv'
      have hd := List.drop_eq_getElem_cons hi'
      unfold sudoers.tokens.Unquoted.Insts.Sudo_rsSudoersBasic_parserToken.construct_loop
      have hcond : i < alloc.vec.Vec.len chars := by
        simpa [alloc.vec.Vec.len] using hif
      rw [ite_eq_left hcond]
      rw [hindex, bind_ok, he, bind_ok]
      cases hb : T'.escaped chars.val[i.val]
      · simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, alloc.string.String.push, hj]
        rw [ih _ j (by omega), hjv]
        simp only [hd, Result.ok.injEq, List.flatMap_cons, String.toList_push]
        generalize hc : chars.val[i.val] = c at hb ⊢
        simp [hb, List.append_assoc]
      · simp only [↓reduceIte, bind_ok, escape_char_eq, alloc.string.String.push, hj]
        rw [ih _ j (by omega), hjv]
        simp only [hd, Result.ok.injEq, List.flatMap_cons, String.toList_push]
        generalize hc : chars.val[i.val] = c at hb ⊢
        simp [hb, List.append_assoc]
    · have hge : chars.val.length ≤ i.val := by omega
      unfold sudoers.tokens.Unquoted.Insts.Sudo_rsSudoersBasic_parserToken.construct_loop
      have hcond : ¬ (i < alloc.vec.Vec.len chars) := by
        simpa [alloc.vec.Vec.len] using hif
      rw [ite_eq_right hcond]
      simp [List.drop_eq_nil_of_le hge]

private theorem unquoted_construct_loop_eq (he : ∀ c, Tk.escaped c = ok (T'.escaped c))
    (chars : alloc.vec.Vec Char) (quoted : String) (i : Usize) :
    sudoers.tokens.Unquoted.Insts.Sudo_rsSudoersBasic_parserToken.construct_loop Tk chars quoted i =
      ok (String.ofList (quoted.toList ++ (chars.val.drop i.val).flatMap
        fun c => if T'.escaped c then ['\\', c] else [c])) :=
  unquoted_construct_loop_aux he chars _ quoted i (Nat.le_refl _)

/-- The re-escaping step depends only on the underlying token's `escaped` predicate. -/
theorem unquoted_construct_eq (he : ∀ c, Tk.escaped c = ok (T'.escaped c))
    (s : String) (hs : s.utf8ByteSize ≤ Usize.max) :
    sudoers.tokens.Unquoted.Insts.Sudo_rsSudoersBasic_parserToken.construct Tk s =
      ok (.Ok (String.ofList (s.toList.flatMap
        fun c => if T'.escaped c then ['\\', c] else [c]), ())) := by
  obtain ⟨v, hv, hd⟩ := chars_of_eq s hs
  rw [SudoRsProofs.Vec.deref_val] at hd
  simp [sudoers.tokens.Unquoted.Insts.Sudo_rsSudoersBasic_parserToken.construct,
    hv, alloc.string.String.new, unquoted_construct_loop_eq he, hd]

/-- Re-escaping adds at most one byte per character, never more than doubling the byte size. -/
theorem unquoted_text_size (T' : TokenSpec α) (cs : List Char) :
    (String.ofList (cs.flatMap fun c => if T'.escaped c then ['\\', c] else [c])).utf8ByteSize ≤
      2 * (String.ofList cs).utf8ByteSize := by
  have hslash : ('\\' : Char).utf8Size = 1 := rfl
  induction cs with
  | nil => simp
  | cons c cs ih =>
    have hc := c.utf8Size_pos
    cases he : T'.escaped c <;>
      simp only [List.flatMap_cons, he, Bool.false_eq_true, ↓reduceIte, List.cons_append,
        List.nil_append, String.ofList_cons, String.utf8ByteSize_append,
        String.utf8ByteSize_singleton, hslash] <;> omega

theorem unquoted_construct_size {f : T → α} {Pre : List Char → Prop}
    (h : TokenRefines Tk f T' Pre) (s : String) (hs : s.utf8ByteSize ≤ Usize.max) :
    ∃ r, sudoers.tokens.Unquoted.Insts.Sudo_rsSudoersBasic_parserToken.construct Tk s =
        ok (.Ok r) ∧
      r.1 = String.ofList (s.toList.flatMap fun c => if T'.escaped c then ['\\', c] else [c]) ∧
      r.1.utf8ByteSize ≤ 2 * s.utf8ByteSize :=
  ⟨_, unquoted_construct_eq h.escaped s hs, rfl,
    by simpa only [String.ofList_toList] using unquoted_text_size T' s.toList⟩

private theorem unquoted_accept_eq {O : CharOracle} (hO : P2CharOracle O) (Tk :
    sudoers.basic_parser.Token T) (T' : TokenSpec α) (c : Char) :
    sudoers.tokens.Unquoted.Insts.Sudo_rsSudoersBasic_parserToken.accept Tk c =
      ok ((unquotedToken O T').accept c) := by
  by_cases hc : c = '"' <;>
    simp [sudoers.tokens.Unquoted.Insts.Sudo_rsSudoersBasic_parserToken.accept, hc,
      hO.is_control, unquotedToken, bne, char_beq]

theorem unquoted_token_refines {O : CharOracle} {f : T → α} {Pre : List Char → Prop}
    (hO : P2CharOracle O) (h : TokenRefines Tk f T' Pre) :
    TokenRefines (sudoers.tokens.Unquoted.Insts.Sudo_rsSudoersBasic_parserToken Tk)
      (fun x => x.1) (unquotedToken O T') (fun _ => True) where
  max_len := ⟨_, rfl, by
    simp [sudoers.tokens.Unquoted.Insts.Sudo_rsSudoersBasic_parserToken.MAX_LEN, unquotedToken]⟩
  max_len_le := by simp only [unquotedToken]; scalar_tac
  allow_escape := by
    change ok (sudoers.basic_parser.Token.ALLOW_ESCAPE.default (sudoers.tokens.Unquoted T)) =
      ok false
    rw [sudoers.basic_parser.Token.ALLOW_ESCAPE.default]
  accept c := unquoted_accept_eq hO Tk T' c
  accept_1st c := unquoted_accept_eq hO Tk T' c
  escaped _ := rfl
  construct s hs _ := by
    obtain ⟨r, hr, he, _⟩ := unquoted_construct_size h s hs
    exact ⟨.Ok r, hr, he⟩

/-- The `impl Parse` instance of `Unquoted<T>` refines `token`; the re-escaping constructor is
total. -/
theorem unquoted_parse_refines {O : CharOracle} {f : T → α} {Pre : List Char → Prop}
    (hO : P2CharOracle O) (h : TokenRefines Tk f T' Pre) :
    ParseRefines
      (sudoers.basic_parser.Parse.Blanket
        (sudoers.tokens.Unquoted.Insts.Sudo_rsSudoersBasic_parserToken Tk))
      (fun x : sudoers.tokens.Unquoted T => x.1)
      (SudoersSpec.Syntax.token (unquotedToken O T')) :=
  token_refines (unquoted_token_refines hO h) (fun _ _ => trivial)

end Unquoted

private theorem chdir_escaped_eq (c : Char) :
    sudoers.tokens.ChDir.Insts.Sudo_rsSudoersBasic_parserToken.escaped c =
      ok (SudoersSpec.Syntax.ChDir.escaped c) := by
  simp only [sudoers.tokens.ChDir.Insts.Sudo_rsSudoersBasic_parserToken.escaped,
    escape_char_eq, bind_ok, SudoersSpec.Syntax.ChDir.escaped, char_beq]
  split_ifs <;> simp_all

private theorem chdir_accept_eq {O : Oracles} (hO : P2CharOracle O.char) (c : Char) :
    sudoers.tokens.ChDir.Insts.Sudo_rsSudoersBasic_parserToken.accept c =
      ok ((chDirToken O).accept c) := by
  cases hc : O.char.isControl c <;>
    simp [sudoers.tokens.ChDir.Insts.Sudo_rsSudoersBasic_parserToken.accept, hO.is_control,
      hc, chdir_escaped_eq, chDirToken]

private theorem chdir_accept_first_eq (O : Oracles) (c : Char) :
    sudoers.tokens.ChDir.Insts.Sudo_rsSudoersBasic_parserToken.accept_1st c =
      ok ((chDirToken O).accept1st c) := by
  simp only [sudoers.tokens.ChDir.Insts.Sudo_rsSudoersBasic_parserToken.accept_1st,
    chDirToken, char_beq]
  split_ifs <;> simp_all

private theorem classify_chdir_eq (s : String) :
    sudoers.tokens.classify_chdir s =
      if s.toList == ['*'] then ok .Any
      else if s.toList.contains '*' then ok .ContainsStar else ok .Path := by
  have hs : s.toList = ['*'] ↔ s = "*" := by
    change s.toList = ("*" : String).toList ↔ s = "*"
    exact String.toList_inj
  simp only [sudoers.tokens.classify_chdir, beq_iff_eq, hs]

private theorem chdir_not_all_star {s : String} (hstar : '*' ∉ s.toList) :
    (s.toList == ['*']) = false := by
  cases hb : (s.toList == ['*'])
  · rfl
  · have he := beq_iff_eq.mp hb
    exact absurd he (fun h => hstar (by rw [h]; simp))

private theorem chdir_not_contains_star {s : String} (hstar : '*' ∉ s.toList) :
    s.toList.contains '*' = false := by
  cases hb : s.toList.contains '*'
  · rfl
  · exact absurd (List.contains_iff_mem.mp hb) hstar

/-- When the constructor reaches `sudo_path`, the extracted error carries the original
string, and the reference error is its `debugPath` diagnostic. -/
theorem chdir_construct_nul_diagnostic (O : Oracles) (s : String)
    (hstar : '*' ∉ s.toList) (hnul : '\x00' ∈ s.toList) :
    sudoers.tokens.ChDir.Insts.Sudo_rsSudoersBasic_parserToken.construct s =
        ok (.Err (.NulInPath s)) ∧
      (validationDiagnostic O.fmt (.NulInPath s)).map Except.error =
        some (SudoersSpec.Syntax.ChDir.construct O s.toList) := by
  have hany : (s.toList == ['*']) = false := chdir_not_all_star hstar
  have hstar' : s.toList.contains '*' = false := chdir_not_contains_star hstar
  have hn : s.toList.contains '\x00' = true := List.contains_iff_mem.mpr hnul
  have hn' : s.toList.contains (Char.ofNat 0) = true := hn
  constructor
  · simp only [sudoers.tokens.ChDir.Insts.Sudo_rsSudoersBasic_parserToken.construct,
      classify_chdir_eq, hany, hstar', Bool.false_eq_true, ↓reduceIte, bind_ok,
      sudoers.tokens.sudo_path, hn']
  · simp only [SudoersSpec.Syntax.ChDir.construct, SudoersSpec.Syntax.sudoPathTryFrom,
      hany, hstar', hn, Bool.false_eq_true, ↓reduceIte, String.ofList_toList,
      validationDiagnostic, Option.map]

theorem chdir_token_refines {O : Oracles} (hO : P2CharOracle O.char) :
    TokenRefines sudoers.tokens.ChDir.Insts.Sudo_rsSudoersBasic_parserToken absChDir
      (chDirToken O) (fun cs => '\x00' ∉ cs) where
  max_len := ⟨_, rfl, by
    simp [sudoers.tokens.ChDir.Insts.Sudo_rsSudoersBasic_parserToken.MAX_LEN, chDirToken]⟩
  max_len_le := by simp only [chDirToken]; scalar_tac
  allow_escape := by
    change ok sudoers.tokens.ChDir.Insts.Sudo_rsSudoersBasic_parserToken.ALLOW_ESCAPE = ok true
    rw [sudoers.tokens.ChDir.Insts.Sudo_rsSudoersBasic_parserToken.ALLOW_ESCAPE]
  accept c := chdir_accept_eq hO c
  accept_1st c := chdir_accept_first_eq O c
  escaped c := chdir_escaped_eq c
  construct s _ hnul := by
    have hn : s.toList.contains '\x00' = false := by
      cases hb : s.toList.contains '\x00'
      · rfl
      · exact absurd (List.contains_iff_mem.mp hb) hnul
    change ∃ r, sudoers.tokens.ChDir.Insts.Sudo_rsSudoersBasic_parserToken.construct s = ok r ∧
      ConstructRel absChDir r (SudoersSpec.Syntax.ChDir.construct O s.toList)
    cases hany : (s.toList == ['*'])
    · cases hstar : s.toList.contains '*'
      · simp only [sudoers.tokens.ChDir.Insts.Sudo_rsSudoersBasic_parserToken.construct,
          classify_chdir_eq, hany, hstar, Bool.false_eq_true, ↓reduceIte, bind_ok,
          sudoers.tokens.sudo_path, SudoersSpec.Syntax.ChDir.construct,
          SudoersSpec.Syntax.sudoPathTryFrom, hn, String.ofList_toList]
        exact ⟨_, rfl, rfl⟩
      · simp only [sudoers.tokens.ChDir.Insts.Sudo_rsSudoersBasic_parserToken.construct,
          classify_chdir_eq, hany, hstar, Bool.false_eq_true, ↓reduceIte, bind_ok,
          SudoersSpec.Syntax.ChDir.construct]
        exact ⟨_, rfl, KindRel.starInPath⟩
    · simp only [sudoers.tokens.ChDir.Insts.Sudo_rsSudoersBasic_parserToken.construct,
        classify_chdir_eq, hany, ↓reduceIte, bind_ok,
        SudoersSpec.Syntax.ChDir.construct]
      exact ⟨_, rfl, rfl⟩

private theorem chdir_text_no_nul {O : Oracles} (hO : P2CharOracle O.char)
    (cs : List Char) (ht : TokenText (chDirToken O) cs) : '\x00' ∉ cs := by
  have h1 : core.char.methods.Char.is_control '\x00' = ok true := by
    simp [core.char.methods.Char.is_control]
  have h2 := hO.is_control '\x00'
  rw [h1] at h2
  have hctrl : O.char.isControl '\x00' = true := by simpa using h2.symm
  have hesc : (chDirToken O).escaped '\x00' = false := by
    show SudoersSpec.Syntax.ChDir.escaped '\x00' = false
    decide
  have hfirst : (chDirToken O).accept1st '\x00' = false := by
    show (('\x00' : Char) == '~' || ('\x00' : Char) == '/' || ('\x00' : Char) == '*') = false
    decide
  have hrest : (chDirToken O).accept '\x00' = false := by
    simp [chDirToken, hctrl, SudoersSpec.Syntax.ChDir.escaped]
  rcases cs with _ | ⟨c, cs⟩
  · simp
  intro hm
  rcases List.mem_cons.mp hm with he | hm
  · subst c
    simpa [Produces, hfirst, hesc] using ht.1
  · simpa [Produces, hrest, hesc] using ht.2 _ hm

/-- Neither literal characters nor escapes can put NUL in the `ChDir` token text. -/
theorem chdir_parse_refines {O : Oracles} (hO : P2CharOracle O.char) :
    ParseRefines
      (sudoers.basic_parser.Parse.Blanket sudoers.tokens.ChDir.Insts.Sudo_rsSudoersBasic_parserToken)
      absChDir (SudoersSpec.Syntax.token (chDirToken O)) :=
  token_refines (chdir_token_refines hO) (chdir_text_no_nul hO)

/-! ## Descriptions -/

theorem string_parameter_description :
    DescRel sudoers.tokens.StringParameter.Insts.Sudo_rsSudoersAst_namesUserFriendly
      SudoersSpec.Syntax.Descriptions.release.stringParameter :=
  ⟨_, rfl, by
    simp only [sudoers.tokens.StringParameter.Insts.Sudo_rsSudoersAst_namesUserFriendly.DESCRIPTION,
      sudoers.tokens.QuotedStringParameter.Insts.Sudo_rsSudoersAst_namesUserFriendly.DESCRIPTION]
    exact toStr_val _ _⟩

/-- `Unquoted<T>` inherits `T`'s description unchanged. -/
theorem unquoted_description {T : Type} {UF : sudoers.ast_names.UserFriendly T} {d : String}
    (hD : DescRel UF d) :
    DescRel (sudoers.tokens.Unquoted.Insts.Sudo_rsSudoersAst_namesUserFriendly UF) d := by
  obtain ⟨s, hs, hv⟩ := hD
  exact ⟨s, by
    simp only [sudoers.tokens.Unquoted.Insts.Sudo_rsSudoersAst_namesUserFriendly.DESCRIPTION, hs], hv⟩

theorem chdir_description :
    DescRel sudoers.tokens.ChDir.Insts.Sudo_rsSudoersAst_namesUserFriendly
      SudoersSpec.Syntax.Descriptions.release.chDir :=
  ⟨_, rfl, by
    simp only [sudoers.tokens.ChDir.Insts.Sudo_rsSudoersAst_namesUserFriendly.DESCRIPTION]
    exact toStr_val _ _⟩

end SudoRsProofs.Parser
