import SudoRsProofs.Parser.DefaultsParse.Text

/-! When a `Defaults` variable list is quoted, both parsers attempt one variable per loop
iteration. The invariant relates the ordered accumulators; each continuation consumes input,
and no live iteration starts with more than 127 entries. -/

open Aeneas Aeneas.Std Result sudo_rs
open SudoersSpec

namespace SudoRsProofs.Parser.DefaultsParse

open Syntax Syntax.Parser

private abbrev varsLoop (O : Oracles) (acc : List String) : Syntax.Parser (List String) :=
  whileSome (tryNonterminal (parseOption (token (envVarToken O.char))))
    (tryNonterminal_parseOption_consumesSome (token_consumes _))
    (parseVarsBody O .release) id acc

private theorem loop_stop (s : CS) (acc : alloc.vec.Vec String) (failure : Option RStatus) :
    sudoers.ast.parse_defaults_vars_loop s acc failure false =
      ok (s.src, s.pos, s.line, s.col, acc, failure) := by
  rw [sudoers.ast.parse_defaults_vars_loop]
  rfl

private abbrev VarsResult (acc : alloc.vec.Vec String) (err : Option RStatus) :
    RParsed (alloc.vec.Vec String) :=
  match err with
  | none => .Ok acc
  | some st => .Err st

private theorem bare_size_le {O : CharOracle} {s t : Stream} {v : String}
    (h : (expectNonterminal Descriptions.release.stringParameter
      (token (stringParameterToken O))).run s = (.ok v, t)) : v.utf8ByteSize ≤ Usize.max := by
  obtain ⟨_, h⟩ := token_before_ws (Grammar.expectNonterminal_ok_iff.mp h)
  have hz := token_size_le (stringParameterToken O) (fun _ => rfl) h
  change v.utf8ByteSize ≤ 1028 at hz
  scalar_tac

private theorem list_limit_fits : (127 : Nat) < Usize.max := by scalar_tac

private theorem vars_loop_refines {O : Oracles} (hO : P2CharOracle O.char)
    (s : CS) (hs : StreamOK s)
    (acc : alloc.vec.Vec String) (hcap : acc.val.length ≤ 127) :
    ∃ (stop : CS) (out : alloc.vec.Vec String) (err : Option RStatus),
      sudoers.ast.parse_defaults_vars_loop s acc none true =
        ok (stop.src, stop.pos, stop.line, stop.col, out, err) ∧
      StreamOK stop ∧
      ResultRel alloc.vec.Vec.val (VarsResult out err) ((varsLoop O acc.val).run (absStream s)).1 ∧
      absStream stop = ((varsLoop O acc.val).run (absStream s)).2 := by
  let opt := parseOption (token (envVarToken O.char))
  let spec := tryNonterminal opt
  have hopt := option_parse_refines (envVar_parse_refines hO)
  obtain ⟨r, s1, e1, hr, hs1, a1⟩ := try_nonterminal_refines hopt hs
  change ResultRel (Option.map id) r (spec.run (absStream s)).1 at hr
  change absStream s1 = (spec.run (absStream s)).2 at a1
  rcases hR : spec.run (absStream s) with ⟨r', t1⟩
  rw [hR] at hr a1
  change absStream s1 = t1 at a1
  subst t1
  rw [sudoers.ast.parse_defaults_vars_loop]
  simp only [ite_true, e1, bind_ok, uncurry_apply_pair, varsLoop, whileSome]
  rw [loop_run]
  simp only [whileSomeBody, run_bind]
  simp only [show (tryNonterminal (parseOption (token (envVarToken O.char)))).run
    (absStream s) = (r', absStream s1) from hR]
  cases r with
  | Err st =>
    cases r' with
    | ok _ => cases hr
    | error e => exact ⟨s1, acc, some st, by simp [loop_stop], hs1, hr, rfl⟩
  | Ok o =>
    cases r' with
    | error _ => cases hr
    | ok oo =>
      have hval : o = oo := by simpa [ResultRel] using hr
      subst oo
      cases o with
      | none =>
        exact ⟨s1, acc, none, by simp [loop_stop], hs1, rfl, rfl⟩
      | some nm =>
        have move : (absStream s1).rest.length < (absStream s).rest.length :=
          (tryNonterminal_parseOption_consumesSome (token_consumes (envVarToken O.char))) _ _ _ hR
        obtain ⟨q, s2, e2, hq, hs2, a2⟩ := is_syntax_refines hs1 '='
        rcases hQ : (isSyntax '=').run (absStream s1) with ⟨q', t2⟩
        rw [hQ] at hq a2
        change absStream s2 = t2 at a2
        subst t2
        simp only [e2, bind_ok, uncurry_apply_pair, id_eq, Option.map_some]
        have refBody : (parseVarsBody O .release acc.val nm).run (absStream s1) =
            match q' with
            | .error e => (.error e, absStream s2)
            | .ok eq => ((if eq then do
                let text ← expectNonterminal Descriptions.release.stringParameter
                  (token (stringParameterToken O.char))
                let xs := acc.val ++ [nm ++ "=" ++ text]
                if xs.length > identifierMany.limit then fatalHere .envVarListTooLong
                else pure (.next xs)
              else
                let xs := acc.val ++ [nm]
                if xs.length > identifierMany.limit then fatalHere .envVarListTooLong
                else pure (.next xs)) : Parser _).run (absStream s2) := by
          conv => lhs; unfold parseVarsBody; rw [run_bind, hQ]
          cases q' with
          | error _ => rfl
          | ok eq => cases eq <;> rfl
        rw [refBody]
        have push_cap : acc.val.length < Usize.max :=
          Nat.lt_of_le_of_lt hcap list_limit_fits
        have emitted (v : String) (s3 : CS) (hs3 : StreamOK s3)
            (moved : (absStream s3).rest.length < (absStream s).rest.length) :
            ∃ (stop : CS) (out : alloc.vec.Vec String) (err : Option RStatus),
              (do
                let acc' ← alloc.vec.Vec.push acc v
                if alloc.vec.Vec.len acc' > sudoers.basic_parser.Many.LIMIT.default sudoers.ast.Identifier then
                  sudoers.ast.parse_defaults_vars_loop s3 acc'
                    (some (.Fatal ⟨(s3.line, s3.col), (s3.line, s3.col)⟩ .EnvironmentListTooLong)) false
                else
                  sudoers.ast.parse_defaults_vars_loop s3 acc' none true) =
                ok (stop.src, stop.pos, stop.line, stop.col, out, err) ∧
              StreamOK stop ∧
              ResultRel alloc.vec.Vec.val (VarsResult out err)
                (if (acc.val ++ [v]).length > identifierMany.limit then
                  .error (.fatal ⟨(absStream s3).getPos, (absStream s3).getPos⟩ .envVarListTooLong)
                else ((varsLoop O (acc.val ++ [v])).run (absStream s3)).1) ∧
              absStream stop = (if (acc.val ++ [v]).length > identifierMany.limit then absStream s3
                else ((varsLoop O (acc.val ++ [v])).run (absStream s3)).2) := by
          obtain ⟨acc', hpush, hval⟩ := exists_eq_ok_of_spec
            (alloc.vec.Vec.push_spec acc v push_cap)
          have hlimit : (sudoers.basic_parser.Many.LIMIT.default sudoers.ast.Identifier).val =
              identifierMany.limit := by simp [sudoers.basic_parser.Many.LIMIT.default, identifierMany]
          have hcmp : (alloc.vec.Vec.len acc' > sudoers.basic_parser.Many.LIMIT.default
              sudoers.ast.Identifier) ↔ (acc.val ++ [v]).length > identifierMany.limit := by
            simp only [gt_iff_lt, UScalar.lt_equiv, alloc.vec.Vec.len_val, hlimit]
            rw [show acc'.length = (acc.val ++ [v]).length from congrArg List.length hval]
          by_cases hgt : (acc.val ++ [v]).length > identifierMany.limit
          · let st : RStatus := .Fatal ⟨(s3.line, s3.col), (s3.line, s3.col)⟩
              .EnvironmentListTooLong
            refine ⟨s3, acc', some st, ?_, hs3, ?_, by simp only [hgt, ite_true]⟩
            · simp only [hpush, bind_ok, hcmp.mpr hgt, ite_true, loop_stop]
              rfl
            · simp only [hgt, ite_true, VarsResult, ResultRel]
              exact StatusRel.here .environmentListTooLong
          · have hcap' : acc'.val.length ≤ 127 := by
              change ¬ (acc.val ++ [v]).length > 127 at hgt
              rw [hval]; omega
            obtain ⟨stop, out, err, he, hstop, hrel, habs⟩ :=
              vars_loop_refines hO s3 hs3 acc' hcap'
            refine ⟨stop, out, err, ?_, hstop, ?_, ?_⟩
            · have hn := mt hcmp.mp hgt
              simpa only [hpush, bind_ok, hn, ite_false] using he
            · simpa only [hval, hgt, ite_false] using hrel
            · simpa only [hval, hgt, ite_false] using habs
        cases q with
        | Err st =>
          cases q' with
          | ok _ => cases hq
          | error e => exact ⟨s2, acc, some st, by simp [loop_stop], hs2, hq, rfl⟩
        | Ok b =>
          cases q' with
          | error _ => cases hq
          | ok b' =>
            have hb : b = b' := hq
            subst b'
            have move2 : (absStream s2).rest.length < (absStream s).rest.length :=
              Nat.lt_of_le_of_lt (length_le_of_run hQ) move
            cases b with
            | false =>
              obtain ⟨stop, out, err, he, hstop, hrel, habs⟩ := emitted nm s2 hs2 move2
              refine ⟨stop, out, err, ?_, hstop, ?_, ?_⟩
              · simpa [get_pos_eq'] using he
              all_goals
                by_cases h : (acc.val ++ [nm]).length > identifierMany.limit
                all_goals
                  simp only [Bool.false_eq_true, ite_false, run_bind, run_pure, h, ite_true,
                    run_fatalHere] at hrel habs ⊢
                  assumption
            | true =>
              obtain ⟨rs, s3, e3, hrel, hs3, a3⟩ := expect_nonterminal_refines
                (string_parameter_parse_refines hO) string_parameter_description hs2
              rcases hE : (expectNonterminal Descriptions.release.stringParameter
                (token (stringParameterToken O.char))).run (absStream s2) with ⟨rs', t3⟩
              rw [hE] at hrel a3
              change absStream s3 = t3 at a3
              subst t3
              simp only [e3, bind_ok, uncurry_apply_pair, id_eq, ite_true, run_bind, hE]
              cases rs with
              | Err st =>
                cases rs' with
                | ok _ => cases hrel
                | error e => exact ⟨s3, acc, some st, by simp [loop_stop], hs3, hrel, rfl⟩
              | Ok raw =>
                cases rs' with
                | error _ => cases hrel
                | ok value =>
                  have hv : raw = value := hrel
                  subst value
                  have moved := Nat.lt_of_le_of_lt (length_le_of_run hE) move2
                  obtain ⟨stop, out, err, he, hstop, hrel, habs⟩ :=
                    emitted (nm ++ "=" ++ raw) s3 hs3 moved
                  refine ⟨stop, out, err, ?_, hstop, ?_, ?_⟩
                  · simpa [join_var_eq nm raw (bare_size_le hE), get_pos_eq'] using he
                  all_goals
                    by_cases h : (acc.val ++ [nm ++ "=" ++ raw]).length > identifierMany.limit
                    all_goals
                      simp only [id_eq, run_pure, run_bind, h, ite_true, ite_false,
                        run_fatalHere] at hrel habs ⊢
                      assumption
termination_by (absStream s).rest.length
decreasing_by simpa only [absStream_rest, List.length_drop] using moved

/-- `parse_defaults_vars` refines `parseVars`, including both diagnostics for malformed list
values and the cursor on failure. -/
theorem parse_defaults_vars_refines {O : Oracles} (hO : P2CharOracle O.char)
    {s : CS} (hs : StreamOK s) :
    Refines alloc.vec.Vec.val (sudoers.ast.parse_defaults_vars s)
      ((parseVars O .release).run (absStream s)) := by
  obtain ⟨s1, e1, hs1, a1⟩ := eat_char_eq hs '"'
  simp only [sudoers.ast.parse_defaults_vars, e1, bind_ok, uncurry_apply_pair, parseVars,
    run_bind, run_eatChar]
  rcases hb : (absStream s).eatChar '"' with ⟨b, t1⟩
  rw [hb] at a1
  change absStream s1 = t1 at a1
  subst t1
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    obtain ⟨r, s2, e2, hr, hs2, a2⟩ := expect_nonterminal_refines
      (envVar_parse_refines hO) envVar_description hs1
    simp only [e2, bind_ok, uncurry_apply_pair]
    rcases hR : (expectNonterminal Descriptions.release.envVar
      (token (envVarToken O.char))).run (absStream s1) with ⟨r', t2⟩
    rw [hR] at hr a2
    change absStream s2 = t2 at a2
    simp only [run_bind, hR]
    subst t2
    cases r with
    | Err st =>
      cases r' <;> simp_all [ResultRel]
    | Ok nm =>
      cases r' with
      | error _ => cases hr
      | ok n =>
        have hnm : nm = n := hr
        subst n
        obtain ⟨q, s3, e3, hq, hs3, a3⟩ := is_syntax_refines hs2 '='
        simp only [branch_Ok, bind_ok, uncurry_apply_pair, e3]
        rcases hQ : (isSyntax '=').run (absStream s2) with ⟨q', t3⟩
        rw [hQ] at hq a3
        change absStream s3 = t3 at a3
        subst t3
        cases q with
        | Err st =>
          cases q' <;> simp only [ResultRel, Prod.fst] at hq <;>
            simp [hq, hs3]
        | Ok eq =>
          cases q' with
          | error _ => cases hq
          | ok eq' =>
            have heq : eq = eq' := hq
            subst eq'
            cases eq
            · simp [alloc.slice.Slice.into_vec, Array.to_slice, Std.Array.make, Std.lift, hs3]
              exact Slice.from_val _ _
            · simp [run_fatalHere, hs3, KindRel.quotesRequiredForVarValue]
  | true =>
    simp only [ite_true]
    obtain ⟨stop, acc, err, el, hl, hrel, al⟩ :=
      vars_loop_refines hO s1 hs1 (alloc.vec.Vec.new _) (by simp)
    have e : (alloc.vec.Vec.new String).val = [] := rfl
    rw [e] at hrel al
    simp only [el, bind_ok, uncurry_apply_pair]
    rcases hA : (varsLoop O []).run (absStream s1) with ⟨r, t⟩
    rw [hA] at hrel al
    change absStream stop = t at al
    simp only [run_bind, hA]
    subst t
    cases err with
    | some st =>
      cases r <;> simp_all [VarsResult, ResultRel]
    | none =>
      cases r with
      | error _ => cases hrel
      | ok vs =>
        have he : acc.val = vs := hrel
        subst vs
        obtain ⟨q, s2, e2, hq, hs2, a2⟩ := expect_syntax_refines hl '"'
        simp only [e2, bind_ok, uncurry_apply_pair]
        rcases hQ : (expectSyntax '"').run (absStream stop) with ⟨q', t2⟩
        rw [hQ] at hq a2
        change absStream s2 = t2 at a2
        subst t2
        cases q with
        | Err st => cases q' <;> simp_all [ResultRel]
        | Ok un =>
          cases q' with
          | error _ => cases hq
          | ok u =>
            cases un
            cases u
            by_cases emp : acc.val = []
            · simp [alloc.vec.Vec.is_empty, emp, run_fatalHere, KindRel.emptyStringNotAllowed, hs2]
            · simp [alloc.vec.Vec.is_empty, List.length_eq_zero_iff, emp, hs2]

end SudoRsProofs.Parser.DefaultsParse
