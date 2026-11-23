import SudoRsProofs.Parser.DefaultsParse.Vars
import SudoRsProofs.Parser.DefaultsParse.Try
import SudoRsProofs.Parser.List

/-! The extracted Defaults modifier production refines the reference on any representable
cursor. The only environment hypothesis is the shared P2 character agreement. -/

open Aeneas Aeneas.Std Result sudo_rs SudoersSpec

namespace SudoRsProofs.Parser

open Syntax Syntax.Parser DefaultsParse

private theorem name_size_le {s t : Stream} {n : String}
    (h : (tryNonterminal (token defaultNameToken)).run s = (.ok n, t)) :
    n.utf8ByteSize ≤ Usize.max := by
  obtain ⟨_, h⟩ := token_before_ws h
  have e := token_size_le defaultNameToken (fun _ => rfl) h
  change n.utf8ByteSize ≤ 259 at e
  scalar_tac

/-- The `+=` / `-=` continuation expects `=` before checking the kind of the setting. -/
theorem parse_defaults_list_refines {O : Oracles} (hO : P2CharOracle O.char)
    (mode : defaults.ListMode) (nm : String) (cfg : defaults.SettingKind)
    (pos : Usize × Usize) {s : CS} (hs : StreamOK s) :
    Refines Defaults.absModifier (sudoers.ast.parse_defaults_list mode nm cfg pos s)
      ((listItems O .release (pos.1.val, pos.2.val) (Defaults.absListMode mode) nm
        (Defaults.absKind cfg)).run (absStream s)) := by
  unfold sudoers.ast.parse_defaults_list listItems
  call_refinement (expect_syntax_refines hs '=') with ignored s1 hs1 heq
  rcases pos with ⟨line, col⟩
  cases cfg with
  | Flag _ => simp [Defaults.absKind, run_fatalFrom, hs1, KindRel.notAListParameter]
  | Integer _ => simp [Defaults.absKind, run_fatalFrom, hs1, KindRel.notAListParameter]
  | Text _ => simp [Defaults.absKind, run_fatalFrom, hs1, KindRel.notAListParameter]
  | List id =>
    simp only [Defaults.absKind]
    call_refinement (parse_defaults_vars_refines hO hs1) with v s2 hs2 hvars
    obtain ⟨m, hm, hmv⟩ := Defaults.build_list_eq id mode v
    simp [hm, hmv, hs2]

private theorem modifier_parse_refines {O : Oracles} (hO : P2CharOracle O.char)
    {s : CS} (hs : StreamOK s) :
    Refines Defaults.absModifier (defaults.SettingsModifier.Insts.Sudo_rsSudoersBasic_parserParse.parse s)
      ((settingsModifier O .release).run (absStream s)) := by
  unfold defaults.SettingsModifier.Insts.Sudo_rsSudoersBasic_parserParse.parse settingsModifier
  simp only [get_pos_eq', bind_ok, run_bind_of_ok (run_getPos _)]
  call_refinement (is_syntax_refines hs '!') with bang s1 hs1 hbang
  cases bang with
  | true =>
    simp only [id_eq, ite_true, get_pos_eq', bind_ok, run_bind_of_ok (run_getPos _)]
    call_refinement (expect_nonterminal_refines defaultName_parse_refines
      defaultName_description hs1) with nm s2 hs2 hnm
    have hnm' := Grammar.expectNonterminal_ok_iff.mp hnm
    obtain ⟨t, ht, hb⟩ := as_str_bytes nm (name_size_le hnm')
    obtain ⟨n, hn, hnv⟩ := Defaults.negate_eq t nm hb
    simp only [id_eq, ht, hn, bind_ok, ← hnv]
    cases n with
    | some m => simp [hs2]
    | none =>
      obtain ⟨cfg, hcfg, hcfgv⟩ := Defaults.set_eq t nm hb
      simp only [hcfg, bind_ok, ← hcfgv]
      cases cfg <;> simp [hs2, run_fatalFrom, KindRel.unknownSetting, KindRel.cannotUseInBoolean]
  | false =>
    simp only [id_eq, Bool.false_eq_true, ite_false]
    call_refinement (try_nonterminal_refines defaultName_parse_refines hs1) with nm s2 hs2 hnm
    obtain ⟨t, ht, hb⟩ := as_str_bytes nm (name_size_le hnm)
    obtain ⟨cfg, hcfg, hcfgv⟩ := Defaults.set_eq t nm hb
    simp only [id_eq, ht, hcfg, bind_ok, ← hcfgv]
    cases cfg with
    | none => simp [hs2, run_fatalFrom, KindRel.unknownSetting]
    | some cfg =>
      simp only [Option.map_some]
      call_refinement (is_syntax_refines hs2 '+') with plus s3 hs3 hplus
      cases plus with
      | true =>
        simpa only [ite_true, Defaults.absListMode, absStream_getPos] using
          parse_defaults_list_refines hO .Add nm cfg
          (s.line, s.col) hs3
      | false =>
        simp only [id_eq, Bool.false_eq_true, ite_false]
        call_refinement (is_syntax_refines hs3 '-') with minus s4 hs4 hminus
        cases minus with
        | true =>
          simpa only [ite_true, Defaults.absListMode, absStream_getPos] using
            parse_defaults_list_refines hO .Del nm cfg
            (s.line, s.col) hs4
        | false =>
          simp only [id_eq, Bool.false_eq_true, ite_false]
          call_refinement (is_syntax_refines hs4 '=') with eq s5 hs5 hassign
          cases eq with
          | false =>
            cases cfg <;> simp [Defaults.absKind, hs5, run_fatalFrom, KindRel.notABooleanSetting]
          | true =>
            simp only [id_eq, ite_true, get_pos_eq', bind_ok, run_bind_of_ok (run_getPos _)]
            cases cfg with
            | Flag _ => simp [Defaults.absKind, hs5, run_fatalHere, KindRel.cannotAssignBoolean]
            | List id =>
              simp only [Defaults.absKind]
              call_refinement (parse_defaults_vars_refines hO hs5) with v s6 hs6 hvars
              obtain ⟨m, hm, hmv⟩ := Defaults.build_list_eq id .Set v
              simp [hm, hmv, Defaults.absListMode, hs6]
            | Integer id =>
              simp only [Defaults.absKind]
              call_refinement (expect_nonterminal_refines numeric_parse_refines
                numeric_description hs5) with value s6 hs6 hvalue
              have hv := Settings.numeric_bytes_le hvalue
              change (Settings.bytes value).length ≤ 18 at hv
              have e : (Settings.bytes value).length = value.utf8ByteSize := by
                unfold Settings.bytes
                rw [List.length_map, Array.length_toList]
                rfl
              have hsizes : value.utf8ByteSize ≤ Usize.max := by rw [e] at hv; scalar_tac
              obtain ⟨arg, ha, hav⟩ := as_str_bytes value hsizes
              obtain ⟨m, hm, hmv⟩ := Defaults.check_integer_eq id arg value hav (fun _ => hv)
              simp only [id_eq, ha, hm, bind_ok, ← hmv]
              cases m <;> simp [hs6, run_fatalFrom, KindRel.invalidSettingValue]
            | Text id =>
              simp only [Defaults.absKind]
              call_refinement (parse_defaults_text_refines hO hs5) with value s6 hs6 hvalue
              have hv := textItem_size_le hvalue
              change value.utf8ByteSize ≤ 1028 at hv
              obtain ⟨arg, ha, hav⟩ := as_str_bytes value (by scalar_tac)
              obtain ⟨m, hm, hmv⟩ := Defaults.check_text_eq id arg value hav
              simp only [id_eq, ha, hm, bind_ok, ← hmv]
              cases m <;> simp [hs6, run_fatalFrom, KindRel.invalidSettingValue]

/-- Concrete Defaults modifier parser instance for `get_directive`. Both error status/span and
cursor are related to the reference, with no extra hypotheses on representable input. -/
theorem settingsModifier_parse_refines {O : Oracles} (hO : P2CharOracle O.char) :
    ParseRefines defaults.SettingsModifier.Insts.Sudo_rsSudoersBasic_parserParse
      Defaults.absModifier (settingsModifier O .release) :=
  ⟨fun _ h => modifier_parse_refines hO h⟩

theorem settingsModifier_many :
    ManyRefines defaults.SettingsModifier.Insts.Sudo_rsSudoersBasic_parserMany
      settingsModifierMany := by
  constructor
  · simp [settingsModifierMany, sudoers.basic_parser.Many.SEP.default]
  · exact ⟨_, rfl, by simp [settingsModifierMany, sudoers.basic_parser.Many.LIMIT.default]⟩

theorem settingsModifier_description :
    DescRel defaults.SettingsModifier.Insts.Sudo_rsSudoersAst_namesUserFriendly
      Descriptions.release.settingsModifier := by
  refine ⟨_, rfl, ?_⟩
  simp only [defaults.SettingsModifier.Insts.Sudo_rsSudoersAst_namesUserFriendly.DESCRIPTION]
  exact Defaults.toStr_val _ _

/-- The nonempty settings list in a `Defaults` directive, using the ordinary `Vec` parser. -/
theorem settingsModifier_vec_refines {O : Oracles} (hO : P2CharOracle O.char) :
    ParseRefines (sudo_rs.alloc.vec.Vec.Insts.Sudo_rsSudoersBasic_parserParse
      defaults.SettingsModifier.Insts.Sudo_rsSudoersBasic_parserParse
      defaults.SettingsModifier.Insts.Sudo_rsSudoersBasic_parserMany
      defaults.SettingsModifier.Insts.Sudo_rsSudoersAst_namesUserFriendly)
      (absVec Defaults.absModifier)
      (parseVec settingsModifierMany Descriptions.release.settingsModifier
        (settingsModifier O .release)) :=
  vec_refines (settingsModifier_parse_refines hO) settingsModifier_many settingsModifier_description

/-- A successful concrete parse yields a modifier produced by the reference settings DSL. -/
theorem parsed_modifier_produced {O : Oracles} (hO : P2CharOracle O.char)
    {s t : CS} (hs : StreamOK s) {m : defaults.SettingsModifier}
    (h : defaults.SettingsModifier.Insts.Sudo_rsSudoersBasic_parserParse.parse s =
      ok (.Ok m, t)) : Settings.Produced (Defaults.absModifier m) := by
  obtain ⟨r, t', he, hr, _, ha⟩ := (settingsModifier_parse_refines hO).parse s hs
  rw [h] at he
  simp only [Result.ok.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  rcases href : (settingsModifier O .release).run (absStream s) with ⟨result, stop⟩
  rw [href] at hr ha
  cases result with
  | error _ => cases hr
  | ok value =>
    have hm : Defaults.absModifier m = value := hr
    exact hm ▸ Settings.settingsModifier_produced O .release href

end SudoRsProofs.Parser
