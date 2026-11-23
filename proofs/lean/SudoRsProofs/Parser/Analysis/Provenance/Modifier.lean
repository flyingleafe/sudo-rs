import SudoRsProofs.Parser.Analysis.Provenance.Common

open Aeneas Aeneas.Std Result
open sudo_rs sudo_rs.sudoers

namespace SudoRsProofs.Parser.Analysis

-- Invert a parser call followed by Rust's `?`. Only the inner `Ok` can produce a modifier.
local macro "modifier_step " value:ident stream:ident : tactic =>
  `(tactic| (
    apply on_return_bind_pair
    intro r $stream _
    rcases r with $value | e <;>
      simp only [uncurry_apply_pair, branch_Ok, branch_Err, from_residual_Err, bind_ok]
    all_goals try exact OnReturn.pure True.intro))

local macro "modifier_fatal" : tactic =>
  `(tactic| (
    simp only [fatal_here_eq, fatal_from_eq, bind_ok]
    exact OnReturn.pure True.intro))

local macro "modifier_make " produced:term : tactic =>
  `(tactic| (
    simp only [make_eq, bind_ok]
    exact OnReturn.pure $produced))

private theorem parse_defaults_list_on_return (mode : defaults.ListMode) (nm : String)
    (cfg : defaults.SettingKind) (pos : Usize × Usize) (s : CS) :
    OnReturn (ast.parse_defaults_list mode nm cfg pos s)
      (fun out => OkOn Defaults.Produced out.1) := by
  unfold ast.parse_defaults_list
  modifier_step eqToken s1
  cases cfg with
  | Flag _ | Integer _ | Text _ => modifier_fatal
  | List setting =>
    modifier_step values s2
    provenance_bind m hbuild
    modifier_make (Defaults.Produced.list hbuild)

/-- Every accepted Defaults modifier comes from a successful call to its extracted producer. -/
theorem settings_modifier_on_return (s : CS) :
    OnReturn (sudo_rs.defaults.SettingsModifier.Insts.Sudo_rsSudoersBasic_parserParse.parse s)
      (fun out => OkOn Defaults.Produced out.1) := by
  unfold defaults.SettingsModifier.Insts.Sudo_rsSudoersBasic_parserParse.parse
  apply OnReturn.bind
  intro idPos _
  modifier_step negated s1
  cases negated <;> simp only [Bool.false_eq_true, ↓reduceIte]
  case true =>
    apply OnReturn.bind
    intro valuePos _
    modifier_step nm s2
    provenance_bind text htext
    provenance_bind found hnegate
    cases found with
    | none =>
      provenance_bind cfg hset
      cases cfg <;>
        simp only [core.option.Option.is_some, Option.isSome_none, Option.isSome_some,
          Bool.false_eq_true, ↓reduceIte] <;> modifier_fatal
    | some m => modifier_make (Defaults.Produced.negate hnegate)
  case false =>
    modifier_step nm s2
    provenance_bind text htext
    provenance_bind found hset
    cases found with
    | none => modifier_fatal
    | some cfg =>
      modifier_step adding s3
      cases adding <;> simp only [Bool.false_eq_true, ↓reduceIte]
      case true => exact parse_defaults_list_on_return .Add nm cfg idPos s3
      case false =>
        modifier_step deleting s4
        cases deleting <;> simp only [Bool.false_eq_true, ↓reduceIte]
        case true => exact parse_defaults_list_on_return .Del nm cfg idPos s4
        case false =>
          modifier_step assigning s5
          cases assigning <;> simp only [Bool.false_eq_true, ↓reduceIte]
          case false =>
            cases cfg with
            | Flag m => modifier_make (Defaults.Produced.flag hset)
            | Integer _ | Text _ | List _ => modifier_fatal
          case true =>
            apply OnReturn.bind
            intro valuePos _
            cases cfg with
            | Flag _ => modifier_fatal
            | Integer setting =>
              modifier_step value s6
              provenance_bind spelling hspelling
              provenance_bind checked hcheck
              cases checked with
              | none => modifier_fatal
              | some m => modifier_make (Defaults.Produced.integer hcheck)
            | Text setting =>
              modifier_step value s6
              provenance_bind spelling hspelling
              provenance_bind checked hcheck
              cases checked with
              | none => modifier_fatal
              | some m => modifier_make (Defaults.Produced.text hcheck)
            | List setting =>
              modifier_step values s6
              provenance_bind m hbuild
              modifier_make (Defaults.Produced.list hbuild)

end SudoRsProofs.Parser.Analysis
