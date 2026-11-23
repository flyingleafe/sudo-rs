import SudoRsProofs.Parser.Analysis.Input
import SudoRsProofs.Parser.Analysis.Provenance.Modifier
import SudoRsProofs.Parser.Analysis.Provenance.Accum

/-!
# Defaults provenance of the extracted sudoers parser

A successful outer Rust-model result carries only modifiers actually returned by the
settings constructors. This is a one-way property of the extraction: it does not assert
termination, equivalence to the reference parser, or agreement of any external oracle.
-/

open Aeneas Aeneas.Std Result
open Aeneas.Std.alloc.vec (Vec)
open sudo_rs sudo_rs.sudoers

namespace SudoRsProofs.Parser.Analysis

private def DirectiveProduced : ast.Directive → Prop
  | .Defaults mods _ => AllOn Defaults.Produced mods
  | _ => True

private def SudoProduced : ast.Sudo → Prop
  | .Decl d => DirectiveProduced d
  | _ => True

private theorem producedOn_iff (r : RItem) : ProducedOn r ↔ OkOn SudoProduced r := by
  rcases r with (_ | d | _ | _ | _) | _ <;> try rfl
  cases d <;> rfl

private abbrev modP := defaults.SettingsModifier.Insts.Sudo_rsSudoersBasic_parserParse
private abbrev modM := defaults.SettingsModifier.Insts.Sudo_rsSudoersBasic_parserMany
private abbrev modUF := defaults.SettingsModifier.Insts.Sudo_rsSudoersAst_namesUserFriendly
private abbrev modsP := sudo_rs.alloc.vec.Vec.Insts.Sudo_rsSudoersBasic_parserParse modP modM modUF
private abbrev modsUF := sudo_rs.alloc.vec.Vec.Insts.Sudo_rsSudoersAst_namesUserFriendly modUF

private theorem settings_modifiers_on_return (s : CS) :
    OnReturn (basic_parser.expect_nonterminal modsP modsUF s)
      (fun out => OkOn (AllOn Defaults.Produced) out.1) :=
  expect_nonterminal_on_return (vec_parse_on_return settings_modifier_on_return) s

-- A token/production followed by the generated Rust `?`.
local macro "take_parsed " x:ident t:ident h:ident : tactic =>
  `(tactic| (
    apply on_return_bind_pair
    intro raw $t $h
    rcases raw with $x | err <;>
      simp only [uncurry_apply_pair, branch_Ok, branch_Err, from_residual_Err, bind_ok]
    all_goals try exact OnReturn.pure True.intro))

local macro "take_test" b:ident : tactic => do
  let test : Lean.TSyntax `term := ⟨b.raw⟩
  `(tactic| (
    apply OnReturn.bind
    intro $b _
    cases ($test:term) <;> simp only [Bool.false_eq_true, ↓reduceIte]))

local macro "return_without_defaults" : tactic =>
  `(tactic| (
    simp only [make_eq, reject_eq, fatal_from_eq, bind_ok]
    exact OnReturn.pure True.intro))

private theorem get_directive_on_return (key : RSpec ast.UserSpecifier) (s start : CS) :
    OnReturn (ast.get_directive key s start) (fun out => OkOn DirectiveProduced out.1) := by
  rcases key with (_ | ((_ | _) | _ | _) | _) | _ <;> unfold ast.get_directive
  all_goals try return_without_defaults
  provenance_bind keyword _hKeyword
  provenance_bind pos _hPos
  take_test isUser
  case true =>
    take_parsed defs s1 _hDefs
    return_without_defaults
  case false =>
    take_test isHost
    case true =>
      take_parsed defs s1 _hDefs
      return_without_defaults
    case false =>
      take_test isCmnd
      case true =>
        take_parsed defs s1 _hDefs
        return_without_defaults
      case false =>
        take_test isCmd
        case true =>
          take_parsed defs s1 _hDefs
          return_without_defaults
        case false =>
          take_test isRunas
          case true =>
            take_parsed defs s1 _hDefs
            return_without_defaults
          case false =>
            take_test isDefaults
            case false => return_without_defaults
            case true =>
              take_parsed scope s1 _hScope
              take_parsed mods s2 hMods
              simp only [make_eq, bind_ok]
              exact OnReturn.pure (settings_modifiers_on_return s1 _ hMods)

private theorem parse_include_on_return (s : CS) :
    OnReturn (ast.parse_include s) (fun out => OkOn SudoProduced out.1) := by
  unfold ast.parse_include
  provenance_bind pos _hPos
  take_parsed key s1 _hKey
  cases key with
  | none => return_without_defaults
  | some key =>
    provenance_bind keyword _hKeyword
    take_test isInclude
    case true =>
      take_parsed pathSpan s2 _hPath
      rcases pathSpan with ⟨path, span⟩
      return_without_defaults
    case false =>
      take_test isDir
      case true =>
        take_parsed pathSpan s2 _hPath
        rcases pathSpan with ⟨path, span⟩
        return_without_defaults
      case false =>
        unfold ast.parse_remote
        return_without_defaults

/-- Invert the optional Rust result without unfolding the production that computed it. -/
local macro "take_inner " r:ident h:ident : tactic =>
  `(tactic| (
    apply OnReturn.bind
    intro raw $h
    rcases raw with $r | err <;>
      simp only [branch_Ok, branch_Err, from_residual_Err, bind_ok]
    all_goals try exact OnReturn.pure True.intro))

private theorem maybe_directive_produced {s t start : CS} {key : RSpec ast.UserSpecifier}
    {r : RParsed ast.Directive} {d : ast.Directive}
    (hGet : ast.get_directive key s start = ok (r, t))
    (hMaybe : basic_parser.maybe r = ok (.Ok (some d))) : DirectiveProduced d := by
  rcases r with d' | (_ | _) <;>
    simp only [maybe_Ok, maybe_Fatal, maybe_Reject, ok.injEq, core.result.Result.Ok.injEq,
      Option.some.injEq, reduceCtorEq] at hMaybe
  subst d'
  exact get_directive_on_return key s start _ hGet

private theorem sudo_on_return (s : CS) :
    OnReturn (ast.Sudo.Insts.Sudo_rsSudoersBasic_parserParse.parse s)
      (fun out => OkOn SudoProduced out.1) := by
  unfold ast.Sudo.Insts.Sudo_rsSudoersBasic_parserParse.parse
  provenance_bind ⟨atSign, s1⟩ _hAt
  simp only [uncurry_apply_pair]
  cases atSign <;> simp only [Bool.false_eq_true, ↓reduceIte]
  case true => exact parse_include_on_return s1
  case false =>
    provenance_bind next _hNext
    take_test isHash
    case true =>
      provenance_bind ⟨ident, s2⟩ _hIdent
      simp only [uncurry_apply_pair]
      cases ident with
      | Ok ident =>
        take_parsed comma s3 _hComma
        cases comma <;> simp only [Bool.false_eq_true, ↓reduceIte]
        case true =>
          take_parsed users s4 _hUsers
          provenance_bind users' _hInsert
          take_parsed perms s5 _hPerms
          return_without_defaults
        case false =>
          provenance_bind users _hUsers
          take_parsed perms s5 _hPerms
          return_without_defaults
      | Err e =>
        provenance_bind ⟨item, s3⟩ hInclude
        simp only [uncurry_apply_pair]
        cases item with
        | Ok i =>
          simp only [make_eq, bind_ok]
          exact OnReturn.pure (parse_include_on_return s2 _ hInclude)
        | Err e =>
          provenance_bind s4 _hSkip
          return_without_defaults
    case false =>
      provenance_bind start _hClone
      take_test isQuote
      case true =>
        take_parsed users s2 _hUsers
        take_parsed perms s3 _hPerms
        return_without_defaults
      case false =>
        provenance_bind ⟨users, s2⟩ _hUsers
        simp only [uncurry_apply_pair]
        take_inner usersOpt _hOpt
        cases usersOpt with
        | none => return_without_defaults
        | some users =>
          provenance_bind key _hKey
          provenance_bind pos _hPos
          provenance_bind ⟨directive, s3⟩ hDirective
          simp only [uncurry_apply_pair]
          take_inner directiveOpt hOpt
          cases directiveOpt with
          | none =>
            take_parsed perms s4 _hPerms
            return_without_defaults
          | some directive =>
            have hd := maybe_directive_produced hDirective hOpt
            simp only [make_eq, bind_ok]
            by_cases hMany : (alloc.vec.Vec.len users != 1#usize) = true
            · simp only [hMany, ↓reduceIte]
              take_test ambiguous
              case true => return_without_defaults
              case false => exact OnReturn.pure hd
            · simp only [hMany, ↓reduceIte]
              exact OnReturn.pure hd

/-- Each returned parser item satisfies raw modifier provenance. No assumptions about size,
termination, the environment, or relation to a reference parse are needed. -/
theorem parse_sudoers_produced {src : Slice Char} {rs : Vec RItem}
    (h : sudoers.parse_sudoers src = ok rs) : ∀ r ∈ rs.val, ProducedOn r := by
  have hs : OnReturn (sudoers.parse_sudoers src) (AllOn (OkOn SudoProduced)) := by
    unfold sudoers.parse_sudoers
    provenance_bind s hFrom
    provenance_bind ⟨items, s'⟩ hLines
    exact OnReturn.pure (parse_lines_on_return sudo_on_return s _ hLines)
  exact fun r hr => (producedOn_iff r).mpr (hs rs h r hr)

end SudoRsProofs.Parser.Analysis
