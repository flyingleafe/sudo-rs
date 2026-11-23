import SudoRsProofs.Parser.PermissionLines.Common
import SudoRsProofs.AbsPolicy

/-! Composition of the permission tuples and the outer colon-separated list. -/

open Aeneas Aeneas.Std Result SudoersSpec
open Syntax.Parser

namespace SudoRsProofs.Parser

private abbrev D := Syntax.Descriptions.release
private abbrev raInst := sudo_rs.sudoers.ast.RunAs.Insts.Sudo_rsSudoersBasic_parserParse
private abbrev cmdInst := sudo_rs.sudoers.ast.CommandSpec.Insts.Sudo_rsSudoersBasic_parserParse
abbrev runasCommandInst := sudo_rs.PairOptionRunAsCommandSpec.Insts.Sudo_rsSudoersBasic_parserParse
private abbrev runasCommandUF := sudo_rs.PairOptionRunAsCommandSpec.Insts.Sudo_rsSudoersAst_namesUserFriendly
private abbrev runasCommandM := sudo_rs.PairOptionRunAsCommandSpec.Insts.Sudo_rsSudoersBasic_parserMany
abbrev hostsRunasCommandsInst :=
  sudo_rs.PairVecQualifiedMetaHostnameVecPairOptionRunAsCommandSpec.Insts.Sudo_rsSudoersBasic_parserParse
private abbrev hostsRunasCommandsUF :=
  sudo_rs.PairVecQualifiedMetaHostnameVecPairOptionRunAsCommandSpec.Insts.Sudo_rsSudoersAst_namesUserFriendly
private abbrev hostsRunasCommandsM :=
  sudo_rs.PairVecQualifiedMetaHostnameVecPairOptionRunAsCommandSpec.Insts.Sudo_rsSudoersBasic_parserMany

abbrev absRunasCommand (A : GlobAbs) (e : REntry) : Option RunAs × CommandSpec :=
  (e.1.map absRunAs, absCommandSpec (absCommand A) e.2)

private theorem command_spec_description :
    DescRel sudo_rs.sudoers.ast.CommandSpec.Insts.Sudo_rsSudoersAst_namesUserFriendly D.commandSpec :=
  ⟨_, rfl, by
    simp only [sudo_rs.sudoers.ast.CommandSpec.Insts.Sudo_rsSudoersAst_namesUserFriendly.DESCRIPTION,
      sudo_rs.PairPatternArgs.Insts.Sudo_rsSudoersAst_namesUserFriendly.DESCRIPTION]
    exact toStr_val _ _⟩

private theorem runas_command_description : DescRel runasCommandUF D.runasCommand :=
  ⟨_, rfl, by
    simp only [sudo_rs.PairOptionRunAsCommandSpec.Insts.Sudo_rsSudoersAst_namesUserFriendly.DESCRIPTION]
    exact toStr_val _ _⟩

private theorem hosts_runas_commands_description : DescRel hostsRunasCommandsUF D.hostsRunasCommands := by
  obtain ⟨s, es, hs⟩ := hostname_description
  refine ⟨s, ?_, hs⟩
  simpa only [sudo_rs.PairVecQualifiedMetaHostnameVecPairOptionRunAsCommandSpec.Insts.Sudo_rsSudoersAst_namesUserFriendly.DESCRIPTION]
    using es

private theorem runas_command_many : ManyRefines runasCommandM Syntax.runasCommandMany :=
  ⟨by simp [sudo_rs.sudoers.basic_parser.Many.SEP.default, Syntax.runasCommandMany],
    ⟨_, rfl, by simp [sudo_rs.sudoers.basic_parser.Many.LIMIT.default, Syntax.runasCommandMany]⟩⟩

private theorem hosts_runas_commands_many : ManyRefines hostsRunasCommandsM Syntax.hostsRunasCommandsMany :=
  ⟨by simp [sudo_rs.PairVecQualifiedMetaHostnameVecPairOptionRunAsCommandSpec.Insts.Sudo_rsSudoersBasic_parserMany.SEP,
        Syntax.hostsRunasCommandsMany],
    ⟨_, rfl, by simp [sudo_rs.sudoers.basic_parser.Many.LIMIT.default, Syntax.hostsRunasCommandsMany]⟩⟩

/-- Rust `(Option<RunAs>, CommandSpec)`; after `Some` it expects a command spec, otherwise it
tries one. Both branches preserve the final cursor even on failure. -/
theorem runas_command_refines_of_parts {A : GlobAbs} {O : Syntax.Oracles}
    (hRa : ParseRefinesOn QuoteRoom raInst absRunAs (Syntax.runAs O D))
    (hCmd : ParseRefines cmdInst (absCommandSpec (absCommand A)) (Syntax.commandSpec O D)) :
    ParseRefinesOn QuoteRoom runasCommandInst (absRunasCommand A) (Syntax.runasCommand O D) := by
  intro s hs hq
  have hOption := option_parse_refines_at (hRa s hs hq)
  obtain ⟨r, s1, e1, hr, h1, a1⟩ := try_nonterminal_refines_at hOption
  change Refines _ (sudo_rs.PairOptionRunAsCommandSpec.Insts.Sudo_rsSudoersBasic_parserParse.parse s) _
  simp only [sudo_rs.PairOptionRunAsCommandSpec.Insts.Sudo_rsSudoersBasic_parserParse.parse,
    Syntax.runasCommand, e1, bind_ok, uncurry_apply_pair, run_bind]
  rcases he : (Syntax.tryNonterminal (Syntax.parseOption (Syntax.runAs O D))).run (absStream s)
    with ⟨r', t⟩
  rw [he] at hr a1
  simp only at a1
  subst t
  rcases r with (_ | ra) | st <;> rcases r' with st' | (_ | ra') <;>
    simp only [ResultRel, Option.map_none, Option.map_some, Option.some.injEq, reduceCtorEq] at hr
  · obtain ⟨r2, s2, e2, hr2, h2, a2⟩ := try_nonterminal_refines hCmd h1
    rcases he2 : (Syntax.tryNonterminal (Syntax.commandSpec O D)).run (absStream s1) with ⟨r2', t⟩
    rw [he2] at hr2 a2
    cases r2 <;> cases r2' <;> simp_all [run_bind, absRunasCommand]
  · subst ra'
    obtain ⟨r2, s2, e2, hr2, h2, a2⟩ := expect_nonterminal_refines hCmd command_spec_description h1
    rcases he2 : (Syntax.expectNonterminal D.commandSpec (Syntax.commandSpec O D)).run (absStream s1)
      with ⟨r2', t⟩
    rw [he2] at hr2 a2
    cases r2 <;> cases r2' <;> simp_all [run_bind, absRunasCommand]
  · simp [h1, hr]

/-- Rust `(SpecList<Hostname>, Vec<(Option<RunAs>, CommandSpec)>)` is one host segment of
`PermissionSpec`. `absSeg` keeps both lists in order. -/
theorem hosts_runas_commands_refines_of_parts {A : GlobAbs} {O : Syntax.Oracles}
    (hUnicode : UnicodeOracle O.char)
    (hEntry : ParseRefinesOn QuoteRoom runasCommandInst (absRunasCommand A) (Syntax.runasCommand O D)) :
    ParseRefinesOn QuoteRoom hostsRunasCommandsInst (absSeg A) (Syntax.hostsRunasCommands O D) := by
  intro s hs hq
  have hHost := try_nonterminal_refines (spec_list_hostname_refines hUnicode D rfl) hs
  obtain ⟨r, s1, e1, hr, h1, a1⟩ := hHost
  have e1' : sudo_rs.sudoers.ast.host_list s = ok (r, s1) := e1
  have hq1 := quoteRoom_stable.after hq (Syntax.tryNonterminal (Syntax.specListHostname O.char D)) a1
  change Refines _
    (sudo_rs.PairVecQualifiedMetaHostnameVecPairOptionRunAsCommandSpec.Insts.Sudo_rsSudoersBasic_parserParse.parse s) _
  simp only [sudo_rs.PairVecQualifiedMetaHostnameVecPairOptionRunAsCommandSpec.Insts.Sudo_rsSudoersBasic_parserParse.parse,
    Syntax.hostsRunasCommands, e1', bind_ok, uncurry_apply_pair, run_bind]
  rcases he : (Syntax.tryNonterminal (Syntax.specListHostname O.char D)).run (absStream s)
    with ⟨r', t⟩
  rw [he] at hr a1
  simp only at a1
  subst t
  rcases r with hosts | st <;> rcases r' with st' | hosts' <;> simp only [ResultRel] at hr
  · obtain ⟨r2, s2, e2, hr2, h2, a2⟩ := expect_syntax_refines h1 '='
    have hq2 := quoteRoom_stable.after hq1 (Syntax.expectSyntax '=') a2
    simp only [branch_Ok, e2, bind_ok, uncurry_apply_pair]
    rcases he2 : (Syntax.expectSyntax '=').run (absStream s1) with ⟨r2', t⟩
    rw [he2] at hr2 a2
    simp only at a2
    subst t
    rcases r2 with ⟨⟩ | st <;> rcases r2' with st' | ⟨⟩ <;> simp only [ResultRel] at hr2
    · have hVec := vec_refines_on quoteRoom_stable hEntry runas_command_many runas_command_description
      obtain ⟨r3, s3, e3, hr3, h3, a3⟩ :=
        expect_nonterminal_refines_at (hVec s2 h2 hq2) (desc_vec runas_command_description)
      rcases he3 : (Syntax.expectNonterminal D.runasCommand
        (Syntax.parseVec Syntax.runasCommandMany D.runasCommand (Syntax.runasCommand O D))).run
          (absStream s2) with ⟨r3', t⟩
      rw [he3] at hr3 a3
      cases r3 <;> cases r3' <;> simp_all [absSeg, absHostList, absLine, absVec]
    · simp [hr2, h2]
  · simp [hr, h1]

/-- `permissions` is the expected, colon-separated sequence of host segments. -/
theorem permissions_refines_of_segments {A : GlobAbs} {O : Syntax.Oracles}
    (hEntry : ParseRefinesOn QuoteRoom hostsRunasCommandsInst (absSeg A) (Syntax.hostsRunasCommands O D))
    {s : CS} (hs : StreamOK s) (hq : QuoteRoom (absStream s)) :
    Refines (absVec (absSeg A)) (sudo_rs.sudoers.ast.permissions s)
      ((Syntax.expectNonterminal D.hostsRunasCommands (Syntax.permissions O D)).run (absStream s)) :=
  expect_nonterminal_refines_at
    (vec_refines_on quoteRoom_stable hEntry hosts_runas_commands_many hosts_runas_commands_description s hs hq)
    (desc_vec hosts_runas_commands_description)

end SudoRsProofs.Parser
