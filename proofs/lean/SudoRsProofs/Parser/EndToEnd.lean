import SudoRsProofs.Parser.Analysis.Text
import SudoRsProofs.Parser.Analysis.Provenance
import SudoRsProofs.Parser.Scoping.Check
import SudoRsProofs.Defaults.Observations
import SudoRsProofs.Parser.Directives.Main
import SudoersSpec.Grammar.SudoUnique

/-! Composition for the stable, include-free text path. The witnesses are the actual outputs
of `analyze_text`, `check` and `Judgement::authorization`. A `Forbidden` judgement is an
ordinary successful Rust return, not a parser error, missing model result, or failed operation. -/

open Aeneas Aeneas.Std Result sudo_rs
open Aeneas.Std.alloc.vec (Vec)
open SudoersSpec

namespace SudoRsProofs.Parser

/-- Witnesses in execution order, including the policy state *after* both Defaults passes. -/
structure FileRun where
  items : List Analysis.Item
  collected : SudoersSpec.Analysis.Collected
  cfg : sudoers.Sudoers
  diagnostics : Vec sudoers.Error
  judgement : sudoers.Judgement
  next : sudoers.Sudoers
  terms : sudoers.policy.Authorization sudoers.policy.Restrictions

variable {U G UG : Type}

/-- The trace of the real functions and the observations that agree with the independent
reference functions. Every policy in a conclusion is built from the parsed file. -/
structure TextAgreement (A : GlobAbs) (E : Syntax.Oracles) (O : Oracle U G)
    (ui : system.interface.UnixUser U UG) (eqi : core.cmp.PartialEq U U)
    (gi : system.interface.UnixGroup G) (path : std.path.Path) (source : Option std.path.PathBuf)
    (src : Slice Char) (invoker : U) (host : system.Hostname) (req : sudoers.Request U G UG)
    (x : FileRun) : Prop where
  parsed : Syntax.parseSudoers E src.val = .ok x.items
  collected : SudoersSpec.Analysis.collect x.items = some x.collected
  analyze : sudoers.analyze_text path src = ok (x.cfg, x.diagnostics)
  policy : Analysis.AnalysisResult A source x.collected x.cfg x.diagnostics
  check : sudoers.Sudoers.check ui eqi gi x.cfg invoker host req = ok (x.judgement, x.next)
  authorization : sudoers.policy.Judgement.authorization x.judgement = ok x.terms
  flags : x.judgement.flags.map absTag = authorize O (SudoersSpec.Analysis.policyOf x.collected)
    (absRequest A invoker host req)
  effective : Settings.Equiv (Defaults.absSettings x.judgement.settings)
    (SudoersSpec.Analysis.settingsInForce O (SudoersSpec.Analysis.policyOf x.collected).aliases x.collected
      (absRequest A invoker host req) Settings.Settings.default)
  result : (SudoersSpec.Analysis.authorizationOfText E O src.val (absRequest A invoker host req)).map
    Settings.observeAuthorization = some (Settings.observeAuthorization (absAuthorization x.terms))
  denied : x.terms = .Forbidden ↔ authorize O (SudoersSpec.Analysis.policyOf x.collected)
    (absRequest A invoker host req) = none
  consumed : x.next.rules = x.cfg.rules ∧ x.next.aliases = x.cfg.aliases ∧
    x.next.customisers.non_cmnd.val = [] ∧ x.next.customisers.cmnd.val = []

private theorem pass_domains {ct : sudoers.CustomiserTable} (h : Analysis.CustomisersOK ct) :
    Scoping.NonCommandEntriesOK ct.non_cmnd.val ∧ Scoping.CommandEntriesOK ct.cmnd.val := by
  refine ⟨⟨h.nonCommandOnly, ?_, fun e he => (h.nonCommand e he).2⟩,
    ⟨fun e he => (h.command e he).1, fun e he => (h.command e he).2⟩⟩
  intro e he
  have hf := (h.nonCommand e he).1
  cases hscope : e.1 <;> simp_all [Scoping.NonCommandScopeFits, Analysis.ScopeFits]

private theorem initially_in_range {s : defaults.Settings} (h : Defaults.absSettings s = Defaults.initialModel) :
    SettingsInRange s := by
  have hp : s.passwd_tries.val = 3 := congrArg Settings.Settings.passwd_tries h
  have hu : s.umask.val = 18 := congrArg Settings.Settings.umask h
  constructor
  · rw [hp, U16.max_eq]; decide
  · rw [hu, U32.max_eq]; decide

/-- **Text to authorization, including Defaults.** The concrete item parser, analyzer,
both scope passes, decision and `Judgement::authorization` return the matching result.
There is no assumed parser agreement, `PolicyOK`, modifier provenance or in-range judgement.
`localFile` records the include-free and representation domain on the reference items. -/
theorem text_to_authorization {A : GlobAbs} {E : Syntax.Oracles} {O : Oracle U G}
    {ui : system.interface.UnixUser U UG} {eqi : core.cmp.PartialEq U U} {gi : system.interface.UnixGroup G}
    (parserEnv : P2Oracle A E) (render : Analysis.RenderAgrees)
    (hO : InstOracle ui eqi gi O) (hG : GlobOracle A O) (hostMatch : O.SudoRsHosts)
    (path : std.path.Path) (source : Option std.path.PathBuf) (src : Slice Char)
    (room : 1 + 2 * src.val.length ≤ Usize.max)
    (localFile : ∀ items, Syntax.parseSudoers E src.val = .ok items → Analysis.LocalFile path source items)
    (invoker : U) (host : system.Hostname) (hostFits : Fits host.inner) (req : sudoers.Request U G UG) :
    ∃ x, TextAgreement A E O ui eqi gi path source src invoker host req x := by
  obtain ⟨items, c, cfg, ds, parsed, collected, entered, policy⟩ :=
    Analysis.analyze_text_of_item (sudo_refines parserEnv) render path source src room localFile
      (fun _ => Analysis.parse_sudoers_produced)
  obtain ⟨hn, hc⟩ := pass_domains policy.customisersOK
  obtain ⟨j, next, checked, hsettings, hflags, range, rules, aliases, nc, cc, _⟩ :=
    Scoping.check_eq hO hG hostMatch cfg invoker host req c policy.policyOK hostFits
      policy.nonCommand.symm policy.command.symm hn hc (initially_in_range policy.settings)
  have htab : absAliasTable A cfg.aliases = (SudoersSpec.Analysis.policyOf c).aliases :=
    congrArg Policy.aliases policy.policy
  rw [htab, policy.settings] at hsettings
  rw [policy.policy] at hflags
  have eff := Defaults.initialModel_equiv.settingsInForce O (SudoersSpec.Analysis.policyOf c).aliases c
    (absRequest A invoker host req)
  rw [← hsettings] at eff
  obtain ⟨terms, ran, hterms⟩ := authorization_eq j range
  rw [Defaults.absDefaults_eq, hflags] at hterms
  let x : FileRun := ⟨items, c, cfg, ds, j, next, terms⟩
  refine ⟨x, ⟨parsed, collected, entered, policy, checked, ran, hflags, eff, ?_, ?_, rules, aliases, nc, cc⟩⟩
  · dsimp only [x]
    rw [hterms, Settings.authorization_congr eff]
    simp [SudoersSpec.Analysis.authorizationOfText, parsed, Except.toOption, collected]
  · dsimp only [x]
    rw [← absAuthorization_eq_forbidden_iff, hterms]
    exact authorization_eq_forbidden_iff _ _

variable {A : GlobAbs} {E : Syntax.Oracles} {O : Oracle U G}
  {ui : system.interface.UnixUser U UG} {eqi : core.cmp.PartialEq U U} {gi : system.interface.UnixGroup G}
  {path : std.path.Path} {source : Option std.path.PathBuf} {src : Slice Char}
  {invoker : U} {host : system.Hostname} {req : sudoers.Request U G UG} {x : FileRun}

/-- **E2E-clean.** The *real analyzer* reported no diagnostic. The exact grammar assigns
one sequence of ASTs and one end position to the file; all aliases are in valid order.
Neither an assertion about what `read` should have returned nor parser cleanliness is a premise. -/
theorem TextAgreement.clean_unique (h : TextAgreement A E O ui eqi gi path source src invoker host req x)
    (clean : x.diagnostics.val = []) :
    (SudoersSpec.Analysis.policyOf x.collected).aliases.OK ∧
    ∃ ast : List Syntax.Sudo, x.items = ast.map Except.ok ∧
      Syntax.Recovery.CleanFile (Grammar.ExactSudoItemG E) (Syntax.Stream.new src.val) ast
        ((Syntax.Stream.new src.val).advance src.val.length) ∧
      ∀ other stop, Syntax.Recovery.CleanFile (Grammar.ExactSudoItemG E) (Syntax.Stream.new src.val) other stop →
        other = ast ∧ stop = (Syntax.Stream.new src.val).advance src.val.length := by
  obtain ⟨aliases, ast, items, _⟩ := h.policy.cleanGrammar h.parsed h.collected clean
  have cert := (Grammar.parseSudoersWith_exact_iff .release E src.val ast).mp (items ▸ h.parsed)
  exact ⟨aliases, ast, items, cert, fun _ _ hother => Grammar.exactSudo_cleanFile_unique E hother cert⟩

/-- Flattening the entire clean policy preserves exact tags under the two conditions of
`authorize_expandAliases`. In particular, an empty diagnostic list does not by itself
justify changing command-alias `SETENV` semantics. -/
theorem TextAgreement.clean_expanded_flags (h : TextAgreement A E O ui eqi gi path source src invoker host req x)
    (clean : x.diagnostics.val = []) (kept : (SudoersSpec.Analysis.policyOf x.collected).RunasUsersKept)
    (noAll : CmndAliasesNoAll (SudoersSpec.Analysis.policyOf x.collected).aliases.cmnd) :
    x.judgement.flags.map absTag = authorize O (SudoersSpec.Analysis.policyOf x.collected).expandAliases
      (absRequest A invoker host req) := by
  rw [authorize_expandAliases O _ (h.policy.aliasesOK_of_clean clean) kept noAll]
  exact h.flags

end SudoRsProofs.Parser
