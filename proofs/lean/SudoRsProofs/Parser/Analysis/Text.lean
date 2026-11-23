import SudoRsProofs.Parser.File
import SudoRsProofs.Parser.Analysis.Input
import SudoRsProofs.Permission
import SudoersSpec.Analysis.Clean

/-!
# Include-free text to analyzed policy

The command-line or kernel environment is not modeled here. The text argument is the actual
character slice passed by `Sudoers::read` to `analyze_text`. The oracle for formatting Rust
errors is distinct from the parser and from the file inclusion oracles.
-/

open Aeneas Aeneas.Std Result sudo_rs
open SudoersSpec
open Aeneas.Std.alloc.vec (Vec)

namespace SudoRsProofs.Parser.Analysis

/-- Bounds and absence of includes checked on the reference parse, rather than on a supplied
Rust configuration. Fatal parse records are allowed. No filename observation is needed unless
there is a diagnostic with a source path. -/
structure LocalFile (path : std.path.Path) (source : Option std.path.PathBuf) (items : List Item) : Prop where
  noIncludes : ∀ p span, .ok (.include p span) ∉ items ∧ .ok (.includeDir p span) ∉ items
  names : ∀ i ∈ items, Ref.itemFits i
  size : (items.map Ref.itemSize).sum ≤ Usize.max
  sourcePath : ∀ i ∈ items, Ref.needsDiagnosticPath i → DiagnosticPath path source

/-- Agreement of the one opaque error renderer; its input is just a diagnostic kind.
In particular this is not an agreement assumption on any parser, rule or policy. -/
def RenderAgrees : Prop := ∀ {k k'}, KindRel k k' → sudo_rs.errorKindText k = k'.render

abbrev sudoItemRefines (A : GlobAbs) (O : Syntax.Oracles) :=
  ParseRefinesOn QuoteRoom sudoers.ast.Sudo.Insts.Sudo_rsSudoersBasic_parserParse
    (absSudo A) (Syntax.sudo O .release)

private theorem sudo_description : DescRel sudoers.ast.Sudo.Insts.Sudo_rsSudoersAst_namesUserFriendly
    Syntax.Descriptions.release.sudo := by
  refine ⟨_, rfl, ?_⟩
  unfold sudoers.ast.Sudo.Insts.Sudo_rsSudoersAst_namesUserFriendly.DESCRIPTION
  exact toStr_val "nothing" _

/-- Composition at the *monomorphic* Rust entrypoint: `parse_sudoers` discards only the final
cursor from `ast::parse_sudo_lines`. The concrete production contract is a premise of this
lemma; when used as PR it must be instantiated, not assumed. -/
theorem parse_sudoers_of_item {A : GlobAbs} {O : Syntax.Oracles} (single : sudoItemRefines A O)
    (src : Slice Char) (room : 1 + 2 * src.val.length ≤ Usize.max) :
    ∃ rs items, sudoers.parse_sudoers src = ok rs ∧ Syntax.parseSudoers O src.val = .ok items ∧
      List.Forall₂ (ResultRel (absSudo A)) rs.val items := by
  obtain ⟨rs, stop, items, run, file, rel, _, _⟩ := parseSudoersWith_of_refinement single sudo_description src room
  refine ⟨rs, items, ?_, file, rel⟩
  unfold sudoers.parse_sudoers sudoers.char_stream.CharStream.from_chars sudoers.char_stream.CharStream.new_with_pos
  simp only [Std.bind_ok, sudoers.ast.parse_sudo_lines, run, uncurry_apply_pair]

/-- The remaining abstraction facts needed by the two separate proven algorithms. Neither
premise says anything about how `analyze` sorts, scopes or decides a policy. -/
theorem analyze_text_of_item {A : GlobAbs} {O : Syntax.Oracles} (single : sudoItemRefines A O)
    (render : RenderAgrees) (path : std.path.Path) (source : Option std.path.PathBuf) (src : Slice Char)
    (room : 1 + 2 * src.val.length ≤ Usize.max)
    (localFile : ∀ items, Syntax.parseSudoers O src.val = .ok items → LocalFile path source items)
    (produced : ∀ rs, sudoers.parse_sudoers src = ok rs → ∀ r ∈ rs.val, ProducedOn r) :
    ∃ items c cfg ds, Syntax.parseSudoers O src.val = .ok items ∧ SudoersSpec.Analysis.collect items = some c ∧
      sudoers.analyze_text path src = ok (cfg, ds) ∧ AnalysisResult A source c cfg ds := by
  obtain ⟨rs, items, run, file, rel⟩ := parse_sudoers_of_item single src room
  have dom := localFile items file
  have localItems : ∀ i ∈ items, SudoersSpec.Analysis.LocalItem i := by
    intro i hi
    rcases i with (⟨_, _⟩ | _) | line
    · trivial
    · exact (Syntax.parseSudoers_ne_reject O src.val items file _ hi rfl).elim
    · cases line with
      | «include» p span => exact ((dom.noIncludes p span).1 hi).elim
      | includeDir p span => exact ((dom.noIncludes p span).2 hi).elim
      | _ => trivial
  obtain ⟨c, collected⟩ := (SudoersSpec.Analysis.collectFrom_some_iff {} items).mpr localItems
  obtain ⟨cfg, ds, ran, analysis⟩ := analyze_refines_of_reference A path source rs items c rel
    collected dom.sourcePath (fun _ _ _ _ related => render related) dom.names (produced rs run) dom.size
  refine ⟨items, c, cfg, ds, file, collected, ?_, analysis⟩
  simpa only [sudoers.analyze_text, run, Std.bind_ok] using ran

/-- The actual analyzer's clean diagnostic vector, not just a clean syntax check, certifies
both the grammar derivation and the alias ordering required by expansion. -/
theorem AnalysisResult.cleanGrammar {A : GlobAbs} {source : Option std.path.PathBuf} {c cfg ds}
    (out : AnalysisResult A source c cfg ds) {O : Syntax.Oracles} {src items}
    (parse : Syntax.parseSudoers O src = .ok items) (collected : SudoersSpec.Analysis.collect items = some c)
    (clean : ds.val = []) : (SudoersSpec.Analysis.policyOf c).aliases.OK ∧
      ∃ ast : List Syntax.Sudo, items = ast.map Except.ok ∧ Syntax.Recovery.CleanFile (Grammar.SudoItemG O)
        (Syntax.Stream.new src) ast ((Syntax.Stream.new src).advance src.length) := by
  refine ⟨out.aliasesOK_of_clean clean, SudoersSpec.Analysis.cleanGrammar_of_collected
    (sanitizerReports := (SudoersSpec.Analysis.orderAliases c.written).2) parse collected ?_⟩
  rw [← out.messages, clean]; rfl

section Decision
variable {U G UG : Type} {ui : system.interface.UnixUser U UG} {eqi : core.cmp.PartialEq U U}
  {gi : system.interface.UnixGroup G} {O : Oracle U G} {A : GlobAbs}

/-- The decision on *this analyzer's output*, not an `authorize` call on a policy provided
by the caller. Valid alias indices and the remaining rule invariants come from PA. -/
theorem AnalysisResult.flags {source c cfg ds} (out : AnalysisResult A source c cfg ds)
    (hO : InstOracle ui eqi gi O) (hG : GlobOracle A O) (hostMatch : O.SudoRsHosts)
    (invoker : U) (host : system.Hostname) (hostFits : Fits host.inner) (req : sudoers.Request U G UG) :
    ∃ flags, sudoers.permission_flags ui eqi gi (Vec.deref cfg.rules) cfg.aliases invoker host req = ok flags ∧
      flags.map absTag = authorize O (SudoersSpec.Analysis.policyOf c) (absRequest A invoker host req) := by
  obtain ⟨flags, run, decision⟩ := permission_flags_eq hO hG hostMatch _ _ out.policyOK invoker host hostFits req
  exact ⟨flags, run, out.policy ▸ decision⟩

end Decision
end SudoRsProofs.Parser.Analysis
