import SudoRsProofs.Parser.Ast
import SudoRsProofs.Parser.Analysis.AliasOrder
import SudoRsProofs.Parser.Analysis.Abs
import SudoRsProofs.Defaults.Range
import SudoRsProofs.Expansion

/-! Refinement of the extracted analysis on local, non-`Reject` items. -/

open Aeneas Aeneas.Std Result
open Aeneas.Std.alloc.vec (Vec)
open sudo_rs sudo_rs.sudoers

namespace SudoRsProofs.Parser.Analysis

private def ignoredMessage : String := "this tag is ignored by sudo-rs"

/-- A file with no local diagnostics need not provide even a `PathBuf` witness. -/
def DiagnosticPath (path : std.path.Path) (source : Option std.path.PathBuf) : Prop :=
  ∃ owned, source = some owned ∧ std.path.Path.to_path_buf path = ok owned

private def rawReport (source : Option std.path.PathBuf) (span : basic_parser.Span)
    (message : String) : sudoers.Error := ⟨source, some span, message⟩

private def ignoredModifier : ast.Modifier → Option basic_parser.Span
  | .Ignored s => some s
  | _ => none

private def ignoredEntry (e : REntry) : List basic_parser.Span :=
  (csMods e.2).filterMap ignoredModifier

private def ignoredSegment (seg : RSeg) : List basic_parser.Span :=
  seg.2.val.flatMap ignoredEntry

/-- The spans in host group, command and modifier order, on the extracted AST. -/
def rawIgnored (rule : ast.PermissionSpec) : List basic_parser.Span :=
  rule.permissions.val.flatMap ignoredSegment

private theorem ignoredMessage_ok :
    alloc.string.String.Insts.CoreConvertFromShared0Str.from (toStr "this tag is ignored by sudo-rs") =
      ok ignoredMessage := by
  simp only [alloc.string.String.Insts.CoreConvertFromShared0Str.from, sudo_rs.stringOfStr,
    toStr_val, Result.ok.injEq]
  have bytes : (⟨(sudo_rs.stringBytes ignoredMessage).map (fun b => UInt8.ofNat b.val)
      |>.toArray⟩ : ByteArray) = ignoredMessage.toByteArray := by decide
  rw [← show ignoredMessage = "this tag is ignored by sudo-rs" from rfl, bytes]
  exact String.fromUTF8Lossy_toByteArray

private theorem report_spec (path : std.path.Path) (source : Option std.path.PathBuf)
    (span : basic_parser.Span) (message : String) (ds : Vec sudoers.Error)
    (hp : DiagnosticPath path source) (hb : ds.val.length < Usize.max) :
    sudoers.report ds path span message ⦃ out => out.val = ds.val ++ [rawReport source span message] ⦄ := by
  obtain ⟨owned, rfl, hp⟩ := hp
  unfold sudoers.report
  rw [hp]
  simp only [Std.bind_ok]
  exact Vec.push_spec ds _ hb

private def ignoredReports (source : Option std.path.PathBuf) (spans : List basic_parser.Span) :
    List sudoers.Error := spans.map fun s => rawReport source s ignoredMessage

private theorem ignored_one_spec (path : std.path.Path) (source : Option std.path.PathBuf)
    (ds : Vec sudoers.Error) (m : ast.Modifier)
    (hp : ∀ s, ignoredModifier m = some s → DiagnosticPath path source)
    (hb : ds.val.length + (ignoredModifier m).toList.length ≤ Usize.max) :
    (match m with
      | .Passwd => ok ds
      | .Nopasswd => ok ds
      | .Setenv => ok ds
      | .Nosetenv => ok ds
      | .Exec => ok ds
      | .Noexec => ok ds
      | .Cwd _ => ok ds
      | .AppArmorProfile _ => ok ds
      | .Ignored span => do
          let message ← alloc.string.String.Insts.CoreConvertFromShared0Str.from
            (toStr "this tag is ignored by sudo-rs")
          sudoers.report ds path span message
      | .NoOp => ok ds)
      ⦃ out => out.val = ds.val ++ ignoredReports source (ignoredModifier m).toList ⦄ := by
  cases m <;> simp only [ignoredModifier, Option.toList, ignoredReports, List.map_nil,
    List.append_nil, WP.spec_ok, ignoredMessage_ok, Std.bind_ok, List.map_cons]
  rename_i span
  exact report_spec path source span ignoredMessage ds (hp span rfl) (by simpa [ignoredModifier] using hb)

private theorem ignored_modifiers_loop_spec (path : std.path.Path) (source : Option std.path.PathBuf)
    (mods : Slice ast.Modifier) (ds : Vec sudoers.Error) (i : Usize)
    (hp : (mods.val.drop i.val).filterMap ignoredModifier ≠ [] →
      DiagnosticPath path source)
    (hb : ds.val.length + ((mods.val.drop i.val).filterMap ignoredModifier).length ≤ Usize.max) :
    sudoers.ignored_modifiers_loop path mods ds i ⦃ out => out.val = ds.val ++
      ignoredReports source ((mods.val.drop i.val).filterMap ignoredModifier) ⦄ := by
  unfold sudoers.ignored_modifiers_loop
  dsimp only
  split
  · have hlt : i.val < mods.val.length := by scalar_tac
    have hdrop := List.drop_eq_getElem_cons hlt
    step as ⟨m, hm⟩
    have hsplit : (mods.val.drop i.val).filterMap ignoredModifier =
        (ignoredModifier m).toList ++ (mods.val.drop (i.val + 1)).filterMap ignoredModifier := by
      rw [hdrop, ← hm]; cases h : ignoredModifier m <;> simp [h]
    have hpath : ∀ s, ignoredModifier m = some s → DiagnosticPath path source := by
      intro s hs; apply hp; simp [hsplit, hs]
    rw [hsplit, List.length_append] at hb
    have one := ignored_one_spec path source ds m hpath (by omega)
    apply WP.spec_bind one
    intro ds' hds'
    apply WP.spec_bind (Usize.add_spec (by scalar_tac))
    intro i' hi'
    change i'.val = i.val + 1 at hi'
    have hlen := congrArg List.length hds'
    simp only [List.length_append, ignoredReports, List.length_map] at hlen
    have hpath' : (mods.val.drop i'.val).filterMap ignoredModifier ≠ [] →
        DiagnosticPath path source := by
      intro hn; apply hp; rw [hsplit]; intro h
      apply hn; rw [hi']; exact (List.append_eq_nil_iff.mp h).2
    have hb' : ds'.val.length + ((mods.val.drop i'.val).filterMap ignoredModifier).length ≤
        Usize.max := by rw [hi']; omega
    step with ignored_modifiers_loop_spec path source mods ds' i' hpath' hb' as ⟨out, hout⟩
    simp only [hout, hds', hsplit, hi', ignoredReports, List.map_append, List.append_assoc]
  · have hle : mods.val.length ≤ i.val := by scalar_tac
    simp [List.drop_eq_nil_of_le hle, ignoredReports]
termination_by mods.val.length - i.val
decreasing_by omega

private theorem ignored_entries_loop_spec (path : std.path.Path) (source : Option std.path.PathBuf)
    (ds : Vec sudoers.Error) (entries : Vec REntry) (i : Usize)
    (hp : ((entries.val.drop i.val).flatMap ignoredEntry) ≠ [] →
      DiagnosticPath path source)
    (hb : ds.val.length + ((entries.val.drop i.val).flatMap ignoredEntry).length ≤ Usize.max) :
    sudoers.ignored_tags_loop0_loop0 path ds entries i ⦃ out => out.val = ds.val ++
      ignoredReports source ((entries.val.drop i.val).flatMap ignoredEntry) ⦄ := by
  unfold sudoers.ignored_tags_loop0_loop0
  dsimp only
  split
  · have hlt : i.val < entries.val.length := by scalar_tac
    have hdrop := List.drop_eq_getElem_cons hlt
    simp only [Vec.index_slice_index]
    apply WP.spec_bind (Vec.index_usize_spec entries i hlt)
    rintro ⟨ra, ⟨mods, command⟩⟩ he
    simp only [uncurry]
    have hsplit : (entries.val.drop i.val).flatMap ignoredEntry =
        mods.val.filterMap ignoredModifier ++ (entries.val.drop (i.val + 1)).flatMap ignoredEntry := by
      rw [hdrop, ← he]; rfl
    rw [hsplit, List.length_append] at hb
    have hpath : mods.val.filterMap ignoredModifier ≠ [] → DiagnosticPath path source := by
      intro hn; apply hp; simp [hsplit, hn]
    have one := ignored_modifiers_loop_spec path source (Vec.deref mods) ds 0#usize
      (by simpa using hpath) (by simpa using (show ds.val.length +
        (mods.val.filterMap ignoredModifier).length ≤ Usize.max by omega))
    step with one as ⟨ds', hds'⟩
    simp only [List.drop_zero, Vec.deref_val] at hds'
    apply WP.spec_bind (Usize.add_spec (by scalar_tac))
    intro i' hi'
    change i'.val = i.val + 1 at hi'
    have hlen := congrArg List.length hds'
    simp only [List.length_append, ignoredReports, List.length_map] at hlen
    have hpath' : (entries.val.drop i'.val).flatMap ignoredEntry ≠ [] →
        DiagnosticPath path source := by
      intro hn; apply hp; rw [hsplit]; intro h
      apply hn; rw [hi']; exact (List.append_eq_nil_iff.mp h).2
    have hb' : ds'.val.length + ((entries.val.drop i'.val).flatMap ignoredEntry).length ≤
        Usize.max := by rw [hi']; omega
    step with ignored_entries_loop_spec path source ds' entries i' hpath' hb' as ⟨out, hout⟩
    simp only [hout, hds', hsplit, hi', ignoredReports, List.map_append, List.append_assoc]
  · have hle : entries.val.length ≤ i.val := by scalar_tac
    simp [List.drop_eq_nil_of_le hle, ignoredReports]
termination_by entries.val.length - i.val
decreasing_by omega

private theorem ignored_segments_loop_spec (path : std.path.Path) (source : Option std.path.PathBuf)
    (ds : Vec sudoers.Error) (segments : Vec RSeg) (i : Usize)
    (hp : ((segments.val.drop i.val).flatMap ignoredSegment) ≠ [] →
      DiagnosticPath path source)
    (hb : ds.val.length + ((segments.val.drop i.val).flatMap ignoredSegment).length ≤ Usize.max) :
    sudoers.ignored_tags_loop0 path ds segments i ⦃ out => out.val = ds.val ++
      ignoredReports source ((segments.val.drop i.val).flatMap ignoredSegment) ⦄ := by
  unfold sudoers.ignored_tags_loop0
  dsimp only
  split
  · have hlt : i.val < segments.val.length := by scalar_tac
    have hdrop := List.drop_eq_getElem_cons hlt
    simp only [Vec.index_slice_index]
    apply WP.spec_bind (Vec.index_usize_spec segments i hlt)
    rintro ⟨hosts, entries⟩ he
    simp only [uncurry]
    have hsplit : (segments.val.drop i.val).flatMap ignoredSegment =
        entries.val.flatMap ignoredEntry ++ (segments.val.drop (i.val + 1)).flatMap ignoredSegment := by
      rw [hdrop, ← he]; rfl
    rw [hsplit, List.length_append] at hb
    have hpath : entries.val.flatMap ignoredEntry ≠ [] → DiagnosticPath path source := by
      intro hn; apply hp; simp [hsplit, hn]
    have one := ignored_entries_loop_spec path source ds entries 0#usize
      (by simpa using hpath) (by simpa using (show ds.val.length +
        (entries.val.flatMap ignoredEntry).length ≤ Usize.max by omega))
    step with one as ⟨ds', hds'⟩
    simp only [List.drop_zero] at hds'
    apply WP.spec_bind (Usize.add_spec (by scalar_tac))
    intro i' hi'
    change i'.val = i.val + 1 at hi'
    have hlen := congrArg List.length hds'
    simp only [List.length_append, ignoredReports, List.length_map] at hlen
    have hpath' : (segments.val.drop i'.val).flatMap ignoredSegment ≠ [] →
        DiagnosticPath path source := by
      intro hn; apply hp; rw [hsplit]; intro h
      apply hn; rw [hi']; exact (List.append_eq_nil_iff.mp h).2
    have hb' : ds'.val.length + ((segments.val.drop i'.val).flatMap ignoredSegment).length ≤
        Usize.max := by rw [hi']; omega
    step with ignored_segments_loop_spec path source ds' segments i' hpath' hb' as ⟨out, hout⟩
    simp only [hout, hds', hsplit, hi', ignoredReports, List.map_append, List.append_assoc]
  · have hle : segments.val.length ≤ i.val := by scalar_tac
    simp [List.drop_eq_nil_of_le hle, ignoredReports]
termination_by segments.val.length - i.val
decreasing_by omega

private theorem ignored_tags_spec (path : std.path.Path) (source : Option std.path.PathBuf)
    (rule : ast.PermissionSpec) (ds : Vec sudoers.Error)
    (hp : rawIgnored rule ≠ [] → DiagnosticPath path source)
    (hb : ds.val.length + (rawIgnored rule).length ≤ Usize.max) :
    sudoers.ignored_tags path rule ds ⦃ out => out.val = ds.val ++ ignoredReports source (rawIgnored rule) ⦄ := by
  simpa [sudoers.ignored_tags, rawIgnored] using ignored_segments_loop_spec path source ds
    rule.permissions 0#usize (by simpa [rawIgnored] using hp) (by simpa [rawIgnored] using hb)

private theorem append_defs_spec {T : Type} (acc ds : Vec (RDef T))
    (hb : acc.val.length + ds.val.length ≤ Usize.max) :
    sudoers.append_defs acc ds ⦃ out => out.val = acc.val ++ ds.val ⦄ := by
  simp [sudoers.append_defs, alloc.vec.Vec.append, hb, uncurry_apply_pair]

private def anyMeta : tokens.Meta glob.Pattern → tokens.Meta RCommand
  | .All => .All
  | .Alias id => .Alias id
  | .Only p => .Only (p, .Prefix (Slice.new _))

private def anySpec : RSpec glob.Pattern → RSpec RCommand
  | .Allow m => .Allow (anyMeta m)
  | .Forbid m => .Forbid (anyMeta m)

private theorem any_arguments_ok (s : RSpec glob.Pattern) :
    sudoers.any_arguments s = ok (anySpec s) := by
  rcases s with m | m <;> cases m <;>
    simp [sudoers.any_arguments, sudoers.any_arguments_meta, anySpec, anyMeta,
      BoxSlice.Insts.CoreDefaultDefault.default]

private theorem intoIter_next_nil {α : Type} (it : alloc.vec.into_iter.IntoIter α)
    (h : it.val = []) :
    alloc.vec.into_iter.IteratorIntoIter.next it = ok (none, it) := by
  unfold alloc.vec.into_iter.IteratorIntoIter.next
  split <;> simp_all

private theorem intoIter_next_cons {α : Type} (it : alloc.vec.into_iter.IntoIter α)
    {x : α} {xs : List α} (h : it.val = x :: xs) :
    ∃ rest : alloc.vec.into_iter.IntoIter α,
      alloc.vec.into_iter.IteratorIntoIter.next it = ok (some x, rest) ∧ rest.val = xs := by
  have bound := Vec.property it
  rw [h] at bound
  refine ⟨Vec.from xs (by simpa using Nat.le_trans (Nat.le_succ _) bound), ?_, Vec.from_val _ _⟩
  unfold alloc.vec.into_iter.IteratorIntoIter.next
  split <;> simp_all

private theorem command_scope_loop_spec
    (remaining : List (RSpec glob.Pattern)) (acc : Vec (RSpec RCommand))
    (it : alloc.vec.into_iter.IntoIter (RSpec glob.Pattern)) (h : it.val = remaining)
    (hb : acc.val.length + remaining.length ≤ Usize.max) :
    sudoers.command_scope_loop acc it true ⦃ out =>
      out.val = acc.val ++ remaining.map anySpec ⦄ := by
  induction remaining generalizing acc it with
  | nil =>
    rw [sudoers.command_scope_loop, ite_eq_left rfl, intoIter_next_nil it h]
    simp only [Std.bind_ok, uncurry_apply_pair]
    rw [sudoers.command_scope_loop, ite_eq_right (by decide : ¬false = true)]
    simp
  | cons s ss ih =>
    obtain ⟨tail, hn, ht⟩ := intoIter_next_cons it h
    rw [sudoers.command_scope_loop, ite_eq_left rfl, hn]
    simp only [Std.bind_ok, uncurry_apply_pair, any_arguments_ok]
    apply WP.spec_bind (Vec.push_spec acc (anySpec s) (by simp at hb; omega))
    intro next hnext
    have hlen := congrArg List.length hnext
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    apply WP.spec_mono (ih next tail ht (by simp at hb; omega))
    intro out hout
    simpa only [hnext, List.map_cons, List.append_assoc, List.singleton_append] using hout

private theorem command_scope_spec (specs : Vec (RSpec glob.Pattern)) :
    sudoers.command_scope specs ⦃ out => out.val = specs.val.map anySpec ⦄ := by
  unfold sudoers.command_scope
  apply WP.spec_bind (Pₘ := (· = specs))
    (spec_of_eq_ok (rfl : alloc.vec.IntoIteratorVec.into_iter specs = ok specs) rfl)
  intro it eq
  subst it
  simpa [Vec.with_capacity] using command_scope_loop_spec specs.val
    (Vec.new _) specs rfl (by simp)

open SudoersSpec.Analysis (Collected LocalItem collectItem collectFrom collect commandScope ignoredSpans policyOf)

abbrev RItem := RParsed ast.Sudo
abbrev Item := SudoersSpec.Syntax.Parsed SudoersSpec.Syntax.Sudo

/-- A diagnostic read with its exact source, optional span, and message. -/
def diagnosticView (e : sudoers.Error) :
    Option std.path.PathBuf × Option SudoersSpec.Span × String :=
  (e.source, e.location.map absSpan, e.message)

def localDiagnosticView (source : Option std.path.PathBuf) (d : SudoersSpec.Span × String) :
    Option std.path.PathBuf × Option SudoersSpec.Span × String :=
  (source, some d.1, d.2)

/-- The raw alias definition vectors are compared in their written order, not through the
sanitizer's index vectors. Diagnostic sources and spans are checked rather than discarded. -/
structure CollectedRel (A : GlobAbs) (source : Option std.path.PathBuf) (cfg : Sudoers)
    (ds : Vec sudoers.Error) (c : Collected) : Prop where
  rules : cfg.rules.val.map (absPermissionSpec A) = c.rules
  user : cfg.aliases.user.2.val.map (absDef absUserSpecifier) = c.written.user
  host : cfg.aliases.host.2.val.map (absDef id) = c.written.host
  cmnd : cfg.aliases.cmnd.2.val.map (absDef (absCommand A)) = c.written.cmnd
  runas : cfg.aliases.runas.2.val.map (absDef absUserSpecifier) = c.written.runas
  nonCommand : absNonCommand cfg.customisers.non_cmnd = c.nonCommand
  command : absCommandCustomisers A cfg.customisers.cmnd = c.command
  diagnostics : ds.val.map diagnosticView = c.diagnostics.map (localDiagnosticView source)

/-- Names needed by the scope matchers, before or after adding empty command arguments. -/
def ScopeFits : ast.ConfigScope → Prop
  | .Host xs => ItemsFit xs.val ∧ ItemsGood Fits xs.val
  | .User xs | .RunAs xs => ItemsFit xs.val ∧ ItemsGood UserSpecFits xs.val
  | .Command xs => ItemsFit xs.val
  | .Generic => True

structure CustomisersOK (c : CustomiserTable) : Prop where
  nonCommandOnly : NonCommandOnly c.non_cmnd
  nonCommand : ∀ e ∈ c.non_cmnd.val, ScopeFits e.1 ∧ ∀ m ∈ e.2.val, Defaults.Produced m
  command : ∀ e ∈ c.cmnd.val, ItemsFit e.1.val ∧ ∀ m ∈ e.2.val, Defaults.Produced m

/-- The representability needed downstream by the decision and by alias sanitization. -/
structure CollectorOK (cfg : Sudoers) : Prop where
  rules : ∀ r ∈ cfg.rules.val, RuleOK r
  user : TableFits cfg.aliases.user ∧ TableGood UserSpecFits cfg.aliases.user
  host : TableFits cfg.aliases.host ∧ TableGood Fits cfg.aliases.host
  cmnd : TableFits cfg.aliases.cmnd
  runas : TableFits cfg.aliases.runas ∧ TableGood UserSpecFits cfg.aliases.runas
  customisers : CustomisersOK cfg.customisers

private def defsSize {T : Type} (ds : Vec (RDef T)) : Nat :=
  ds.val.length + (ds.val.map fun d => d.2.val.length).sum

/-- A single bound suffices for every push/append during collection and for the
sanitizer's diagnostic allowance, including a place per alias member. -/
def collectSize (cfg : Sudoers) (ds : Vec sudoers.Error) : Nat :=
  ds.val.length + tableSize cfg.aliases.user + tableSize cfg.aliases.host +
    tableSize cfg.aliases.cmnd + tableSize cfg.aliases.runas + cfg.rules.val.length +
    cfg.customisers.non_cmnd.val.length + cfg.customisers.cmnd.val.length

def itemSize : RItem → Nat
  | .Err (.Fatal ..) => 1
  | .Ok (.Spec r) => (rawIgnored r).length + 1
  | .Ok (.Decl (.UserAlias ds)) => defsSize ds
  | .Ok (.Decl (.HostAlias ds)) => defsSize ds
  | .Ok (.Decl (.CmndAlias ds)) => defsSize ds
  | .Ok (.Decl (.RunasAlias ds)) => defsSize ds
  | .Ok (.Decl (.Defaults ..)) => 1
  | _ => 0

def ItemFits : RItem → Prop
  | .Ok (.Spec r) => RuleOK r
  | .Ok (.Decl (.UserAlias ds)) | .Ok (.Decl (.RunasAlias ds)) =>
      Sanitize.DefsFit ds.val ∧ ∀ d ∈ ds.val, ItemsGood UserSpecFits d.2.val
  | .Ok (.Decl (.HostAlias ds)) =>
      Sanitize.DefsFit ds.val ∧ ∀ d ∈ ds.val, ItemsGood Fits d.2.val
  | .Ok (.Decl (.CmndAlias ds)) => Sanitize.DefsFit ds.val
  | .Ok (.Decl (.Defaults mods scope)) =>
      ScopeFits scope ∧ ∀ m ∈ mods.val, Defaults.Produced m
  | _ => True

/-- The path view is needed only for a call that emits a local diagnostic. -/
def NeedsDiagnosticPath : RItem → Prop
  | .Err (.Fatal ..) => True
  | .Ok (.Spec rule) => rawIgnored rule ≠ []
  | _ => False

/-- Only the fatal error that is actually reported needs the rendering model. -/
def RenderOn : RItem → Item → Prop
  | .Err (.Fatal _ k), .error (.fatal _ k') => sudo_rs.errorKindText k = k'.render
  | _, _ => True

/-- Lift the parser's result relation, requiring only render agreement on the fatal errors
that occur in this stream. -/
theorem related_rendered_items (A : GlobAbs) {rs : List RItem} {items : List Item}
    (hr : List.Forall₂ (ResultRel (absSudo A)) rs items)
    (hm : ∀ span k, .Err (.Fatal span k) ∈ rs → ∀ k',
      KindRel k k' → sudo_rs.errorKindText k = k'.render) :
    List.Forall₂ (fun r i => ResultRel (absSudo A) r i ∧ RenderOn r i) rs items := by
  induction hr with
  | nil => exact .nil
  | @cons r i rs items hhead _ ih =>
    refine .cons ⟨hhead, ?_⟩ (ih fun span k hk k' hkind =>
      hm span k (List.mem_cons_of_mem r hk) k' hkind)
    cases r with
    | Ok _ => trivial
    | Err status =>
      cases i with
      | ok _ => exact False.elim hhead
      | error status' =>
        change StatusRel status status' at hhead
        cases hhead with
        | reject => trivial
        | fatal span k k' hkind => exact hm span k (by simp) k' hkind

private theorem ignoredModifier_view (m : ast.Modifier) :
    (ignoredModifier m).map absSpan =
      (match absModifier m with | .ignored s => some s | _ => none) := by
  cases m <;> rfl

theorem rawIgnored_eq (A : GlobAbs) (r : ast.PermissionSpec) :
    (rawIgnored r).map absSpan = ignoredSpans (absPermissionSpec A r) := by
  simp only [rawIgnored, ignoredSpans, absPermissionSpec, List.flatMap_map, List.map_flatMap]
  apply List.flatMap_congr
  intro seg _
  simp only [ignoredSegment, absSeg, absLine, List.flatMap_map, List.map_flatMap]
  apply List.flatMap_congr
  intro e _
  simp only [ignoredEntry, absCommandSpec, List.filterMap_map, List.map_filterMap, Function.comp_def]
  exact List.filterMap_congr (fun m _ => ignoredModifier_view m)

private theorem anySpec_view (A : GlobAbs) (s : RSpec glob.Pattern) :
    absSpec (absCommand A) (anySpec s) =
      SudoersSpec.mapSpec (fun p => ⟨p, .prefix []⟩) (absSpec A.pat s) := by
  rcases s with m | m <;> cases m <;> rfl

private theorem commandScope_view (A : GlobAbs) (xs : List (RSpec glob.Pattern)) :
    absSpecList (absCommand A) (xs.map anySpec) = commandScope (absSpecList A.pat xs) := by
  simp only [commandScope, absSpecList, List.map_map]
  exact List.map_congr_left (fun s _ => anySpec_view A s)

private theorem anySpec_fits (xs : List (RSpec glob.Pattern)) (h : ItemsFit xs) :
    ItemsFit (xs.map anySpec) := by
  intro item hitem id hid
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hitem
  apply h s hs
  rcases s with m | m <;> cases m <;> exact hid

private theorem tableFits_append {T : Type} {old new : VecOrd (RDef T)} {ds : Vec (RDef T)}
    (he : new.2.val = old.2.val ++ ds.val) (ho : TableFits old) (hd : Sanitize.DefsFit ds.val) :
    TableFits new := by
  intro d hm
  rw [he, List.mem_append] at hm
  exact hm.elim (ho d) (hd d)

private theorem tableGood_append {T : Type} {Good : T → Prop} {old new : VecOrd (RDef T)}
    {ds : Vec (RDef T)} (he : new.2.val = old.2.val ++ ds.val) (ho : TableGood Good old)
    (hd : ∀ d ∈ ds.val, ItemsGood Good d.2.val) : TableGood Good new := by
  intro d hm
  rw [he, List.mem_append] at hm
  exact hm.elim (ho d) (hd d)

private theorem ignoredReports_view (A : GlobAbs) (source : Option std.path.PathBuf)
    (rule : ast.PermissionSpec) :
    (ignoredReports source (rawIgnored rule)).map diagnosticView =
      ((ignoredSpans (absPermissionSpec A rule)).map (·, ignoredMessage)).map
        (localDiagnosticView source) := by
  rw [← rawIgnored_eq]
  simp only [ignoredReports, List.map_map]
  rfl

private theorem customisersOK_push_nonCommand {c : CustomiserTable}
    {scope : ast.ConfigScope} {mods : Vec defaults.SettingsModifier}
    (old : CustomisersOK c) (valid : (absNonCommandScope scope).isSome)
    (fits : ScopeFits scope ∧ ∀ m ∈ mods.val, Defaults.Produced m) {v}
    (hv : v.val = c.non_cmnd.val ++ [(scope, mods)]) :
    CustomisersOK { c with non_cmnd := v } := by
  refine ⟨?_, ?_, old.command⟩
  · intro entry he
    change entry ∈ v.val at he
    rw [hv, List.mem_append, List.mem_singleton] at he
    exact he.elim (old.nonCommandOnly entry) (fun h => h ▸ valid)
  · intro entry he
    change entry ∈ v.val at he
    rw [hv, List.mem_append, List.mem_singleton] at he
    exact he.elim (old.nonCommand entry) (fun h => h ▸ fits)

private theorem customisersOK_push_command {c : CustomiserTable}
    {scope : Vec (RSpec RCommand)} {mods : Vec defaults.SettingsModifier}
    (old : CustomisersOK c) (fits : ItemsFit scope.val ∧ ∀ m ∈ mods.val, Defaults.Produced m)
    {v} (hv : v.val = c.cmnd.val ++ [(scope, mods)]) :
    CustomisersOK { c with cmnd := v } := by
  refine ⟨old.nonCommandOnly, old.nonCommand, ?_⟩
  intro entry he
  change entry ∈ v.val at he
  rw [hv, List.mem_append, List.mem_singleton] at he
  exact he.elim (old.command entry) (fun h => h ▸ fits)

private theorem update_nonCommand {A : GlobAbs} {source : Option std.path.PathBuf} {cfg : Sudoers}
    {ds : Vec sudoers.Error} {c : Collected} (h : CollectedRel A source cfg ds c)
    {scope : ast.ConfigScope} {mods : Vec defaults.SettingsModifier}
    {s : SudoersSpec.Analysis.NonCommandScope} (hs : absNonCommandScope scope = some s)
    {v} (hv : v.val = cfg.customisers.non_cmnd.val ++ [(scope, mods)]) :
    CollectedRel A source { cfg with customisers := { cfg.customisers with non_cmnd := v } } ds
      { c with nonCommand := c.nonCommand ++ [(s, mods.val.map Defaults.absModifier)] } := by
  refine { h with nonCommand := ?_ }
  have hn := h.nonCommand
  unfold absNonCommand at hn ⊢
  simp [hv, hn, hs]

private theorem update_command {A : GlobAbs} {source : Option std.path.PathBuf} {cfg : Sudoers}
    {ds : Vec sudoers.Error} {c : Collected} (h : CollectedRel A source cfg ds c)
    {scope : Vec (RSpec RCommand)} {mods : Vec defaults.SettingsModifier}
    {s : SudoersSpec.SpecList SudoersSpec.Command}
    (hs : absSpecList (absCommand A) scope.val = s)
    {v} (hv : v.val = cfg.customisers.cmnd.val ++ [(scope, mods)]) :
    CollectedRel A source { cfg with customisers := { cfg.customisers with cmnd := v } } ds
      { c with command := c.command ++ [(s, mods.val.map Defaults.absModifier)] } := by
  refine { h with command := ?_ }
  have hc := h.command
  unfold absCommandCustomisers at hc ⊢
  simp [hv, hc, hs]

/-- One extracted local iteration agrees with the reference and preserves the domains needed
by sanitization, scope matching, and the decision. In particular it neither calls an include
oracle nor touches the include attempt counter: the only two oracle branches cannot satisfy
the `collectItem` premise. -/
theorem process_item_refines (A : GlobAbs) (path : std.path.Path) (source : Option std.path.PathBuf)
    (cfg : Sudoers) (ds : Vec sudoers.Error) (st : IncludeState)
    (item : RItem) (ref : Item) (c c' : Collected)
    (hitem : collectItem c ref = some c')
    (hr : ResultRel (absSudo A) item ref) (hm : RenderOn item ref)
    (hp : NeedsDiagnosticPath item → DiagnosticPath path source)
    (hfits : ItemFits item) (hok : CollectorOK cfg)
    (hab : CollectedRel A source cfg ds c)
    (hb : collectSize cfg ds + itemSize item ≤ Usize.max) :
    sudoers.process_item cfg path item ds st ⦃ out =>
      CollectedRel A source out.1 out.2.1 c' ∧ CollectorOK out.1 ∧
      out.1.settings = cfg.settings ∧ out.2.2 = st ∧
      collectSize out.1 out.2.1 = collectSize cfg ds + itemSize item ⦄ := by
  cases item with
  | Err status =>
    cases ref with
    | ok _ => exact False.elim hr
    | error status' =>
      change StatusRel status status' at hr
      cases hr with
      | reject => simp [collectItem] at hitem
      | fatal span kind kind' hkind =>
        simp only [collectItem, Option.some.injEq] at hitem
        subst c'
        change sudo_rs.errorKindText kind = kind'.render at hm
        simp only [collectSize, itemSize] at hb
        rw [sudoers.process_item]
        simp only [sudoers.fatal_message, Std.bind_ok, hm]
        apply WP.spec_bind (report_spec path source span kind'.render ds (hp trivial) (by omega))
        intro next hn
        simp only [WP.spec_ok]
        refine ⟨{ hab with diagnostics := ?_ }, hok, trivial, trivial, ?_⟩
        · simp [hn, hab.diagnostics, rawReport, diagnosticView, localDiagnosticView]
        · simp only [collectSize, itemSize, hn, List.length_append, List.length_singleton]
          omega
  | Ok line =>
    cases ref with
    | error _ => exact False.elim hr
    | ok line' =>
      change absSudo A line = line' at hr
      subst line'
      cases line with
      | Include path span | IncludeDir path span => simp [absSudo, collectItem] at hitem
      | LineComment =>
        simp only [absSudo, collectItem, Option.some.injEq] at hitem
        subst c'
        simp [sudoers.process_item, itemSize, hab, hok]
      | Spec rule =>
        simp only [absSudo, collectItem, Option.some.injEq] at hitem
        subst c'
        simp only [collectSize, itemSize] at hb
        rw [sudoers.process_item]
        apply WP.spec_bind (ignored_tags_spec path source rule ds hp (by omega))
        intro diags hdiags
        apply WP.spec_bind (Vec.push_spec cfg.rules rule (by omega))
        intro rules hrules
        simp only [WP.spec_ok]
        refine ⟨{ hab with rules := ?_, diagnostics := ?_ }, { hok with rules := ?_ },
          trivial, trivial, ?_⟩
        · simp [hrules, hab.rules]
        · rw [hdiags, List.map_append, hab.diagnostics, List.map_append, ignoredReports_view A source rule]
          rfl
        · intro r h
          change r ∈ rules.val at h
          rw [hrules, List.mem_append, List.mem_singleton] at h
          exact h.elim (hok.rules r) (fun eq => eq ▸ hfits)
        · simp only [collectSize, itemSize, hdiags, hrules, List.length_append,
            List.length_singleton, ignoredReports, List.length_map]
          omega
      | Decl directive =>
        cases directive with
        | UserAlias defs =>
          simp only [absSudo, absDirective, collectItem, Option.some.injEq] at hitem
          subst c'
          simp only [collectSize, itemSize, defsSize, tableSize] at hb
          rw [sudoers.process_item]
          apply WP.spec_bind (append_defs_spec cfg.aliases.user.2 defs (by omega))
          intro dst hv
          simp only [WP.spec_ok]
          refine ⟨{ hab with user := ?_ }, { hok with user := ⟨?_, ?_⟩ }, trivial, trivial, ?_⟩
          · simp [hv, hab.user]
          · exact tableFits_append hv hok.user.1 hfits.1
          · exact tableGood_append hv hok.user.2 hfits.2
          · simp only [collectSize, itemSize, tableSize, defsSize, hv,
              List.length_append, List.map_append, List.sum_append]
            omega
        | HostAlias defs =>
          simp only [absSudo, absDirective, collectItem, Option.some.injEq] at hitem
          subst c'
          simp only [collectSize, itemSize, defsSize, tableSize] at hb
          rw [sudoers.process_item]
          apply WP.spec_bind (append_defs_spec cfg.aliases.host.2 defs (by omega))
          intro dst hv
          simp only [WP.spec_ok]
          refine ⟨{ hab with host := ?_ }, { hok with host := ⟨?_, ?_⟩ }, trivial, trivial, ?_⟩
          · simp [hv, hab.host]
          · exact tableFits_append hv hok.host.1 hfits.1
          · exact tableGood_append hv hok.host.2 hfits.2
          · simp only [collectSize, itemSize, tableSize, defsSize, hv,
              List.length_append, List.map_append, List.sum_append]
            omega
        | CmndAlias defs =>
          simp only [absSudo, absDirective, collectItem, Option.some.injEq] at hitem
          subst c'
          simp only [collectSize, itemSize, defsSize, tableSize] at hb
          rw [sudoers.process_item]
          apply WP.spec_bind (append_defs_spec cfg.aliases.cmnd.2 defs (by omega))
          intro dst hv
          simp only [WP.spec_ok]
          refine ⟨{ hab with cmnd := ?_ }, { hok with cmnd := ?_ }, trivial, trivial, ?_⟩
          · simp [hv, hab.cmnd]
          · exact tableFits_append hv hok.cmnd hfits
          · simp only [collectSize, itemSize, tableSize, defsSize, hv,
              List.length_append, List.map_append, List.sum_append]
            omega
        | RunasAlias defs =>
          simp only [absSudo, absDirective, collectItem, Option.some.injEq] at hitem
          subst c'
          simp only [collectSize, itemSize, defsSize, tableSize] at hb
          rw [sudoers.process_item]
          apply WP.spec_bind (append_defs_spec cfg.aliases.runas.2 defs (by omega))
          intro dst hv
          simp only [WP.spec_ok]
          refine ⟨{ hab with runas := ?_ }, { hok with runas := ⟨?_, ?_⟩ }, trivial, trivial, ?_⟩
          · simp [hv, hab.runas]
          · exact tableFits_append hv hok.runas.1 hfits.1
          · exact tableGood_append hv hok.runas.2 hfits.2
          · simp only [collectSize, itemSize, tableSize, defsSize, hv,
              List.length_append, List.map_append, List.sum_append]
            omega
        | Defaults mods scope =>
          simp only [collectSize, itemSize] at hb
          cases scope with
          | Command patterns =>
            simp only [absSudo, absDirective, absConfigScope, collectItem, Option.some.injEq] at hitem
            subst c'
            rw [sudoers.process_item]
            apply WP.spec_bind (command_scope_spec patterns)
            intro scope hs
            apply WP.spec_bind (Vec.push_spec cfg.customisers.cmnd (scope, mods) (by omega))
            intro v hv
            have hcmd := commandScope_view A patterns.val
            have hfit : ItemsFit scope.val := hs.symm ▸ anySpec_fits patterns.val hfits.1
            simp only [WP.spec_ok]
            refine ⟨update_command hab (by rw [hs, hcmd]) hv,
              { hok with customisers := (customisersOK_push_command hok.customisers
                ⟨hfit, hfits.2⟩ hv) }, trivial, trivial, ?_⟩
            simp only [collectSize, itemSize, hv, List.length_append, List.length_singleton]
            omega
          | _ =>
            simp only [absSudo, absDirective, absConfigScope, collectItem, Option.some.injEq] at hitem
            subst c'
            rw [sudoers.process_item]
            apply WP.spec_bind (Vec.push_spec cfg.customisers.non_cmnd _ (by omega))
            intro v hv
            simp only [WP.spec_ok]
            refine ⟨update_nonCommand hab rfl hv,
              { hok with customisers := (customisersOK_push_nonCommand hok.customisers
                rfl hfits hv) }, trivial, trivial, ?_⟩
            simp only [collectSize, itemSize, hv, List.length_append, List.length_singleton]
            omega

/-- The iterator uses the real Rust owning iteration model. The induction consumes one parsed
item and its matching reference item at the same time; it never unfolds an include oracle. -/
theorem process_loop_refines (A : GlobAbs) (path : std.path.Path) (source : Option std.path.PathBuf)
    (cfg : Sudoers) (ds : Vec sudoers.Error) (st : IncludeState)
    (it : alloc.vec.into_iter.IntoIter RItem) (rs : List RItem) (items : List Item)
    (hi : it.val = rs) (hr : List.Forall₂ (fun r i => ResultRel (absSudo A) r i ∧ RenderOn r i) rs items)
    (c c' : Collected) (hc : collectFrom c items = some c')
    (hp : ∀ r ∈ rs, NeedsDiagnosticPath r → DiagnosticPath path source)
    (hf : ∀ r ∈ rs, ItemFits r) (hok : CollectorOK cfg) (hab : CollectedRel A source cfg ds c)
    (hb : collectSize cfg ds + (rs.map itemSize).sum ≤ Usize.max) :
    sudoers.process_loop cfg path ds st it true ⦃ out =>
      CollectedRel A source out.1 out.2.1 c' ∧ CollectorOK out.1 ∧
      out.1.settings = cfg.settings ∧ out.2.2 = st ∧
      collectSize out.1 out.2.1 = collectSize cfg ds + (rs.map itemSize).sum ⦄ := by
  induction hr generalizing cfg ds it c with
  | nil =>
    have e : c = c' := by simpa [collectFrom] using hc
    subst c'
    rw [sudoers.process_loop, ite_eq_left rfl, intoIter_next_nil it hi]
    simp only [Std.bind_ok, uncurry_apply_pair]
    rw [sudoers.process_loop, ite_eq_right (by decide : ¬false = true)]
    simp [hab, hok]
  | @cons r ref rest refs hhead htail ih =>
    obtain ⟨tail, e, ht⟩ := intoIter_next_cons it hi
    cases first : collectItem c ref with
    | none => simp [collectFrom, first] at hc
    | some next =>
      have hc' : collectFrom next refs = some c' := by
        simpa [collectFrom, first] using hc
      rw [sudoers.process_loop, ite_eq_left rfl, e]
      simp only [Std.bind_ok, uncurry_apply_pair]
      apply WP.spec_bind (process_item_refines A path source cfg ds st r ref c next first
        hhead.1 hhead.2 (hp r (by simp)) (hf r (by simp)) hok hab (by simp at hb; omega))
      rintro ⟨cfg', ds', st'⟩ ⟨hab', hok', hsettings, rfl, hsize⟩
      simp only [uncurry_apply_pair]
      have tailFits : ∀ x ∈ rest, ItemFits x := fun x hx => hf x (List.mem_cons_of_mem _ hx)
      have tailPath : ∀ x ∈ rest, NeedsDiagnosticPath x → DiagnosticPath path source :=
        fun x hx => hp x (List.mem_cons_of_mem _ hx)
      have tailBound : collectSize cfg' ds' + (rest.map itemSize).sum ≤ Usize.max := by
        simp at hb
        simp only [hsize]
        omega
      apply WP.spec_mono (ih cfg' ds' tail ht next hc' tailPath tailFits hok' hab' tailBound)
      rintro ⟨out, diags, state⟩ ⟨habs, hgood, hs, hstate, hbudget⟩
      exact ⟨habs, hgood, hs.trans hsettings, hstate, by simpa [hsize, Nat.add_assoc] using hbudget⟩

/-- The parsed-item loop implements the reference collection fold, including fatal items.
No include-oracle hypothesis is needed, even for files with diagnostics. -/
theorem process_refines (A : GlobAbs) (path : std.path.Path) (source : Option std.path.PathBuf)
    (cfg : Sudoers) (ds : Vec sudoers.Error) (st : IncludeState)
    (rs : Vec RItem) (items : List Item)
    (hr : List.Forall₂ (fun r i => ResultRel (absSudo A) r i ∧ RenderOn r i) rs.val items)
    (c c' : Collected) (hc : collectFrom c items = some c')
    (hp : ∀ r ∈ rs.val, NeedsDiagnosticPath r → DiagnosticPath path source)
    (hf : ∀ r ∈ rs.val, ItemFits r) (hok : CollectorOK cfg) (hab : CollectedRel A source cfg ds c)
    (hb : collectSize cfg ds + (rs.val.map itemSize).sum ≤ Usize.max) :
    sudoers.process cfg path rs ds st ⦃ out =>
      CollectedRel A source out.1 out.2.1 c' ∧ CollectorOK out.1 ∧
      out.1.settings = cfg.settings ∧ out.2.2 = st ∧
      collectSize out.1 out.2.1 = collectSize cfg ds + (rs.val.map itemSize).sum ⦄ := by
  rw [sudoers.process]
  apply WP.spec_bind (Pₘ := (· = rs))
    (spec_of_eq_ok (rfl : alloc.vec.IntoIteratorVec.into_iter rs = ok rs) rfl)
  intro it eq
  subst it
  exact process_loop_refines A path source cfg ds st rs rs.val items rfl hr c c' hc hp hf hok hab hb

/-- Every raw input accepted by the reference collector takes a local branch of
`process_item`: neither of the two include-oracle arms can be entered. -/
theorem no_include_dispatch (A : GlobAbs) {rs : List RItem} {items : List Item}
    (hr : List.Forall₂ (ResultRel (absSudo A)) rs items) {c c' : Collected}
    (hc : collectFrom c items = some c') :
    ∀ r ∈ rs, (∀ p s, r ≠ .Ok (.Include p s)) ∧
      (∀ p s, r ≠ .Ok (.IncludeDir p s)) ∧ r ≠ .Err .Reject := by
  have hl := (SudoersSpec.Analysis.collectFrom_some_iff c items).mp ⟨c', hc⟩
  clear hc c c'
  induction hr with
  | nil => simp
  | @cons r item rs items hhead htail ih =>
    intro x hx
    rcases List.mem_cons.mp hx with he | hx
    · subst x
      have h := hl item (by simp)
      refine ⟨?_, ?_, ?_⟩
      · intro p s he
        subst r
        cases item with
        | error _ => exact hhead
        | ok a =>
          change SudoersSpec.Syntax.Sudo.include p (absSpan s) = a at hhead
          subst a
          exact h
      · intro p s he
        subst r
        cases item with
        | error _ => exact hhead
        | ok a =>
          change SudoersSpec.Syntax.Sudo.includeDir p (absSpan s) = a at hhead
          subst a
          exact h
      · intro he
        subst r
        cases item with
        | ok _ => exact hhead
        | error status =>
          change StatusRel .Reject status at hhead
          cases hhead
          exact h
    · exact ih (fun y hy => hl y (List.mem_cons_of_mem _ hy)) x hx

private def emptyOrder (T : Type) : VecOrd T := (Vec.new _, Vec.new _)

private def emptyCfg (s : defaults.Settings) : Sudoers :=
  ⟨Vec.new _, ⟨emptyOrder _, emptyOrder _, emptyOrder _, emptyOrder _⟩, s,
    ⟨Vec.new _, Vec.new _⟩⟩

private theorem emptyCfg_rel (A : GlobAbs) (source : Option std.path.PathBuf) (s : defaults.Settings) :
    CollectedRel A source (emptyCfg s) (Vec.new _) {} := by
  constructor <;> simp [emptyCfg, emptyOrder, absNonCommand, absCommandCustomisers]

private theorem emptyCfg_OK (s : defaults.Settings) : CollectorOK (emptyCfg s) := by
  have hc : CustomisersOK (emptyCfg s).customisers :=
    ⟨by simp [NonCommandOnly, emptyCfg], by simp [emptyCfg], by simp [emptyCfg]⟩
  exact ⟨by simp [emptyCfg], by simp [TableFits, TableGood, emptyCfg, emptyOrder],
    by simp [TableFits, TableGood, emptyCfg, emptyOrder], by simp [TableFits, emptyCfg, emptyOrder],
    by simp [TableFits, TableGood, emptyCfg, emptyOrder], hc⟩

private theorem emptyCfg_size (s : defaults.Settings) : collectSize (emptyCfg s) (Vec.new _) = 0 := by
  simp [collectSize, tableSize, emptyCfg, emptyOrder]

private theorem default_returns_empty :
    ∃ s, sudoers.Sudoers.Insts.CoreDefaultDefault.default = ok (emptyCfg s) ∧
      Defaults.absSettings s = Defaults.initialModel := by
  obtain ⟨s, e, ha⟩ := Defaults.default_eq
  refine ⟨s, ?_, ha⟩
  simp [sudoers.Sudoers.Insts.CoreDefaultDefault.default,
    sudoers.AliasTable.Insts.CoreDefaultDefault.default,
    sudoers.VecOrd.Insts.CoreDefaultDefault.default,
    sudoers.CustomiserTable.Insts.CoreDefaultDefault.default,
    alloc.vec.Vec.Insts.CoreDefaultDefault.default, sudoers.VecOrd, e, Std.bind_ok,
    emptyCfg, emptyOrder]

/-- Collection and the actual sanitizer are the two phases of `analyze`.
The intermediate state exposes the four written definition lists, untouched settings, and
local source/span/message triples. Sanitization establishes policy index well-formedness.
The bound is on the parsed items alone, not on a caller-supplied analyzed policy. -/
theorem analyze_partition (A : GlobAbs) (path : std.path.Path) (source : Option std.path.PathBuf)
    (rs : Vec RItem) (items : List Item) (c : Collected)
    (hr : List.Forall₂ (fun r i => ResultRel (absSudo A) r i ∧ RenderOn r i) rs.val items)
    (hc : collect items = some c)
    (hp : ∀ r ∈ rs.val, NeedsDiagnosticPath r → DiagnosticPath path source)
    (hf : ∀ r ∈ rs.val, ItemFits r) (hb : (rs.val.map itemSize).sum ≤ Usize.max) :
    ∃ pre ds aliases finalDs,
      sudoers.analyze path rs = ok ({ pre with aliases := aliases }, finalDs) ∧
      CollectedRel A source pre ds c ∧ CollectorOK pre ∧
      Defaults.absSettings pre.settings = Defaults.initialModel ∧
      sanitize_alias_tables pre.aliases ds = ok (aliases, finalDs) ∧
      PolicyOK (Vec.deref pre.rules) aliases := by
  obtain ⟨settings, hdefault, hsettings⟩ := default_returns_empty
  let ds0 := Vec.new sudoers.Error
  have bound : collectSize (emptyCfg settings) ds0 + (rs.val.map itemSize).sum ≤ Usize.max := by
    simpa [ds0, emptyCfg_size] using hb
  obtain ⟨⟨pre, ds, state⟩, hpure, hab, hok, hunchanged, -, hsize⟩ := exists_eq_ok_of_spec
    (process_refines A path source (emptyCfg settings) ds0 (.Allowed 0#u8) rs items hr
      {} c hc hp hf (emptyCfg_OK settings) (emptyCfg_rel A source settings) bound)
  have hsbound : ds.val.length + tableSize pre.aliases.user + tableSize pre.aliases.host +
      tableSize pre.aliases.cmnd + tableSize pre.aliases.runas ≤ Usize.max := by
    change collectSize pre ds = collectSize (emptyCfg settings) ds0 + (rs.val.map itemSize).sum at hsize
    simp only [ds0, emptyCfg_size, Nat.zero_add] at hsize
    unfold collectSize at hsize
    omega
  obtain ⟨⟨aliases, finalDs⟩, hsan⟩ := sanitize_alias_tables_returns pre.aliases ds
    hok.user.1 hok.host.1 hok.cmnd hok.runas.1 hsbound
  refine ⟨pre, ds, aliases, finalDs, ?_, hab, hok, ?_, hsan, ?_⟩
  · rw [sudoers.analyze, hdefault]
    simp only [Std.bind_ok, hpure, uncurry_apply_pair, hsan, ds0]
  · exact (congrArg Defaults.absSettings hunchanged).trans hsettings
  · exact ⟨AliasTableOK.of_sanitize_alias_tables hsan hok.user.1 hok.user.2
      hok.host.1 hok.host.2 hok.cmnd hok.runas.1 hok.runas.2, by simpa using hok.rules⟩

/-- The exact include-free PA postcondition. Rules and aliases are ready for the verified
decision; the original definition vectors and both customiser lists are still available.
The diagnostics preserve the raw local prefix, then the sanitizer's exact message sequence. -/
structure AnalysisResult (A : GlobAbs) (source : Option std.path.PathBuf) (c : Collected)
    (cfg : Sudoers) (diags : Vec sudoers.Error) : Prop where
  policy : absPolicy A (Vec.deref cfg.rules) cfg.aliases = policyOf c
  written : absWrittenAliasTable A cfg.aliases = c.written
  nonCommand : absNonCommand cfg.customisers.non_cmnd = c.nonCommand
  command : absCommandCustomisers A cfg.customisers.cmnd = c.command
  settings : Defaults.absSettings cfg.settings = Defaults.initialModel
  policyOK : PolicyOK (Vec.deref cfg.rules) cfg.aliases
  customisersOK : CustomisersOK cfg.customisers
  localPrefix : ∃ localDiags : List sudoers.Error, localDiags <+: diags.val ∧
    localDiags.map diagnosticView = c.diagnostics.map (localDiagnosticView source)
  messages : diags.val.map sudoers.Error.message =
    c.diagnostics.map Prod.snd ++ (SudoersSpec.Analysis.orderAliases c.written).2
  aliasesOK_of_clean : diags.val = [] → (policyOf c).aliases.OK

/-- PA: on local, non-`Reject` items, the real analyzer returns the reference `policyOf`, the
customisers in collection order, and the item diagnostics followed by the exact sanitizer
messages. The include oracles are not reached (`no_include_dispatch` and `process_refines`). -/
theorem analyze_refines (A : GlobAbs) (path : std.path.Path) (source : Option std.path.PathBuf)
    (rs : Vec RItem) (items : List Item) (c : Collected)
    (hr : List.Forall₂ (fun r i => ResultRel (absSudo A) r i ∧ RenderOn r i) rs.val items)
    (hc : collect items = some c)
    (hp : ∀ r ∈ rs.val, NeedsDiagnosticPath r → DiagnosticPath path source)
    (hf : ∀ r ∈ rs.val, ItemFits r) (hb : (rs.val.map itemSize).sum ≤ Usize.max) :
    ∃ cfg diags, sudoers.analyze path rs = ok (cfg, diags) ∧ AnalysisResult A source c cfg diags := by
  obtain ⟨pre, ds, aliases, out, eq, hab, hok, hsettings, hsan, hpolicy⟩ :=
    analyze_partition A path source rs items c hr hc hp hf hb
  obtain ⟨haliases, hprefix, hmessages⟩ := sanitize_alias_tables_exact A hsan
  obtain ⟨⟨eu, eh, ec, er⟩, _, _⟩ := sanitize_alias_tables_tableWF hsan
  have written : absWrittenAliasTable A pre.aliases = c.written := by
    unfold absWrittenAliasTable
    rw [hab.user, hab.host, hab.cmnd, hab.runas]
  refine ⟨{ pre with aliases := aliases }, out, eq, ?_⟩
  refine ⟨?_, ?_, hab.nonCommand, hab.command, hsettings, hpolicy,
    hok.customisers, ⟨ds.val, hprefix, hab.diagnostics⟩, ?_, ?_⟩
  · simp only [absPolicy, policyOf, Vec.deref_val, hab.rules, haliases, written]
  · simpa only [absWrittenAliasTable, eu, eh, ec, er] using written
  · have hlocal : ds.val.map sudoers.Error.message = c.diagnostics.map Prod.snd := by
      have e := congrArg (List.map (fun x => x.2.2)) hab.diagnostics
      simpa only [List.map_map, Function.comp_def, diagnosticView, localDiagnosticView] using e
    simpa only [written, hlocal] using hmessages
  · intro clean
    have hlen := hprefix.length_le
    rw [clean, List.length_nil] at hlen
    have exactLength : out.val.length = ds.val.length := by
      rw [clean, List.length_nil]
      omega
    have sorted := absAliasTable_OK_of_sanitize hsan exactLength A
    simpa only [haliases, written, policyOf] using sorted

end SudoRsProofs.Parser.Analysis
