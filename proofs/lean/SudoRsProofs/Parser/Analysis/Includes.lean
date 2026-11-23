import SudoRsProofs.Parser.Analysis.Collect

/-! Conditional PA for includes. A witness elaborates a tree of oracle responses into an
ordered collection. It consumes the actual answers of the two opaque Rust leaves, not an
oracle for analyzed policies. It describes one stable snapshot; it does not model races,
secure open, or privileges. -/

open Aeneas Aeneas.Std Result
open Aeneas.Std.alloc.vec (Vec)
open sudo_rs
open sudo_rs.sudoers
open SudoersSpec.Analysis (Collected collectItem policyOf orderAliases)

namespace SudoRsProofs.Parser.Analysis.Includes

/-- Report provenance is recorded at each site. `policy.diagnostics` is kept empty: all
reports are in `reports`, because successive source files need not be the same. -/
structure Located where
  policy : Collected := {}
  reports : List Diagnostic := []

def Located.addItem (a : Located) (source : Option std.path.PathBuf) (delta : Collected) :
    Located := ⟨{ delta with diagnostics := [] },
      a.reports ++ delta.diagnostics.map (localDiagnosticView source)⟩

def Located.addReport (a : Located) (source : Option std.path.PathBuf)
    (span : basic_parser.Span) (message : String) : Located :=
  { a with reports := a.reports ++ [localDiagnosticView source (absSpan span, message)] }

/-- Three traversal loops and the directory-oracle operation; vectors record their file order.
For `listed`, this is the sorted, filtered enumeration supplied by `include_dir_files`. -/
inductive Work where
  | items (path : std.path.Path) (items : Vec RItem)
  | file (parent : std.path.Path) (candidate : IncludeFile) (span : basic_parser.Span)
  | directory (parent : std.path.Path) (raw : String) (span : basic_parser.Span)
  | listed (parent : std.path.Path) (span : basic_parser.Span) (files : Vec std.path.PathBuf)

/-- Refusal requests a diagnostic from the file oracle without permitting a read. -/
def refusal (n : U8) : Option IncludeState :=
  if n.val < 128 then none else some (.Allowed n)

/-- One regular include attempt, including unsuccessful opens. A refused attempt consumes no
budget. Directories only consume budget for each eligible entry in their returned listing. -/
inductive Attempt : U8 → U8 → Prop where
  | refused {n : U8} : 128 ≤ n.val → Attempt n n
  | allowed {n n' : U8} : n.val < 128 → n'.val = n.val + 1 → Attempt n n'

/-- Snapshot-conditioned reference elaboration. Start count, collection, end count,
collection, and number of slots needed for collection plus subsequent sanitization.

Oracle equations are only required where the traversal visits a directive. Successful include
files are elaborated before the parent's next item; directory entries are processed in the
order of the snapshot vector. Both sequence rules pass on the count of the completed child,
so siblings share the 128-attempt limit. -/
inductive Walk (A : GlobAbs) : Work → U8 → Located → U8 → Located → Nat → Prop where
  | itemsEmpty {path} {all : Vec RItem} {n a} (empty : all.val = []) :
      Walk A (.items path all) n a n a 0
  | item {path source} {all tail : Vec RItem} {raw : RItem} {ref : Item}
      {n last a out cost} {delta : Collected}
      (items : all.val = raw :: tail.val)
      (item : collectItem a.policy ref = some delta)
      (parsed : ResultRel (absSudo A) raw ref) (render : RenderOn raw ref)
      (location : NeedsDiagnosticPath raw → DiagnosticPath path source) (fits : ItemFits raw)
      (rest : Walk A (.items path tail) n (a.addItem source delta) last out cost) :
      Walk A (.items path all) n a last out (itemSize raw + cost)
  | includeItem {path raw span} {all tail : Vec RItem} {n mid last a b out c d}
      (items : all.val = .Ok (.Include raw span) :: tail.val)
      (child : Walk A (.file path (.Named raw) span) n a mid b c)
      (rest : Walk A (.items path tail) mid b last out d) :
      Walk A (.items path all) n a last out (c + d)
  | directoryItem {path raw span} {all tail : Vec RItem} {n mid last a b out c d}
      (items : all.val = .Ok (.IncludeDir raw span) :: tail.val)
      (child : Walk A (.directory path raw span) n a mid b c)
      (rest : Walk A (.items path tail) mid b last out d) :
      Walk A (.items path all) n a last out (c + d)
  | opened {parent file span owned childPath} {children : Vec RItem} {n next last a out cost}
      (within : n.val < 128) (incr : next.val = n.val + 1)
      (read : sudoers.include_file parent file (refusal n) = ok (.Ok (owned, children)))
      (view : std.path.PathBuf.as_path owned = ok childPath)
      (child : Walk A (.items childPath children) next a last out cost) :
      Walk A (.file parent file span) n a last out cost
  | openError {parent source file span message n next a}
      (attempt : Attempt n next)
      (read : sudoers.include_file parent file (refusal n) = ok (.Err message))
      (location : DiagnosticPath parent source) :
      Walk A (.file parent file span) n a next (a.addReport source span message) 1
  | directoryRead {path raw span files n last a out cost}
      (listing : sudoers.include_dir_files path raw = ok (.Ok files))
      (contents : Walk A (.listed path span files) n a last out cost) :
      Walk A (.directory path raw span) n a last out cost
  | directoryError {path source raw span message n a}
      (listing : sudoers.include_dir_files path raw = ok (.Err message))
      (location : DiagnosticPath path source) :
      Walk A (.directory path raw span) n a n (a.addReport source span message) 1
  | listedEmpty {path span} {all : Vec std.path.PathBuf} {n a} (empty : all.val = []) :
      Walk A (.listed path span all) n a n a 0
  | listedFile {path span file} {all tail : Vec std.path.PathBuf} {n mid last a b out c d}
      (files : all.val = file :: tail.val)
      (first : Walk A (.file path (.Listed file) span) n a mid b c)
      (rest : Walk A (.listed path span tail) mid b last out d) :
      Walk A (.listed path span all) n a last out (c + d)

/-- The shared attempt counter does not exceed 128 during elaboration from any valid start. -/
theorem Walk.count_le {A : GlobAbs} {w n a last out cost}
    (h : Walk A w n a last out cost) (hn : n.val ≤ 128) : last.val ≤ 128 := by
  induction h with
  | itemsEmpty | listedEmpty | directoryError => exact hn
  | item _ _ _ _ _ _ _ ih => exact ih hn
  | includeItem _ _ _ before after | directoryItem _ _ _ before after
  | listedFile _ _ _ before after => exact after (before hn)
  | opened within incr _ _ _ ih => exact ih (by omega)
  | openError attempt _ _ => cases attempt with
    | refused _ => exact hn
    | allowed hlt he => omega
  | directoryRead _ _ ih => exact ih hn

private def Rel (A : GlobAbs) (cfg : Sudoers) (ds : Vec sudoers.Error) (a : Located) : Prop :=
  CollectedRel A none cfg ds a.policy a.reports ∧ a.policy.diagnostics = []

private theorem Rel.diagnostics {A : GlobAbs} {cfg ds a} (h : Rel A cfg ds a) :
    ds.val.map diagnosticView = a.reports := by
  simpa [h.2] using h.1.diagnostics

private abbrev RawState := Sudoers × Vec sudoers.Error × IncludeState

private def vecIter {T : Type} (v : Vec T) : alloc.vec.into_iter.IntoIter T := v

private def execution (cfg : Sudoers) (ds : Vec sudoers.Error) (state : IncludeState) :
    Work → Result RawState
  | .items path items => sudoers.process_loop cfg path ds state (vecIter items) true
  | .file path file span => sudoers.include cfg path file span ds state
  | .directory path dir span => sudoers.include_dir cfg path dir span ds state
  | .listed path span files => sudoers.include_dir_loop cfg path span ds state (vecIter files) true

private def Post (A : GlobAbs) (cfg : Sudoers) (ds : Vec sudoers.Error) (n : U8)
    (a : Located) (cost : Nat) (out : RawState) : Prop :=
  Rel A out.1 out.2.1 a ∧ CollectorOK out.1 ∧ out.1.settings = cfg.settings ∧
    out.2.2 = .Allowed n ∧ collectSize out.1 out.2.1 = collectSize cfg ds + cost

private theorem combine {A : GlobAbs} {cfg ds mid last b out c d}
    {head : Result RawState} {rest : RawState → Result RawState}
    (h : head ⦃ s => Post A cfg ds mid b c s ⦄)
    (t : ∀ cfg' ds', Rel A cfg' ds' b → CollectorOK cfg' →
      collectSize cfg' ds' + d ≤ Usize.max →
      rest (cfg', ds', .Allowed mid) ⦃ s => Post A cfg' ds' last out d s ⦄)
    (bound : collectSize cfg ds + (c + d) ≤ Usize.max) :
    Std.bind head rest ⦃ s => Post A cfg ds last out (c + d) s ⦄ := by
  apply WP.spec_bind h
  rintro ⟨cfg', ds', st'⟩ hs
  rcases hs with ⟨hm, hok, hsettings, rfl, hcost⟩
  have enough : collectSize cfg' ds' + d ≤ Usize.max := by
    change collectSize cfg' ds' = collectSize cfg ds + c at hcost
    omega
  apply WP.spec_mono (t cfg' ds' hm hok enough)
  rintro ⟨cfg'', ds'', st''⟩ ⟨hr, hOK, hsettings', hst, hlen⟩
  exact ⟨hr, hOK, hsettings'.trans hsettings, hst, by simpa [Post, hcost, Nat.add_assoc] using hlen⟩

private theorem iterator_cons {T : Type} {xs ys : Vec T} {x : T}
    (h : xs.val = x :: ys.val) :
    alloc.vec.into_iter.IteratorIntoIter.next (vecIter xs) = ok (some x, vecIter ys) := by
  obtain ⟨rest, e, hrest⟩ := intoIter_next_cons (vecIter xs) h
  have eq : rest = vecIter ys := Vec.ext rest ys hrest
  rw [e, eq]

private theorem process_eq_loop (cfg : Sudoers) (path : std.path.Path) (xs : Vec RItem)
    (ds : Vec sudoers.Error) (st : IncludeState) :
    sudoers.process cfg path xs ds st = sudoers.process_loop cfg path ds st (vecIter xs) true := by
  rw [sudoers.process]
  exact Std.bind_ok _ _

private theorem include_read_eq (cfg : Sudoers) (parent : std.path.Path) (file : IncludeFile)
    (span : basic_parser.Span) (ds : Vec sudoers.Error) {n next : U8} (ha : Attempt n next)
    (r : core.result.Result (std.path.PathBuf × Vec RItem) String)
    (h : sudoers.include_file parent file (refusal n) = ok r) :
    sudoers.include cfg parent file span ds (.Allowed n) =
      (match r with
      | .Ok (path, xs) => do
        let child ← std.path.PathBuf.as_path path
        sudoers.process_loop cfg child ds (.Allowed next) (vecIter xs) true
      | .Err message => do
        let reports ← sudoers.report ds parent span message
        ok (cfg, reports, .Allowed next)) := by
  simp only [sudoers.include, sudoers.IncludeState.limit_reached, sudoers.INCLUDE_LIMIT,
    Std.bind_ok]
  cases ha with
  | refused hge =>
    have ge : n ≥ 128#u8 := hge
    have no : ¬ n.val < 128 := by omega
    rw [refusal, ite_eq_right no] at h
    simp only [ge, decide_true, ↓reduceIte, Std.bind_ok, h]
    cases r with
    | Ok p => rcases p with ⟨path, xs⟩; simp only [process_eq_loop]; rfl
    | Err _ => rfl
  | allowed hlt he =>
    have lt : ¬ n ≥ 128#u8 := by exact fun hx => Nat.not_le_of_gt hlt hx
    rw [refusal, ite_eq_left hlt] at h
    have incr : n + 1#u8 = ok next := by
      have e : (1#u8 : U8).val = 1 := rfl
      have max : U8.max = 255 := by scalar_tac
      have ha : n.val + (1#u8 : U8).val ≤ U8.max := by omega
      apply eq_ok_of_spec
      apply WP.spec_mono (U8.add_spec ha)
      intro x hx
      apply UScalar.val_eq_imp_iff.mpr
      omega
    simp only [lt, decide_false, Bool.false_eq_true, ite_false, Std.bind_ok, h,
      sudoers.IncludeState.inc, incr]
    cases r with
    | Ok p => rcases p with ⟨path, xs⟩; simp only [process_eq_loop]; rfl
    | Err _ => rfl

private theorem item_spec (A : GlobAbs) (path : std.path.Path) (source : Option std.path.PathBuf)
    (cfg : Sudoers) (ds : Vec sudoers.Error) (n : U8)
    (raw : RItem) (ref : Item) (a : Located) (delta : Collected)
    (hc : collectItem a.policy ref = some delta) (hr : ResultRel (absSudo A) raw ref)
    (hm : RenderOn raw ref) (hp : NeedsDiagnosticPath raw → DiagnosticPath path source)
    (hf : ItemFits raw) (hab : Rel A cfg ds a) (hok : CollectorOK cfg)
    (hb : collectSize cfg ds + itemSize raw ≤ Usize.max) :
    sudoers.process_item cfg path raw ds (.Allowed n) ⦃ out =>
      Post A cfg ds n (a.addItem source delta) (itemSize raw) out ⦄ := by
  have sourceRel : CollectedRel A source cfg ds a.policy a.reports :=
    { hab.1 with diagnostics := by simp [hab.2, hab.diagnostics] }
  apply WP.spec_mono (process_item_refines A path source cfg ds (.Allowed n)
    raw ref a.policy delta hc hr hm hp hf hok sourceRel hb)
  intro out h
  refine ⟨⟨{ h.1 with diagnostics := ?_ }, rfl⟩, h.2⟩
  simpa [Located.addItem] using h.1.diagnostics

private theorem report_post (A : GlobAbs) (path : std.path.Path) (source : Option std.path.PathBuf)
    (span : basic_parser.Span) (message : String)
    (cfg : Sudoers) (ds : Vec sudoers.Error) (n : U8) (a : Located)
    (hp : DiagnosticPath path source) (hab : Rel A cfg ds a) (hok : CollectorOK cfg)
    (hb : collectSize cfg ds + 1 ≤ Usize.max) :
    (do
      let ds' ← sudoers.report ds path span message
      ok (cfg, ds', IncludeState.Allowed n)) ⦃ out =>
        Post A cfg ds n (a.addReport source span message) 1 out ⦄ := by
  have room : ds.val.length < Usize.max := by unfold collectSize at hb; omega
  apply WP.spec_bind (report_spec path source span message ds hp room)
  intro next hnext
  apply spec_of_eq_ok rfl
  refine ⟨⟨{ hab.1 with diagnostics := ?_ }, hab.2⟩, hok, rfl, rfl, ?_⟩
  · simp [Located.addReport, hnext, hab.2, hab.diagnostics, diagnosticView, localDiagnosticView,
      rawReport]
  · simp only [collectSize, hnext, List.length_append, List.length_singleton]
    omega

private theorem walk_returns {A : GlobAbs} {job n a last out cost}
    (h : Walk A job n a last out cost)
    (cfg : Sudoers) (ds : Vec sudoers.Error) (hab : Rel A cfg ds a) (hok : CollectorOK cfg)
    (hb : collectSize cfg ds + cost ≤ Usize.max) :
    execution cfg ds (.Allowed n) job ⦃ v => Post A cfg ds last out cost v ⦄ := by
  induction h generalizing cfg ds with
  | @itemsEmpty path all n a hnil =>
    change sudoers.process_loop cfg path ds (.Allowed n) (vecIter all) true ⦃ v =>
      Post A cfg ds n a 0 v ⦄
    rw [sudoers.process_loop, ite_eq_left rfl, intoIter_next_nil (vecIter all) hnil]
    simp only [Std.bind_ok, uncurry_apply_pair]
    rw [sudoers.process_loop, ite_eq_right (by decide : ¬false = true)]
    exact spec_of_eq_ok rfl ⟨hab, hok, rfl, rfl, (Nat.add_zero _).symm⟩
  | @item path source all tail raw ref n last a out cost delta hcons hc hr hm hp hf _ ih =>
    change sudoers.process_loop cfg path ds (.Allowed n) (vecIter all) true ⦃ v =>
      Post A cfg ds last out (itemSize raw + cost) v ⦄
    rw [sudoers.process_loop, ite_eq_left rfl, iterator_cons hcons]
    simp only [Std.bind_ok, uncurry_apply_pair]
    apply combine (item_spec A path source cfg ds n raw ref a delta hc hr hm hp hf hab hok (by omega))
      ?_ hb
    intro cfg' ds' e g bound
    simpa only [execution, uncurry_apply_pair] using ih cfg' ds' e g bound
  | @includeItem path raw span all tail n mid last a b out c d hcons _ _ child ih =>
    change sudoers.process_loop cfg path ds (.Allowed n) (vecIter all) true ⦃ v =>
      Post A cfg ds last out (c + d) v ⦄
    rw [sudoers.process_loop, ite_eq_left rfl, iterator_cons hcons]
    simp only [Std.bind_ok, uncurry_apply_pair]
    rw [sudoers.process_item]
    apply combine (child cfg ds hab hok (by omega)) ?_ hb
    intro cfg' ds' e g bound
    simpa only [execution, uncurry_apply_pair] using ih cfg' ds' e g bound
  | @directoryItem path raw span all tail n mid last a b out c d hcons _ _ child ih =>
    change sudoers.process_loop cfg path ds (.Allowed n) (vecIter all) true ⦃ v =>
      Post A cfg ds last out (c + d) v ⦄
    rw [sudoers.process_loop, ite_eq_left rfl, iterator_cons hcons]
    simp only [Std.bind_ok, uncurry_apply_pair]
    rw [sudoers.process_item]
    apply combine (child cfg ds hab hok (by omega)) ?_ hb
    intro cfg' ds' e g bound
    simpa only [execution, uncurry_apply_pair] using ih cfg' ds' e g bound
  | @opened parent file span owned childPath children n next last a out cost hlt hincr he hv _ ih =>
    simp only [execution]
    rw [include_read_eq cfg parent file span ds (.allowed hlt hincr) _ he]
    simp only [hv, Std.bind_ok]
    exact ih cfg ds hab hok hb
  | @openError parent source file span message n next a ha he hp =>
    simp only [execution]
    rw [include_read_eq cfg parent file span ds ha _ he]
    exact report_post A parent source span message cfg ds next a hp hab hok hb
  | @directoryRead path raw span files n last a out cost he _ ih =>
    simp only [execution]
    rw [sudoers.include_dir, he]
    simp only [Std.bind_ok]
    rw [show alloc.vec.IntoIteratorVec.into_iter files = ok (vecIter files) from rfl, Std.bind_ok]
    exact ih cfg ds hab hok hb
  | @directoryError path source raw span message n a he hp =>
    simp only [execution]
    rw [sudoers.include_dir, he]
    simp only [Std.bind_ok]
    exact report_post A path source span message cfg ds n a hp hab hok hb
  | @listedEmpty path span all n a hnil =>
    change sudoers.include_dir_loop cfg path span ds (.Allowed n) (vecIter all) true ⦃ v =>
      Post A cfg ds n a 0 v ⦄
    rw [sudoers.include_dir_loop, ite_eq_left rfl, intoIter_next_nil (vecIter all) hnil]
    simp only [Std.bind_ok, uncurry_apply_pair]
    rw [sudoers.include_dir_loop, ite_eq_right (by decide : ¬false = true)]
    exact spec_of_eq_ok rfl ⟨hab, hok, rfl, rfl, (Nat.add_zero _).symm⟩
  | @listedFile path span file all tail n mid last a b out c d hcons _ _ child ih =>
    change sudoers.include_dir_loop cfg path span ds (.Allowed n) (vecIter all) true ⦃ v =>
      Post A cfg ds last out (c + d) v ⦄
    rw [sudoers.include_dir_loop, ite_eq_left rfl, iterator_cons hcons]
    simp only [Std.bind_ok, uncurry_apply_pair]
    apply combine (child cfg ds hab hok (by omega)) ?_ hb
    intro cfg' ds' e g bound
    simpa only [execution, uncurry_apply_pair] using ih cfg' ds' e g bound

/-- Replay a finite snapshot elaboration through the real `process`, including the actual
returned include counter. The reference cost bounds all pushes by the traversal and leaves
enough capacity for the alias sanitizer. -/
theorem process_refines (A : GlobAbs) (path : std.path.Path) (items : Vec RItem)
    (n last : U8) (a out : Located) (cost : Nat)
    (hwalk : Walk A (.items path items) n a last out cost)
    (cfg : Sudoers) (ds : Vec sudoers.Error)
    (hab : CollectedRel A none cfg ds a.policy a.reports) (hdiag : a.policy.diagnostics = [])
    (hok : CollectorOK cfg) (hb : collectSize cfg ds + cost ≤ Usize.max) :
    ∃ cfg' ds',
      sudoers.process cfg path items ds (.Allowed n) = ok (cfg', ds', .Allowed last) ∧
      CollectedRel A none cfg' ds' out.policy out.reports ∧ out.policy.diagnostics = [] ∧
      CollectorOK cfg' ∧ cfg'.settings = cfg.settings ∧
      collectSize cfg' ds' = collectSize cfg ds + cost := by
  obtain ⟨⟨cfg', ds', st⟩, hrun, hout, hgood, hsettings, hcount, hbudget⟩ :=
    exists_eq_ok_of_spec (walk_returns hwalk cfg ds ⟨hab, hdiag⟩ hok hb)
  change st = .Allowed last at hcount
  subst st
  refine ⟨cfg', ds', ?_, hout.1, hout.2, hgood, hsettings, hbudget⟩
  rw [process_eq_loop]
  exact hrun

/-- PA with includes, conditional on a finite elaboration of actual oracle answers.
It establishes written-order collection, child and parent report provenance, exact sanitized
policy, and the output domains needed by the decision. No sortedness assumption is imposed
on the alias tables; directory order is that of the snapshot's listing. -/
theorem analyze_refines (A : GlobAbs) (path : std.path.Path) (items : Vec RItem)
    (n : U8) (c : Located) (cost : Nat)
    (hwalk : Walk A (.items path items) 0#u8 {} n c cost) (hb : cost ≤ Usize.max) :
    ∃ cfg ds traversalReports,
      sudoers.analyze path items = ok (cfg, ds) ∧
      absPolicy A (Vec.deref cfg.rules) cfg.aliases = policyOf c.policy ∧
      absWrittenAliasTable A cfg.aliases = c.policy.written ∧
      absNonCommand cfg.customisers.non_cmnd = c.policy.nonCommand ∧
      absCommandCustomisers A cfg.customisers.cmnd = c.policy.command ∧
      Defaults.absSettings cfg.settings = Defaults.initialModel ∧
      PolicyOK (Vec.deref cfg.rules) cfg.aliases ∧ CustomisersOK cfg.customisers ∧
      traversalReports <+: ds.val ∧ traversalReports.map diagnosticView = c.reports ∧
      ds.val.map sudoers.Error.message = c.reports.map (fun x => x.2.2) ++
        (orderAliases c.policy.written).2 := by
  obtain ⟨initial, hi, hok, hab, hzero, hs⟩ := default_collection_seed A
  let d0 := Vec.new sudoers.Error
  have bound : collectSize initial d0 + cost ≤ Usize.max := by simpa [d0, hzero] using hb
  obtain ⟨⟨pre, diags, st⟩, hrun, hlocal, hgood, hsettings, _, hbudget⟩ :=
    exists_eq_ok_of_spec (walk_returns hwalk initial d0 ⟨hab, rfl⟩ hok bound)
  change collectSize pre diags = collectSize initial d0 + cost at hbudget
  have hsbound : diags.val.length + tableSize pre.aliases.user + tableSize pre.aliases.host +
      tableSize pre.aliases.cmnd + tableSize pre.aliases.runas ≤ Usize.max := by
    change collectSize pre diags = collectSize initial (Vec.new _) + cost at hbudget
    rw [hzero, Nat.zero_add] at hbudget
    unfold collectSize at hbudget
    omega
  obtain ⟨aliases, reports, hsan, ha, hprefix, hmessages⟩ :=
    sanitize_alias_tables_exact_returns A pre.aliases diags
      hgood.user.1 hgood.host.1 hgood.cmnd hgood.runas.1 hsbound
  obtain ⟨⟨eu, eh, ec, er⟩, _, _⟩ := sanitize_alias_tables_tableWF hsan
  have written : absWrittenAliasTable A pre.aliases = c.policy.written := by
    unfold absWrittenAliasTable
    rw [hlocal.1.user, hlocal.1.host, hlocal.1.cmnd, hlocal.1.runas]
  have hop : PolicyOK (Vec.deref pre.rules) aliases :=
    ⟨AliasTableOK.of_sanitize_alias_tables hsan hgood.user.1 hgood.user.2 hgood.host.1
      hgood.host.2 hgood.cmnd hgood.runas.1 hgood.runas.2, by simpa using hgood.rules⟩
  refine ⟨{ pre with aliases := aliases }, reports, diags.val, ?_, ?_, ?_,
    hlocal.1.nonCommand, hlocal.1.command, (congrArg Defaults.absSettings hsettings).trans hs,
    hop, hgood.customisers, hprefix, hlocal.diagnostics, ?_⟩
  · rw [sudoers.analyze, hi]
    simp only [execution, d0] at hrun
    simp only [Std.bind_ok, process_eq_loop, hrun, uncurry_apply_pair, hsan]
  · simp only [absPolicy, policyOf, Vec.deref_val, hlocal.1.rules, ha, written]
  · simpa only [absWrittenAliasTable, eu, eh, ec, er] using written
  · have messages : diags.val.map sudoers.Error.message = c.reports.map (fun x => x.2.2) := by
      have equality := congrArg (List.map (fun x => x.2.2)) hlocal.diagnostics
      simpa only [List.map_map, Function.comp_def, diagnosticView] using equality
    simpa only [written, messages] using hmessages

end SudoRsProofs.Parser.Analysis.Includes
