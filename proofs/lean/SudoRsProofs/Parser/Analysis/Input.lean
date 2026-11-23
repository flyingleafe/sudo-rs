import SudoRsProofs.Parser.Analysis.Collect
import SudoRsProofs.Parser.Lines

/-! Input-only bounds for PA. The reference outcomes determine the required element counts,
UTF-8 name bounds and rule/tag domains. `ProducedOn` separately records the provenance of
Rust Defaults modifiers; it is not an assumption about the analyzed policy. -/

open Aeneas Aeneas.Std Result
open Aeneas.Std.alloc.vec (Vec)
open sudo_rs

namespace SudoRsProofs.Parser.Analysis

namespace Ref

open SudoersSpec

private def defsSize (ds : List (Def α)) : Nat :=
  ds.length + (ds.map fun d => d.items.length).sum

/-- The collection/sanitizer budget, computed on reference parser outcomes alone. -/
def itemSize : Item → Nat
  | .error (.fatal ..) => 1
  | .ok (.spec r) => (SudoersSpec.Analysis.ignoredSpans r).length + 1
  | .ok (.decl (.userAlias ds)) => defsSize ds
  | .ok (.decl (.hostAlias ds)) => defsSize ds
  | .ok (.decl (.cmndAlias ds)) => defsSize ds
  | .ok (.decl (.runasAlias ds)) => defsSize ds
  | .ok (.decl (.defaults ..)) => 1
  | _ => 0

/-- A leaf is checked exactly where the matching code dereferences a name. -/
def specFits (Good : α → Prop) : Spec α → Prop
  | .allow (.alias n) | .forbid (.alias n) => Fits n
  | .allow (.only x) | .forbid (.only x) => Good x
  | _ => True

def listFits (Good : α → Prop) (xs : SpecList α) : Prop := ∀ x ∈ xs, specFits Good x

def identFits : Identifier → Prop
  | .name n => Fits n
  | .id _ => True

def userFits : UserSpecifier → Prop
  | .user i => identFits i
  | _ => True

def runasFits (r : RunAs) : Prop := listFits userFits r.users ∧ listFits identFits r.groups

def ruleFits (r : PermissionSpec) : Prop :=
  listFits userFits r.users ∧ ∀ g ∈ r.permissions,
    listFits Fits g.1 ∧ ((g.2.map fun e => e.2.mods.length).sum ≤ Usize.max) ∧
    ∀ e ∈ g.2, (∀ ra, e.1 = some ra → runasFits ra) ∧ specFits (fun _ => True) e.2.cmd

def scopeFits : Syntax.ConfigScope → Prop
  | .host xs => listFits Fits xs
  | .user xs | .runAs xs => listFits userFits xs
  | .command xs => listFits (fun _ => True) xs
  | .generic => True

def defsFit (Good : α → Prop) (ds : List (Def α)) : Prop :=
  ∀ d ∈ ds, Fits d.name ∧ listFits Good d.items

/-- All name and tag-count side conditions of collection and policy matching. -/
def itemFits : Item → Prop
  | .ok (.spec r) => ruleFits r
  | .ok (.decl (.userAlias ds)) | .ok (.decl (.runasAlias ds)) => defsFit userFits ds
  | .ok (.decl (.hostAlias ds)) => defsFit Fits ds
  | .ok (.decl (.cmndAlias ds)) => defsFit (fun _ => True) ds
  | .ok (.decl (.defaults _ scope)) => scopeFits scope
  | _ => True

def needsDiagnosticPath : Item → Prop
  | .error (.fatal ..) => True
  | .ok (.spec rule) => SudoersSpec.Analysis.ignoredSpans rule ≠ []
  | _ => False

end Ref

private theorem defsSize_abs {α β : Type} (f : α → β) (ds : Aeneas.Std.alloc.vec.Vec (RDef α)) :
    Ref.defsSize (ds.val.map (absDef f)) =
      ds.val.length + (ds.val.map fun d => d.2.val.length).sum := by
  simp [Ref.defsSize, absDef, absSpecList, List.map_map, Function.comp_def]

theorem itemSize_eq_of_rel (A : GlobAbs) {r : RItem} {i : Item}
    (h : ResultRel (absSudo A) r i) : itemSize r = Ref.itemSize i := by
  cases r with
  | Err status =>
    cases i with
    | ok _ => exact False.elim h
    | error status' =>
      change StatusRel status status' at h
      cases h <;> rfl
  | Ok line =>
    cases i with
    | error _ => exact False.elim h
    | ok l =>
      change absSudo A line = l at h
      subst l
      cases line with
      | Spec rule =>
        have e := congrArg List.length (rawIgnored_eq A rule)
        simp only [List.length_map] at e
        simp [itemSize, Ref.itemSize, absSudo, e]
      | Decl d =>
        cases d <;> simp [absSudo, absDirective, itemSize, Ref.itemSize, defsSize_abs] <;> rfl
      | _ => rfl

/-- The parsed-input budget in `analyze_refines` can be checked on the reference stream. -/
theorem itemSize_sum_eq_of_rel (A : GlobAbs) {rs : List RItem} {items : List Item}
    (hr : List.Forall₂ (ResultRel (absSudo A)) rs items) :
    (rs.map itemSize).sum = (items.map Ref.itemSize).sum := by
  induction hr with
  | nil => rfl
  | cons h _ ih => simp [itemSize_eq_of_rel A h, ih]

private theorem alias_fits_of_ref {α β : Type} (f : α → β) (good : β → Prop) (s : RSpec α)
    (hs : Ref.specFits good (absSpec f s)) (n : String) (h : aliasName s = some n) : Fits n := by
  rcases s with m | m <;> cases m <;> simp_all [Ref.specFits, absSpec, absMeta, absQualified, aliasName]

private theorem only_fits_of_ref {α β : Type} (f : α → β) (good : β → Prop) (s : RSpec α)
    (hs : Ref.specFits good (absSpec f s)) (x : α) (h : onlyItem s = some x) : good (f x) := by
  rcases s with m | m <;> cases m <;> simp_all [Ref.specFits, absSpec, absMeta, absQualified, onlyItem]

private theorem specs_fit_of_ref {α β : Type} (f : α → β) {raw : α → Prop} {ref : β → Prop}
    (lift : ∀ x, ref (f x) → raw x) (xs : List (RSpec α))
    (h : Ref.listFits ref (absSpecList f xs)) : ItemsFit xs ∧ ItemsGood raw xs := by
  have hs : ∀ s ∈ xs, Ref.specFits ref (absSpec f s) := fun s hmem =>
    h _ (List.mem_map.mpr ⟨s, hmem, rfl⟩)
  exact ⟨fun s hm n hn => alias_fits_of_ref f ref s (hs s hm) n hn,
    fun s hm x hx => lift x (only_fits_of_ref f ref s (hs s hm) x hx)⟩

private theorem ident_fits_of_ref (i : sudoers.ast.Identifier) :
    Ref.identFits (absIdentifier i) → IdentFits i := by cases i <;> exact id

private theorem user_fits_of_ref (i : sudoers.ast.UserSpecifier) :
    Ref.userFits (absUserSpecifier i) → UserSpecFits i := by
  cases i with
  | User id => exact ident_fits_of_ref id
  | _ => exact id

private theorem runas_fits_of_ref (r : sudoers.ast.RunAs)
    (h : Ref.runasFits (absRunAs r)) : RunAsOK r :=
  let hu := specs_fit_of_ref absUserSpecifier user_fits_of_ref r.users.val h.1
  let hg := specs_fit_of_ref absIdentifier ident_fits_of_ref r.groups.val h.2
  ⟨hu.1, hu.2, hg.1, hg.2⟩

private theorem rule_fits_of_ref (A : GlobAbs) (r : sudoers.ast.PermissionSpec)
    (h : Ref.ruleFits (absPermissionSpec A r)) : RuleOK r := by
  obtain ⟨uf, ug⟩ := specs_fit_of_ref absUserSpecifier user_fits_of_ref r.users.val h.1
  refine ⟨uf, ug, ?_⟩
  intro seg hm
  have hseg := h.2 (absSeg A seg) (List.mem_map.mpr ⟨seg, hm, rfl⟩)
  obtain ⟨hf, hg⟩ := specs_fit_of_ref id (fun _ => id) seg.1.val hseg.1
  refine ⟨hf, hg, ?_, ?_⟩
  · simpa [absSeg, absLine, absCommandSpec, csMods, lineMods, List.length_flatMap,
      List.map_map, Function.comp_def] using hseg.2.1
  · intro entry he
    let rentry : Option SudoersSpec.RunAs × SudoersSpec.CommandSpec :=
      (entry.1.map absRunAs, absCommandSpec (absCommand A) entry.2)
    have hh := hseg.2.2 rentry (List.mem_map.mpr ⟨entry, he, rfl⟩)
    exact ⟨fun ra hra => runas_fits_of_ref ra (hh.1 _ (by simp [rentry, hra])),
      fun n hn => alias_fits_of_ref (absCommand A) (fun _ => True) _ hh.2 n hn⟩

private theorem scope_fits_of_ref (A : GlobAbs) (s : sudoers.ast.ConfigScope)
    (h : Ref.scopeFits (absConfigScope A s)) : ScopeFits s := by
  cases s with
  | Generic => trivial
  | Host xs => exact specs_fit_of_ref id (fun _ => id) xs.val h
  | User xs | RunAs xs => exact specs_fit_of_ref absUserSpecifier user_fits_of_ref xs.val h
  | Command xs => exact (specs_fit_of_ref A.pat (raw := fun _ => True) (fun _ _ => trivial) xs.val h).1

private theorem defs_fit_of_ref {α β : Type} (f : α → β) {raw : α → Prop} {ref : β → Prop}
    (lift : ∀ x, ref (f x) → raw x) (ds : List (RDef α))
    (h : Ref.defsFit ref (ds.map (absDef f))) :
    Sanitize.DefsFit ds ∧ ∀ d ∈ ds, ItemsGood raw d.2.val := by
  have hd : ∀ d ∈ ds, Fits d.1 ∧ ItemsFit d.2.val ∧ ItemsGood raw d.2.val := by
    intro d hm
    have hdef := h (absDef f d) (List.mem_map.mpr ⟨d, hm, rfl⟩)
    exact ⟨hdef.1, specs_fit_of_ref f lift d.2.val hdef.2⟩
  exact ⟨fun d hm => ⟨(hd d hm).1, (hd d hm).2.1⟩, fun d hm => (hd d hm).2.2⟩

/-- Raw provenance, needed only on actual parsed `Defaults` modifiers. It is separate from
`Ref.itemFits` because a parser proof, not equality of the abstract directive, supplies it. -/
def ProducedOn : RItem → Prop
  | .Ok (.Decl (.Defaults mods _)) => ∀ m ∈ mods.val, Defaults.Produced m
  | _ => True

/-- Given the Rust modifier provenance, all remaining `ItemFits` conditions can be checked
on the reference parse, before any analysis is run. -/
theorem itemFits_of_rel (A : GlobAbs) {r : RItem} {i : Item}
    (h : ResultRel (absSudo A) r i) (hf : Ref.itemFits i) (hp : ProducedOn r) : ItemFits r := by
  cases r with
  | Err status => cases status <;> trivial
  | Ok line =>
    cases i with
    | error _ => exact False.elim h
    | ok l =>
      change absSudo A line = l at h
      subst l
      cases line with
      | Spec rule => exact rule_fits_of_ref A rule hf
      | Decl d =>
        cases d with
        | UserAlias ds | RunasAlias ds =>
          exact defs_fit_of_ref absUserSpecifier user_fits_of_ref ds.val hf
        | HostAlias ds => exact defs_fit_of_ref id (fun _ => id) ds.val hf
        | CmndAlias ds => exact (defs_fit_of_ref (absCommand A) (raw := fun _ => True)
            (fun _ _ => trivial) ds.val hf).1
        | Defaults mods scope => exact ⟨scope_fits_of_ref A scope hf, hp⟩
      | _ => trivial

/-- Input fit transfers through the parser relation, independently of analysis. -/
theorem itemsFit_of_rel (A : GlobAbs) {rs : List RItem} {items : List Item}
    (hr : List.Forall₂ (ResultRel (absSudo A)) rs items)
    (hf : ∀ i ∈ items, Ref.itemFits i) (hp : ∀ r ∈ rs, ProducedOn r) :
    ∀ r ∈ rs, ItemFits r := by
  induction hr with
  | nil => simp
  | @cons r i rs items h _ ih =>
    intro x hx
    rcases List.mem_cons.mp hx with he | he
    · subst x
      exact itemFits_of_rel A h (hf i (by simp)) (hp r (by simp))
    · exact ih (fun y hy => hf y (List.mem_cons_of_mem _ hy))
        (fun y hy => hp y (List.mem_cons_of_mem _ hy)) x he

theorem needsDiagnosticPath_of_rel (A : GlobAbs) {r : RItem} {i : Item}
    (h : ResultRel (absSudo A) r i) (hn : NeedsDiagnosticPath r) :
    Ref.needsDiagnosticPath i := by
  cases r with
  | Err status =>
    cases i with
    | ok _ => exact False.elim h
    | error status' =>
      change StatusRel status status' at h
      cases h with
      | fatal => exact True.intro
      | reject => exact hn
  | Ok line =>
    cases i with
    | error _ => exact False.elim h
    | ok l =>
      change absSudo A line = l at h
      subst l
      cases line with
      | Spec rule =>
        change SudoersSpec.Analysis.ignoredSpans (absPermissionSpec A rule) ≠ []
        rw [← rawIgnored_eq]
        exact fun hnil => hn (List.map_eq_nil_iff.mp hnil)
      | _ => exact False.elim hn

/-- PA with name, tag-count, report and sanitizer budget measured from the reference parser
output. The one representation premise still on raw items is modifier provenance. -/
theorem analyze_refines_of_reference (A : GlobAbs) (path : std.path.Path)
    (source : Option std.path.PathBuf) (rs : Vec RItem) (items : List Item)
    (c : SudoersSpec.Analysis.Collected)
    (hr : List.Forall₂ (ResultRel (absSudo A)) rs.val items)
    (hc : SudoersSpec.Analysis.collect items = some c)
    (hp : ∀ i ∈ items, Ref.needsDiagnosticPath i → DiagnosticPath path source)
    (hm : ∀ span k, .Err (.Fatal span k) ∈ rs.val → ∀ k',
      KindRel k k' → sudo_rs.errorKindText k = k'.render)
    (hf : ∀ i ∈ items, Ref.itemFits i) (hproduced : ∀ r ∈ rs.val, ProducedOn r)
    (hb : (items.map Ref.itemSize).sum ≤ Usize.max) :
    ∃ cfg diags, sudoers.analyze path rs = ok (cfg, diags) ∧ AnalysisResult A source c cfg diags := by
  refine analyze_refines A path source rs items c (related_rendered_items A hr hm) hc ?_
    (itemsFit_of_rel A hr hf hproduced) (by rwa [itemSize_sum_eq_of_rel A hr])
  intro r hmem hn
  obtain ⟨i, hi, hri⟩ := forall₂_mem_left hr hmem
  exact hp i hi (needsDiagnosticPath_of_rel A hri hn)

end SudoRsProofs.Parser.Analysis
