import SudoRsProofs.FindItem
import SudoRsProofs.Commands

/-!
# `checkPermission` in the shape of the Rust loops

`SudoersSpec.checkPermission` collects the allowed entries of all applicable lines and runs one
`findItem` over them. The Rust `check_permission` (since `46d955a1`) walks the rules, then the
host groups of an applicable rule, and folds `check_commands` into a running `Option<Tag>`.
`checkRules` is that loop structure at the spec level; `checkRules_eq` proves it equal to
`checkPermission`. Pure Lean, no extracted code.
-/

open SudoersSpec

namespace SudoRsProofs

variable {α β τ : Type}

/-- `findItemStep` reads the verdict of the entry. -/
theorem findItemStep_verdict (p : β → Bool) (A : FoundAliases) (r : Option τ) (s : Spec β)
    (t : τ) :
    findItemStep p A r (s, t) =
      match itemVerdict p A s with
      | none => r
      | some true => some t
      | some false => none := by
  cases s with
  | allow m | forbid m =>
    cases m with
    | all => rfl
    | «only» x => by_cases h : p x <;> simp [findItemStep, itemVerdict, h, boolThen]
    | «alias» n =>
      rcases h : A n with _ | _ | _ <;> simp [findItemStep, itemVerdict, h, boolThen]

theorem foldl_filterMap {γ : Type} (f : γ → β → γ) (g : α → Option β) (l : List α) (acc : γ) :
    (l.filterMap g).foldl f acc =
      l.foldl (fun acc x => (g x).elim acc (f acc)) acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons x l ih =>
    rw [List.filterMap_cons, List.foldl_cons]
    cases g x <;> simp [ih]

variable {User Group : Type} (O : Oracle User Group)

/-- The verdict of the `check_permission` closure: the runas test, then the command entry's
own verdict. -/
def permVerdict (r : Request User Group) (RU RG CA : FoundAliases) : SpecVerdict :=
  fun ra cmd =>
    (runasCheck O r RU RG ra).bind fun _ =>
      itemVerdict (matchCommand O r.command r.arguments) CA cmd

theorem allowed_foldl (r : Request User Group) (RU RG CA : FoundAliases)
    (es : List MatchedCommand) (acc : Option Tag) :
    ((es.filterMap fun e => (runasCheck O r RU RG e.1).map fun _ => e.2).map Prod.swap).foldl
        (findItemStep (matchCommand O r.command r.arguments) CA) acc =
      checkCommandsSpec (permVerdict O r RU RG CA) es acc := by
  rw [List.foldl_map, foldl_filterMap, checkCommandsSpec]
  congr 1
  funext acc e
  simp only [commandsStep, permVerdict]
  cases runasCheck O r RU RG e.1 with
  | none => rfl
  | some u =>
    simp only [Option.map_some, Option.bind_some, Option.elim_some]
    rw [findItemStep_verdict]
    rfl

theorem allowed_findItem (r : Request User Group) (RU RG CA : FoundAliases)
    (es : List MatchedCommand) :
    findItem (matchCommand O r.command r.arguments) CA
        ((es.filterMap fun e => (runasCheck O r RU RG e.1).map fun _ => e.2).map Prod.swap) =
      checkCommandsSpec (permVerdict O r RU RG CA) es none :=
  allowed_foldl O r RU RG CA es none

/-- One `Host_List = Cmnd_Spec_List` group of an applicable rule. -/
def segStep (hostOK : SpecList Hostname → Bool) (V : SpecVerdict) (res : Option Tag)
    (seg : SpecList Hostname × List (Option RunAs × CommandSpec)) : Option Tag :=
  if hostOK seg.1 then checkCommandsSpec V (distributeTags seg.2) res else res

/-- One rule (user specification line). -/
def ruleStep (userOK : SpecList UserSpecifier → Bool) (hostOK : SpecList Hostname → Bool)
    (V : SpecVerdict) (res : Option Tag) (rule : PermissionSpec) : Option Tag :=
  if userOK rule.users then rule.permissions.foldl (segStep hostOK V) res else res

/-- The user-list test of a rule. -/
def userOK (p : Policy) (r : Request User Group) (us : SpecList UserSpecifier) : Bool :=
  (findItem (matchUser O r.invokingUser) (getAliases p.aliases.user (matchUser O r.invokingUser))
    (withUnit us)).isSome

/-- The host-list test of a group. -/
def hostOK (p : Policy) (r : Request User Group) (hs : SpecList Hostname) : Bool :=
  (findItem (matchHost O r.host) (getAliases p.aliases.host (matchHost O r.host))
    (withUnit hs)).isSome

/-- The verdict closure of `check_permission`, with the three alias tables of the request. -/
def policyVerdict (p : Policy) (r : Request User Group) : SpecVerdict :=
  permVerdict O r (runasUserAliases O p r) (runasGroupAliases O p r) (cmndAliases O p r)

/-- `check_permission` in the shape of the Rust loops, from an arbitrary accumulator. -/
def checkRulesFrom (p : Policy) (r : Request User Group) (rules : List PermissionSpec)
    (res : Option Tag) : Option Tag :=
  rules.foldl (ruleStep (userOK O p r) (hostOK O p r) (policyVerdict O p r)) res

theorem checkRules_eq (p : Policy) (r : Request User Group) :
    checkRulesFrom O p r p.rules none = checkPermission O p r := by
  simp only [checkPermission, allowedCommands, matchingUserSpecs]
  rw [allowed_findItem, checkCommandsSpec, List.foldl_flatten, foldl_filterMap, List.foldl_flatten,
    foldl_filterMap, checkRulesFrom]
  congr 1
  funext res rule
  simp only [ruleStep, userOK]
  rcases Option.eq_none_or_eq_some (findItem (matchUser O r.invokingUser)
      (getAliases p.aliases.user (matchUser O r.invokingUser)) (withUnit rule.users)) with
    h | ⟨u, h⟩
  · simp [h]
  · simp only [h, Option.map_some, Option.isSome_some, ite_true, Option.elim_some]
    congr 1
    funext res seg
    simp only [segStep, hostOK, checkCommandsSpec, policyVerdict]
    rcases Option.eq_none_or_eq_some (findItem (matchHost O r.host)
        (getAliases p.aliases.host (matchHost O r.host)) (withUnit seg.1)) with h' | ⟨u', h'⟩
    · simp [h']
    · simp [h']

end SudoRsProofs
