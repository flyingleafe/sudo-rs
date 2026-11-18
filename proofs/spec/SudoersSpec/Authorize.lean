import SudoersSpec.Oracle
import SudoersSpec.Aliases
import SudoersSpec.Distribute

/-!
# The authorization decision

Form (b) transcribes `mod.rs` `Sudoers::matching_user_specs`, `check_permission` and the flag
part of `Sudoers::check` as list folds / `filterMap`s in the iteration order of the Rust
iterators; it is the target for a refinement proof from the Aeneas extraction.

Form (a) says the same declaratively: collect every command entry of every line that applies
to the invoking user and host (with runas and tags distributed along the line), keep those
whose runas spec permits the requested target user and group, and let the final entry whose
command spec takes part decide.

`checkPermission_eq_spec` and `authorize_eq_spec` prove (a) = (b).
-/

namespace SudoersSpec

variable {User Group : Type} (O : Oracle User Group)

/-! ## Form (b): structural, following the Rust iterators -/

/-- `Sudoers::matching_user_specs`: the outer list ranges over the `Host_List = Cmnd_Spec_List`
groups of the lines whose user list matches `amUser`, filtered by the host list; the inner
lists are the distributed command entries. -/
def matchingUserSpecs (p : Policy) (amUser : User) (host : Hostname) :
    List (List MatchedCommand) :=
  let userAliases := getAliases p.aliases.user (matchUser O amUser)
  let hostAliases := getAliases p.aliases.host (matchHost O host)
  let perms := (p.rules.filterMap fun sudo =>
    (findItem (matchUser O amUser) userAliases (withUnit sudo.users)).map
      fun _ => sudo.permissions).flatten
  perms.filterMap fun seg =>
    (findItem (matchHost O host) hostAliases (withUnit seg.1)).map fun _ => distributeTags seg.2

/-- The runas test inside the `filter_map` closure of `check_permission` (`mod.rs` lines
510-520); `some ()` keeps the entry. -/
def runasCheck (r : Request User Group) (runasUserAliases runasGroupAliases : FoundAliases) :
    Option RunAs → Option Unit
  | some ra =>
    let staysInGroup := inGroup O r.targetUser r.targetGroup
    (if !O.userEq r.targetUser r.invokingUser || (staysInGroup && !ra.users.isEmpty) then
        findItem (matchUser O r.targetUser) runasUserAliases (withUnit ra.users)
      else some ()).bind fun _ =>
    if !staysInGroup then
      findItem (matchGroup O r.targetGroup) runasGroupAliases (withUnit ra.groups)
    else some ()
  | none =>
    if !(O.isRoot r.targetUser && inGroup O r.targetUser r.targetGroup) then none else some ()

/-- `runas_user_aliases` of `check_permission`. -/
def runasUserAliases (p : Policy) (r : Request User Group) : FoundAliases :=
  getAliases p.aliases.runas (matchUser O r.targetUser)

/-- `runas_group_aliases` of `check_permission`. -/
def runasGroupAliases (p : Policy) (r : Request User Group) : FoundAliases :=
  getAliases p.aliases.runas (matchGroupAlias O r.targetGroup)

/-- `cmnd_aliases` of `check_permission`. -/
def cmndAliases (p : Policy) (r : Request User Group) : FoundAliases :=
  getAliases p.aliases.cmnd (matchCommand O r.command r.arguments)

/-- `allowed_commands` of `check_permission`. -/
def allowedCommands (p : Policy) (r : Request User Group) : List (Tag × Spec Command) :=
  (matchingUserSpecs O p r.invokingUser r.host).flatten.filterMap fun e =>
    (runasCheck O r (runasUserAliases O p r) (runasGroupAliases O p r) e.1).map fun _ => e.2

/-- `mod.rs` `check_permission`. Entries are `(Tag, Spec<Command>)` in Rust; `Prod.swap`
puts the spec first as `findItem` expects (`impl WithInfo for (Tag, &Spec<Command>)`). -/
def checkPermission (p : Policy) (r : Request User Group) : Option Tag :=
  findItem (matchCommand O r.command r.arguments) (cmndAliases O p r)
    ((allowedCommands O p r).map Prod.swap)

/-- `skip_passwd` of `Sudoers::check`: the invoking user is root, or runs as themself with a
group they are in. -/
def skipPasswd (r : Request User Group) : Bool :=
  O.isRoot r.invokingUser ||
    (O.userEq r.targetUser r.invokingUser && inGroup O r.invokingUser r.targetGroup)

/-- The authorization decision: `Sudoers::check(..).flags`. `none` means "deny". -/
def authorize (p : Policy) (r : Request User Group) : Option Tag :=
  (checkPermission O p r).map fun t =>
    if skipPasswd O r then { t with authenticate := .nopasswd } else t

/-! ## Form (a): declarative -/

/-- The user list of a line accepts the invoking user. -/
def userListMatches (p : Policy) (r : Request User Group) (users : SpecList UserSpecifier) :
    Bool :=
  (findItemSpec (matchUser O r.invokingUser) (getAliases p.aliases.user (matchUser O r.invokingUser))
    (withUnit users)).isSome

/-- A host list accepts the current host. -/
def hostListMatches (p : Policy) (r : Request User Group) (hosts : SpecList Hostname) : Bool :=
  (findItemSpec (matchHost O r.host) (getAliases p.aliases.host (matchHost O r.host))
    (withUnit hosts)).isSome

/-- Every command entry, in file order, of every `Host_List = Cmnd_Spec_List` group whose
line applies to the invoking user and whose host list applies to the host. -/
def candidatesSpec (p : Policy) (r : Request User Group) : List MatchedCommand :=
  p.rules.flatMap fun rule =>
    if userListMatches O p r rule.users then
      rule.permissions.flatMap fun seg =>
        if hostListMatches O p r seg.1 then distributeTagsSpec seg.2 else []
    else []

/-- The runas rules: with an explicit `(users : groups)`, the target user must be in `users`
unless the user stays themself (and, when the target group is one of the target user's
groups, `users` is empty); the target group must be in `groups` unless it is one of the
target user's groups. Without a runas spec only root with one of root's groups is allowed. -/
def runasPermits (r : Request User Group) (RU RG : FoundAliases) : Option RunAs → Bool
  | none => O.isRoot r.targetUser && inGroup O r.targetUser r.targetGroup
  | some ra =>
    let stays := inGroup O r.targetUser r.targetGroup
    let checkUser := !O.userEq r.targetUser r.invokingUser || (stays && !ra.users.isEmpty)
    (!checkUser || (findItemSpec (matchUser O r.targetUser) RU (withUnit ra.users)).isSome) &&
      (stays || (findItemSpec (matchGroup O r.targetGroup) RG (withUnit ra.groups)).isSome)

/-- The candidates whose runas spec permits the request. -/
def allowedSpec (p : Policy) (r : Request User Group) : List (Tag × Spec Command) :=
  ((candidatesSpec O p r).filter fun e =>
    runasPermits O r (runasUserAliases O p r) (runasGroupAliases O p r) e.1).map (·.2)

/-- Does an allowed entry's command spec take part in the decision for this command? -/
def cmdParticipates (p : Policy) (r : Request User Group) (e : Tag × Spec Command) : Bool :=
  matchedBy (cmndAliases O p r) (matchCommand O r.command r.arguments) e.2

/-- Declarative `check_permission`: the final participating allowed entry decides. -/
def checkPermissionSpec (p : Policy) (r : Request User Group) : Option Tag :=
  (lastMatch (cmdParticipates O p r) (allowedSpec O p r)).bind fun e =>
    condition (cmndAliases O p r) (e.2, e.1)

/-- Declarative `Sudoers::check(..).flags`. -/
def authorizeSpec (p : Policy) (r : Request User Group) : Option Tag :=
  (checkPermissionSpec O p r).map fun t =>
    if skipPasswd O r then { t with authenticate := .nopasswd } else t

/-! ## (a) = (b) -/

theorem flatten_filterMap_map {γ δ ε : Type} (l : List γ) (o : γ → Option ε) (g : γ → List δ) :
    (l.filterMap fun x => (o x).map fun _ => g x).flatten =
      l.flatMap fun x => if (o x).isSome then g x else [] := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.filterMap_cons, List.flatMap_cons]
    cases o x <;> simp [ih]

theorem matchingUserSpecs_eq (p : Policy) (r : Request User Group) :
    (matchingUserSpecs O p r.invokingUser r.host).flatten = candidatesSpec O p r := by
  simp only [matchingUserSpecs, candidatesSpec, userListMatches, hostListMatches,
    flatten_filterMap_map, ← findItem_eq_spec, ← distributeTags_eq_spec]
  induction p.rules with
  | nil => rfl
  | cons rule rules ih =>
    simp only [List.flatMap_cons, List.flatMap_append, ih]
    split <;> simp

theorem runasCheck_eq (r : Request User Group) (RU RG : FoundAliases) (ra : Option RunAs) :
    runasCheck O r RU RG ra = if runasPermits O r RU RG ra then some () else none := by
  cases ra with
  | none =>
    simp only [runasCheck, runasPermits]
    by_cases h : (O.isRoot r.targetUser && inGroup O r.targetUser r.targetGroup) = true <;>
      simp [h]
  | some ra =>
    simp only [runasCheck, runasPermits, ← findItem_eq_spec]
    cases inGroup O r.targetUser r.targetGroup <;>
      cases O.userEq r.targetUser r.invokingUser <;>
      cases ra.users.isEmpty <;>
      cases findItem (matchUser O r.targetUser) RU (withUnit ra.users) <;>
      cases findItem (matchGroup O r.targetGroup) RG (withUnit ra.groups) <;> rfl

theorem allowedCommands_eq (p : Policy) (r : Request User Group) :
    allowedCommands O p r = allowedSpec O p r := by
  simp only [allowedCommands, allowedSpec, matchingUserSpecs_eq, runasCheck_eq]
  induction candidatesSpec O p r with
  | nil => rfl
  | cons e l ih =>
    rw [List.filterMap_cons, List.filter_cons]
    split <;> simp_all

/-- **(a) = (b)** for `check_permission`. -/
theorem checkPermission_eq_spec (p : Policy) (r : Request User Group) :
    checkPermission O p r = checkPermissionSpec O p r := by
  rw [checkPermission, findItem_eq_spec, findItemSpec, allowedCommands_eq, lastMatch_map,
    checkPermissionSpec, Option.bind_map]
  rfl

/-- **(a) = (b)** for the authorization decision. -/
theorem authorize_eq_spec (p : Policy) (r : Request User Group) :
    authorize O p r = authorizeSpec O p r := by
  rw [authorize, authorizeSpec, checkPermission_eq_spec]

end SudoersSpec
