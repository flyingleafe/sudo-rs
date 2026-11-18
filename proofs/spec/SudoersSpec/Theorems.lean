import SudoersSpec.Authorize

/-!
# Meta-theorems about the authorization decision

All statements are about `authorize`/`checkPermission` (form (b), the Rust structure) and are
proved through form (a).
-/

namespace SudoersSpec

variable {User Group : Type} (O : Oracle User Group)

/-- Append a user specification line at the end of the policy. -/
def Policy.addRule (p : Policy) (rule : PermissionSpec) : Policy :=
  { p with rules := p.rules ++ [rule] }

/-- The line `users hosts = runas cmdspec` with a single command entry. -/
def singleLine (users : SpecList UserSpecifier) (hosts : SpecList Hostname)
    (runas : Option RunAs) (cs : CommandSpec) : PermissionSpec :=
  ⟨users, [(hosts, [(runas, cs)])]⟩

/-! ## Last match wins -/

/-- **Last match wins.** The decision is granted with tag `t` iff the final allowed entry
whose command spec takes part grants `t`. -/
theorem checkPermission_eq_some_iff (p : Policy) (r : Request User Group) (t : Tag) :
    checkPermission O p r = some t ↔
      ∃ e, IsFinalMatch (cmdParticipates O p r) (allowedSpec O p r) e ∧
        condition (cmndAliases O p r) (e.2, e.1) = some t := by
  rw [checkPermission_eq_spec, checkPermissionSpec, Option.bind_eq_some_iff]
  simp only [lastMatch_eq_some_iff]

/-- **Last match wins**, deny side: denied iff no allowed entry takes part, or the final one
that does denies. -/
theorem checkPermission_eq_none_iff (p : Policy) (r : Request User Group) :
    checkPermission O p r = none ↔
      ∀ e, IsFinalMatch (cmdParticipates O p r) (allowedSpec O p r) e →
        condition (cmndAliases O p r) (e.2, e.1) = none := by
  rw [checkPermission_eq_spec, checkPermissionSpec]
  constructor
  · intro h e he
    rw [(lastMatch_eq_some_iff _ _ _).2 he] at h
    exact h
  · intro h
    cases hl : lastMatch (cmdParticipates O p r) (allowedSpec O p r) with
    | none => rfl
    | some e => exact h e ((lastMatch_eq_some_iff _ _ _).1 hl)

/-! ## The `Sudoers::check` wrapper -/

/-- The wrapper never changes whether the request is allowed. -/
theorem authorize_isSome_iff (p : Policy) (r : Request User Group) :
    (authorize O p r).isSome = (checkPermission O p r).isSome := by
  simp [authorize]

/-- Without the root/self exception the tag of `check_permission` is returned unchanged. -/
theorem authorize_of_not_skipPasswd (p : Policy) (r : Request User Group)
    (h : skipPasswd O r = false) : authorize O p r = checkPermission O p r := by
  simp [authorize, h]

/-- **NOPASSWD rule** of `Sudoers::check`: if the invoking user is root, or runs as themself
with a group they are a member of, every granted tag says `NOPASSWD`. -/
theorem authorize_nopasswd (p : Policy) (r : Request User Group) (t : Tag)
    (h : O.isRoot r.invokingUser = true ∨
      (O.userEq r.targetUser r.invokingUser = true ∧ inGroup O r.invokingUser r.targetGroup = true))
    (ht : authorize O p r = some t) : t.authenticate = .nopasswd := by
  have hs : skipPasswd O r = true := by
    rcases h with h | ⟨h1, h2⟩ <;> simp [skipPasswd, *]
  simp only [authorize, hs, ite_true, Option.map_eq_some_iff] at ht
  obtain ⟨_, _, rfl⟩ := ht
  rfl

/-- The exact shape of the root/self exception: only the `authenticate` field changes. -/
theorem authorize_of_skipPasswd (p : Policy) (r : Request User Group)
    (h : skipPasswd O r = true) :
    authorize O p r = (checkPermission O p r).map fun t => { t with authenticate := .nopasswd } := by
  simp [authorize, h]

/-! ## Default deny -/

/-- **Default deny.** If no allowed entry's command spec takes part, the request is denied. -/
theorem default_deny (p : Policy) (r : Request User Group)
    (h : ∀ e ∈ allowedSpec O p r, cmdParticipates O p r e = false) : authorize O p r = none := by
  rw [authorize_eq_spec, authorizeSpec, checkPermissionSpec, (lastMatch_eq_none_iff _ _).2 h]
  rfl

/-- The empty policy denies everything. -/
theorem default_deny_no_rules (p : Policy) (r : Request User Group) (h : p.rules = []) :
    authorize O p r = none := by
  apply default_deny
  simp [allowedSpec, candidatesSpec, h]

/-- A policy none of whose lines applies to the invoking user denies everything. -/
theorem default_deny_no_applicable_line (p : Policy) (r : Request User Group)
    (h : ∀ rule ∈ p.rules, userListMatches O p r rule.users = false) : authorize O p r = none := by
  apply default_deny
  intro e he
  exfalso
  simp only [allowedSpec, candidatesSpec, List.mem_map, List.mem_filter, List.mem_flatMap] at he
  obtain ⟨c, ⟨⟨rule, hr, hc⟩, -⟩, -⟩ := he
  simp [h rule hr] at hc

/-! ## Appending a line -/

theorem userListMatches_addRule (p : Policy) (R : PermissionSpec) (r : Request User Group) :
    userListMatches O (p.addRule R) r = userListMatches O p r := rfl

theorem hostListMatches_addRule (p : Policy) (R : PermissionSpec) (r : Request User Group) :
    hostListMatches O (p.addRule R) r = hostListMatches O p r := rfl

/-- The candidates of a policy with a single-entry line appended. -/
theorem candidatesSpec_addRule_singleLine (p : Policy) (r : Request User Group)
    (users : SpecList UserSpecifier) (hosts : SpecList Hostname) (runas : Option RunAs)
    (cs : CommandSpec) (hu : userListMatches O p r users = true)
    (hh : hostListMatches O p r hosts = true) :
    candidatesSpec O (p.addRule (singleLine users hosts runas cs)) r =
      candidatesSpec O p r ++ [(runas, (implicitSetenv cs.cmd (applyMods cs.mods {}), cs.cmd))] := by
  simp only [candidatesSpec, userListMatches_addRule, hostListMatches_addRule]
  simp only [Policy.addRule, List.flatMap_append, singleLine, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, hu, hh, ite_true]
  congr 1
  cases runas <;> simp [distributeTagsSpec, runasInEffect, tagInEffect]

/-- The allowed entries of a policy with a single-entry line appended whose runas spec permits
the request. -/
theorem allowedSpec_addRule_singleLine (p : Policy) (r : Request User Group)
    (users : SpecList UserSpecifier) (hosts : SpecList Hostname) (runas : Option RunAs)
    (cs : CommandSpec) (hu : userListMatches O p r users = true)
    (hh : hostListMatches O p r hosts = true)
    (hra : runasPermits O r (runasUserAliases O p r) (runasGroupAliases O p r) runas = true) :
    allowedSpec O (p.addRule (singleLine users hosts runas cs)) r =
      allowedSpec O p r ++ [(implicitSetenv cs.cmd (applyMods cs.mods {}), cs.cmd)] := by
  have : allowedSpec O (p.addRule (singleLine users hosts runas cs)) r =
      ((candidatesSpec O (p.addRule (singleLine users hosts runas cs)) r).filter fun e =>
        runasPermits O r (runasUserAliases O p r) (runasGroupAliases O p r) e.1).map (·.2) := rfl
  rw [this, candidatesSpec_addRule_singleLine O p r users hosts runas cs hu hh,
    List.filter_append, List.map_append]
  simp [hra, allowedSpec]

/-- Deciding after appending a single-entry line whose user list, host list and runas spec
accept the request: if its command spec takes part it decides, otherwise nothing changes. -/
theorem checkPermission_addRule_singleLine (p : Policy) (r : Request User Group)
    (users : SpecList UserSpecifier) (hosts : SpecList Hostname) (runas : Option RunAs)
    (cs : CommandSpec) (hu : userListMatches O p r users = true)
    (hh : hostListMatches O p r hosts = true)
    (hra : runasPermits O r (runasUserAliases O p r) (runasGroupAliases O p r) runas = true) :
    checkPermission O (p.addRule (singleLine users hosts runas cs)) r =
      if matchedBy (cmndAliases O p r) (matchCommand O r.command r.arguments) cs.cmd then
        condition (cmndAliases O p r) (cs.cmd, implicitSetenv cs.cmd (applyMods cs.mods {}))
      else checkPermission O p r := by
  rw [checkPermission_eq_spec, checkPermission_eq_spec, checkPermissionSpec,
    allowedSpec_addRule_singleLine O p r users hosts runas cs hu hh hra]
  have hcp : cmdParticipates O (p.addRule (singleLine users hosts runas cs)) r =
    cmdParticipates O p r := rfl
  have hca : cmndAliases O (p.addRule (singleLine users hosts runas cs)) r =
    cmndAliases O p r := rfl
  rw [hcp, hca, lastMatch_concat]
  unfold cmdParticipates
  split <;> rfl

/-- **A trailing negated entry denies.** Appending `users hosts = runas !cmd` where the user
list, host list and runas spec accept the request and `cmd` matches the command (`ALL`, a
matching command, or an alias that contains it) denies the request, whatever came before. -/
theorem trailing_forbid_denies (p : Policy) (r : Request User Group)
    (users : SpecList UserSpecifier) (hosts : SpecList Hostname) (runas : Option RunAs)
    (mods : List Modifier) (m : Meta Command)
    (hu : userListMatches O p r users = true) (hh : hostListMatches O p r hosts = true)
    (hra : runasPermits O r (runasUserAliases O p r) (runasGroupAliases O p r) runas = true)
    (hm : matchedBy (cmndAliases O p r) (matchCommand O r.command r.arguments) (.forbid m) = true)
    (hal : ∀ k, m = .alias k → cmndAliases O p r k = some true) :
    authorize O (p.addRule (singleLine users hosts runas ⟨mods, .forbid m⟩)) r = none := by
  rw [authorize, checkPermission_addRule_singleLine O p r users hosts runas _ hu hh hra]
  simp only [hm, ite_true]
  cases m with
  | alias k => simp [condition, hal k rfl]
  | _ => rfl

/-- Special case: a trailing `!ALL` revokes everything the line's users may run there. -/
theorem trailing_forbid_all_denies (p : Policy) (r : Request User Group)
    (users : SpecList UserSpecifier) (hosts : SpecList Hostname) (runas : Option RunAs)
    (mods : List Modifier)
    (hu : userListMatches O p r users = true) (hh : hostListMatches O p r hosts = true)
    (hra : runasPermits O r (runasUserAliases O p r) (runasGroupAliases O p r) runas = true) :
    authorize O (p.addRule (singleLine users hosts runas ⟨mods, .forbid .all⟩)) r = none :=
  trailing_forbid_denies O p r users hosts runas mods .all hu hh hra rfl (by simp)

/-- **A trailing matching command grants**, with exactly the tag its modifiers build. -/
theorem trailing_allow_grants (p : Policy) (r : Request User Group)
    (users : SpecList UserSpecifier) (hosts : SpecList Hostname) (runas : Option RunAs)
    (mods : List Modifier) (c : Command)
    (hu : userListMatches O p r users = true) (hh : hostListMatches O p r hosts = true)
    (hra : runasPermits O r (runasUserAliases O p r) (runasGroupAliases O p r) runas = true)
    (hc : matchCommand O r.command r.arguments c = true) :
    checkPermission O (p.addRule (singleLine users hosts runas ⟨mods, .allow (.only c)⟩)) r =
      some (applyMods mods {}) := by
  rw [checkPermission_addRule_singleLine O p r users hosts runas _ hu hh hra]
  simp [matchedBy, Qualified.who, hc, condition, implicitSetenv]

/-! ## Lines that do not apply are irrelevant -/

/-- Policies with the same alias tables and the same candidate entries decide alike. -/
theorem authorize_congr (p q : Policy) (r : Request User Group) (ha : p.aliases = q.aliases)
    (hc : candidatesSpec O p r = candidatesSpec O q r) : authorize O p r = authorize O q r := by
  rw [authorize_eq_spec, authorize_eq_spec]
  unfold authorizeSpec checkPermissionSpec allowedSpec cmdParticipates cmndAliases
    runasUserAliases runasGroupAliases
  rw [hc, ha]

/-- **Negated users only make a line inapplicable.** Deleting a line whose user list does not
accept the invoking user (for instance `!alice ...` for alice) does not change any decision:
negation in a `User_List` cannot revoke what another line grants. -/
theorem inapplicable_line_irrelevant (p : Policy) (r : Request User Group)
    (pre post : List PermissionSpec) (R : PermissionSpec)
    (hR : userListMatches O p r R.users = false) :
    authorize O { p with rules := pre ++ R :: post } r =
      authorize O { p with rules := pre ++ post } r := by
  refine authorize_congr O { p with rules := pre ++ R :: post } { p with rules := pre ++ post } r
    rfl ?_
  simp only [candidatesSpec, List.flatMap_append, List.flatMap_cons]
  have : userListMatches O { p with rules := pre ++ R :: post } r R.users = false := hR
  simp [this]
  rfl

/-! ## Implicit SETENV -/

/-- **Implicit SETENV for ALL.** When the deciding entry is a literal `ALL`, the granted tag
carries `SETENV` unless `NOSETENV` was given explicitly. -/
theorem allow_all_setenv (p : Policy) (r : Request User Group) (e : Tag × Spec Command)
    (he : IsFinalMatch (cmdParticipates O p r) (allowedSpec O p r) e)
    (hall : e.2 = .allow .all) :
    checkPermission O p r = some e.1 ∧ (e.1.env = .setenv ∨ e.1.env = .nosetenv) := by
  refine ⟨(checkPermission_eq_some_iff O p r e.1).2 ⟨e, he, by rw [hall]; rfl⟩, ?_⟩
  obtain ⟨pre, post, hsplit, -, -⟩ := he
  have hmem : e ∈ allowedSpec O p r := by rw [hsplit]; simp
  simp only [allowedSpec, candidatesSpec, List.mem_map, List.mem_filter,
    List.mem_flatMap] at hmem
  obtain ⟨c, ⟨⟨rule, -, hc⟩, -⟩, rfl⟩ := hmem
  split at hc
  · obtain ⟨seg, -, hs⟩ := List.mem_flatMap.1 hc
    split at hs
    · exact distributeTagsSpec_allow_all_env seg.2 c hs hall
    · simp at hs
  · simp at hc

end SudoersSpec
