import SudoersSpec.Properties

/-!
# The runas rule read off the manual, for lists without `!`

`runasManual` transcribes what `docs/man/sudoers.5.md` (fork head) says a `Runas_Spec` permits,
for runas lists without `!`; `runasPermits_eq_manual` proves that the sudo-rs rule
(`runasPermits`, `mod.rs` `check_permission`) agrees with it except in exactly three situations,
F2, F4 and F5 of `proofs/differential/README.md`, and gives the sudo-rs value there.
`Certificates.lean` has a kernel-checked example of each disagreement.

## The manual text used

sudoers.5 line 222 (Runas_Spec):

> A Runas_Spec determines the user and/or the group that a command may be run as. [...] The
> first Runas_List indicates which users the command may be run as via the -u option. The second
> defines a list of groups that may be specified via the -g option (in addition to any of the
> target user's groups). If both Runas_Lists are specified, the command may be run with any
> combination of users and groups listed in their respective Runas_Lists. If only the first is
> specified, the command may be run as any user in the list and, optionally, with any group the
> target user belongs to. If the first Runas_List is empty but the second is specified, the
> command may be run as the invoking user with the group set to any listed in the Runas_List. If
> both Runas_Lists are empty, the command may only be run as the invoking user and the group, if
> specified, must be one that the invoking user is a member of. If no Runas_Spec is specified,
> the command may only be run as root and the group, if specified, must be one that root is a
> member of.

sudoers.5 lines 238-247, for `dgb boulder = (operator : operator) /bin/ls, ...`:

> Note that while the group portion of the Runas_Spec permits the user to run as command with
> that group, it does not force the user to do so. [...] The following would all be permitted
> by the sudoers entry above:
>     $ sudo -u operator /bin/ls
>     $ sudo -u operator -g operator /bin/ls
>     $ sudo -g operator /bin/ls

sudoers.5 lines 249-256, for `tcm boulder = (:dialer) /usr/bin/tip, ...`: "only the group will be
set, the command still runs as user tcm. E.g. `$ sudo -g dialer /usr/bin/cu`".

sudoers.5 line 128: "Note that user names and groups are matched as strings. In other words,
two users (groups) with the same user (group) ID are considered to be distinct."

sudo.8 line 148: `-u` "Run the command as another user than the default (root)"; line 61:
`-g` "Use this group as the primary group instead of [the target user's]".

## Reading

* `-g` without `-u` runs as the invoking user (sudoers.5 254; `src/common/resolve.rs`
  `resolve_target_user_and_group` does the same). The request the decision sees has the
  invoking user as target in that case, and nothing records that `-u` was absent; the manual
  distinguishes the two (`sudo -g operator` is permitted for dgb, who is not in `(operator)`).
  `runasManual` therefore takes `gOnly` ("`-g` was given without `-u`") as a parameter; it
  can only be `true` when the target is the invoking user.
* "the group, if specified" / "optionally": the request always carries a group (the target
  user's primary group when `-g` is absent), which is one of the target user's groups, so "a
  group the target user belongs to" covers the unspecified case.
* "in addition to any of the target user's groups" applies wherever a group list is given.
* A list is "specified" when it is non-empty: `(root)` and `(root :)` have an empty group list
  in the parsed form.
* Members: `user name`, `#uid`, `%group`, `%#gid` and `ALL` are matched with the oracle
  matchers (`matchUser`, `matchGroup`); names are compared as strings by `Oracle.hasName`.
  **Runas_Aliases are included**: a member `ALIAS` counts when the alias table affirms the item
  (`A n = some true`). For alias tables without `!` that is plain membership
  (`getAliases_ne_false`, `runasAliases_ne_false`). How a target *group* is matched against a
  Runas_Alias is not described by the manual; the table the code builds for it
  (`runasGroupAliases`, `match_group_alias`) is used (finding 15 of `proofs/spec/README.md`).
* No Runas_Spec: "only as root" is read with line 128: the target user is the user *named*
  `root`.
-/

namespace SudoersSpec

variable {User Group : Type} (O : Oracle User Group)

/-- One member of a Runas_List without `!` contains the item. -/
def memberHas {α : Type} (pred : α → Bool) (A : FoundAliases) : Spec α → Bool
  | .allow .all => true
  | .allow (.only x) => pred x
  | .allow (.alias n) => A n == some true
  | .forbid _ => false

/-- The Runas_List contains the item. -/
def listHas {α : Type} (pred : α → Bool) (A : FoundAliases) (l : SpecList α) : Bool :=
  l.any (memberHas pred A)

/-- A list without `!`. -/
def Positive {α : Type} (l : SpecList α) : Prop := ∀ s ∈ l, s.isAllow = true

instance {α : Type} (l : SpecList α) : Decidable (Positive l) := by
  unfold Positive; infer_instance

/-- **The manual's runas rule** for lists without `!` (sudoers.5 222, 238-256, 128). `gOnly`:
`-g` was given without `-u`, so the target user is the invoking user. -/
def runasManual (r : Request User Group) (RU RG : FoundAliases) (gOnly : Bool) :
    Option RunAs → Bool
  -- "If no Runas_Spec is specified, the command may only be run as root and the group, if
  -- specified, must be one that root is a member of." Names are matched as strings (128).
  | none => O.hasName r.targetUser "root" && inGroup O r.targetUser r.targetGroup
  | some ra =>
    let userListed := listHas (matchUser O r.targetUser) RU ra.users
    -- "a list of groups that may be specified via the -g option (in addition to any of the
    -- target user's groups)"
    let groupOK := listHas (matchGroup O r.targetGroup) RG ra.groups ||
      inGroup O r.targetUser r.targetGroup
    let self := O.userEq r.targetUser r.invokingUser
    if !ra.users.isEmpty && !ra.groups.isEmpty then
      -- "If both Runas_Lists are specified, the command may be run with any combination of
      -- users and groups listed"; the group portion "does not force the user" to change user:
      -- `sudo -g operator` is permitted (238-247).
      (gOnly || userListed) && groupOK
    else if !ra.users.isEmpty then
      -- "If only the first is specified, the command may be run as any user in the list and,
      -- optionally, with any group the target user belongs to."
      userListed && inGroup O r.targetUser r.targetGroup
    else if !ra.groups.isEmpty then
      -- "If the first Runas_List is empty but the second is specified, the command may be run
      -- as the invoking user with the group set to any listed in the Runas_List."
      self && groupOK
    else
      -- "If both Runas_Lists are empty, the command may only be run as the invoking user and
      -- the group, if specified, must be one that the invoking user is a member of."
      self && inGroup O r.targetUser r.targetGroup

/-! ## The disagreements -/

/-- F2, sudo-rs allows, the manual denies: a uid-0 target not named `root` without a runas
spec (`toor`). -/
def F2Allows (r : Request User Group) : Bool :=
  O.isRoot r.targetUser && !O.hasName r.targetUser "root" && inGroup O r.targetUser r.targetGroup

/-- F2, the manual allows, sudo-rs denies: a target named `root` whose uid is not 0. -/
def F2Denies (r : Request User Group) : Bool :=
  !O.isRoot r.targetUser && O.hasName r.targetUser "root"

/-- F4, the manual allows, sudo-rs denies: `sudo -g grp` where the invoker is in `grp`, both
lists are given and the user list does not contain the invoker. -/
def F4Case (r : Request User Group) (RU : FoundAliases) (gOnly : Bool) (ra : RunAs) : Bool :=
  gOnly && O.userEq r.targetUser r.invokingUser && inGroup O r.targetUser r.targetGroup &&
    !ra.users.isEmpty && !ra.groups.isEmpty && !listHas (matchUser O r.targetUser) RU ra.users

/-- F5, sudo-rs allows, the manual denies: `sudo -u self -g grp` where the invoker is not in
`grp`, `grp` is listed, and the user list does not contain the invoker. -/
def F5Case (r : Request User Group) (RU RG : FoundAliases) (gOnly : Bool) (ra : RunAs) : Bool :=
  !gOnly && O.userEq r.targetUser r.invokingUser && !inGroup O r.targetUser r.targetGroup &&
    !ra.users.isEmpty && !ra.groups.isEmpty && !listHas (matchUser O r.targetUser) RU ra.users &&
    listHas (matchGroup O r.targetGroup) RG ra.groups

/-! ## Agreement -/

theorem memberHas_eq_matchedBy {α : Type} (pred : α → Bool) (A : FoundAliases)
    (hA : ∀ n, A n ≠ some false) (s : Spec α) (hs : s.isAllow = true) :
    memberHas pred A s = matchedBy A pred s := by
  cases s with
  | forbid m => simp [Qualified.isAllow] at hs
  | allow m =>
    cases m with
    | all => rfl
    | only x => rfl
    | alias n =>
      have := hA n
      simp only [memberHas, matchedBy, Qualified.who]
      cases h : A n with
      | none => rfl
      | some b => cases b <;> simp_all

theorem lastMatch_isSome {β : Type} (p : β → Bool) (l : List β) :
    (lastMatch p l).isSome = l.any p := by
  cases h : lastMatch p l with
  | none =>
    have := (lastMatch_eq_none_iff p l).1 h
    symm
    simpa [List.any_eq_false] using this
  | some x =>
    obtain ⟨hx, hp⟩ := lastMatch_spec h
    symm
    exact List.any_eq_true.2 ⟨x, hx, hp⟩

/-- **For lists without `!` and alias tables without explicit exclusions, `find_item` is plain
membership.** -/
theorem findItemSpec_isSome_positive {α : Type} (pred : α → Bool) (A : FoundAliases)
    (hA : ∀ n, A n ≠ some false) (l : SpecList α) (hl : Positive l) :
    (findItemSpec pred A (withUnit l)).isSome = listHas pred A l := by
  have hlm := lastMatch_withUnit (matchedBy A pred) l
  have hany : l.any (memberHas pred A) = l.any (matchedBy A pred) := by
    rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
    constructor
    · rintro ⟨s, hs, h⟩
      exact ⟨s, hs, by rwa [← memberHas_eq_matchedBy pred A hA s (hl s hs)]⟩
    · rintro ⟨s, hs, h⟩
      exact ⟨s, hs, by rwa [memberHas_eq_matchedBy pred A hA s (hl s hs)]⟩
  unfold findItemSpec listHas
  rw [hlm, hany, ← lastMatch_isSome]
  cases h : lastMatch (matchedBy A pred) l with
  | none => rfl
  | some s =>
    obtain ⟨hs, hm⟩ := lastMatch_spec h
    simp only [Option.map_some, Option.bind_some, Option.isSome_some]
    cases s with
    | forbid m => have := hl _ hs; simp [Qualified.isAllow] at this
    | allow m =>
      cases m with
      | all => rfl
      | only x => rfl
      | alias n =>
        have := hA n
        simp only [matchedBy, Qualified.who] at hm
        simp only [condition]
        cases hn : A n with
        | none => rw [hn] at hm; cases hm
        | some b => cases b <;> simp_all

/-- **`runasPermits` against the manual, explicit runas spec, lists without `!`.** sudo-rs
agrees with `runasManual` except in case F4 (the manual allows, sudo-rs denies) and F5 (the
manual denies, sudo-rs allows). -/
theorem runasPermits_eq_manual (r : Request User Group) (RU RG : FoundAliases) (gOnly : Bool)
    (ra : RunAs) (hg : gOnly = true → O.userEq r.targetUser r.invokingUser = true)
    (hu : Positive ra.users) (hgr : Positive ra.groups)
    (hRU : ∀ n, RU n ≠ some false) (hRG : ∀ n, RG n ≠ some false) :
    runasPermits O r RU RG (some ra) =
      ((runasManual O r RU RG gOnly (some ra) && !F4Case O r RU gOnly ra) ||
        F5Case O r RU RG gOnly ra) := by
  rw [runasPermits_some_eq, findItemSpec_isSome_positive _ _ hRU _ hu,
    findItemSpec_isSome_positive _ _ hRG _ hgr]
  simp only [runasManual, F4Case, F5Case]
  have hc : ra.users.isEmpty = true → listHas (matchUser O r.targetUser) RU ra.users = false := by
    intro h; simp [List.isEmpty_iff.1 h, listHas]
  have hd : ra.groups.isEmpty = true →
      listHas (matchGroup O r.targetGroup) RG ra.groups = false := by
    intro h; simp [List.isEmpty_iff.1 h, listHas]
  revert hg hc hd
  generalize O.userEq r.targetUser r.invokingUser = a
  generalize inGroup O r.targetUser r.targetGroup = b
  generalize ra.users.isEmpty = c
  generalize ra.groups.isEmpty = d
  generalize listHas (matchUser O r.targetUser) RU ra.users = x
  generalize listHas (matchGroup O r.targetGroup) RG ra.groups = y
  cases gOnly <;> cases a <;> cases b <;> cases c <;> cases d <;> cases x <;> cases y <;> simp

/-- Outside F4 and F5 the two rules agree. -/
theorem runasPermits_eq_manual_of_not (r : Request User Group) (RU RG : FoundAliases)
    (gOnly : Bool) (ra : RunAs) (hg : gOnly = true → O.userEq r.targetUser r.invokingUser = true)
    (hu : Positive ra.users) (hgr : Positive ra.groups)
    (hRU : ∀ n, RU n ≠ some false) (hRG : ∀ n, RG n ≠ some false)
    (h4 : F4Case O r RU gOnly ra = false) (h5 : F5Case O r RU RG gOnly ra = false) :
    runasPermits O r RU RG (some ra) = runasManual O r RU RG gOnly (some ra) := by
  rw [runasPermits_eq_manual O r RU RG gOnly ra hg hu hgr hRU hRG, h4, h5]
  simp

/-- A target other than the invoking user (so `-u` was given) is judged exactly as the manual
says, for lists without `!`. -/
theorem runasPermits_eq_manual_of_other (r : Request User Group) (RU RG : FoundAliases)
    (ra : RunAs) (hne : O.userEq r.targetUser r.invokingUser = false)
    (hu : Positive ra.users) (hgr : Positive ra.groups)
    (hRU : ∀ n, RU n ≠ some false) (hRG : ∀ n, RG n ≠ some false) :
    runasPermits O r RU RG (some ra) = runasManual O r RU RG false (some ra) :=
  runasPermits_eq_manual_of_not O r RU RG false ra (by simp) hu hgr hRU hRG
    (by simp [F4Case]) (by simp [F5Case, hne])

/-- **`runasPermits` against the manual, no runas spec.** sudo-rs agrees with "only as root"
except for F2: uid-0 targets not named `root` are allowed, targets named `root` without uid 0
denied. -/
theorem runasPermits_none_eq_manual (r : Request User Group) (RU RG : FoundAliases)
    (gOnly : Bool) :
    runasPermits O r RU RG none =
      ((runasManual O r RU RG gOnly none && !F2Denies O r) || F2Allows O r) := by
  simp only [runasPermits, runasManual, F2Denies, F2Allows]
  cases O.isRoot r.targetUser <;> cases O.hasName r.targetUser "root" <;>
    cases inGroup O r.targetUser r.targetGroup <;> rfl

/-- Runas_Alias definitions without `!` never exclude a user. -/
theorem runasUserAliases_ne_false (p : Policy) (r : Request User Group)
    (h : ∀ d ∈ p.aliases.runas, Positive d.items) (n : String) :
    runasUserAliases O p r n ≠ some false :=
  getAliases_ne_false _ _ (fun d hd => h d hd) n

/-- Runas_Alias definitions without `!` never exclude a group. -/
theorem runasGroupAliases_ne_false (p : Policy) (r : Request User Group)
    (h : ∀ d ∈ p.aliases.runas, Positive d.items) (n : String) :
    runasGroupAliases O p r n ≠ some false :=
  getAliases_ne_false _ _ (fun d hd => h d hd) n

/-- **Policy level.** For a policy whose Runas_Alias definitions have no `!`, an explicit runas
spec without `!` is judged by the manual's rule except in F4 and F5. -/
theorem runasPermits_policy_eq_manual (p : Policy) (r : Request User Group) (gOnly : Bool)
    (ra : RunAs) (hg : gOnly = true → O.userEq r.targetUser r.invokingUser = true)
    (hal : ∀ d ∈ p.aliases.runas, Positive d.items)
    (hu : Positive ra.users) (hgr : Positive ra.groups) :
    runasPermits O r (runasUserAliases O p r) (runasGroupAliases O p r) (some ra) =
      ((runasManual O r (runasUserAliases O p r) (runasGroupAliases O p r) gOnly (some ra) &&
          !F4Case O r (runasUserAliases O p r) gOnly ra) ||
        F5Case O r (runasUserAliases O p r) (runasGroupAliases O p r) gOnly ra) :=
  runasPermits_eq_manual O r _ _ gOnly ra hg hu hgr (runasUserAliases_ne_false O p r hal)
    (runasGroupAliases_ne_false O p r hal)

end SudoersSpec
