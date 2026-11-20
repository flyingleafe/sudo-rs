import SudoersSpec.Theorems

/-!
# Alias expansion at the policy level

`Policy.expandAliases` is what a tool that flattens a sudoers file would print: every alias
reference in a user list (`User_Alias`), a host list (`Host_Alias`), a runas user or group list
(`Runas_Alias`) and a command position (`Cmnd_Alias`) is replaced by the full expansion of the
alias (`Aliases.expandAll` over the table; a negated reference flips every qualifier of the
body), and the alias tables are emptied. The command position is expanded syntactically: an
entry `(runas) TAGS: ALIAS` becomes one entry per command of the expansion, the first keeping
the runas spec and the tags, the others written without them (they inherit both along the
line); an entry whose expansion is empty disappears and hands its runas spec and tags on to
the next entry of the line.

The runas group position needs a change of item type: a `Runas_Alias` holds `UserSpecifier`s,
a group list `Identifier`s, and `match_group_alias` compares a member `name`/`#id` with the
group like the group list item `name`/`#id`, while `%group` and `%:group` members never match.
`expandGroups` therefore reads the group list as user specifiers (`liftGroups`), expands, and
maps back (`lowerGroup`), dropping the `%group`/`%:group` members.

Main results, for a policy whose alias tables are uniquely named and sorted (`AliasTable.OK`,
which a clean `sanitize_alias_tables` guarantees):

* `findItem_expandAll`: on any list, deciding on the expansion with no table equals deciding
  with the table `get_aliases` computes. Unlike `demonstration` it does not need every
  referenced alias to be defined (references to undefined aliases are not diagnosed by
  `sanitize_alias_tables` when they occur in a rule).
* `authorize_expandAliases`: the decision on the expanded policy is the decision on the
  original policy, provided no `Cmnd_Alias` body mentions `ALL` (`CmndAliasesNoAll`) and
  expansion empties no non-empty runas user list (`Policy.RunasUsersKept`).
* `authorize_expandAliases_rel`: without `CmndAliasesNoAll` the decisions agree except that the
  expanded policy may add `SETENV` to a tag whose `env` was `implicit` (`SetenvAdded`): the
  implicit `SETENV` of a literal `ALL` (`mod.rs` 542-549) is not given to `ALL` reached through
  a `Cmnd_Alias`.
* `expandAliases_setenv_counterexample`, `expandAliases_runas_counterexample`: both hypotheses
  are needed.
-/

namespace SudoersSpec

variable {α β τ : Type}

/-! ## The no-diagnostic conditions of an alias table -/

/-- One alias table in processing order: unique names, every reference points to an earlier
definition (the conclusion of `sanitize_alias_table_sorted` for a clean run). -/
def TableOK (t : List (Def α)) : Prop := (names t).Nodup ∧ Sorted t

/-- All four alias tables are `TableOK`. -/
def AliasTable.OK (X : AliasTable) : Prop :=
  TableOK X.user ∧ TableOK X.host ∧ TableOK X.cmnd ∧ TableOK X.runas

/-! ## Deciding on the full expansion of one list -/

/-- Every alias an entry refers to is defined in `P` or not defined in `t` at all. -/
def RefsInOrUndef (t P : List (Def α)) (l : List (Spec α × τ)) : Prop :=
  ∀ x ∈ l, ∀ k, x.1.who = .alias k → k ∈ names P ∨ k ∉ names t

theorem lookupDef_of_not_mem {t : List (Def α)} {k : String} (h : k ∉ names t) :
    lookupDef t k = none := by
  cases hl : lookupDef t k with
  | none => rfl
  | some body =>
    obtain ⟨d, hd, rfl, -⟩ := lookupDef_some hl
    exact absurd (mem_names hd) h

/-- One round of expansion lowers the rank of every defined reference and removes the
undefined ones. -/
theorem refsInOrUndef_expandStep (t : List (Def α)) (hu : (names t).Nodup) (hs : Sorted t)
    (P rest : List (Def α)) (d' : Def α) (hsplit : t = P ++ d' :: rest)
    (l : List (Spec α × τ)) (hl : RefsInOrUndef t (P ++ [d']) l) :
    RefsInOrUndef t P (expandStep t l) := by
  intro y hy k' hk'
  obtain ⟨x, hx, hyx⟩ := List.mem_flatMap.1 hy
  obtain ⟨q, i⟩ := x
  -- a reference to a defined alias: expand `[x]` alone and use `refsIn_expandStep`
  have viaDefined : ∀ k body, q.who = .alias k → lookupDef t k = some body →
      k' ∈ names P ∨ k' ∉ names t := by
    intro k body hq hb
    obtain ⟨d, hd, hdk, -⟩ := lookupDef_some hb
    have hkt : k ∈ names t := hdk ▸ mem_names hd
    have h1 : RefsIn (P ++ [d']) [(q, i)] := by
      intro z hz k₂ hk₂
      rw [List.mem_singleton] at hz
      subst hz
      rcases hl _ hx k₂ hk₂ with h | h
      · exact h
      · rw [hq] at hk₂
        injection hk₂ with hk
        exact absurd (hk ▸ hkt) h
    have h2 := refsIn_expandStep t t (List.Perm.refl t) hu hs P rest d' hsplit [(q, i)] h1
    exact Or.inl (h2 y (by simpa [expandStep] using hyx) k' hk')
  cases q with
  | allow m =>
    cases m with
    | all => simp [expandItem] at hyx; subst hyx; cases hk'
    | only _ => simp [expandItem] at hyx; subst hyx; cases hk'
    | alias k =>
      cases hb : lookupDef t k with
      | none => simp [expandItem, hb] at hyx
      | some body => exact viaDefined k body rfl hb
  | forbid m =>
    cases m with
    | all => simp [expandItem] at hyx; subst hyx; cases hk'
    | only _ => simp [expandItem] at hyx; subst hyx; cases hk'
    | alias k =>
      cases hb : lookupDef t k with
      | none => simp [expandItem, hb] at hyx
      | some body => exact viaDefined k body rfl hb

theorem refsInOrUndef_expandN (t : List (Def α)) (hu : (names t).Nodup) (hs : Sorted t)
    (n : Nat) :
    ∀ (P : List (Def α)) (l : List (Spec α × τ)), (∃ rest, t = P ++ rest) →
      P.length = n → RefsInOrUndef t P l → RefsInOrUndef t [] (expandN t n l) := by
  induction n with
  | zero =>
    intro P l _ hP hl
    rw [List.length_eq_zero_iff] at hP
    subst hP
    exact hl
  | succ n ih =>
    intro P l ⟨rest, hrest⟩ hP hl
    rcases List.eq_nil_or_concat P with rfl | ⟨P', d', rfl⟩
    · simp at hP
    · rw [List.concat_eq_append] at hrest hP hl
      simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hP
      have hsplit : t = P' ++ d' :: rest := by rw [hrest]; simp
      exact ih P' (expandStep t l) ⟨d' :: rest, hsplit⟩ hP
        (refsInOrUndef_expandStep t hu hs P' rest d' hsplit l hl)

/-- After full expansion the only alias references left are to aliases the table does not
define (there are none at all unless the table is empty). -/
theorem expandAll_undefined (t : List (Def α)) (hu : (names t).Nodup) (hs : Sorted t)
    (l : List (Spec α × τ)) :
    ∀ x ∈ expandAll t l, ∀ k, x.1.who = .alias k → k ∉ names t := by
  have h := refsInOrUndef_expandN t hu hs t.length t l ⟨[], by simp⟩ rfl
    (fun _ _ k _ => Classical.em (k ∈ names t))
  intro x hx k hk
  rcases h x hx k hk with h | h
  · simp [names] at h
  · exact h

/-- **Expansion of one list.** For a uniquely named sorted table, deciding on the full
expansion of any list without an alias table equals deciding on the list with the table
`get_aliases` precomputes. Undefined references may occur. -/
theorem findItem_expandAll (t : List (Def α)) (hu : (names t).Nodup) (hs : Sorted t)
    (pred : α → Bool) (l : List (Spec α × τ)) :
    findItem pred FoundAliases.empty (expandAll t l) = findItem pred (getAliases t pred) l := by
  rw [findItem_congr pred (A := FoundAliases.empty) (B := getAliases t pred) _ (fun x hx k hk =>
    (getAliases_undefined pred t k (expandAll_undefined t hu hs l x hx k hk)).symm)]
  apply findItem_expandN
  · intro k body hb
    obtain ⟨d, hdt, rfl, rfl⟩ := lookupDef_some hb
    exact getAliases_fixpoint pred t hu hs d hdt
  · intro k hk
    exact getAliases_undefined pred t k (lookupDef_none hk)

/-- Full expansion of a plain spec list. -/
def expandList (t : List (Def α)) (l : SpecList α) : SpecList α :=
  (expandAll t (withUnit l)).map Prod.fst

theorem withUnit_map_fst (l : List (Spec α × Unit)) : withUnit (l.map Prod.fst) = l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    obtain ⟨s, ⟨⟩⟩ := x
    show (s, ()) :: withUnit (l.map Prod.fst) = (s, ()) :: l
    rw [ih]

theorem withUnit_expandList (t : List (Def α)) (l : SpecList α) :
    withUnit (expandList t l) = expandAll t (withUnit l) :=
  withUnit_map_fst _

theorem findItem_expandList (t : List (Def α)) (ht : TableOK t) (pred : α → Bool)
    (l : SpecList α) :
    findItem pred FoundAliases.empty (withUnit (expandList t l)) =
      findItem pred (getAliases t pred) (withUnit l) := by
  rw [withUnit_expandList]
  exact findItem_expandAll t ht.1 ht.2 pred _

theorem expandN_nil (t : List (Def α)) (n : Nat) : expandN t n ([] : List (Spec α × τ)) = [] := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem expandList_nil (t : List (Def α)) : expandList t [] = [] := by
  simp only [expandList, expandAll, withUnit, List.map_nil, expandN_nil]

/-! ## The runas group position -/

/-- Apply `f` to the item of a spec, keeping `ALL`, alias references and the qualifier. -/
def mapSpec (f : α → β) : Spec α → Spec β
  | .allow .all => .allow .all
  | .allow (.only x) => .allow (.only (f x))
  | .allow (.alias k) => .allow (.alias k)
  | .forbid .all => .forbid .all
  | .forbid (.only x) => .forbid (.only (f x))
  | .forbid (.alias k) => .forbid (.alias k)

/-- A runas group list read as `Runas_Alias` members: the group `name`/`#gid` becomes the
member `name`/`#id`, which `match_group_alias` compares with the target group exactly as
`match_group` compares the group list item. -/
def liftGroups (l : SpecList Identifier) : SpecList UserSpecifier := l.map (mapSpec .user)

/-- A `Runas_Alias` member as a group list item. `name`/`#id` becomes the group `name`/`#gid`;
`%group` and `%:group` members, which `match_group_alias` never matches, have no group list
counterpart and are dropped. -/
def lowerGroup : Spec UserSpecifier → Option (Spec Identifier)
  | .allow (.only (.user i)) => some (.allow (.only i))
  | .forbid (.only (.user i)) => some (.forbid (.only i))
  | .allow (.only _) => none
  | .forbid (.only _) => none
  | .allow .all => some (.allow .all)
  | .forbid .all => some (.forbid .all)
  | .allow (.alias k) => some (.allow (.alias k))
  | .forbid (.alias k) => some (.forbid (.alias k))

/-- Full expansion of a runas group list over the `Runas_Alias` table. -/
def expandGroups (t : List (Def UserSpecifier)) (l : SpecList Identifier) : SpecList Identifier :=
  (expandList t (liftGroups l)).filterMap lowerGroup

theorem foldl_findItemStep_mapSpec (pred : β → Bool) (f : α → β) (S : FoundAliases)
    (r : Option Unit) (l : SpecList α) :
    (withUnit (l.map (mapSpec f))).foldl (findItemStep pred S) r =
      (withUnit l).foldl (findItemStep (fun x => pred (f x)) S) r := by
  induction l generalizing r with
  | nil => rfl
  | cons s l ih =>
    show (withUnit (l.map (mapSpec f))).foldl (findItemStep pred S)
        (findItemStep pred S r (mapSpec f s, ())) =
      (withUnit l).foldl (findItemStep (fun x => pred (f x)) S)
        (findItemStep (fun x => pred (f x)) S r (s, ()))
    rw [ih]
    congr 1
    rcases s with (_ | _ | _) | (_ | _ | _) <;> rfl

theorem foldl_findItemStep_lowerGroup {User Group : Type} (O : Oracle User Group) (g : Group)
    (S : FoundAliases) (r : Option Unit) (l : SpecList UserSpecifier) :
    (withUnit (l.filterMap lowerGroup)).foldl (findItemStep (matchGroup O g) S) r =
      (withUnit l).foldl (findItemStep (matchGroupAlias O g) S) r := by
  induction l generalizing r with
  | nil => rfl
  | cons s l ih =>
    have key : findItemStep (matchGroupAlias O g) S r (s, ()) =
        match lowerGroup s with
        | none => r
        | some s' => findItemStep (matchGroup O g) S r (s', ()) := by
      rcases s with (_ | (_ | _ | _) | _) | (_ | (_ | _ | _) | _) <;> rfl
    show _ = (withUnit l).foldl _ (findItemStep (matchGroupAlias O g) S r (s, ()))
    rw [key, List.filterMap_cons]
    cases lowerGroup s with
    | none => exact ih r
    | some s' => exact ih _

/-- **Runas group position.** Deciding on the expanded group list without an alias table
equals deciding with the `runas_group_aliases` table (`match_group_alias`). -/
theorem findItem_expandGroups {User Group : Type} (O : Oracle User Group)
    (t : List (Def UserSpecifier)) (ht : TableOK t) (g : Group) (l : SpecList Identifier) :
    findItem (matchGroup O g) FoundAliases.empty (withUnit (expandGroups t l)) =
      findItem (matchGroup O g) (getAliases t (matchGroupAlias O g)) (withUnit l) := by
  unfold findItem expandGroups
  rw [foldl_findItemStep_lowerGroup]
  change findItem (matchGroupAlias O g) FoundAliases.empty
      (withUnit (expandList t (liftGroups l))) = _
  rw [findItem_expandList t ht, findItem, liftGroups, foldl_findItemStep_mapSpec]
  rfl

/-! ## The runas user position -/

/-- Expand both lists of a runas spec over the `Runas_Alias` table. -/
def RunAs.expand (t : List (Def UserSpecifier)) (ra : RunAs) : RunAs :=
  ⟨expandList t ra.users, expandGroups t ra.groups⟩

/-- Expansion leaves the runas user list empty iff it was empty. `check_permission` treats an
empty user list specially (`ra.users.is_empty()`, `mod.rs` 512), so this is needed: a list
that only names undefined aliases (or aliases with empty bodies) expands to `()`. -/
def RunAs.UsersKept (t : List (Def UserSpecifier)) (ra : RunAs) : Prop :=
  (expandList t ra.users).isEmpty = ra.users.isEmpty

variable {User Group : Type} (O : Oracle User Group)

theorem runasPermits_expand (r : Request User Group) (t : List (Def UserSpecifier))
    (ht : TableOK t) (ra : Option RunAs) (hk : ∀ x, ra = some x → RunAs.UsersKept t x) :
    runasPermits O r FoundAliases.empty FoundAliases.empty (ra.map (RunAs.expand t)) =
      runasPermits O r (getAliases t (matchUser O r.targetUser))
        (getAliases t (matchGroupAlias O r.targetGroup)) ra := by
  cases ra with
  | none => rfl
  | some ra =>
    have hk : (expandList t ra.users).isEmpty = ra.users.isEmpty := hk ra rfl
    simp only [Option.map_some, runasPermits, RunAs.expand, ← findItem_eq_spec]
    rw [findItem_expandList t ht, findItem_expandGroups O t ht, hk]

/-! ## The command position -/

/-- Is the spec an alias reference? -/
def isAliasRef (s : Spec α) : Bool :=
  match s.who with
  | .alias _ => true
  | _ => false

/-- What a distributed entry `(tag, cmd)` becomes: one entry per command of the expansion.
An alias reference got no implicit `SETENV` (it is not a literal `ALL`); the commands of its
expansion get it if they are a literal `ALL`. Other entries are unchanged. -/
def expandCmd (t : List (Def Command)) (e : Tag × Spec Command) : List (Tag × Spec Command) :=
  (expandList t [e.2]).map fun c => (if isAliasRef e.2 then implicitSetenv c e.1 else e.1, c)

/-- `expandCmd` on a distributed entry, with its runas spec expanded. -/
def expandMatched (X : AliasTable) (e : MatchedCommand) : List MatchedCommand :=
  (expandCmd X.cmnd e.2).map fun x => (e.1.map (RunAs.expand X.runas), x)

/-- Expand the commands of a `Cmnd_Spec_List`. `pr`/`pm` are the runas spec and tags of
entries that expanded to nothing; they go to the next entry. The first command of an
expansion keeps the entry's runas spec and tags, the others inherit them. -/
def expandEntries (X : AliasTable) :
    Option RunAs → List Modifier → List (Option RunAs × CommandSpec) →
      List (Option RunAs × CommandSpec)
  | _, _, [] => []
  | pr, pm, (ra, ⟨mods, cmd⟩) :: rest =>
    match expandList X.cmnd [cmd] with
    | [] => expandEntries X (ra.or pr) (pm ++ mods) rest
    | c :: cs =>
      ((ra.or pr).map (RunAs.expand X.runas), ⟨pm ++ mods, c⟩) ::
        ((cs.map fun c => (none, ⟨[], c⟩)) ++ expandEntries X none [] rest)

/-- Expand a `Cmnd_Spec_List`. -/
def expandLine (X : AliasTable) (l : List (Option RunAs × CommandSpec)) :
    List (Option RunAs × CommandSpec) :=
  expandEntries X none [] l

/-- Expand every alias reference of a user specification line. -/
def PermissionSpec.expand (X : AliasTable) (ps : PermissionSpec) : PermissionSpec :=
  ⟨expandList X.user ps.users,
    ps.permissions.map fun seg => (expandList X.host seg.1, expandLine X seg.2)⟩

/-- **The flattened policy**: every alias reference expanded, no alias tables. -/
def Policy.expandAliases (p : Policy) : Policy :=
  ⟨p.rules.map (PermissionSpec.expand p.aliases), {}⟩

/-- Expansion empties no non-empty runas user list of the policy. -/
def Policy.RunasUsersKept (p : Policy) : Prop :=
  ∀ rule ∈ p.rules, ∀ seg ∈ rule.permissions, ∀ x ∈ seg.2, ∀ ra, x.1 = some ra →
    RunAs.UsersKept p.aliases.runas ra

/-- No `Cmnd_Alias` body mentions `ALL` (allowed or negated). -/
def CmndAliasesNoAll (t : List (Def Command)) : Prop := ∀ d ∈ t, ∀ s ∈ d.items, s.who ≠ .all

/-- `t'` is `t`, or `t` with the `SETENV` that a literal `ALL` implies added to an `env` that
was not set explicitly. -/
def SetenvAdded (t t' : Tag) : Prop :=
  t' = t ∨ (t.env = .implicit ∧ t' = { t with env := .setenv })

/-! ### Expansion of a line -/

theorem expandStep_single (t : List (Def α)) (x : Spec α × τ) :
    expandStep t [x] = expandItem t x := by
  simp [expandStep]

theorem expandN_single_of_not_alias (t : List (Def α)) (x : Spec α × τ)
    (hx : isAliasRef x.1 = false) (n : Nat) : expandN t n [x] = [x] := by
  have h1 : expandItem t x = [x] := by
    obtain ⟨q, i⟩ := x
    rcases q with (_ | _ | _) | (_ | _ | _) <;> first | rfl | cases hx
  induction n with
  | zero => rfl
  | succ n ih => rw [expandN, expandStep_single, h1, ih]

theorem expandList_single_of_not_alias (t : List (Def α)) (s : Spec α)
    (hs : isAliasRef s = false) : expandList t [s] = [s] := by
  simp only [expandList, expandAll, withUnit, List.map_cons, List.map_nil]
  rw [expandN_single_of_not_alias t (s, ()) hs]
  rfl

theorem implicitSetenv_of_alias (s : Spec Command) (hs : isAliasRef s = true) (t : Tag) :
    implicitSetenv s t = t := by
  rcases s with (_ | _ | _) | (_ | _ | _) <;> first | rfl | cases hs

/-- The tag of an expanded entry is the accumulated tag with the implicit `SETENV` of its own
command. -/
theorem expandMatched_distributed (X : AliasTable) (R : Option RunAs) (T : Tag)
    (cmd : Spec Command) :
    expandMatched X (R, (implicitSetenv cmd T, cmd)) =
      (expandList X.cmnd [cmd]).map fun c => (R.map (RunAs.expand X.runas), (implicitSetenv c T, c)) := by
  unfold expandMatched expandCmd
  rw [List.map_map]
  cases h : isAliasRef cmd
  · rw [expandList_single_of_not_alias X.cmnd cmd h]
    simp
  · apply List.map_congr_left
    intro c _
    simp [implicitSetenv_of_alias cmd h]

theorem distributeTagsGo_map_none (r : Option RunAs) (t : Tag) (cs : List (Spec Command))
    (rest : List (Option RunAs × CommandSpec)) :
    distributeTagsGo r t ((cs.map fun c => (none, ⟨[], c⟩)) ++ rest) =
      (cs.map fun c => (r, (implicitSetenv c t, c))) ++ distributeTagsGo r t rest := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    show (r, (implicitSetenv c t, c)) :: distributeTagsGo r t ((cs.map fun c => (none, ⟨[], c⟩)) ++ rest) = _
    rw [ih]
    rfl

theorem distributeTagsGo_expand (X : AliasTable) (L : List (Option RunAs × CommandSpec)) :
    ∀ (r pr : Option RunAs) (t : Tag) (pm : List Modifier),
      distributeTagsGo (r.map (RunAs.expand X.runas)) t (expandEntries X pr pm L) =
        (distributeTagsGo (pr.or r) (applyMods pm t) L).flatMap (expandMatched X) := by
  induction L with
  | nil => intros; rfl
  | cons e rest ih =>
    intro r pr t pm
    obtain ⟨ra, mods, cmd⟩ := e
    rw [distributeTagsGo, List.flatMap_cons, expandMatched_distributed]
    simp only [expandEntries]
    split
    · rename_i hnil
      rw [hnil, ih, List.map_nil, List.nil_append, applyMods_append, Option.or_assoc]
    · rename_i c cs hcs
      rw [hcs, distributeTagsGo, distributeTagsGo_map_none, ← Option.map_or, List.map_cons,
        List.cons_append]
      have := ih ((ra.or pr).or r) none (applyMods (pm ++ mods) t) []
      rw [Option.none_or] at this
      rw [this]
      simp only [Option.or_assoc, applyMods_append]
      rfl

theorem distributeTagsSpec_expandLine (X : AliasTable) (l : List (Option RunAs × CommandSpec)) :
    distributeTagsSpec (expandLine X l) = (distributeTagsSpec l).flatMap (expandMatched X) := by
  rw [← distributeTags_eq_spec, ← distributeTags_eq_spec]
  exact distributeTagsGo_expand X l none none {} []

/-! ### Candidates and allowed entries of the expanded policy -/

theorem userListMatches_expand (p : Policy) (hX : p.aliases.OK) (r : Request User Group)
    (users : SpecList UserSpecifier) :
    userListMatches O p.expandAliases r (expandList p.aliases.user users) =
      userListMatches O p r users := by
  unfold userListMatches
  rw [← findItem_eq_spec, ← findItem_eq_spec]
  exact congrArg Option.isSome (findItem_expandList p.aliases.user hX.1 _ users)

theorem hostListMatches_expand (p : Policy) (hX : p.aliases.OK) (r : Request User Group)
    (hosts : SpecList Hostname) :
    hostListMatches O p.expandAliases r (expandList p.aliases.host hosts) =
      hostListMatches O p r hosts := by
  unfold hostListMatches
  rw [← findItem_eq_spec, ← findItem_eq_spec]
  exact congrArg Option.isSome (findItem_expandList p.aliases.host hX.2.1 _ hosts)

theorem candidatesSpec_expandAliases (p : Policy) (hX : p.aliases.OK) (r : Request User Group) :
    candidatesSpec O p.expandAliases r = (candidatesSpec O p r).flatMap (expandMatched p.aliases) := by
  unfold candidatesSpec
  conv => lhs; rw [show p.expandAliases.rules = p.rules.map (PermissionSpec.expand p.aliases) from rfl]
  rw [List.flatMap_map, List.flatMap_assoc]
  congr 1
  funext rule
  rw [show (PermissionSpec.expand p.aliases rule).users = expandList p.aliases.user rule.users
    from rfl, userListMatches_expand O p hX]
  split
  · rw [show (PermissionSpec.expand p.aliases rule).permissions =
        rule.permissions.map fun seg => (expandList p.aliases.host seg.1, expandLine p.aliases seg.2)
      from rfl, List.flatMap_map, List.flatMap_assoc]
    congr 1
    funext seg
    rw [hostListMatches_expand O p hX]
    split
    · exact distributeTagsSpec_expandLine p.aliases seg.2
    · rfl
  · rfl

theorem runas_of_mem_distributeTagsSpec {l : List (Option RunAs × CommandSpec)}
    {e : MatchedCommand} (he : e ∈ distributeTagsSpec l) {ra : RunAs} (hra : e.1 = some ra) :
    ∃ x ∈ l, x.1 = some ra := by
  simp only [distributeTagsSpec, List.mem_mapIdx] at he
  obtain ⟨i, hi, hie⟩ := he
  rw [← hie] at hra
  simp only [runasInEffect] at hra
  obtain ⟨x, hx, hx1⟩ := List.mem_filterMap.1 (List.mem_of_getLast? hra)
  exact ⟨x, List.mem_of_mem_take hx, hx1⟩

theorem runas_of_mem_candidatesSpec (p : Policy) (r : Request User Group) {e : MatchedCommand}
    (he : e ∈ candidatesSpec O p r) {ra : RunAs} (hra : e.1 = some ra) :
    ∃ rule ∈ p.rules, ∃ seg ∈ rule.permissions, ∃ x ∈ seg.2, x.1 = some ra := by
  obtain ⟨rule, hrule, he⟩ := List.mem_flatMap.1 he
  split at he
  · obtain ⟨seg, hseg, he⟩ := List.mem_flatMap.1 he
    split at he
    · obtain ⟨x, hx, h⟩ := runas_of_mem_distributeTagsSpec he hra
      exact ⟨rule, hrule, seg, hseg, x, hx, h⟩
    · simp at he
  · simp at he

theorem allowedSpec_expandAliases (p : Policy) (hX : p.aliases.OK) (hk : p.RunasUsersKept)
    (r : Request User Group) :
    allowedSpec O p.expandAliases r = (allowedSpec O p r).flatMap (expandCmd p.aliases.cmnd) := by
  have hC : ∀ e ∈ candidatesSpec O p r,
      runasPermits O r FoundAliases.empty FoundAliases.empty
          (e.1.map (RunAs.expand p.aliases.runas)) =
        runasPermits O r (runasUserAliases O p r) (runasGroupAliases O p r) e.1 := by
    intro e he
    apply runasPermits_expand O r p.aliases.runas hX.2.2.2 e.1
    intro ra hra
    obtain ⟨rule, hrule, seg, hseg, x, hx, h⟩ := runas_of_mem_candidatesSpec O p r he hra
    exact hk rule hrule seg hseg x hx ra h
  unfold allowedSpec
  rw [candidatesSpec_expandAliases O p hX]
  generalize candidatesSpec O p r = C at hC
  induction C with
  | nil => rfl
  | cons e C ih =>
    rw [List.flatMap_cons, List.filter_append, List.map_append,
      ih (fun e' he' => hC e' (List.mem_cons_of_mem _ he')), List.filter_cons]
    have he := hC e List.mem_cons_self
    have hfilter : (expandMatched p.aliases e).filter
        (fun e => runasPermits O r (runasUserAliases O p.expandAliases r)
          (runasGroupAliases O p.expandAliases r) e.1) =
        if runasPermits O r (runasUserAliases O p r) (runasGroupAliases O p r) e.1 then
          expandMatched p.aliases e else [] := by
      unfold expandMatched
      rw [List.filter_map]
      split
      · rename_i hp
        congr 1
        apply List.filter_eq_self.2
        intro x _
        exact he.trans hp
      · rename_i hp
        rw [List.filter_eq_nil_iff.2]
        · rfl
        · intro x _
          simp only [Function.comp_apply]
          exact fun h => hp (he.symm.trans h)
    rw [hfilter]
    split
    · rw [List.map_cons, List.flatMap_cons]
      unfold expandMatched
      simp only [List.map_map, Function.comp_def, List.map_id']
    · rfl

/-! ### The decision -/

theorem expandItem_satellite {τ' : Type} (t : List (Def α)) (g : τ → τ') (x : Spec α × τ) :
    expandItem t (x.1, g x.2) = (expandItem t x).map fun y => (y.1, g y.2) := by
  obtain ⟨q, i⟩ := x
  rcases q with (_ | _ | k) | (_ | _ | k) <;> simp [expandItem]

theorem expandN_satellite {τ' : Type} (t : List (Def α)) (g : τ → τ') (n : Nat) :
    ∀ l : List (Spec α × τ),
      expandN t n (l.map fun y => (y.1, g y.2)) = (expandN t n l).map fun y => (y.1, g y.2) := by
  induction n with
  | zero => intro l; rfl
  | succ n ih =>
    intro l
    have : expandStep t (l.map fun y => (y.1, g y.2)) = (expandStep t l).map fun y => (y.1, g y.2) := by
      simp only [expandStep, List.flatMap_map, List.map_flatMap]
      congr 1
      funext x
      exact expandItem_satellite t g x
    rw [expandN, this, ih]
    rfl

theorem expandN_append (t : List (Def α)) (n : Nat) :
    ∀ l₁ l₂ : List (Spec α × τ), expandN t n (l₁ ++ l₂) = expandN t n l₁ ++ expandN t n l₂ := by
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro l₁ l₂
    rw [expandN, expandStep, List.flatMap_append, ih]
    rfl

theorem expandAll_cmds (t : List (Def Command)) (A : List (Tag × Spec Command)) :
    expandAll t (A.map Prod.swap) =
      A.flatMap fun e => (expandList t [e.2]).map fun c => (c, e.1) := by
  induction A with
  | nil => exact expandN_nil t _
  | cons e A ih =>
    rw [List.map_cons, List.flatMap_cons, ← ih]
    show expandN t t.length ([Prod.swap e] ++ A.map Prod.swap) =
      _ ++ expandN t t.length (A.map Prod.swap)
    rw [expandN_append]
    congr 1
    have h := expandN_satellite t (fun _ : Unit => e.1) t.length [(e.2, ())]
    simp only [List.map_cons, List.map_nil] at h
    rw [show Prod.swap e = (e.2, e.1) from rfl, h, expandList, List.map_map]
    rfl

theorem findItem_map_rel {σ τ' : Type} (R : τ → τ' → Prop) (pred : α → Bool) (S : FoundAliases)
    (L : List (Spec α × σ)) (f₁ : Spec α × σ → τ) (f₂ : Spec α × σ → τ')
    (h : ∀ z ∈ L, R (f₁ z) (f₂ z)) :
    Option.Rel R (findItem pred S (L.map fun z => (z.1, f₁ z)))
      (findItem pred S (L.map fun z => (z.1, f₂ z))) := by
  unfold findItem
  suffices ∀ (r₁ : Option τ) (r₂ : Option τ'), Option.Rel R r₁ r₂ →
      Option.Rel R ((L.map fun z => (z.1, f₁ z)).foldl (findItemStep pred S) r₁)
        ((L.map fun z => (z.1, f₂ z)).foldl (findItemStep pred S) r₂) from this none none .none
  induction L with
  | nil => intro r₁ r₂ hr; exact hr
  | cons z L ih =>
    intro r₁ r₂ hr
    simp only [List.map_cons, List.foldl_cons]
    apply ih (fun z hz => h z (List.mem_cons_of_mem _ hz))
    rw [findItemStep_eq, findItemStep_eq]
    split
    · rw [condition_info, condition_info (i := f₂ z)]
      cases condition S (z.1, ()) with
      | none => exact .none
      | some _ => exact .some (h z List.mem_cons_self)
    · exact hr

theorem implicitSetenv_added (c : Spec Command) (t : Tag) : SetenvAdded t (implicitSetenv c t) := by
  unfold implicitSetenv SetenvAdded
  split
  · split
    · exact Or.inl rfl
    · rename_i h
      cases he : t.env
      · exact Or.inr ⟨rfl, rfl⟩
      · left
        rcases t with ⟨a, b, env, d, f, g⟩
        simp only at he
        subst he
        rfl
      · exact absurd he h
  · exact Or.inl rfl

theorem implicitSetenv_of_not_all (s : Spec Command) (hs : s.who ≠ .all) (t : Tag) :
    implicitSetenv s t = t := by
  rcases s with (_ | _ | _) | (_ | _ | _) <;> first | rfl | exact absurd rfl hs

theorem noAll_expandN (t : List (Def α)) (ht : ∀ d ∈ t, ∀ s ∈ d.items, s.who ≠ .all) (n : Nat) :
    ∀ l : List (Spec α × τ), (∀ x ∈ l, x.1.who ≠ .all) → ∀ x ∈ expandN t n l, x.1.who ≠ .all := by
  induction n with
  | zero => intro l hl; exact hl
  | succ n ih =>
    intro l hl
    apply ih
    intro y hy
    obtain ⟨x, hx, hyx⟩ := List.mem_flatMap.1 hy
    obtain ⟨q, i⟩ := x
    have viaBody : ∀ k body, lookupDef t k = some body → ∀ s ∈ body, s.who ≠ .all := by
      intro k body hb s hs
      obtain ⟨d, hd, -, rfl⟩ := lookupDef_some hb
      exact ht d hd s hs
    rcases q with (_ | _ | k) | (_ | _ | k)
    · simp [expandItem] at hyx; subst hyx; exact hl _ hx
    · simp [expandItem] at hyx; subst hyx; exact hl _ hx
    · cases hb : lookupDef t k with
      | none => simp [expandItem, hb] at hyx
      | some body =>
        simp only [expandItem, hb, Option.getD_some, List.mem_map] at hyx
        obtain ⟨s, hs, rfl⟩ := hyx
        exact viaBody k body hb s hs
    · simp [expandItem] at hyx; subst hyx; exact hl _ hx
    · simp [expandItem] at hyx; subst hyx; exact hl _ hx
    · cases hb : lookupDef t k with
      | none => simp [expandItem, hb] at hyx
      | some body =>
        simp only [expandItem, hb, Option.getD_some, List.mem_map] at hyx
        obtain ⟨s, hs, rfl⟩ := hyx
        rw [who_negate]
        exact viaBody k body hb s hs

/-- The commands of the allowed entries' expansions, each with the entry it comes from. -/
def cmdsWithOrigin (t : List (Def Command)) (A : List (Tag × Spec Command)) :
    List (Spec Command × (Tag × Spec Command)) :=
  A.flatMap fun e => (expandList t [e.2]).map fun c => (c, e)

theorem checkPermission_eq_cmdsWithOrigin (p : Policy) (hX : p.aliases.OK)
    (r : Request User Group) :
    checkPermission O p r =
      findItem (matchCommand O r.command r.arguments) FoundAliases.empty
        ((cmdsWithOrigin p.aliases.cmnd (allowedSpec O p r)).map fun z => (z.1, z.2.1)) := by
  rw [checkPermission, allowedCommands_eq, cmndAliases,
    ← findItem_expandAll p.aliases.cmnd hX.2.2.1.1 hX.2.2.1.2, expandAll_cmds, cmdsWithOrigin,
    List.map_flatMap]
  congr 1
  congr 1
  funext e
  rw [List.map_map]
  rfl

theorem checkPermission_expandAliases_eq_cmdsWithOrigin (p : Policy) (hX : p.aliases.OK)
    (hk : p.RunasUsersKept) (r : Request User Group) :
    checkPermission O p.expandAliases r =
      findItem (matchCommand O r.command r.arguments) FoundAliases.empty
        ((cmdsWithOrigin p.aliases.cmnd (allowedSpec O p r)).map fun z =>
          (z.1, if isAliasRef z.2.2 then implicitSetenv z.1 z.2.1 else z.2.1)) := by
  rw [checkPermission, allowedCommands_eq, allowedSpec_expandAliases O p hX hk, cmdsWithOrigin,
    List.map_flatMap, List.map_flatMap]
  congr 1
  congr 1
  funext e
  rw [expandCmd, List.map_map, List.map_map]
  rfl

/-- `check_permission` on the flattened policy: related by `SetenvAdded`. -/
theorem checkPermission_expandAliases_rel (p : Policy) (hX : p.aliases.OK)
    (hk : p.RunasUsersKept) (r : Request User Group) :
    Option.Rel SetenvAdded (checkPermission O p r) (checkPermission O p.expandAliases r) := by
  rw [checkPermission_eq_cmdsWithOrigin O p hX, checkPermission_expandAliases_eq_cmdsWithOrigin O p hX hk]
  apply findItem_map_rel
  intro z _
  split
  · exact implicitSetenv_added _ _
  · exact Or.inl rfl

/-- `check_permission` on the flattened policy, when no `Cmnd_Alias` body mentions `ALL`. -/
theorem checkPermission_expandAliases (p : Policy) (hX : p.aliases.OK) (hk : p.RunasUsersKept)
    (hc : CmndAliasesNoAll p.aliases.cmnd) (r : Request User Group) :
    checkPermission O p.expandAliases r = checkPermission O p r := by
  rw [checkPermission_eq_cmdsWithOrigin O p hX, checkPermission_expandAliases_eq_cmdsWithOrigin O p hX hk]
  congr 1
  apply List.map_congr_left
  intro z hz
  obtain ⟨e, -, hz⟩ := List.mem_flatMap.1 hz
  obtain ⟨c, hc', rfl⟩ := List.mem_map.1 hz
  simp only
  split
  · rename_i hal
    have hw : ∀ x ∈ withUnit [e.2], x.1.who ≠ .all := by
      intro x hx
      simp only [withUnit, List.map_cons, List.map_nil, List.mem_singleton] at hx
      subst hx
      rcases e with ⟨_, (_ | _ | _) | (_ | _ | _)⟩ <;> simp_all [Qualified.who, isAliasRef]
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc'
    rw [implicitSetenv_of_not_all _ (noAll_expandN p.aliases.cmnd hc _ _ hw x hx)]
  · rfl

/-- **Flattening the aliases preserves the decision up to the implicit `SETENV`.** For alias
tables without diagnostics, and when expansion empties no runas user list, the decision on
the flattened policy grants exactly when the original does, with the same tag except that
`SETENV` may be added where `env` was `implicit` (an `ALL` reached through a `Cmnd_Alias`
becomes a literal `ALL`). -/
theorem authorize_expandAliases_rel (p : Policy) (hX : p.aliases.OK) (hk : p.RunasUsersKept)
    (r : Request User Group) :
    Option.Rel SetenvAdded (authorize O p r) (authorize O p.expandAliases r) := by
  unfold authorize
  have h := checkPermission_expandAliases_rel O p hX hk r
  generalize checkPermission O p r = a at h ⊢
  generalize checkPermission O p.expandAliases r = b at h ⊢
  cases h with
  | none => exact .none
  | some h =>
    apply Option.Rel.some
    rcases h with rfl | ⟨he, rfl⟩
    · exact Or.inl rfl
    · split
      · exact Or.inr ⟨he, rfl⟩
      · exact Or.inr ⟨he, rfl⟩

/-- **Alias expansion preserves the decision.** For alias tables without diagnostics
(`AliasTable.OK`), when expansion empties no runas user list and no `Cmnd_Alias` body mentions
`ALL`, the flattened, alias-free policy decides every request exactly as the original. -/
theorem authorize_expandAliases (p : Policy) (hX : p.aliases.OK) (hk : p.RunasUsersKept)
    (hc : CmndAliasesNoAll p.aliases.cmnd) (r : Request User Group) :
    authorize O p.expandAliases r = authorize O p r := by
  unfold authorize
  rw [checkPermission_expandAliases O p hX hk hc r]

end SudoersSpec
