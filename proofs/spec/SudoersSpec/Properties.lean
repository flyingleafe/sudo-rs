import SudoersSpec.Theorems

/-!
# Policy-level properties of the decision

Properties a reader of a sudoers file relies on, stated about `authorize` (the form-(b)
transcription of `Sudoers::check(..).flags`) and proved through the declarative form. Where
sudo-rs does not have the property as the documentation suggests it, the file proves the exact
sudo-rs behaviour instead; the kernel-checked counterexamples are in `Certificates.lean`.

| | Property | Lean |
|---|---|---|
| P1 | An allowed request has a witness: an applicable line, an applicable host group, and a command entry of it that decides | `allow_witness`, `condition_grants_iff` |
| P2 | A user, host or command that no list mentions is never allowed | `unmentioned_user_unmatched`, `unmentioned_host_unmatched`, `unmentioned_command_unmatched` |
| P2r | A target user other than the invoker that no runas list mentions: only uid 0, only through an entry without a runas spec (F2) | `unmentioned_runas_target` |
| P3 | A denial of a request some allowed entry matches comes from a `!` on the command side | `deny_needs_cmd_negation` |
| P3b | `!` in a host list only switches a host group off; in runas lists it does not even do that (F3, F5) | `inapplicable_hostgroup_irrelevant`, `runasPermits_some_eq`, `runas_grouplist_ignored`, `runas_userlist_ignored` |
| P4 | The last line with a deciding entry decides; earlier lines are irrelevant | `last_line_decides` |
| P5 | Lines of other users are irrelevant | `insert_other_user_irrelevant` |
| P6 | Adding a line without a command-side `!` never revokes | `add_positive_preserves_allow` |
| P7 | `()` and `(: group)` only run as oneself | `myself_no_impersonation`, `myself_no_impersonation_decision` |
| P8 | A target group is one of the target user's groups or listed | `runas_group_justified`, `runas_group_justified_decision` |
| P9 | NOPASSWD comes from the root/self exception or a `NOPASSWD` tag earlier in the deciding host group | `nopasswd_needs_explicit_tag` |
| P10 | Alias resolution is adequate | `demonstration` (`Aliases.lean`): `get_aliases` is a fold without fuel |
-/

namespace SudoersSpec

variable {User Group : Type} (O : Oracle User Group)

/-! ## The deciding entry -/

/-- A candidate entry takes part in the decision: its runas spec permits the request and its
command spec takes part for the requested command. -/
def entryDecides (p : Policy) (r : Request User Group) (e : MatchedCommand) : Bool :=
  runasPermits O r (runasUserAliases O p r) (runasGroupAliases O p r) e.1 &&
    cmdParticipates O p r e.2

/-- The entry that decides the request: the final candidate that takes part. -/
def decidingEntry (p : Policy) (r : Request User Group) : Option MatchedCommand :=
  lastMatch (entryDecides O p r) (candidatesSpec O p r)

/-- The candidate entries one line contributes. -/
def ruleCandidates (p : Policy) (r : Request User Group) (rule : PermissionSpec) :
    List MatchedCommand :=
  if userListMatches O p r rule.users then
    rule.permissions.flatMap fun seg =>
      if hostListMatches O p r seg.1 then distributeTagsSpec seg.2 else []
  else []

theorem candidatesSpec_eq_flatMap (p : Policy) (r : Request User Group) :
    candidatesSpec O p r = p.rules.flatMap (ruleCandidates O p r) := rfl

theorem lastMatch_filter {β : Type} (p q : β → Bool) (l : List β) :
    lastMatch p (l.filter q) = lastMatch (fun x => q x && p x) l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases hq : q x = true
    · simp [hq, lastMatch_cons, ih]
    · simp [hq, lastMatch_cons, ih]

/-- `check_permission` is the verdict of the deciding entry. -/
theorem checkPermission_eq_deciding (p : Policy) (r : Request User Group) :
    checkPermission O p r =
      (decidingEntry O p r).bind fun e => condition (cmndAliases O p r) (e.2.2, e.2.1) := by
  rw [checkPermission_eq_spec]
  unfold checkPermissionSpec allowedSpec decidingEntry
  rw [lastMatch_map, lastMatch_filter, Option.bind_map]
  rfl

theorem authorize_eq_some_iff_deciding (p : Policy) (r : Request User Group) (t : Tag) :
    authorize O p r = some t ↔
      ∃ e, decidingEntry O p r = some e ∧
        ∃ t', condition (cmndAliases O p r) (e.2.2, e.2.1) = some t' ∧
          t = (if skipPasswd O r then { t' with authenticate := .nopasswd } else t') := by
  rw [authorize, checkPermission_eq_deciding]
  constructor
  · intro h
    obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨e, he, hc⟩ := Option.bind_eq_some_iff.1 ht'
    exact ⟨e, he, t', hc, rfl⟩
  · rintro ⟨e, he, t', hc, rfl⟩
    rw [he]
    simp [hc]

/-- No candidate takes part: deny. -/
theorem deny_of_no_deciding (p : Policy) (r : Request User Group)
    (h : ∀ e ∈ candidatesSpec O p r, entryDecides O p r e = false) : authorize O p r = none := by
  rw [authorize, checkPermission_eq_deciding, decidingEntry, (lastMatch_eq_none_iff _ _).2 h]
  rfl

theorem decidingEntry_spec {p : Policy} {r : Request User Group} {e : MatchedCommand}
    (h : decidingEntry O p r = some e) :
    e ∈ candidatesSpec O p r ∧
      runasPermits O r (runasUserAliases O p r) (runasGroupAliases O p r) e.1 = true ∧
      cmdParticipates O p r e.2 = true := by
  obtain ⟨hm, hd⟩ := lastMatch_spec h
  simp only [entryDecides, Bool.and_eq_true] at hd
  exact ⟨hm, hd.1, hd.2⟩

theorem mem_ruleCandidates (p : Policy) (r : Request User Group) (rule : PermissionSpec)
    (e : MatchedCommand) :
    e ∈ ruleCandidates O p r rule ↔
      userListMatches O p r rule.users = true ∧
        ∃ seg ∈ rule.permissions, hostListMatches O p r seg.1 = true ∧
          e ∈ distributeTagsSpec seg.2 := by
  unfold ruleCandidates
  by_cases hu : userListMatches O p r rule.users = true
  · simp only [hu, ite_true, List.mem_flatMap, true_and]
    constructor
    · rintro ⟨seg, hs, he⟩
      by_cases hh : hostListMatches O p r seg.1 = true
      · simp only [hh, ite_true] at he
        exact ⟨seg, hs, hh, he⟩
      · simp [hh] at he
    · rintro ⟨seg, hs, hh, he⟩
      exact ⟨seg, hs, by simp [hh, he]⟩
  · simp [hu]

theorem mem_candidatesSpec (p : Policy) (r : Request User Group) (e : MatchedCommand) :
    e ∈ candidatesSpec O p r ↔
      ∃ rule ∈ p.rules, userListMatches O p r rule.users = true ∧
        ∃ seg ∈ rule.permissions, hostListMatches O p r seg.1 = true ∧
          e ∈ distributeTagsSpec seg.2 := by
  simp only [candidatesSpec_eq_flatMap, List.mem_flatMap, mem_ruleCandidates]

/-- Every distributed entry carries the command spec of an entry of the list. -/
theorem mem_distributeTagsSpec_cmd {l : List (Option RunAs × CommandSpec)} {e : MatchedCommand}
    (he : e ∈ distributeTagsSpec l) : ∃ x ∈ l, e.2.2 = x.2.cmd := by
  simp only [distributeTagsSpec, List.mem_mapIdx] at he
  obtain ⟨i, hi, rfl⟩ := he
  exact ⟨l[i], List.getElem_mem hi, rfl⟩

/-- The runas spec in effect for a distributed entry was written explicitly on an entry of
the same list. -/
theorem mem_distributeTagsSpec_runas {l : List (Option RunAs × CommandSpec)}
    {e : MatchedCommand} (he : e ∈ distributeTagsSpec l) {ra : RunAs} (hra : e.1 = some ra) :
    ∃ x ∈ l, x.1 = some ra := by
  simp only [distributeTagsSpec, List.mem_mapIdx] at he
  obtain ⟨i, hi, rfl⟩ := he
  simp only [runasInEffect] at hra
  have hm := List.mem_of_getLast? hra
  obtain ⟨x, hx, hxr⟩ := List.mem_filterMap.1 hm
  exact ⟨x, List.mem_of_mem_take hx, hxr⟩

/-! ## P1: allow witness -/

/-- **P1, allow witness.** An allowed request has an applicable line, an applicable host group
of it, and a distributed command entry of that group that is the deciding entry: its runas spec
permits the request, its command spec takes part and grants `t'`, and the result is `t'` with
the root/self NOPASSWD exception applied. -/
theorem allow_witness (p : Policy) (r : Request User Group) (t : Tag)
    (h : authorize O p r = some t) :
    ∃ rule ∈ p.rules, userListMatches O p r rule.users = true ∧
      ∃ seg ∈ rule.permissions, hostListMatches O p r seg.1 = true ∧
        ∃ e ∈ distributeTagsSpec seg.2, decidingEntry O p r = some e ∧
          runasPermits O r (runasUserAliases O p r) (runasGroupAliases O p r) e.1 = true ∧
          cmdParticipates O p r e.2 = true ∧
          ∃ t', condition (cmndAliases O p r) (e.2.2, e.2.1) = some t' ∧
            t = (if skipPasswd O r then { t' with authenticate := .nopasswd } else t') := by
  obtain ⟨e, he, t', hc, ht⟩ := (authorize_eq_some_iff_deciding O p r t).1 h
  obtain ⟨hmem, hra, hcp⟩ := decidingEntry_spec O he
  obtain ⟨rule, hr, hu, seg, hs, hh, hd⟩ := (mem_candidatesSpec O p r e).1 hmem
  exact ⟨rule, hr, hu, seg, hs, hh, e, hd, he, hra, hcp, t', hc, ht⟩

/-- **When a participating entry grants**: `ALL`, a matching command, an alias that affirms
the item, or a negated alias that explicitly excludes it (substitution semantics). The granted
value is always the entry's own satellite data (the tag). -/
theorem condition_grants_iff {α τ : Type} (A : FoundAliases) (pred : α → Bool) (s : Spec α)
    (t t' : τ) (hm : matchedBy A pred s = true) :
    condition A (s, t) = some t' ↔ t' = t ∧
      (s = .allow .all ∨ (∃ c, s = .allow (.only c) ∧ pred c = true) ∨
        (∃ n, s = .allow (.alias n) ∧ A n = some true) ∨
        (∃ n, s = .forbid (.alias n) ∧ A n = some false)) := by
  have key : (condition A (s, ())).isSome = true ↔
      (s = .allow .all ∨ (∃ c, s = .allow (.only c) ∧ pred c = true) ∨
        (∃ n, s = .allow (.alias n) ∧ A n = some true) ∨
        (∃ n, s = .forbid (.alias n) ∧ A n = some false)) := by
    cases s with
    | allow m =>
      cases m with
      | all => simp [condition]
      | only c =>
        simp only [matchedBy, Qualified.who] at hm
        simp [condition, hm]
      | alias n =>
        cases hn : A n with
        | none => simp [matchedBy, Qualified.who, hn] at hm
        | some b => cases b <;> simp [condition, hn]
    | forbid m =>
      cases m with
      | all => simp [condition]
      | only c => simp [condition]
      | alias n =>
        cases hn : A n with
        | none => simp [matchedBy, Qualified.who, hn] at hm
        | some b => cases b <;> simp [condition, hn]
  rw [condition_info]
  constructor
  · intro h
    obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨rfl, key.1 (by simp [hu])⟩
  · rintro ⟨rfl, hs⟩
    have := key.2 hs
    cases hc : condition A (s, ()) with
    | none => rw [hc] at this; cases this
    | some u => rfl

/-- **When a participating entry denies**: `!ALL`, a matching `!command`, a negated alias that
affirms the item, or an alias that explicitly excludes it. -/
theorem condition_denies_iff {α τ : Type} (A : FoundAliases) (pred : α → Bool) (s : Spec α)
    (t : τ) (hm : matchedBy A pred s = true) :
    condition A (s, t) = none ↔
      (s = .forbid .all ∨ (∃ c, s = .forbid (.only c) ∧ pred c = true) ∨
        (∃ n, s = .forbid (.alias n) ∧ A n = some true) ∨
        (∃ n, s = .allow (.alias n) ∧ A n = some false)) := by
  cases s with
  | allow m =>
    cases m with
    | all => simp [condition]
    | only c => simp [condition]
    | alias n =>
      cases hn : A n with
      | none => simp [matchedBy, Qualified.who, hn] at hm
      | some b => cases b <;> simp [condition, hn]
  | forbid m =>
    cases m with
    | all => simp [condition]
    | only c =>
      simp only [matchedBy, Qualified.who] at hm
      simp [condition, hm]
    | alias n =>
      cases hn : A n with
      | none => simp [matchedBy, Qualified.who, hn] at hm
      | some b => cases b <;> simp [condition, hn]

theorem condition_some_eq {α τ : Type} {A : FoundAliases} {s : Spec α} {t t' : τ}
    (h : condition A (s, t) = some t') : t' = t := by
  cases s with
  | allow m =>
    cases m <;> simp only [condition] at h <;> (try split at h) <;> simp_all
  | forbid m =>
    cases m <;> simp only [condition] at h <;> (try split at h) <;> simp_all

/-! ## Alias tables: what a `some false` needs, and what an unmentioned item gets -/

/-- One spec mentions an item: it is `ALL` or a direct item that matches; the qualifier does
not matter, an alias reference alone does not count. -/
def specMentions {α : Type} (pred : α → Bool) (s : Spec α) : Bool :=
  match s.who with
  | .all => true
  | .only x => pred x
  | .alias _ => false

/-- A list mentions an item. -/
def mentions {α : Type} (pred : α → Bool) (l : SpecList α) : Bool := l.any (specMentions pred)

/-- Some definition of an alias table mentions an item. -/
def tableMentions {α : Type} (pred : α → Bool) (t : List (Def α)) : Bool :=
  t.any fun d => mentions pred d.items

theorem matchedBy_of_none {α : Type} (pred : α → Bool) (A : FoundAliases)
    (hA : ∀ k, A k = none) (s : Spec α) (h : specMentions pred s = false) :
    matchedBy A pred s = false := by
  unfold matchedBy
  unfold specMentions at h
  split <;> simp_all

theorem getAliasesStep_unmentioned {α : Type} (pred : α → Bool) (G : FoundAliases)
    (hG : ∀ k, G k = none) (d : Def α) (h : mentions pred d.items = false) :
    getAliasesStep pred G d = G := by
  rw [getAliasesStep_eq]
  have : aliasValue pred G d.items = none := by
    unfold aliasValue
    rw [(lastMatch_eq_none_iff _ _).2]
    · rfl
    · intro s hs
      exact matchedBy_of_none pred G hG s (by simpa using List.any_eq_false.1 h s hs)
  rw [this]

/-- **An item no alias definition mentions is in no alias.** -/
theorem getAliases_unmentioned {α : Type} (pred : α → Bool) (t : List (Def α))
    (h : tableMentions pred t = false) (k : String) : getAliases t pred k = none := by
  have key : ∀ (l : List (Def α)) (G : FoundAliases), (∀ k, G k = none) →
      (∀ d ∈ l, mentions pred d.items = false) → l.foldl (getAliasesStep pred) G = G := by
    intro l
    induction l with
    | nil => intro _ _ _; rfl
    | cons d l ih =>
      intro G hG hl
      rw [List.foldl_cons, getAliasesStep_unmentioned pred G hG d (hl d List.mem_cons_self)]
      exact ih G hG (fun d' hd' => hl d' (List.mem_cons_of_mem _ hd'))
  unfold getAliases
  rw [key t FoundAliases.empty (fun _ => rfl)]
  · rfl
  · intro d hd
    simpa using List.any_eq_false.1 h d hd

/-- A list that does not mention an item, with an alias table that holds nothing, does not
accept it. -/
theorem findItemSpec_unmentioned {α : Type} (pred : α → Bool) (A : FoundAliases)
    (hA : ∀ k, A k = none) (l : SpecList α) (h : mentions pred l = false) :
    findItemSpec pred A (withUnit l) = none := by
  rw [← findItem_eq_spec]
  apply findItem_of_no_match
  intro x hx
  simp only [withUnit, List.mem_map] at hx
  obtain ⟨s, hs, rfl⟩ := hx
  exact matchedBy_of_none pred A hA s (by simpa using List.any_eq_false.1 h s hs)

/-- An alias table entry `some false` needs a `!` somewhere in the table. -/
theorem getAliases_false {α : Type} (pred : α → Bool) (t : List (Def α)) (k : String)
    (h : getAliases t pred k = some false) :
    ∃ d ∈ t, ∃ s ∈ d.items, ∃ m, s = .forbid m := by
  have key : ∀ (l : List (Def α)) (G : FoundAliases), (∀ d ∈ l, d ∈ t) →
      (∀ k, G k = some false → ∃ d ∈ t, ∃ s ∈ d.items, ∃ m, s = .forbid m) →
      ∀ k, l.foldl (getAliasesStep pred) G k = some false →
        ∃ d ∈ t, ∃ s ∈ d.items, ∃ m, s = .forbid m := by
    intro l
    induction l with
    | nil => intro G _ hG k hk; exact hG k hk
    | cons d l ih =>
      intro G hl hG
      rw [List.foldl_cons]
      apply ih _ (fun d' hd' => hl d' (List.mem_cons_of_mem _ hd'))
      intro k hk
      rw [getAliasesStep_eq] at hk
      cases hv : aliasValue pred G d.items with
      | none => rw [hv] at hk; exact hG k hk
      | some b =>
        rw [hv] at hk
        simp only [FoundAliases.insert] at hk
        split at hk
        · cases hk
          unfold aliasValue at hv
          obtain ⟨s, hs, hsb⟩ := Option.map_eq_some_iff.1 hv
          obtain ⟨hsmem, hsm⟩ := lastMatch_spec hs
          have hnone : condition G (s, ()) = none := by
            cases hc : condition G (s, ()) with
            | none => rfl
            | some _ => rw [hc] at hsb; cases hsb
          rcases (condition_denies_iff G pred s () hsm).1 hnone with
            rfl | ⟨c, rfl, -⟩ | ⟨n, rfl, -⟩ | ⟨n, rfl, hn⟩
          · exact ⟨d, hl d List.mem_cons_self, _, hsmem, _, rfl⟩
          · exact ⟨d, hl d List.mem_cons_self, _, hsmem, _, rfl⟩
          · exact ⟨d, hl d List.mem_cons_self, _, hsmem, _, rfl⟩
          · exact hG n hn
        · exact hG k hk
  exact key t _ (fun _ hd => hd) (fun _ hk => by cases hk) k h

/-- The spec is not negated (an even number of `!`). -/
def Qualified.isAllow {α : Type} : Qualified α → Bool
  | .allow _ => true
  | .forbid _ => false

/-- A table without `!` never explicitly excludes an item. -/
theorem getAliases_ne_false {α : Type} (pred : α → Bool) (t : List (Def α))
    (h : ∀ d ∈ t, ∀ s ∈ d.items, s.isAllow = true) (k : String) :
    getAliases t pred k ≠ some false := by
  intro hk
  obtain ⟨d, hd, s, hs, m, rfl⟩ := getAliases_false pred t k hk
  have := h d hd _ hs
  simp [Qualified.isAllow] at this

/-! ## P2: unmentioned users, hosts and commands are never allowed -/

/-- Some user list of a line or some `User_Alias` definition mentions the invoking user. -/
def userMentioned (p : Policy) (r : Request User Group) : Bool :=
  p.rules.any (fun rule => mentions (matchUser O r.invokingUser) rule.users) ||
    tableMentions (matchUser O r.invokingUser) p.aliases.user

/-- Some host list of a host group or some `Host_Alias` definition mentions the host. -/
def hostMentioned (p : Policy) (r : Request User Group) : Bool :=
  p.rules.any (fun rule => rule.permissions.any fun seg => mentions (matchHost O r.host) seg.1) ||
    tableMentions (matchHost O r.host) p.aliases.host

/-- Some command spec of an entry or some `Cmnd_Alias` definition mentions the command. -/
def cmdMentioned (p : Policy) (r : Request User Group) : Bool :=
  p.rules.any (fun rule => rule.permissions.any fun seg =>
      seg.2.any fun e => specMentions (matchCommand O r.command r.arguments) e.2.cmd) ||
    tableMentions (matchCommand O r.command r.arguments) p.aliases.cmnd

/-- **P2, users.** An invoking user that no user list and no `User_Alias` definition mentions
(by `ALL` or a direct item that matches, under any number of `!`) is never allowed. -/
theorem unmentioned_user_unmatched (p : Policy) (r : Request User Group)
    (h : userMentioned O p r = false) : authorize O p r = none := by
  simp only [userMentioned, Bool.or_eq_false_iff] at h
  apply default_deny_no_applicable_line
  intro rule hr
  unfold userListMatches
  rw [findItemSpec_unmentioned _ _ (getAliases_unmentioned _ _ h.2)]
  · rfl
  · simpa using List.any_eq_false.1 h.1 rule hr

/-- **P2, hosts.** A host that no host list and no `Host_Alias` definition mentions is never
allowed. -/
theorem unmentioned_host_unmatched (p : Policy) (r : Request User Group)
    (h : hostMentioned O p r = false) : authorize O p r = none := by
  simp only [hostMentioned, Bool.or_eq_false_iff] at h
  apply deny_of_no_deciding
  intro e he
  exfalso
  obtain ⟨rule, hr, -, seg, hs, hh, -⟩ := (mem_candidatesSpec O p r e).1 he
  have hrule := List.any_eq_false.1 h.1 rule hr
  simp only [Bool.not_eq_true, List.any_eq_false] at hrule
  have hseg := hrule seg hs
  unfold hostListMatches at hh
  rw [findItemSpec_unmentioned _ _ (getAliases_unmentioned _ _ h.2) _ (by simpa using hseg)] at hh
  cases hh

/-- **P2, commands.** A command that no command spec of an entry and no `Cmnd_Alias`
definition mentions is never allowed. -/
theorem unmentioned_command_unmatched (p : Policy) (r : Request User Group)
    (h : cmdMentioned O p r = false) : authorize O p r = none := by
  simp only [cmdMentioned, Bool.or_eq_false_iff] at h
  apply deny_of_no_deciding
  intro e he
  obtain ⟨rule, hr, -, seg, hs, -, hd⟩ := (mem_candidatesSpec O p r e).1 he
  obtain ⟨x, hx, hcmd⟩ := mem_distributeTagsSpec_cmd hd
  have hrule := List.any_eq_false.1 h.1 rule hr
  simp only [Bool.not_eq_true, List.any_eq_false] at hrule
  have hx' := hrule seg hs x hx
  have hpart : cmdParticipates O p r e.2 = false := by
    unfold cmdParticipates
    rw [hcmd]
    exact matchedBy_of_none _ _ (getAliases_unmentioned _ _ h.2) _ (by simpa using hx')
  simp [entryDecides, hpart]

/-! ## P2r: unmentioned runas targets -/

/-- Some runas user list of an entry or some `Runas_Alias` definition mentions the target
user. -/
def runasUserMentioned (p : Policy) (r : Request User Group) : Bool :=
  p.rules.any (fun rule => rule.permissions.any fun seg =>
      seg.2.any fun e => match e.1 with
        | some ra => mentions (matchUser O r.targetUser) ra.users
        | none => false) ||
    tableMentions (matchUser O r.targetUser) p.aliases.runas

/-- **P2r, the sudo-rs form.** The documented analogue of P2 for runas ("a target user other
than the invoker that no runas list mentions is never allowed", an absent runas spec meaning
the user named `root`) does not hold (finding F2; certificate `Certificates.d_f2_toor`). What
does hold: such a target is allowed only if it is root by `is_root` (uid 0, not by name), and
only through a deciding entry without a runas spec. -/
theorem unmentioned_runas_target (p : Policy) (r : Request User Group) (t : Tag)
    (h : runasUserMentioned O p r = false)
    (hne : O.userEq r.targetUser r.invokingUser = false) (ht : authorize O p r = some t) :
    O.isRoot r.targetUser = true ∧ ∃ e, decidingEntry O p r = some e ∧ e.1 = none := by
  simp only [runasUserMentioned, Bool.or_eq_false_iff] at h
  obtain ⟨e, he, -⟩ := (authorize_eq_some_iff_deciding O p r t).1 ht
  obtain ⟨hmem, hra, -⟩ := decidingEntry_spec O he
  cases he1 : e.1 with
  | none =>
    rw [he1] at hra
    simp only [runasPermits, Bool.and_eq_true] at hra
    exact ⟨hra.1, e, he, he1⟩
  | some ra =>
    exfalso
    obtain ⟨rule, hr, -, seg, hs, -, hd⟩ := (mem_candidatesSpec O p r e).1 hmem
    obtain ⟨x, hx, hxr⟩ := mem_distributeTagsSpec_runas hd he1
    have hrule := List.any_eq_false.1 h.1 rule hr
    simp only [Bool.not_eq_true, List.any_eq_false] at hrule
    have hx' := hrule seg hs x hx
    rw [hxr] at hx'
    have hf : findItemSpec (matchUser O r.targetUser) (runasUserAliases O p r)
        (withUnit ra.users) = none :=
      findItemSpec_unmentioned _ _ (getAliases_unmentioned _ _ h.2) _ (by simpa using hx')
    rw [he1] at hra
    simp [runasPermits, hne, hf] at hra

/-! ## P3: denial needs a `!` on the command side -/

/-- **P3, denial needs a command-side `!`.** If some allowed entry takes part for the command
and the request is denied, the final such entry is a negated command spec, or a reference to a
`Cmnd_Alias` that explicitly excludes the command, and then the `Cmnd_Alias` table contains a
negated item. -/
theorem deny_needs_cmd_negation (p : Policy) (r : Request User Group)
    (hex : ∃ e ∈ allowedSpec O p r, cmdParticipates O p r e = true)
    (hden : authorize O p r = none) :
    ∃ e, IsFinalMatch (cmdParticipates O p r) (allowedSpec O p r) e ∧
      ((∃ m, e.2 = .forbid m) ∨
        (∃ n, e.2 = .allow (.alias n) ∧ cmndAliases O p r n = some false ∧
          ∃ d ∈ p.aliases.cmnd, ∃ s ∈ d.items, ∃ m, s = .forbid m)) := by
  cases hl : lastMatch (cmdParticipates O p r) (allowedSpec O p r) with
  | none =>
    obtain ⟨e, he, hp⟩ := hex
    rw [(lastMatch_eq_none_iff _ _).1 hl e he] at hp
    cases hp
  | some e =>
    have hfin := (lastMatch_eq_some_iff _ _ _).1 hl
    have hcp : checkPermission O p r = none := by
      simpa [authorize] using hden
    have hc := (checkPermission_eq_none_iff O p r).1 hcp e hfin
    have hm : matchedBy (cmndAliases O p r) (matchCommand O r.command r.arguments) e.2 = true :=
      (lastMatch_spec hl).2
    refine ⟨e, hfin, ?_⟩
    rcases (condition_denies_iff _ _ e.2 e.1 hm).1 hc with
      h | ⟨c, h, -⟩ | ⟨n, h, -⟩ | ⟨n, h, hn⟩
    · exact Or.inl ⟨_, h⟩
    · exact Or.inl ⟨_, h⟩
    · exact Or.inl ⟨_, h⟩
    · exact Or.inr ⟨n, h, hn, getAliases_false _ _ _ hn⟩

/-! ## P3b: `!` in host lists and runas lists -/

/-- **P3b, hosts.** Deleting a `Host_List = Cmnd_Spec_List` group whose host list does not
accept the host changes no decision: a `!` in a host list only switches its group off. Runas
specs and tags restart at each group (`distribute_tags` runs per group), so the neighbouring
groups are unaffected. -/
theorem inapplicable_hostgroup_irrelevant (p : Policy) (r : Request User Group)
    (pre post : List PermissionSpec) (users : SpecList UserSpecifier)
    (sp ss : List (SpecList Hostname × List (Option RunAs × CommandSpec)))
    (seg : SpecList Hostname × List (Option RunAs × CommandSpec))
    (h : hostListMatches O p r seg.1 = false) :
    authorize O { p with rules := pre ++ ⟨users, sp ++ seg :: ss⟩ :: post } r =
      authorize O { p with rules := pre ++ ⟨users, sp ++ ss⟩ :: post } r := by
  refine authorize_congr O _ _ r rfl ?_
  simp only [candidatesSpec, List.flatMap_append, List.flatMap_cons]
  have : hostListMatches O { p with rules := pre ++ ⟨users, sp ++ seg :: ss⟩ :: post } r seg.1 =
    false := h
  simp [this]
  rfl

/-- **The runas rule of sudo-rs, exactly.** With an explicit runas spec: a target other than
the invoker must be in the user list and the target group one of the target's groups or in the
group list; the invoker running as themself with one of their groups needs nothing if the user
list is empty and to be in the user list otherwise; the invoker running as themself with a
foreign group needs the group in the group list, whatever the user list says. -/
theorem runasPermits_some_eq (r : Request User Group) (RU RG : FoundAliases) (ra : RunAs) :
    runasPermits O r RU RG (some ra) =
      if O.userEq r.targetUser r.invokingUser then
        if inGroup O r.targetUser r.targetGroup then
          ra.users.isEmpty ||
            (findItemSpec (matchUser O r.targetUser) RU (withUnit ra.users)).isSome
        else (findItemSpec (matchGroup O r.targetGroup) RG (withUnit ra.groups)).isSome
      else (findItemSpec (matchUser O r.targetUser) RU (withUnit ra.users)).isSome &&
        (inGroup O r.targetUser r.targetGroup ||
          (findItemSpec (matchGroup O r.targetGroup) RG (withUnit ra.groups)).isSome) := by
  simp only [runasPermits]
  cases O.userEq r.targetUser r.invokingUser <;>
    cases inGroup O r.targetUser r.targetGroup <;>
    cases ra.users.isEmpty <;>
    cases (findItemSpec (matchUser O r.targetUser) RU (withUnit ra.users)).isSome <;>
    cases (findItemSpec (matchGroup O r.targetGroup) RG (withUnit ra.groups)).isSome <;> rfl

/-- **F3: the group list is ignored when the target user is in the target group**, including a
`!group` that names it: the documented "a `!` in a runas list switches the entry off" fails
(certificate `Certificates.e_f3_negated_group`). -/
theorem runas_grouplist_ignored (r : Request User Group) (RU RG : FoundAliases)
    (users : SpecList UserSpecifier) (gs gs' : SpecList Identifier)
    (h : inGroup O r.targetUser r.targetGroup = true) :
    runasPermits O r RU RG (some ⟨users, gs⟩) = runasPermits O r RU RG (some ⟨users, gs'⟩) := by
  simp [runasPermits_some_eq, h]

/-- **F5: the user list is ignored when the invoker runs as themself with a group that is not
theirs**, including a `!user` that names the invoker (certificate
`Certificates.g_f5_negated_self`). -/
theorem runas_userlist_ignored (r : Request User Group) (RU RG : FoundAliases)
    (us us' : SpecList UserSpecifier) (groups : SpecList Identifier)
    (hself : O.userEq r.targetUser r.invokingUser = true)
    (h : inGroup O r.targetUser r.targetGroup = false) :
    runasPermits O r RU RG (some ⟨us, groups⟩) = runasPermits O r RU RG (some ⟨us', groups⟩) := by
  simp [runasPermits_some_eq, hself, h]

/-! ## P4, P5, P6: lines -/

/-- **P4, the last line decides.** If line `R` has an entry that takes part (runas permits,
command spec participates) and no entry of a later line does, the lines before `R` are
irrelevant: any `pre'` in place of `pre` gives the same decision. -/
theorem last_line_decides (p : Policy) (r : Request User Group)
    (pre pre' post : List PermissionSpec) (R : PermissionSpec)
    (hR : ∃ e ∈ ruleCandidates O p r R, entryDecides O p r e = true)
    (hpost : ∀ R' ∈ post, ∀ e ∈ ruleCandidates O p r R', entryDecides O p r e = false) :
    authorize O { p with rules := pre ++ R :: post } r =
      authorize O { p with rules := pre' ++ R :: post } r := by
  have hd : ∀ q : List PermissionSpec,
      decidingEntry O { p with rules := q ++ R :: post } r =
        lastMatch (entryDecides O p r) (ruleCandidates O p r R) := by
    intro q
    have hpn : lastMatch (entryDecides O p r) (post.flatMap (ruleCandidates O p r)) = none := by
      apply (lastMatch_eq_none_iff _ _).2
      intro e he
      obtain ⟨R', hR', he'⟩ := List.mem_flatMap.1 he
      exact hpost R' hR' e he'
    obtain ⟨e₀, he₀, hd₀⟩ := hR
    cases hRm : lastMatch (entryDecides O p r) (ruleCandidates O p r R) with
    | none => rw [(lastMatch_eq_none_iff _ _).1 hRm e₀ he₀] at hd₀; cases hd₀
    | some e =>
      show lastMatch (entryDecides O p r)
        ((q ++ R :: post).flatMap (ruleCandidates O p r)) = some e
      rw [List.flatMap_append, List.flatMap_cons, lastMatch_append, lastMatch_append, hpn, hRm]
      rfl
  rw [authorize, authorize, checkPermission_eq_deciding, checkPermission_eq_deciding, hd, hd]
  rfl

/-- **P5, lines of other users are irrelevant.** Inserting, at any position, a line whose user
list does not accept the invoking user changes no decision (`inapplicable_line_irrelevant`). -/
theorem insert_other_user_irrelevant (p : Policy) (r : Request User Group)
    (pre post : List PermissionSpec) (R : PermissionSpec)
    (hR : userListMatches O p r R.users = false) :
    authorize O { p with rules := pre ++ R :: post } r =
      authorize O { p with rules := pre ++ post } r :=
  inapplicable_line_irrelevant O p r pre post R hR

/-- **P6, adding a line without a command-side `!` never revokes.** If no command spec of `R`
is negated and the `Cmnd_Alias` table contains no negated item, inserting `R` anywhere keeps
every allowed request allowed. -/
theorem add_positive_preserves_allow (p : Policy) (r : Request User Group)
    (pre post : List PermissionSpec) (R : PermissionSpec)
    (hR : ∀ seg ∈ R.permissions, ∀ x ∈ seg.2, x.2.cmd.isAllow = true)
    (hA : ∀ d ∈ p.aliases.cmnd, ∀ s ∈ d.items, s.isAllow = true)
    (h : (authorize O { p with rules := pre ++ post } r).isSome = true) :
    (authorize O { p with rules := pre ++ R :: post } r).isSome = true := by
  rw [authorize_isSome_iff, checkPermission_eq_deciding] at h ⊢
  have hca : ∀ q : List PermissionSpec, cmndAliases O { p with rules := q } r = cmndAliases O p r :=
    fun _ => rfl
  have hdq : ∀ q : List PermissionSpec, decidingEntry O { p with rules := q } r =
      lastMatch (entryDecides O p r) (q.flatMap (ruleCandidates O p r)) := fun _ => rfl
  rw [hca, hdq] at h ⊢
  rw [List.flatMap_append, lastMatch_append] at h
  rw [List.flatMap_append, List.flatMap_cons, lastMatch_append, lastMatch_append]
  cases hpo : lastMatch (entryDecides O p r) (post.flatMap (ruleCandidates O p r)) with
  | some e => rw [hpo] at h; exact h
  | none =>
    rw [hpo] at h
    cases hRm : lastMatch (entryDecides O p r) (ruleCandidates O p r R) with
    | none => exact h
    | some e =>
      simp only [Option.none_or, Option.some_or, Option.bind_some]
      obtain ⟨hmem, hdec⟩ := lastMatch_spec hRm
      obtain ⟨-, seg, hs, -, hd⟩ := (mem_ruleCandidates O p r R e).1 hmem
      obtain ⟨x, hx, hcmd⟩ := mem_distributeTagsSpec_cmd hd
      simp only [entryDecides, Bool.and_eq_true] at hdec
      have hm := hdec.2
      unfold cmdParticipates at hm
      cases hc : condition (cmndAliases O p r) (e.2.2, e.2.1) with
      | some _ => rfl
      | none =>
        exfalso
        have hx' := hR seg hs x hx
        rw [← hcmd] at hx'
        rcases (condition_denies_iff _ _ e.2.2 e.2.1 hm).1 hc with
          h' | ⟨c, h', -⟩ | ⟨n, h', -⟩ | ⟨n, -, hn⟩
        · rw [h'] at hx'; cases hx'
        · rw [h'] at hx'; cases hx'
        · rw [h'] at hx'; cases hx'
        · exact getAliases_ne_false _ _ hA n hn

/-! ## P7, P8: runas -/

/-- **P7, `()` and `(: group)` only run as oneself.** A runas spec with an empty user list only
permits the invoking user as target. -/
theorem myself_no_impersonation (r : Request User Group) (RU RG : FoundAliases)
    (gs : SpecList Identifier) (h : runasPermits O r RU RG (some ⟨[], gs⟩) = true) :
    O.userEq r.targetUser r.invokingUser = true := by
  cases hu : O.userEq r.targetUser r.invokingUser with
  | true => rfl
  | false =>
    simp [runasPermits, hu, findItemSpec, withUnit, lastMatch] at h

/-- **P7 at the decision level.** If the deciding entry's runas user list is empty, the target
user is the invoking user. -/
theorem myself_no_impersonation_decision (p : Policy) (r : Request User Group)
    (e : MatchedCommand) (he : decidingEntry O p r = some e) (gs : SpecList Identifier)
    (hra : e.1 = some ⟨[], gs⟩) : O.userEq r.targetUser r.invokingUser = true := by
  obtain ⟨-, hr, -⟩ := decidingEntry_spec O he
  rw [hra] at hr
  exact myself_no_impersonation O r _ _ gs hr

/-- **P8, `-g group` is justified.** A target group permitted by a runas spec is one of the
target user's groups or is accepted by the spec's group list. -/
theorem runas_group_justified (r : Request User Group) (RU RG : FoundAliases)
    (ra : Option RunAs) (h : runasPermits O r RU RG ra = true) :
    inGroup O r.targetUser r.targetGroup = true ∨
      ∃ ra', ra = some ra' ∧
        (findItemSpec (matchGroup O r.targetGroup) RG (withUnit ra'.groups)).isSome = true := by
  cases ra with
  | none =>
    simp only [runasPermits, Bool.and_eq_true] at h
    exact Or.inl h.2
  | some ra =>
    simp only [runasPermits, Bool.and_eq_true, Bool.or_eq_true] at h
    rcases h.2 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr ⟨ra, rfl, h2⟩

/-- **P8 at the decision level.** -/
theorem runas_group_justified_decision (p : Policy) (r : Request User Group)
    (e : MatchedCommand) (he : decidingEntry O p r = some e) :
    inGroup O r.targetUser r.targetGroup = true ∨
      ∃ ra', e.1 = some ra' ∧
        (findItemSpec (matchGroup O r.targetGroup) (runasGroupAliases O p r)
          (withUnit ra'.groups)).isSome = true :=
  runas_group_justified O r _ _ e.1 (decidingEntry_spec O he).2.1

/-! ## P9: NOPASSWD needs an explicit tag -/

theorem implicitSetenv_authenticate (cmd : Spec Command) (t : Tag) :
    (implicitSetenv cmd t).authenticate = t.authenticate := by
  unfold implicitSetenv
  split
  · split <;> rfl
  · rfl

theorem applyMods_nopasswd (mods : List Modifier) (t : Tag)
    (h : (applyMods mods t).authenticate = .nopasswd) :
    t.authenticate = .nopasswd ∨ Modifier.nopasswd ∈ mods := by
  induction mods generalizing t with
  | nil => exact Or.inl h
  | cons m ms ih =>
    have h' : (applyMods ms (m.apply t)).authenticate = .nopasswd := h
    rcases ih _ h' with h1 | h1
    · cases m <;> simp_all [Modifier.apply]
    · exact Or.inr (List.mem_cons_of_mem _ h1)

/-- **P9, NOPASSWD needs an explicit tag.** A granted tag without password comes from the
root/self exception of `Sudoers::check` (`skipPasswd`), or from a `NOPASSWD` modifier written in
the deciding host group at or before the deciding entry: no NOPASSWD leaks in from another
line, another host group, or another user's line. -/
theorem nopasswd_needs_explicit_tag (p : Policy) (r : Request User Group) (t : Tag)
    (ht : authorize O p r = some t) (hn : t.authenticate = .nopasswd) :
    skipPasswd O r = true ∨
      ∃ rule ∈ p.rules, userListMatches O p r rule.users = true ∧
        ∃ seg ∈ rule.permissions, hostListMatches O p r seg.1 = true ∧
          ∃ i e, decidingEntry O p r = some e ∧ (distributeTagsSpec seg.2)[i]? = some e ∧
            Modifier.nopasswd ∈ (seg.2.take (i + 1)).flatMap (·.2.mods) := by
  cases hs : skipPasswd O r with
  | true => exact Or.inl rfl
  | false =>
    right
    obtain ⟨e, he, t', hc, htt⟩ := (authorize_eq_some_iff_deciding O p r t).1 ht
    rw [hs] at htt
    simp only [Bool.false_eq_true, ite_false] at htt
    subst htt
    have het := condition_some_eq hc
    subst het
    obtain ⟨hmem, -, -⟩ := decidingEntry_spec O he
    obtain ⟨rule, hr, hu, seg, hseg, hh, hd⟩ := (mem_candidatesSpec O p r e).1 hmem
    refine ⟨rule, hr, hu, seg, hseg, hh, ?_⟩
    simp only [distributeTagsSpec, List.mem_mapIdx] at hd
    obtain ⟨i, hi, rfl⟩ := hd
    refine ⟨i, _, he, ?_, ?_⟩
    · simp [distributeTagsSpec, hi]
    · simp only [implicitSetenv_authenticate, tagInEffect] at hn
      rcases applyMods_nopasswd _ {} hn with h0 | h0
      · cases h0
      · exact h0

end SudoersSpec
