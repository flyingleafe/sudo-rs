import Differential.GeneratorRange
import SudoersSpec.Grammar.PermissionExamples

namespace Differential.OrdinaryPolicyRange

open SudoersSpec SudoersSpec.Grammar SudoersSpec.Syntax
open Differential.GeneratorRange Differential.Generate

private abbrev Both (P : Spec α → Prop) (a : Meta α) : Prop := P (.allow a) ∧ P (.forbid a)

private theorem negate_range {a : Meta α} {P : Spec α → Prop} (h : Both P a) :
    Produces (Generate.negate (.allow a)) P := by
  unfold Generate.negate
  refine seq (Q := P) (P := fun _ => True) (fun _ => trivial) ?_
  intro b _
  cases b
  · exact ret _ P h.1
  · exact ret _ P h.2

private theorem item_range {P : Spec α → Prop} {plain : Gen α} {aliases : List String}
    (ha : Both P .all) (ht : ∀ a ∈ aliases, Both P (.alias a))
    (hp : Produces plain (fun v => Both P (.only v))) :
    Produces (Generate.item plain aliases []) P := by
  unfold Generate.item
  simp only [List.isEmpty_nil, ite_true]
  have hn : 0 < totalWeight [(1, 0), (if aliases.isEmpty then 0 else 3, 1), (0, 3), (8, 2)] := by
    cases aliases <;> simp [totalWeight]
  refine seq (Q := P) (weighted_mem _ hn) ?_
  rintro a ⟨w, hm, hw⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
  rcases hm with ⟨_, rfl⟩ | ⟨he, rfl⟩ | ⟨rfl, rfl⟩ | ⟨_, rfl⟩
  · exact negate_range ha
  · have hne : aliases ≠ [] := by rintro rfl; simp at he; omega
    exact seq (Q := P) (pick_mem aliases hne) (fun n hn => negate_range (ht n hn))
  · exact False.elim (by omega)
  · exact seq (Q := P) hp (fun x hx => negate_range hx)

private theorem commandItem_range {P : Spec Command → Prop} {aliases : List String}
    (ha : Both P .all) (ht : ∀ a ∈ aliases, Both P (.alias a))
    (hc : Produces Generate.command (fun a => Both P (.only a))) :
    Produces (Generate.cmndSpecItem {} aliases) P := by
  unfold Generate.cmndSpecItem
  simp only [Bool.false_eq_true, ite_false]
  have hn : 0 < totalWeight [(2, 0), (if aliases.isEmpty then 0 else 2, 1), (0, 3), (7, 2)] := by
    cases aliases <;> simp [totalWeight]
  refine seq (Q := P) (weighted_mem _ hn) ?_
  rintro a ⟨w, hm, hw⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
  rcases hm with ⟨_, rfl⟩ | ⟨he, rfl⟩ | ⟨rfl, rfl⟩ | ⟨_, rfl⟩
  · exact negate_range ha
  · have hne : aliases ≠ [] := by rintro rfl; simp at he; omega
    exact seq (Q := P) (pick_mem aliases hne) (fun n hn => negate_range (ht n hn))
  · exact False.elim (by omega)
  · exact seq (Q := P) hc (fun x hx => negate_range hx)

private def plainUsers : List UserSpecifier :=
  ((policyUserNames.map (.user ∘ .name) ++ uids.map (.user ∘ .id)) ++
    groupNames.map (.group ∘ .name)) ++ gids.map (.group ∘ .id)

private def plainGroups : List Identifier :=
  (groupNames.filter (!capsGroups.contains ·)).map .name ++ gids.map .id

private def plainHosts : List Hostname := hosts.filter (!capsHosts.contains ·)

private def argShapes : List Args :=
  [.prefix [], .exact []] ++
    argPool.map (fun a => .exact [a]) ++
    argPool.flatMap (fun a => argPool.map (fun b => .exact [a, b])) ++
    argPool.map (fun a => .prefix [a])

private theorem user_mem : Produces Generate.userSpecifier (· ∈ plainUsers) := by
  unfold Generate.userSpecifier
  refine seq (Q := fun u => u ∈ plainUsers)
    (weighted_mem [(6, 0), (2, 1), (3, 2), (1, 3)] (by decide)) ?_
  rintro v ⟨w, hm, _⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
  rcases hm with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · refine seq (Q := fun u => u ∈ plainUsers) (pick_mem policyUserNames (by decide)) ?_
    intro u hu; apply ret
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨u, hu, rfl⟩)))
  · refine seq (Q := fun u => u ∈ plainUsers) (pick_mem uids (by decide)) ?_
    intro u hu; apply ret
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨u, hu, rfl⟩)))
  · refine seq (Q := fun u => u ∈ plainUsers) (pick_mem groupNames (by decide)) ?_
    intro u hu; apply ret
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨u, hu, rfl⟩))
  · refine seq (Q := fun u => u ∈ plainUsers) (pick_mem gids (by decide)) ?_
    intro u hu; apply ret
    exact List.mem_append_right _ (List.mem_map.mpr ⟨u, hu, rfl⟩)

private theorem group_mem : Produces Generate.groupIdentifier (· ∈ plainGroups) := by
  unfold Generate.groupIdentifier
  refine seq (Q := fun a => a ∈ plainGroups) (P := fun _ => True) (fun _ => trivial) ?_
  intro b _; cases b
  · exact seq (Q := fun a => a ∈ plainGroups) (pick_mem gids (by decide))
      (fun n hn => ret _ _ (List.mem_append_right _ (List.mem_map.mpr ⟨n, hn, rfl⟩)))
  · exact seq (Q := fun a => a ∈ plainGroups) (pick_mem (groupNames.filter (!capsGroups.contains ·)) (by decide))
      (fun n hn => ret _ _ (List.mem_append_left _ (List.mem_map.mpr ⟨n, hn, rfl⟩)))

private theorem args_mem : Produces Generate.args (· ∈ argShapes) := by
  unfold Generate.args
  refine seq (Q := fun a => a ∈ argShapes)
    (weighted_mem [(5, 0), (2, 1), (3, 2), (1, 3)] (by decide)) ?_
  rintro n ⟨w, hm, _⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
  rcases hm with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact ret _ _ (by decide)
  · exact ret _ _ (by decide)
  · refine seq (Q := fun a => a ∈ argShapes) (listOf_range (pick_mem argPool (by decide)) 1 2 (by decide)) ?_
    rintro l ⟨h₁, h₂, hc⟩
    apply ret
    rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩
    · simp at h₁
    · apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_right
      exact List.mem_map.mpr ⟨a, hc a (by simp), rfl⟩
    · apply List.mem_append_left
      apply List.mem_append_right
      exact List.mem_flatMap.mpr ⟨a, hc a (by simp), List.mem_map.mpr ⟨b, hc b (by simp), rfl⟩⟩
    · simp at h₂
  · refine seq (Q := fun a => a ∈ argShapes) (listOf_range (pick_mem argPool (by decide)) 1 1 (by decide)) ?_
    rintro l ⟨h₁, h₂, hc⟩
    apply ret
    rcases l with _ | ⟨a, _ | ⟨b, bs⟩⟩
    · simp at h₁
    · apply List.mem_append_right
      exact List.mem_map.mpr ⟨a, hc a (by simp), rfl⟩
    · simp at h₂

private theorem command_mem :
    Produces Generate.command (fun c => c.pattern ∈ paths ∧ c.args ∈ argShapes) := by
  unfold Generate.command
  refine seq (Q := fun c : Command => c.pattern ∈ paths ∧ c.args ∈ argShapes) (pick_mem paths (by decide)) ?_
  intro p hp
  exact seq (Q := fun c : Command => c.pattern ∈ paths ∧ c.args ∈ argShapes) args_mem
    (fun a ha => ret (⟨p, a⟩ : Command) (fun c => c.pattern ∈ paths ∧ c.args ∈ argShapes) ⟨hp, ha⟩)

/-! The ordinary policy generator uses ASCII spellings, so use the reference Latin-1
character oracle, with an explicit filesystem and glob snapshot. -/

def snapshot (fs : FsOracle) (glob : GlobOracle) : Oracles :=
  { PermissionExamples.O with fs, glob }

def PathSnapshot (fs : FsOracle) (glob : GlobOracle) : Prop :=
  ∀ p ∈ paths, (fs.canonicalize p = .err ∨ fs.canonicalize p = .ok p) ∧ glob.compile p = none

private abbrev UserGood (O : Oracles) (u : Spec UserSpecifier) := UserValue O u.who ∧ FirstUserValue u
private abbrev HostGood (O : Oracles) (u : Spec Hostname) := PrintableMeta O.char u.who
private abbrev GroupGood (O : Oracles) (u : Spec Identifier) := IdentifierValue O u.who
private abbrev CmdGood (O : Oracles) (u : Spec Command) := CommandMemberValue O u.who

private theorem userLeaves (fs : FsOracle) (glob : GlobOracle) (a : UserSpecifier)
    (ha : a ∈ plainUsers) : Both (UserGood (snapshot fs glob)) (.only a) := by
  have h : ∀ a ∈ plainUsers, Both (UserGood PermissionExamples.O) (.only a) := by decide
  cases a with
  | user i => cases i <;> exact h _ ha
  | group i | nonunixGroup i => cases i <;> exact h _ ha

private theorem userAlias (fs : FsOracle) (glob : GlobOracle) (p : String)
    (hp : p = "UA" ∨ p = "RA") {n : String} (hn : n ∈ aliasPool p) :
    Both (UserGood (snapshot fs glob)) (.alias n) := by
  have hUA : ∀ n ∈ aliasPool "UA", Both (UserGood PermissionExamples.O) (.alias n) := by decide
  have hRA : ∀ n ∈ aliasPool "RA", Both (UserGood PermissionExamples.O) (.alias n) := by decide
  rcases hp with rfl | rfl
  · exact hUA n hn
  · exact hRA n hn

private theorem groupLeaves (fs : FsOracle) (glob : GlobOracle) (a : Identifier)
    (ha : a ∈ plainGroups) : Both (GroupGood (snapshot fs glob)) (.only a) := by
  have h : ∀ a ∈ plainGroups, Both (GroupGood PermissionExamples.O) (.only a) := by decide
  cases a <;> exact h _ ha

private theorem groupAlias (fs : FsOracle) (glob : GlobOracle) {a : String}
    (ha : a ∈ aliasPool "RA") : Both (GroupGood (snapshot fs glob)) (.alias a) := by
  have h : ∀ a ∈ aliasPool "RA", Both (GroupGood PermissionExamples.O) (.alias a) := by decide
  exact h a ha

private theorem hostLeaves (fs : FsOracle) (glob : GlobOracle) (a : Hostname)
    (ha : a ∈ plainHosts) : Both (HostGood (snapshot fs glob)) (.only a) := by
  have h : ∀ a ∈ plainHosts, Both (HostGood PermissionExamples.O) (.only a) := by decide
  exact h a ha

private theorem hostAlias (fs : FsOracle) (glob : GlobOracle) {a : String} (ha : a ∈ aliasPool "HA") :
    Both (HostGood (snapshot fs glob)) (.alias a) := by
  have h : ∀ a ∈ aliasPool "HA", Both (HostGood PermissionExamples.O) (.alias a) := by decide
  exact h a ha

private theorem cmdPool_ls : ∀ a ∈ argShapes, CommandValue PermissionExamples.O ⟨"/bin/ls", a⟩ := by decide
private theorem cmdPool_cat : ∀ a ∈ argShapes, CommandValue PermissionExamples.O ⟨"/bin/cat", a⟩ := by decide
private theorem cmdPool_id : ∀ a ∈ argShapes, CommandValue PermissionExamples.O ⟨"/usr/bin/id", a⟩ := by decide
private theorem cmdPool_local : ∀ a ∈ argShapes, CommandValue PermissionExamples.O ⟨"/usr/local/bin/ls", a⟩ := by decide

private theorem commandLeaves {fs : FsOracle} {glob : GlobOracle} (hs : PathSnapshot fs glob)
    {c : Command} (hp : c.pattern ∈ paths) (ha : c.args ∈ argShapes) :
    CommandValue (snapshot fs glob) c := by
  rcases c with ⟨p, a⟩
  have h : CommandValue PermissionExamples.O ⟨p, a⟩ := by
    change p ∈ ["/bin/ls", "/bin/cat", "/usr/bin/id", "/usr/local/bin/ls"] at hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact cmdPool_ls a ha
    · exact cmdPool_cat a ha
    · exact cmdPool_id a ha
    · exact cmdPool_local a ha
  obtain ⟨hc, hg⟩ := hs p hp
  refine ⟨⟨h.path.absolute, h.path.notDir, h.path.oneWord, hc, hg⟩, ⟨h.args.words, h.args.sentinel⟩, ?_⟩
  intro b
  have hl := h.lexeme b
  exact ⟨hl.ne, hl.first, hl.tail, hl.noEscape, hl.bytes⟩

private theorem commandAll (fs : FsOracle) (glob : GlobOracle) :
    CommandMemberValue (snapshot fs glob) .all := by
  have h : CommandMemberValue PermissionExamples.O .all := by decide
  intro b
  have hl := h b
  have hv : (metaToken (snapshot fs glob).char (commandToken (snapshot fs glob))).construct
      ("ALL".toList ++ gap b) = .ok .all := by cases b <;> rfl
  exact ⟨⟨hl.ne, hl.first, hl.tail, hl.noEscape, hl.bytes⟩, hv⟩

private theorem commandAlias (fs : FsOracle) (glob : GlobOracle) {n : String}
    (hn : n ∈ aliasPool "CA") : CommandMemberValue (snapshot fs glob) (.alias n) := by
  have h : ∀ n ∈ aliasPool "CA", CommandMemberValue PermissionExamples.O (.alias n) := by decide
  have h := h n hn
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  intro b
  have hl := h.2.2.2 b
  have hv : (metaToken (snapshot fs glob).char (commandToken (snapshot fs glob))).construct
      (n.toList ++ gap b) = .ok (.alias n) := by
    change n ∈ ["CA0", "CA1", "CA2"] at hn
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn
    rcases hn with rfl | rfl | rfl <;> cases b <;> rfl
  exact ⟨⟨hl.ne, hl.first, hl.tail, hl.noEscape, hl.bytes⟩, hv⟩

/-! ## Composing the actual `Generate.policy {}` branches -/

private theorem itemBounded {xs : List α} {P : α → Prop} {hi : Nat}
    (h : ItemRange 1 hi P xs) (hl : hi ≤ 127) : BoundedItems P xs := by
  refine ⟨?_, Nat.le_trans h.2.1 hl, h.2.2⟩
  intro e; subst xs; have := h.1; simp at this

private theorem userItem (fs : FsOracle) (glob : GlobOracle) (t : List (Def α)) (p : String)
    (hp : p = "UA" ∨ p = "RA") (ht : ∀ d ∈ t, d.name ∈ aliasPool p) :
    Produces (Generate.item Generate.userSpecifier (namesOf t) []) (UserGood (snapshot fs glob)) := by
  refine item_range ?_ ?_ (mono user_mem (userLeaves fs glob))
  · exact (by decide : Both (UserGood PermissionExamples.O) .all)
  · intro a ha
    exact userAlias fs glob p hp (namesOf_range ht a ha)

private theorem runas_range (fs : FsOracle) (glob : GlobOracle) (t : List (Def UserSpecifier))
    (ht : ∀ d ∈ t, d.name ∈ aliasPool "RA") :
    Produces (Generate.runAs {} (namesOf t))
      (fun o => ∀ ra ∈ o, RunasValue (snapshot fs glob) ra) := by
  unfold Generate.runAs
  simp only [Bool.false_eq_true, ite_false]
  have hu : Produces (Gen.listOf 1 2 (Generate.item Generate.userSpecifier (namesOf t) []))
      (UserItems (snapshot fs glob)) :=
    mono (listOf_range (mono (userItem fs glob t "RA" (.inr rfl) ht) (fun _ h => h.1)) 1 2 (by decide))
      (fun _ h => itemBounded h (by decide))
  have hg : Produces (Gen.listOf 1 2 (Generate.item Generate.groupIdentifier (namesOf t) []))
      (IdentifierItems (snapshot fs glob)) :=
    mono (listOf_range (item_range ⟨trivial, trivial⟩ (fun _ h => groupAlias fs glob (namesOf_range ht _ h))
      (mono group_mem (groupLeaves fs glob))) 1 2 (by decide)) (fun _ h => itemBounded h (by decide))
  have someGood (a : RunAs) (ha : RunasValue (snapshot fs glob) a) :
      ∀ ra ∈ (some a), RunasValue (snapshot fs glob) ra := by
    intro r hr; cases hr; exact ha
  let P := fun o : Option RunAs => ∀ ra ∈ o, RunasValue (snapshot fs glob) ra
  refine seq (Q := P) (weighted_mem [(5, 0), (4, 1), (2, 2), (2, 3), (1, 4)] (by decide)) ?_
  rintro k ⟨w, hm, _⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
  rcases hm with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact ret _ _ (by intro _ h; cases h)
  · exact seq (Q := P) hu (fun u h => ret _ _ (someGood ⟨u, []⟩ ⟨.inr h, .inl rfl⟩))
  · exact seq (Q := P) hu (fun u h => seq (Q := P) hg (fun g hg => ret _ _ (someGood ⟨u, g⟩ ⟨.inr h, .inr hg⟩)))
  · exact seq (Q := P) hg (fun g h => ret _ _ (someGood ⟨[], g⟩ ⟨.inl rfl, .inr h⟩))
  · exact ret _ _ (someGood ⟨[], []⟩ ⟨.inl rfl, .inl rfl⟩)

private theorem modifier_range : Produces Generate.modifier supportedModifier := by
  unfold Generate.modifier
  refine mono (Q := supportedModifier)
    (pick_mem [Modifier.nopasswd, .passwd, .setenv, .nosetenv, .noexec, .exec] (by decide)) ?_
  exact (by decide : ∀ k ∈ [Modifier.nopasswd, .passwd, .setenv, .nosetenv, .noexec, .exec], supportedModifier k)

private theorem mods_range :
    Produces (Gen.weighted [(5, 0), (3, 1), (1, 2)] >>= fun n => Gen.listOf n n Generate.modifier)
      (fun a => a.length ≤ 127 ∧ ∀ m ∈ a, supportedModifier m) := by
  refine seq (Q := fun a : List Modifier => a.length ≤ 127 ∧ ∀ m ∈ a, supportedModifier m)
    (weighted_mem [(5, 0), (3, 1), (1, 2)] (by decide)) ?_
  rintro n ⟨w, hm, _⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
  have hn : n ≤ 127 := by rcases hm with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
  exact mono (listOf_range modifier_range n n (by omega)) (fun _ h => ⟨Nat.le_trans h.2.1 hn, h.2.2⟩)

private def TableRange (t : AliasTable) : Prop :=
  (∀ d ∈ t.user, d.name ∈ aliasPool "UA") ∧
  (∀ d ∈ t.runas, d.name ∈ aliasPool "RA") ∧
  (∀ d ∈ t.host, d.name ∈ aliasPool "HA") ∧
  (∀ d ∈ t.cmnd, d.name ∈ aliasPool "CA")

private theorem entry_range {fs : FsOracle} {glob : GlobOracle} (hs : PathSnapshot fs glob)
    (t : AliasTable) (ht : TableRange t) :
    Produces (Generate.entry {} t) (EntryValue (snapshot fs glob)) := by
  have hc := commandItem_range (P := CmdGood (snapshot fs glob)) ⟨commandAll fs glob, commandAll fs glob⟩
    (fun _ hn => let hh := commandAlias fs glob (namesOf_range ht.2.2.2 _ hn); ⟨hh, hh⟩)
    (mono command_mem (fun _ h => let hh := commandLeaves hs h.1 h.2; ⟨hh, hh⟩))
  unfold Generate.entry
  refine seq (Q := EntryValue (snapshot fs glob)) (runas_range fs glob t.runas ht.2.1) ?_
  intro a ha
  refine seq (Q := EntryValue (snapshot fs glob)) mods_range ?_
  intro mods hm
  exact seq (Q := EntryValue (snapshot fs glob)) hc (fun cmd h => ret _ _ ⟨ha, ⟨hm.1, hm.2, h⟩⟩)

private theorem hostGroup_range {fs : FsOracle} {glob : GlobOracle} (hs : PathSnapshot fs glob)
    (t : AliasTable) (ht : TableRange t) :
    Produces (Generate.hostGroup {} t) (GroupValue (snapshot fs glob)) := by
  have hp : Produces Generate.plainHost (· ∈ plainHosts) := pick_mem _ (by decide)
  have hi := item_range (P := HostGood (snapshot fs glob)) ⟨trivial, trivial⟩
    (fun _ ha => hostAlias fs glob (namesOf_range ht.2.2.1 _ ha)) (mono hp (hostLeaves fs glob))
  unfold Generate.hostGroup
  refine seq (Q := GroupValue (snapshot fs glob)) (listOf_range hi 1 2 (by decide)) ?_
  intro a ha
  exact seq (Q := GroupValue (snapshot fs glob)) (listOf_range (entry_range hs t ht) 1 3 (by decide))
    (fun es he => ret _ _ ⟨itemBounded ha (by decide), itemBounded he (by decide)⟩)

private theorem rule_range {fs : FsOracle} {glob : GlobOracle} (hs : PathSnapshot fs glob)
    (t : AliasTable) (ht : TableRange t) :
    Produces (Generate.rule {} t) (PermissionValue (snapshot fs glob)) := by
  unfold Generate.rule
  refine seq (Q := PermissionValue (snapshot fs glob))
    (listOf_range (userItem fs glob t.user "UA" (.inl rfl) ht.1) 1 3 (by decide)) ?_
  intro u hu
  refine seq (Q := PermissionValue (snapshot fs glob))
    (listOf_range (hostGroup_range hs t ht) 1 2 (by decide)) ?_
  intro gs hg
  apply ret
  refine ⟨itemBounded ⟨hu.1, hu.2.1, fun x hx => (hu.2.2 x hx).1⟩ (by decide),
    ?_, itemBounded hg (by decide)⟩
  cases u with
  | nil => have h := hu.1; simp at h
  | cons k ks => exact (hu.2.2 k (by simp)).2

/-- The exact existing, unfiltered `Generate.policy {}` has only structurally
printable rules in its range under the stated ordinary snapshot, for every seed.
The theorem is about permission clauses, not alias definitions or file analysis. -/
theorem ordinaryPolicy_range {fs : FsOracle} {glob : GlobOracle} (hs : PathSnapshot fs glob) :
    Produces (Generate.policy {}) (fun p => ItemRange 1 4 (PermissionValue (snapshot fs glob)) p.2) := by
  unfold Generate.policy
  let Q : AliasTable × List PermissionSpec → Prop :=
    fun p => ItemRange 1 4 (PermissionValue (snapshot fs glob)) p.2
  refine seq (Q := Q) (defs_names "UA" Generate.userSpecifier _) ?_
  intro user hu
  refine seq (Q := Q) (defs_names "RA" Generate.userSpecifier _) ?_
  intro runas hr
  refine seq (Q := Q) (defs_names "HA" Generate.plainHost _) ?_
  intro host hh
  refine seq (Q := Q) (defs_names "CA" Generate.command _) ?_
  intro cmnd hc
  let t : AliasTable := { user, runas, host, cmnd }
  exact seq (Q := Q) (listOf_range (rule_range hs t ⟨hu, hr, hh, hc⟩) 1 4 (by decide))
    (fun l hl => ret (t, l) Q hl)

theorem ordinaryPolicy_check {fs : FsOracle} {glob : GlobOracle} (hs : PathSnapshot fs glob)
    (seed : Rng) (a : PermissionSpec) (ha : a ∈ ((Generate.policy {}).run seed).1.2) :
    checkPermissionValue (snapshot fs glob) a = true :=
  (checkPermissionValue_iff _ _).mpr ((ordinaryPolicy_range hs seed).2.2 a ha)

theorem ordinaryPolicy_roundTrip {fs : FsOracle} {glob : GlobOracle} (hs : PathSnapshot fs glob)
    (seed : Rng) {a : PermissionSpec} (ha : a ∈ ((Generate.policy {}).run seed).1.2)
    (D : Descriptions) (rest : List Char) (line col : Nat) :
    let c := (PermissionPrint.permissionSpec a).toList
    (sudo (snapshot fs glob) D).run ⟨c ++ '\n' :: rest, line, col⟩ =
      (.ok (.spec a), ⟨'\n' :: rest, (posAfter c (line, col)).1, (posAfter c (line, col)).2⟩) :=
  sudo_permission_checked_roundTrip (snapshot fs glob) D PermissionExamples.permissionLexical_latin1
    (ordinaryPolicy_check hs seed a ha) rest line col

#print axioms ordinaryPolicy_range
#print axioms ordinaryPolicy_check
#print axioms ordinaryPolicy_roundTrip

end Differential.OrdinaryPolicyRange
