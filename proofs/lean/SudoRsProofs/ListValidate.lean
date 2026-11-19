import SudoRsProofs.Permission

/-!
# `validate_flags` and `list_flags` refine `validateFlags` and `listFlags`

`select_tag` walks the rules and host groups like `check_permission` and folds the
`max_by_key` step of `select_commands` over the distributed tags. `selRules_eq` proves that loop
structure, at the spec level, equal to `maxByKey` over `SudoersSpec.entryTags`; the loop proofs
below mirror those of `Permission.lean`.

Besides the hypotheses of `permission_flags_eq`, `list_flags` needs two more, both about calls
the decision makes only for another user's entries (`sudo -l -U`):
* `GroupOracle uInst grp`: `UnixUser::group` is pure, total and returns `grp u`;
* `ListPath A`: `Path::new("list")` returns a path that reads as `"list"` through `A`
  (`Path::new` and `Path` are opaque).
`list_flags` is generic in the group type of its `ListRequest`; the theorem covers the instance
where it is the user's own group type `User::Group` with its `UnixGroup` instance (the only
instantiation in sudo-rs: `system::User` and `system::Group`).
-/

open Aeneas Aeneas.Std Result
open SudoersSpec (maxByKeyStep maxByKey)

namespace SudoRsProofs

/-! ## The loop structure at the spec level -/

/-- The key of `select_tag`: `needs_passwd() == prefer_passwd`. -/
def selKey (prefer : Bool) (t : SudoersSpec.Tag) : Bool := t.needsPasswd == prefer

/-- One `max_by_key` step on a distributed entry. -/
def selEntryStep (prefer : Bool) (res : Option SudoersSpec.Tag) (e : SudoersSpec.MatchedCommand) :
    Option SudoersSpec.Tag :=
  maxByKeyStep (selKey prefer) res e.2.1

/-- One `Host_List = Cmnd_Spec_List` group of an applicable rule. -/
def selSegStep (hostOK : SudoersSpec.SpecList SudoersSpec.Hostname → Bool) (prefer : Bool)
    (res : Option SudoersSpec.Tag)
    (seg : SudoersSpec.SpecList SudoersSpec.Hostname ×
      List (Option SudoersSpec.RunAs × SudoersSpec.CommandSpec)) : Option SudoersSpec.Tag :=
  if hostOK seg.1 then (SudoersSpec.distributeTags seg.2).foldl (selEntryStep prefer) res else res

/-- One rule (user specification line). -/
def selRuleStep (userOK : SudoersSpec.SpecList SudoersSpec.UserSpecifier → Bool)
    (hostOK : SudoersSpec.SpecList SudoersSpec.Hostname → Bool) (prefer : Bool)
    (res : Option SudoersSpec.Tag) (rule : SudoersSpec.PermissionSpec) : Option SudoersSpec.Tag :=
  if userOK rule.users then rule.permissions.foldl (selSegStep hostOK prefer) res else res

section Spec

variable {U G : Type} (O : SudoersSpec.Oracle U G)

/-- **`select_tag` in the shape of the Rust loops** is `maxByKey` over the applicable tags. -/
theorem selRules_eq (p : SudoersSpec.Policy) (u : U) (host : SudoersSpec.Hostname)
    (prefer : Bool) :
    p.rules.foldl (selRuleStep
        (fun us => (SudoersSpec.findItem (SudoersSpec.matchUser O u)
          (SudoersSpec.getAliases p.aliases.user (SudoersSpec.matchUser O u))
          (SudoersSpec.withUnit us)).isSome)
        (fun hs => (SudoersSpec.findItem (SudoersSpec.matchHost O host)
          (SudoersSpec.getAliases p.aliases.host (SudoersSpec.matchHost O host))
          (SudoersSpec.withUnit hs)).isSome) prefer) none =
      maxByKey (selKey prefer) (SudoersSpec.entryTags O p u host) := by
  simp only [maxByKey, SudoersSpec.entryTags, SudoersSpec.matchingUserSpecs]
  rw [List.foldl_map, List.foldl_flatten, foldl_filterMap, List.foldl_flatten, foldl_filterMap]
  congr 1
  funext res rule
  simp only [selRuleStep]
  rcases Option.eq_none_or_eq_some (SudoersSpec.findItem (SudoersSpec.matchUser O u)
      (SudoersSpec.getAliases p.aliases.user (SudoersSpec.matchUser O u))
      (SudoersSpec.withUnit rule.users)) with h | ⟨_, h⟩
  · simp [h]
  · simp only [h, Option.map_some, Option.isSome_some, ite_true, Option.elim_some]
    congr 1
    funext res seg
    simp only [selSegStep]
    rcases Option.eq_none_or_eq_some (SudoersSpec.findItem (SudoersSpec.matchHost O host)
        (SudoersSpec.getAliases p.aliases.host (SudoersSpec.matchHost O host))
        (SudoersSpec.withUnit seg.1)) with h' | ⟨_, h'⟩
    · simp [h']
    · simp [h']
      rfl

end Spec

/-! ## `Tag::needs_passwd` and `select_commands` -/

theorem Tag.needs_passwd_eq (t : sudo_rs.sudoers.ast.Tag) :
    sudo_rs.sudoers.ast.Tag.needs_passwd t = ok (absTag t).needsPasswd := by
  unfold sudo_rs.sudoers.ast.Tag.needs_passwd
  cases h : t.authenticate <;> simp [absTag, absAuthenticate, SudoersSpec.Tag.needsPasswd, h]

theorem Tag.clone_eq (t : sudo_rs.sudoers.ast.Tag) :
    sudo_rs.sudoers.ast.Tag.Insts.CoreCloneClone.clone t = ok t :=
  eq_ok_of_spec (Tag.clone_spec t)

theorem select_commands_loop_spec (prefer : Bool) (result : Option sudo_rs.sudoers.ast.Tag)
    (tags : alloc.vec.Vec (Option Usize × sudo_rs.sudoers.ast.Tag)) (i : Usize) :
    sudo_rs.sudoers.select_commands_loop result prefer tags i ⦃ r =>
      r.map absTag = (tags.val.drop i.val).foldl
        (fun acc x => maxByKeyStep (selKey prefer) acc (absTag x.2)) (result.map absTag) ⦄ := by
  unfold sudo_rs.sudoers.select_commands_loop
  dsimp only
  split
  · have hlt : i.val < tags.val.length := by scalar_tac
    simp only [alloc.vec.Vec.index_slice_index]
    apply WP.spec_bind (alloc.vec.Vec.index_usize_spec tags i hlt)
    rintro ⟨lr, tag⟩ hq
    simp only [uncurry]
    have hstep : ∀ r1 : Option sudo_rs.sudoers.ast.Tag,
        r1.map absTag = maxByKeyStep (selKey prefer) (result.map absTag) (absTag tag) →
        (do
          let i2 ← i + 1#usize
          sudo_rs.sudoers.select_commands_loop r1 prefer tags i2) ⦃ r =>
        r.map absTag = (tags.val.drop i.val).foldl
          (fun acc x => maxByKeyStep (selKey prefer) acc (absTag x.2)) (result.map absTag) ⦄ := by
      intro r1 hr1
      step as ⟨i2, hi2⟩
      step with select_commands_loop_spec prefer r1 tags i2 as ⟨r, hr⟩
      rw [hr, hi2, List.drop_eq_getElem_cons hlt, ← hq, List.foldl_cons, ← hr1]
    cases result with
    | none =>
      simp only [Tag.clone_eq, Aeneas.Std.bind_ok, Bool.false_eq_true, ite_false]
      exact hstep (some tag) rfl
    | some best =>
      simp only [Tag.needs_passwd_eq, Tag.clone_eq, Aeneas.Std.bind_ok]
      cases hb : (absTag best).needsPasswd <;> cases ht : (absTag tag).needsPasswd <;>
        cases prefer <;>
        simp only [Bool.false_eq_true, ite_false, ite_true, bne_self_eq_false, Bool.bne_true,
          Bool.bne_false, Bool.not_false, Aeneas.Std.bind_ok, reduceCtorEq] <;>
        first
          | exact hstep (some best) (by simp [maxByKeyStep, selKey, hb, ht])
          | exact hstep (some tag) (by simp [maxByKeyStep, selKey, hb, ht])
  · have : tags.val.length ≤ i.val := by scalar_tac
    simp [List.drop_eq_nil_of_le this]
termination_by tags.val.length - i.val
decreasing_by all_goals scalar_decr_tac

theorem foldl_zipWith_resolveEntry {β : Type} (fr : sudo_rs.sudoers.ast.RunAs → SudoersSpec.RunAs)
    (fc : RCommand → SudoersSpec.Command) (L : List REntry) (g : β → SudoersSpec.Tag → β) :
    ∀ (l : List REntry) (tags : List (Option Usize × sudo_rs.sudoers.ast.Tag)) (init : β),
      l.length = tags.length →
      (List.zipWith (resolveEntry fr fc L) l tags).foldl (fun acc e => g acc e.2.1) init =
        tags.foldl (fun acc x => g acc (absTag x.2)) init
  | [], [], _, _ => rfl
  | _ :: l, x :: tags, init, h => by
    simp only [List.zipWith_cons_cons, List.foldl_cons]
    exact foldl_zipWith_resolveEntry fr fc L g l tags _ (by simpa using h)
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

/-- **`select_commands` folds the `max_by_key` step over the distributed tags** of the line. -/
theorem select_commands_spec (A : GlobAbs) (prefer : Bool) (result : Option sudo_rs.sudoers.ast.Tag)
    (l : Slice REntry) (hig : (lineMods l.val).length ≤ Usize.max) :
    sudo_rs.sudoers.select_commands result l prefer ⦃ r =>
      r.map absTag = (SudoersSpec.distributeTags (absLine absRunAs (absCommand A) l.val)).foldl
        (selEntryStep prefer) (result.map absTag) ⦄ := by
  unfold sudo_rs.sudoers.select_commands
  step with distribute_tags_spec absRunAs (absCommand A) l hig as ⟨tags, hlen, hzip, _⟩
  step with select_commands_loop_spec prefer result tags 0#usize as ⟨r, hr⟩
  rw [hr, ← hzip]
  rw [List.drop_zero]
  exact (foldl_zipWith_resolveEntry absRunAs (absCommand A) l.val
    (maxByKeyStep (selKey prefer)) l.val tags.val _ hlen.symm).symm

/-! ## The loops of `select_tag` -/

variable {U G UG : Type} {uInst : sudo_rs.system.interface.UnixUser U UG}
  {eqInst : core.cmp.PartialEq U U} {gInst : sudo_rs.system.interface.UnixGroup G}
  {O : SudoersSpec.Oracle U G} {A : GlobAbs}

theorem sel_inner_loop_spec (hH : O.SudoRsHosts) (prefer : Bool) (host : String) (s1 : Str)
    (hs1 : s1.val = sudo_rs.stringBytes host) (HA : sudo_rs.sudoers.FoundAliases)
    (hHA : FoundFits HA) (result : Option sudo_rs.sudoers.ast.Tag) (perms : alloc.vec.Vec RSeg)
    (hperms : ∀ seg ∈ perms.val, SegOK seg) (j : Usize) :
    sudo_rs.sudoers.select_tag_loop0_loop0 prefer s1 HA result perms j ⦃ res =>
      res.map absTag = ((perms.val.drop j.val).map (absSeg A)).foldl
        (selSegStep (hostTest O host HA) prefer) (result.map absTag) ⦄ := by
  unfold sudo_rs.sudoers.select_tag_loop0_loop0
  dsimp only
  split
  · have hlt : j.val < perms.val.length := by scalar_tac
    have hdrop := List.drop_eq_getElem_cons hlt
    simp only [alloc.vec.Vec.index_slice_index]
    apply WP.spec_bind (alloc.vec.Vec.index_usize_spec perms j hlt)
    rintro ⟨v, v1⟩ hq
    simp only [uncurry]
    obtain ⟨hvi, hvg, hl⟩ := hperms (v, v1) (by rw [hq]; exact List.getElem_mem hlt)
    obtain ⟨hlig, -⟩ := hl
    step with find_item_match_token_spec hH host s1 hs1 (alloc.vec.Vec.deref v) HA hHA
      (by simpa using hvi) (by simpa using hvg) as ⟨b, hb⟩
    have hrec : ∀ r1 : Option sudo_rs.sudoers.ast.Tag,
        r1.map absTag = selSegStep (hostTest O host HA) prefer (result.map absTag)
          (absSeg A (v, v1)) →
        (do
          let j1 ← j + 1#usize
          sudo_rs.sudoers.select_tag_loop0_loop0 prefer s1 HA r1 perms j1) ⦃ res =>
        res.map absTag = ((perms.val.drop j.val).map (absSeg A)).foldl
          (selSegStep (hostTest O host HA) prefer) (result.map absTag) ⦄ := by
      intro r1 hr1
      step as ⟨j1, hj1⟩
      step with sel_inner_loop_spec hH prefer host s1 hs1 HA hHA r1 perms hperms j1
        as ⟨res, hres⟩
      rw [hres, hj1, hdrop, ← hq, List.map_cons, List.foldl_cons, ← hr1]
    have hseg : ∀ x, selSegStep (hostTest O host HA) prefer x (absSeg A (v, v1)) =
        if b then (SudoersSpec.distributeTags (absLine absRunAs (absCommand A) v1.val)).foldl
          (selEntryStep prefer) x else x := by
      intro x
      simp only [selSegStep, hostTest, absSeg, hb, Vec.deref_val]
      try rfl
    split
    · rename_i hbt
      step with select_commands_spec A prefer result (alloc.vec.Vec.deref v1)
        (by simpa using hlig) as ⟨r1, hr1⟩
      refine hrec r1 ?_
      rw [hseg, hbt, hr1]
      simp [Vec.deref_val]
    · rename_i hbf
      simp only [Aeneas.Std.bind_ok]
      refine hrec result ?_
      rw [hseg]
      simp [hbf]
  · have : perms.val.length ≤ j.val := by scalar_tac
    simp [List.drop_eq_nil_of_le this]
termination_by perms.val.length - j.val
decreasing_by all_goals scalar_decr_tac

theorem sel_outer_loop_spec (hO : InstOracle uInst eqInst gInst O) (hH : O.SudoRsHosts)
    (prefer : Bool) (u : U) (host : String) (s1 : Str) (hs1 : s1.val = sudo_rs.stringBytes host)
    (UA HA : sudo_rs.sudoers.FoundAliases) (hUA : FoundFits UA) (hHA : FoundFits HA)
    (rules : Slice sudo_rs.sudoers.ast.PermissionSpec) (hrules : ∀ ps ∈ rules.val, RuleOK ps)
    (result : Option sudo_rs.sudoers.ast.Tag) (i : Usize) :
    sudo_rs.sudoers.select_tag_loop0 uInst rules prefer u s1 UA HA result i ⦃ res =>
      res.map absTag = ((rules.val.drop i.val).map (absPermissionSpec A)).foldl
        (selRuleStep (userTest O u UA) (hostTest O host HA) prefer) (result.map absTag) ⦄ := by
  unfold sudo_rs.sudoers.select_tag_loop0
  dsimp only
  split
  · have hlt : i.val < rules.val.length := by scalar_tac
    have hdrop := List.drop_eq_getElem_cons hlt
    step as ⟨ps, hps⟩
    obtain ⟨hui, hug, hsegs⟩ := hrules ps (by rw [hps]; exact List.getElem_mem hlt)
    step with find_item_match_user_spec hO u (alloc.vec.Vec.deref ps.users) UA hUA
      (by simpa using hui) (by simpa using hug) as ⟨b, hb⟩
    have hrule : ∀ x, selRuleStep (userTest O u UA) (hostTest O host HA) prefer x
        (absPermissionSpec A ps) =
        if b then ((ps.permissions.val.drop 0).map (absSeg A)).foldl
          (selSegStep (hostTest O host HA) prefer) x else x := by
      intro x
      simp only [selRuleStep, userTest, absPermissionSpec, hb, Vec.deref_val, List.drop_zero]
      try rfl
    have hrec : ∀ r1 : Option sudo_rs.sudoers.ast.Tag,
        r1.map absTag = selRuleStep (userTest O u UA) (hostTest O host HA) prefer
          (result.map absTag) (absPermissionSpec A ps) →
        (do
          let i2 ← i + 1#usize
          sudo_rs.sudoers.select_tag_loop0 uInst rules prefer u s1 UA HA r1 i2) ⦃ res =>
        res.map absTag = ((rules.val.drop i.val).map (absPermissionSpec A)).foldl
          (selRuleStep (userTest O u UA) (hostTest O host HA) prefer) (result.map absTag) ⦄ := by
      intro r1 hr1
      step as ⟨i2, hi2⟩
      step with sel_outer_loop_spec hO hH prefer u host s1 hs1 UA HA hUA hHA rules hrules r1 i2
        as ⟨res, hres⟩
      rw [hres, hi2, hdrop, ← hps, List.map_cons, List.foldl_cons, ← hr1]
    split
    · rename_i hbt
      step with sel_inner_loop_spec (O := O) (A := A) hH prefer host s1 hs1 HA hHA result
        ps.permissions hsegs 0#usize as ⟨r1, hr1⟩
      exact hrec r1 (by rw [hrule, hbt, hr1]; rfl)
    · rename_i hbf
      exact hrec result (by rw [hrule]; simp [hbf])
  · have : rules.val.length ≤ i.val := by scalar_tac
    simp [List.drop_eq_nil_of_le this]
termination_by rules.val.length - i.val
decreasing_by all_goals scalar_decr_tac

/-! ## `select_tag` -/

/-- **`select_tag` is `max_by_key` over the applicable tags** with the key
`needs_passwd() == prefer_passwd`. -/
theorem select_tag_spec (hO : InstOracle uInst eqInst gInst O) (hH : O.SudoRsHosts)
    (rules : Slice sudo_rs.sudoers.ast.PermissionSpec) (aliases : sudo_rs.sudoers.AliasTable)
    (hpol : PolicyOK rules aliases) (u : U) (onHost : sudo_rs.system.Hostname)
    (hhost : Fits onHost.inner) (prefer : Bool) :
    sudo_rs.sudoers.select_tag uInst rules aliases u onHost prefer ⦃ res =>
      res.map absTag = maxByKey (selKey prefer)
        (SudoersSpec.entryTags O (absPolicy A rules aliases) u (absSysHostname onHost)) ⦄ := by
  obtain ⟨⟨⟨hu1, hu2, hu3⟩, ⟨hh1, hh2, hh3⟩, -, -⟩, hrules⟩ := hpol
  unfold sudo_rs.sudoers.select_tag
  simp only [sudo_rs.sudoers.match_user, sudo_rs.sudoers.match_token, Aeneas.Std.bind_ok]
  step with system_hostname_deref_spec onHost hhost as ⟨s1, hs1⟩
  step with get_aliases_match_user_spec hO u aliases.user hu1 hu2 hu3 as ⟨UA, hUA, hUAf⟩
  step with get_aliases_match_token_spec hH (absSysHostname onHost) s1 hs1 aliases.host hh1 hh2
    hh3 as ⟨HA, hHA, hHAf⟩
  refine WP.spec_mono (sel_outer_loop_spec (A := A) hO hH prefer u (absSysHostname onHost) s1 hs1
    UA HA hUAf hHAf rules hrules none 0#usize) ?_
  intro res hres
  rw [hres, ← selRules_eq]
  have h0 : (0#usize : Usize).val = 0 := by simp
  rw [h0, List.drop_zero]
  have h1 : userTest O u UA = fun us => (SudoersSpec.findItem (SudoersSpec.matchUser O u)
      (SudoersSpec.getAliases (absPolicy A rules aliases).aliases.user (SudoersSpec.matchUser O u))
      (SudoersSpec.withUnit us)).isSome := by
    funext us
    simp only [userTest, hUA]
    rfl
  have h2 : hostTest O (absSysHostname onHost) HA = fun hs =>
      (SudoersSpec.findItem (SudoersSpec.matchHost O (absSysHostname onHost))
        (SudoersSpec.getAliases (absPolicy A rules aliases).aliases.host
          (SudoersSpec.matchHost O (absSysHostname onHost)))
        (SudoersSpec.withUnit hs)).isSome := by
    funext hs
    simp only [hostTest, hHA]
    rfl
  rw [h1, h2]
  rfl

/-! ## `validate_flags` -/

theorem absTag_nopasswd (t : sudo_rs.sudoers.ast.Tag) :
    absTag { t with authenticate := .Nopasswd } = { absTag t with authenticate := .nopasswd } :=
  rfl

theorem selKey_true : selKey true = SudoersSpec.Tag.needsPasswd := by
  funext t; simp [selKey]

theorem selKey_false : selKey false = fun t => !t.needsPasswd := by
  funext t; simp [selKey]

/-- **`validate_flags` refines `SudoersSpec.validateFlags`** (`sudo -v`). The hypotheses are
those of `permission_flags_spec`; the command abstraction `A` is irrelevant here. -/
theorem validate_flags_spec (hO : InstOracle uInst eqInst gInst O) (hH : O.SudoRsHosts)
    (rules : Slice sudo_rs.sudoers.ast.PermissionSpec) (aliases : sudo_rs.sudoers.AliasTable)
    (hpol : PolicyOK rules aliases) (amUser : U) (onHost : sudo_rs.system.Hostname)
    (hhost : Fits onHost.inner) :
    sudo_rs.sudoers.validate_flags uInst rules aliases amUser onHost ⦃ res =>
      res.map absTag = SudoersSpec.validateFlags O (absPolicy A rules aliases) amUser
        (absSysHostname onHost) ⦄ := by
  unfold sudo_rs.sudoers.validate_flags
  rw [hO.is_root, Aeneas.Std.bind_ok]
  step with select_tag_spec (A := A) hO hH rules aliases hpol amUser onHost hhost true
    as ⟨flags, hflags⟩
  simp only [SudoersSpec.validateFlags, ← selKey_true, ← hflags]
  cases flags with
  | none => simp
  | some t =>
    cases O.isRoot amUser
    · simp [SudoersSpec.withNopasswd]
    · simp [SudoersSpec.withNopasswd, absTag, absAuthenticate]

/-- `validate_flags` returns `ok r` with `r.map absTag = SudoersSpec.validateFlags …`. -/
theorem validate_flags_eq (hO : InstOracle uInst eqInst gInst O) (hH : O.SudoRsHosts)
    (rules : Slice sudo_rs.sudoers.ast.PermissionSpec) (aliases : sudo_rs.sudoers.AliasTable)
    (hpol : PolicyOK rules aliases) (amUser : U) (onHost : sudo_rs.system.Hostname)
    (hhost : Fits onHost.inner) :
    ∃ r, sudo_rs.sudoers.validate_flags uInst rules aliases amUser onHost = ok r ∧
      r.map absTag = SudoersSpec.validateFlags O (absPolicy A rules aliases) amUser
        (absSysHostname onHost) :=
  exists_eq_ok_of_spec (validate_flags_spec hO hH rules aliases hpol amUser onHost hhost)

end SudoRsProofs

/-! ## `list_flags` -/

namespace SudoRsProofs

variable {U UG : Type} {uInst : sudo_rs.system.interface.UnixUser U UG}
  {eqInst : core.cmp.PartialEq U U} {O : SudoersSpec.Oracle U UG} {A : GlobAbs}

/-- **`UnixUser::group` is pure and total and returns `grp u`** (the primary group of `u`). -/
def GroupOracle (uInst : sudo_rs.system.interface.UnixUser U UG) (grp : U → UG) : Prop :=
  ∀ u, uInst.group u = ok (grp u)

/-- **`Path::new("list")` returns a path that reads as `"list"`** through `A`. -/
def ListPath (A : GlobAbs) : Prop :=
  ∃ p, std.path.Path.new sudo_rs.Str.Insts.CoreConvertAsRefOsStr (toStr "list") = ok p ∧
    A.path p = "list"

/-- `ListRequest { inspected_user, target_user, target_group }` with the invoking user and the
host folded in. -/
def absListRequest (amUser : U) (onHost : sudo_rs.system.Hostname)
    (req : sudo_rs.sudoers.ListRequest U UG UG) : SudoersSpec.ListRequest U UG where
  invokingUser := amUser
  host := absSysHostname onHost
  inspectedUser := req.inspected_user
  targetUser := req.target_user
  targetGroup := req.target_group

/-- **Listing one's own entries**: `list_flags` refines `SudoersSpec.listFlags` without the
hypotheses about the glob matcher, `UnixUser::group` and `Path::new` (that branch calls none of
them). -/
theorem list_flags_self_spec (hO : InstOracle uInst eqInst uInst.UnixGroupInst O)
    (hH : O.SudoRsHosts) (grp : U → UG) (rules : Slice sudo_rs.sudoers.ast.PermissionSpec)
    (aliases : sudo_rs.sudoers.AliasTable) (hpol : PolicyOK rules aliases) (amUser : U)
    (onHost : sudo_rs.system.Hostname) (hhost : Fits onHost.inner)
    (request : sudo_rs.sudoers.ListRequest U UG UG)
    (hne : O.userEq request.inspected_user amUser = true) :
    sudo_rs.sudoers.list_flags uInst eqInst uInst.UnixGroupInst rules aliases amUser onHost request
      ⦃ res => res.map absTag = SudoersSpec.listFlags O grp (absPolicy A rules aliases)
        (absListRequest amUser onHost request) ⦄ := by
  have hlr : SudoersSpec.listFlags O grp (absPolicy A rules aliases)
      (absListRequest amUser onHost request) =
      (maxByKey (selKey false)
        (SudoersSpec.entryTags O (absPolicy A rules aliases) amUser (absSysHostname onHost))).map
        (SudoersSpec.withNopasswd (O.isRoot amUser || (O.userEq request.target_user amUser &&
          SudoersSpec.inGroup O amUser request.target_group))) := by
    simp [SudoersSpec.listFlags, SudoersSpec.listSkipPasswd, absListRequest, hne, selKey_false]
  rw [hlr]
  unfold sudo_rs.sudoers.list_flags
  simp only [core.cmp.impls.PartialEqShared.ne, hO.ne, hne, Bool.not_true, Bool.false_eq_true,
    ite_false, hO.is_root, Aeneas.Std.bind_ok]
  rcases Bool.eq_false_or_eq_true (O.isRoot amUser) with hr | hr <;>
    rcases Bool.eq_false_or_eq_true (O.userEq request.target_user amUser) with hu | hu <;>
    simp only [hr, hu, ite_true, ite_false, Bool.false_eq_true, Aeneas.Std.bind_ok,
      core.cmp.impls.PartialEqShared.eq, hO.eq, in_group_eq hO, Bool.true_or, Bool.false_or,
      Bool.true_and, Bool.false_and] <;>
    step with select_tag_spec (A := A) hO hH rules aliases hpol amUser onHost hhost false
      as ⟨flags, hflags⟩ <;>
    rw [← hflags] <;>
    cases flags <;>
    by_cases hs : SudoersSpec.inGroup O amUser request.target_group = true <;>
    simp [hs, absTag_nopasswd, SudoersSpec.withNopasswd]

/-- **`list_flags` refines `SudoersSpec.listFlags`** (`sudo -l`, `sudo -l -U other`), with
`UnixUser::group` as `grp`, for a `ListRequest` whose group type is `User::Group` with its
`UnixGroup` instance. Hypotheses: those of `permission_flags_spec`, plus `GroupOracle` and
`ListPath` for the request to run `list` as another user. -/
theorem list_flags_spec (hO : InstOracle uInst eqInst uInst.UnixGroupInst O)
    (hG : GlobOracle A O) (hH : O.SudoRsHosts) (grp : U → UG) (hgrp : GroupOracle uInst grp)
    (hpath : ListPath A) (rules : Slice sudo_rs.sudoers.ast.PermissionSpec)
    (aliases : sudo_rs.sudoers.AliasTable) (hpol : PolicyOK rules aliases) (amUser : U)
    (onHost : sudo_rs.system.Hostname) (hhost : Fits onHost.inner)
    (request : sudo_rs.sudoers.ListRequest U UG UG) :
    sudo_rs.sudoers.list_flags uInst eqInst uInst.UnixGroupInst rules aliases amUser onHost request
      ⦃ res => res.map absTag = SudoersSpec.listFlags O grp (absPolicy A rules aliases)
        (absListRequest amUser onHost request) ⦄ := by
  cases hne : O.userEq request.inspected_user amUser
  · -- another user's entries
    obtain ⟨lp, hlp, hlpA⟩ := hpath
    unfold sudo_rs.sudoers.list_flags
    simp only [core.cmp.impls.PartialEqShared.ne, hO.ne, Aeneas.Std.bind_ok, hne]
    simp only [Bool.not_false, ite_true, hO.is_root, hgrp request.inspected_user, hlp, lift,
      Aeneas.Std.bind_ok]
    step with permission_flags_spec (A := A) hO hG hH rules aliases hpol amUser onHost hhost _
      as ⟨flags, hflags⟩
    have hreq : absRequest (G := UG) (UG := UG) A amUser onHost
        ⟨request.inspected_user, grp request.inspected_user, lp,
          Array.to_slice (Std.Array.empty std.ffi.os_str.OsString)⟩ =
        SudoersSpec.listCommandRequest grp (absListRequest amUser onHost request) := by
      simp [absRequest, SudoersSpec.listCommandRequest, absListRequest, hlpA, Array.to_slice,
        Std.Array.empty]
    rw [hreq] at hflags
    simp only [SudoersSpec.listFlags, absListRequest, hne, Bool.not_false, ite_true]
    simp only [absListRequest] at hflags
    rw [← hflags]
    cases flags with
    | none =>
      by_cases hr : O.isRoot amUser = true
      · simp only [hr, Option.isNone_none, ite_true]
        step as ⟨t, ht, _⟩
        simp [absTag_nopasswd, ht, SudoersSpec.withNopasswd]
      · simp [hr]
    | some t =>
      by_cases hr : O.isRoot amUser = true
      · simp [hr, absTag_nopasswd, SudoersSpec.withNopasswd]
      · simp [hr, SudoersSpec.withNopasswd]
  · exact list_flags_self_spec hO hH grp rules aliases hpol amUser onHost hhost request hne

/-- `list_flags` returns `ok r` with `r.map absTag = SudoersSpec.listFlags …`. -/
theorem list_flags_eq (hO : InstOracle uInst eqInst uInst.UnixGroupInst O)
    (hG : GlobOracle A O) (hH : O.SudoRsHosts) (grp : U → UG) (hgrp : GroupOracle uInst grp)
    (hpath : ListPath A) (rules : Slice sudo_rs.sudoers.ast.PermissionSpec)
    (aliases : sudo_rs.sudoers.AliasTable) (hpol : PolicyOK rules aliases) (amUser : U)
    (onHost : sudo_rs.system.Hostname) (hhost : Fits onHost.inner)
    (request : sudo_rs.sudoers.ListRequest U UG UG) :
    ∃ r, sudo_rs.sudoers.list_flags uInst eqInst uInst.UnixGroupInst rules aliases amUser onHost
        request = ok r ∧
      r.map absTag = SudoersSpec.listFlags O grp (absPolicy A rules aliases)
        (absListRequest amUser onHost request) :=
  exists_eq_ok_of_spec
    (list_flags_spec hO hG hH grp hgrp hpath rules aliases hpol amUser onHost hhost request)

end SudoRsProofs
