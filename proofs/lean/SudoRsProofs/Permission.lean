import SudoRsProofs.Matchers
import SudoRsProofs.PermSpec
import SudoRsProofs.AbsPolicy

/-!
# `check_permission` and `permission_flags` refine `checkPermission` and `authorize`

Hypotheses: the user/group instances agree with an oracle `O` (`InstOracle`), the glob matcher
agrees with it (`GlobOracle`), host names are compared by string equality (`O.SudoRsHosts`),
the policy satisfies `PolicyOK`, and the current host name fits in memory.
-/

open Aeneas Aeneas.Std Result

namespace SudoRsProofs

local notation "matchUserFn" uInst =>
  sudo_rs.sudoers.match_user.closure.Insts.CoreOpsFunctionFnTupleShared1UserSpecifierBool uInst
local notation "matchGroupFn" gInst =>
  sudo_rs.sudoers.match_group.closure.Insts.CoreOpsFunctionFnTupleShared1IdentifierBool gInst
local notation "matchTokenFn" =>
  sudo_rs.sudoers.match_token.closure.Insts.CoreOpsFunctionFnTupleShared1TBool
    sudo_rs.sudoers.tokens.Hostname.Insts.CoreOpsDerefDerefString
local notation "matchCommandFn" =>
  sudo_rs.sudoers.match_command.closure.Insts.CoreOpsFunctionFnTupleShared2PairPatternArgsBool
/-- The `Fn` instance of the verdict closure of `check_permission`. -/
local notation "permFn" =>
  sudo_rs.sudoers.check_permission.closure.Insts.CoreOpsFunctionFnPairOptionShared10RunAsShared11QualifiedMetaPairPatternArgsOptionBool

variable {U G UG : Type} {uInst : sudo_rs.system.interface.UnixUser U UG}
  {eqInst : core.cmp.PartialEq U U} {gInst : sudo_rs.system.interface.UnixGroup G}
  {O : SudoersSpec.Oracle U G} {A : GlobAbs}

/-! ## The verdict closure -/

/-- **The closure of `check_permission` is `permVerdict`**: the runas test of the spec
(`runasCheck`), then the command entry's verdict. `r` is the spec request; the closure state
holds its target user and group, the invoking user, the three alias tables and the
`match_command` closure state. -/
theorem perm_closure_call (hO : InstOracle uInst eqInst gInst O) (hG : GlobOracle A O)
    (r : SudoersSpec.Request U G) (p : std.path.Path) (s : Slice std.ffi.os_str.OsString)
    (hp : r.command = A.path p) (hs : r.arguments = s.val.map A.os)
    (RU RG CA : sudo_rs.sudoers.FoundAliases) (hRU : FoundFits RU) (hRG : FoundFits RG)
    (hCA : FoundFits CA) (ra : Option sudo_rs.sudoers.ast.RunAs)
    (hra : ∀ x, ra = some x → RunAsOK x) (cmd : RSpec RCommand) (hcmd : CmdOK cmd) :
    (permFn uInst eqInst gInst).call
        (r.targetUser, r.targetGroup, r.invokingUser, RU, RG, (p, matchCommandOptions, s), CA)
        (ra, cmd) =
      ok (permVerdict O r (absFound RU) (absFound RG) (absFound CA) (ra.map absRunAs)
        (absSpec (absCommand A) cmd)) := by
  have hIV := eq_ok_of_spec (item_verdict_match_command_spec (A := A) hG p s cmd CA hCA hcmd)
  rw [← hp, ← hs] at hIV
  have hIG := in_group_eq hO r.targetUser r.targetGroup
  simp only [sudo_rs.sudoers.check_permission.closure.Insts.CoreOpsFunctionFnPairOptionShared10RunAsShared11QualifiedMetaPairPatternArgsOptionBool.call,
    uncurry]
  cases ra with
  | none =>
    simp only [hO.is_root, hIG, hIV, Aeneas.Std.bind_ok, permVerdict, SudoersSpec.runasCheck,
      Option.map_none]
    cases O.isRoot r.targetUser <;> cases SudoersSpec.inGroup O r.targetUser r.targetGroup <;> rfl
  | some x =>
    obtain ⟨hui, hug, hgi, hgg⟩ := hra x rfl
    have hFU := eq_ok_of_spec (find_item_runas_users_spec hO r.targetUser x RU hRU hui hug)
    have hFG := eq_ok_of_spec (find_item_runas_groups_spec hO r.targetGroup x RG hRG hgi hgg)
    have hE : (absRunAs x).users.isEmpty = decide (x.users.val.length = 0) := by
      simp only [absRunAs, absSpecList, List.isEmpty_map, List.length_eq_zero_iff]
      cases x.users.val <;> rfl
    simp only [hIG, core.cmp.impls.PartialEqShared.ne, hO.ne, sudo_rs.sudoers.match_user,
      sudo_rs.sudoers.match_group, hFU, hFG, hIV, alloc.vec.Vec.is_empty, Aeneas.Std.bind_ok,
      permVerdict, SudoersSpec.runasCheck, Option.map_some]
    rw [hE]
    cases O.userEq r.targetUser r.invokingUser <;>
      cases SudoersSpec.inGroup O r.targetUser r.targetGroup <;>
      cases decide (x.users.val.length = 0) <;>
      cases SudoersSpec.findItem (SudoersSpec.matchUser O r.targetUser) (absFound RU)
        (SudoersSpec.withUnit (absRunAs x).users) <;>
      cases SudoersSpec.findItem (SudoersSpec.matchGroup O r.targetGroup) (absFound RG)
        (SudoersSpec.withUnit (absRunAs x).groups) <;> rfl

/-! ## The loop over the host groups of an applicable rule -/

/-- The host-list test with the host alias table `HA`. -/
def hostTest (O : SudoersSpec.Oracle U G) (host : String) (HA : sudo_rs.sudoers.FoundAliases)
    (hs : SudoersSpec.SpecList SudoersSpec.Hostname) : Bool :=
  (SudoersSpec.findItem (SudoersSpec.matchHost O host) (absFound HA) (SudoersSpec.withUnit hs)).isSome

/-- The user-list test with the user alias table `UA`. -/
def userTest (O : SudoersSpec.Oracle U G) (u : U) (UA : sudo_rs.sudoers.FoundAliases)
    (us : SudoersSpec.SpecList SudoersSpec.UserSpecifier) : Bool :=
  (SudoersSpec.findItem (SudoersSpec.matchUser O u) (absFound UA) (SudoersSpec.withUnit us)).isSome

theorem perm_inner_loop_spec (hO : InstOracle uInst eqInst gInst O) (hG : GlobOracle A O)
    (hH : O.SudoRsHosts) (r : SudoersSpec.Request U G) (p : std.path.Path)
    (s : Slice std.ffi.os_str.OsString) (hp : r.command = A.path p)
    (hs : r.arguments = s.val.map A.os) (RU RG CA HA : sudo_rs.sudoers.FoundAliases)
    (hRU : FoundFits RU) (hRG : FoundFits RG) (hCA : FoundFits CA) (hHA : FoundFits HA)
    (s1 : Str) (hs1 : s1.val = sudo_rs.stringBytes r.host)
    (result : Option sudo_rs.sudoers.ast.Tag) (perms : alloc.vec.Vec RSeg)
    (hperms : ∀ seg ∈ perms.val, SegOK seg) (j : Usize) :
    sudo_rs.sudoers.check_permission_loop0_loop0 uInst eqInst gInst r.invokingUser r.targetUser p
        matchCommandOptions s CA RU RG r.targetGroup s1 HA result perms j ⦃ res =>
      res.map absTag = ((perms.val.drop j.val).map (absSeg A)).foldl
        (segStep (hostTest O r.host HA) (permVerdict O r (absFound RU) (absFound RG) (absFound CA)))
        (result.map absTag) ⦄ := by
  unfold sudo_rs.sudoers.check_permission_loop0_loop0
  dsimp only
  split
  · have hlt : j.val < perms.val.length := by scalar_tac
    have hdrop := List.drop_eq_getElem_cons hlt
    simp only [alloc.vec.Vec.index_slice_index]
    apply WP.spec_bind (alloc.vec.Vec.index_usize_spec perms j hlt)
    rintro ⟨v, v1⟩ hq
    simp only [uncurry]
    obtain ⟨hvi, hvg, hl⟩ := hperms (v, v1) (by rw [hq]; exact List.getElem_mem hlt)
    obtain ⟨hlig, hle⟩ := hl
    step with find_item_match_token_spec hH r.host s1 hs1 (alloc.vec.Vec.deref v) HA hHA
      (by simpa using hvi) (by simpa using hvg) as ⟨b, hb⟩
    have hrec : ∀ r1 : Option sudo_rs.sudoers.ast.Tag,
        r1.map absTag = segStep (hostTest O r.host HA)
          (permVerdict O r (absFound RU) (absFound RG) (absFound CA)) (result.map absTag)
          (absSeg A (v, v1)) →
        (do
          let j1 ← j + 1#usize
          sudo_rs.sudoers.check_permission_loop0_loop0 uInst eqInst gInst r.invokingUser
            r.targetUser p matchCommandOptions s CA RU RG r.targetGroup s1 HA r1 perms j1) ⦃ res =>
        res.map absTag = ((perms.val.drop j.val).map (absSeg A)).foldl
          (segStep (hostTest O r.host HA)
            (permVerdict O r (absFound RU) (absFound RG) (absFound CA)))
          (result.map absTag) ⦄ := by
      intro r1 hr1
      step as ⟨j1, hj1⟩
      step with perm_inner_loop_spec hO hG hH r p s hp hs RU RG CA HA hRU hRG hCA hHA s1 hs1 r1
        perms hperms j1 as ⟨res, hres⟩
      rw [hres, hj1, hdrop, ← hq, List.map_cons, List.foldl_cons, ← hr1]
    have hseg : ∀ x, segStep (hostTest O r.host HA)
        (permVerdict O r (absFound RU) (absFound RG) (absFound CA)) x (absSeg A (v, v1)) =
        if b then checkCommandsSpec (permVerdict O r (absFound RU) (absFound RG) (absFound CA))
          (SudoersSpec.distributeTags (absLine absRunAs (absCommand A) v1.val)) x else x := by
      intro x
      simp only [segStep, hostTest, absSeg, hb, Vec.deref_val]
      try rfl
    split
    · rename_i hbt
      step with check_commands_spec (permFn uInst eqInst gInst)
        (r.targetUser, r.targetGroup, r.invokingUser, RU, RG, (p, matchCommandOptions, s), CA)
        absRunAs (absCommand A) (permVerdict O r (absFound RU) (absFound RG) (absFound CA))
        RunAsOK CmdOK
        (fun ra cmd hra hcmd =>
          perm_closure_call hO hG r p s hp hs RU RG CA hRU hRG hCA ra hra cmd hcmd)
        (alloc.vec.Vec.deref v1) (by simpa using hle) (by simpa using hlig)
        result as ⟨r1, hr1⟩
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

/-! ## The loop over the rules -/

theorem perm_outer_loop_spec (hO : InstOracle uInst eqInst gInst O) (hG : GlobOracle A O)
    (hH : O.SudoRsHosts) (r : SudoersSpec.Request U G) (p : std.path.Path)
    (s : Slice std.ffi.os_str.OsString) (hp : r.command = A.path p)
    (hs : r.arguments = s.val.map A.os) (RU RG CA UA HA : sudo_rs.sudoers.FoundAliases)
    (hRU : FoundFits RU) (hRG : FoundFits RG) (hCA : FoundFits CA) (hUA : FoundFits UA)
    (hHA : FoundFits HA) (s1 : Str) (hs1 : s1.val = sudo_rs.stringBytes r.host)
    (rules : Slice sudo_rs.sudoers.ast.PermissionSpec) (hrules : ∀ ps ∈ rules.val, RuleOK ps)
    (result : Option sudo_rs.sudoers.ast.Tag) (i : Usize) :
    sudo_rs.sudoers.check_permission_loop0 uInst eqInst gInst rules r.invokingUser r.targetUser p
        matchCommandOptions s CA RU RG r.targetGroup r.invokingUser s1 UA HA result i ⦃ res =>
      res.map absTag = ((rules.val.drop i.val).map (absPermissionSpec A)).foldl
        (ruleStep (userTest O r.invokingUser UA) (hostTest O r.host HA)
          (permVerdict O r (absFound RU) (absFound RG) (absFound CA)))
        (result.map absTag) ⦄ := by
  unfold sudo_rs.sudoers.check_permission_loop0
  dsimp only
  split
  · have hlt : i.val < rules.val.length := by scalar_tac
    have hdrop := List.drop_eq_getElem_cons hlt
    step as ⟨ps, hps⟩
    obtain ⟨hui, hug, hsegs⟩ := hrules ps (by rw [hps]; exact List.getElem_mem hlt)
    step with find_item_match_user_spec hO r.invokingUser (alloc.vec.Vec.deref ps.users) UA hUA
      (by simpa using hui) (by simpa using hug) as ⟨b, hb⟩
    have hrule : ∀ x, ruleStep (userTest O r.invokingUser UA) (hostTest O r.host HA)
        (permVerdict O r (absFound RU) (absFound RG) (absFound CA)) x (absPermissionSpec A ps) =
        if b then ((ps.permissions.val.drop 0).map (absSeg A)).foldl
          (segStep (hostTest O r.host HA) (permVerdict O r (absFound RU) (absFound RG) (absFound CA)))
          x else x := by
      intro x
      simp only [ruleStep, userTest, absPermissionSpec, hb, Vec.deref_val,
        List.drop_zero]
      try rfl
    have hrec : ∀ r1 : Option sudo_rs.sudoers.ast.Tag,
        r1.map absTag = ruleStep (userTest O r.invokingUser UA) (hostTest O r.host HA)
          (permVerdict O r (absFound RU) (absFound RG) (absFound CA)) (result.map absTag)
          (absPermissionSpec A ps) →
        (do
          let i2 ← i + 1#usize
          sudo_rs.sudoers.check_permission_loop0 uInst eqInst gInst rules r.invokingUser
            r.targetUser p matchCommandOptions s CA RU RG r.targetGroup r.invokingUser s1 UA HA r1
            i2) ⦃ res =>
        res.map absTag = ((rules.val.drop i.val).map (absPermissionSpec A)).foldl
          (ruleStep (userTest O r.invokingUser UA) (hostTest O r.host HA)
            (permVerdict O r (absFound RU) (absFound RG) (absFound CA)))
          (result.map absTag) ⦄ := by
      intro r1 hr1
      step as ⟨i2, hi2⟩
      step with perm_outer_loop_spec hO hG hH r p s hp hs RU RG CA UA HA hRU hRG hCA hUA hHA s1
        hs1 rules hrules r1 i2 as ⟨res, hres⟩
      rw [hres, hi2, hdrop, ← hps, List.map_cons, List.foldl_cons, ← hr1]
    split
    · rename_i hbt
      step with perm_inner_loop_spec hO hG hH r p s hp hs RU RG CA HA hRU hRG hCA hHA s1 hs1
        result ps.permissions hsegs 0#usize as ⟨r1, hr1⟩
      exact hrec r1 (by rw [hrule, hbt, hr1]; rfl)
    · rename_i hbf
      exact hrec result (by rw [hrule]; simp [hbf])
  · have : rules.val.length ≤ i.val := by scalar_tac
    simp [List.drop_eq_nil_of_le this]
termination_by rules.val.length - i.val
decreasing_by all_goals scalar_decr_tac

/-! ## `check_permission` -/

/-- **`check_permission` refines `SudoersSpec.checkPermission`**: on a policy satisfying
`PolicyOK` and a host name that fits in memory, with the user/group instances, the glob
matcher and host matching agreeing with the oracle `O`, the Rust function returns (no panic,
no divergence) a tag whose abstraction is the spec's decision on the abstracted policy and
request. -/
theorem check_permission_spec (hO : InstOracle uInst eqInst gInst O) (hG : GlobOracle A O)
    (hH : O.SudoRsHosts) (rules : Slice sudo_rs.sudoers.ast.PermissionSpec)
    (aliases : sudo_rs.sudoers.AliasTable) (hpol : PolicyOK rules aliases) (amUser : U)
    (onHost : sudo_rs.system.Hostname) (hhost : Fits onHost.inner)
    (request : sudo_rs.sudoers.Request U G UG) :
    sudo_rs.sudoers.check_permission uInst eqInst gInst rules aliases amUser onHost request
      ⦃ res => res.map absTag = SudoersSpec.checkPermission O (absPolicy A rules aliases)
        (absRequest A amUser onHost request) ⦄ := by
  obtain ⟨⟨⟨hu1, hu2, hu3⟩, ⟨hh1, hh2, hh3⟩, ⟨hc1, hc2⟩, ⟨hr1, hr2, hr3⟩⟩, hrules⟩ := hpol
  unfold sudo_rs.sudoers.check_permission
  step with match_command_spec (A := A) hG request.command request.arguments as ⟨c, hc, _⟩
  subst hc
  simp only [uncurry]
  step with get_aliases_match_command_spec hG request.command request.arguments aliases.cmnd
    hc1 hc2 as ⟨CA, hCA, hCAf⟩
  simp only [sudo_rs.sudoers.match_user, sudo_rs.sudoers.match_group_alias,
    sudo_rs.sudoers.match_token, Aeneas.Std.bind_ok]
  step with get_aliases_match_user_spec hO request.user aliases.runas hr1 hr2 hr3
    as ⟨RU, hRU, hRUf⟩
  step with get_aliases_match_group_alias_spec hO request.group aliases.runas hr1 hr2 hr3
    as ⟨RG, hRG, hRGf⟩
  step with system_hostname_deref_spec onHost hhost as ⟨s1, hs1⟩
  step with get_aliases_match_user_spec hO amUser aliases.user hu1 hu2 hu3 as ⟨UA, hUA, hUAf⟩
  step with get_aliases_match_token_spec hH (absSysHostname onHost) s1 hs1 aliases.host hh1 hh2
    hh3 as ⟨HA, hHA, hHAf⟩
  refine WP.spec_mono (perm_outer_loop_spec (A := A) hO hG hH
    (absRequest A amUser onHost request) request.command request.arguments rfl rfl
    RU RG CA UA HA hRUf hRGf hCAf hUAf hHAf s1 hs1 rules hrules none 0#usize) ?_
  intro res hres
  rw [hres, ← checkRules_eq, checkRulesFrom]
  have h1 : userTest O (absRequest A amUser onHost request).invokingUser UA =
      userOK O (absPolicy A rules aliases) (absRequest A amUser onHost request) := by
    funext us
    simp only [userTest, userOK, hUA]
    rfl
  have h2 : hostTest O (absRequest A amUser onHost request).host HA =
      hostOK O (absPolicy A rules aliases) (absRequest A amUser onHost request) := by
    funext hs
    simp only [hostTest, hostOK, hHA]
    rfl
  have h3 : permVerdict O (absRequest A amUser onHost request) (absFound RU) (absFound RG)
      (absFound CA) = policyVerdict O (absPolicy A rules aliases)
        (absRequest A amUser onHost request) := by
    simp only [policyVerdict, hRU, hRG, hCA]
    rfl
  have h0 : (0#usize : Usize).val = 0 := by simp
  rw [h1, h2, h3, h0, List.drop_zero]
  rfl

/-! ## `permission_flags` -/

/-- **`permission_flags` refines `SudoersSpec.authorize`** (the flags of `Sudoers::check`):
`check_permission` followed by the NOPASSWD rule for root and for running as oneself with one
of one's own groups. Same hypotheses as `check_permission_spec`. -/
theorem permission_flags_spec (hO : InstOracle uInst eqInst gInst O) (hG : GlobOracle A O)
    (hH : O.SudoRsHosts) (rules : Slice sudo_rs.sudoers.ast.PermissionSpec)
    (aliases : sudo_rs.sudoers.AliasTable) (hpol : PolicyOK rules aliases) (amUser : U)
    (onHost : sudo_rs.system.Hostname) (hhost : Fits onHost.inner)
    (request : sudo_rs.sudoers.Request U G UG) :
    sudo_rs.sudoers.permission_flags uInst eqInst gInst rules aliases amUser onHost request
      ⦃ res => res.map absTag = SudoersSpec.authorize O (absPolicy A rules aliases)
        (absRequest A amUser onHost request) ⦄ := by
  unfold sudo_rs.sudoers.permission_flags
  rw [hO.is_root, Aeneas.Std.bind_ok]
  apply WP.spec_bind
    (Pₘ := fun b => b = SudoersSpec.skipPasswd O (absRequest A amUser onHost request))
  · simp only [SudoersSpec.skipPasswd, absRequest]
    cases O.isRoot amUser
    · simp only [core.cmp.impls.PartialEqShared.eq, hO.eq, Bool.false_eq_true, ite_false,
        Aeneas.Std.bind_ok, Bool.false_or]
      cases O.userEq request.user amUser
      · simp
      · simp [in_group_eq hO]
    · simp
  intro skip hskip
  step with check_permission_spec (A := A) hO hG hH rules aliases hpol amUser onHost hhost request
    as ⟨flags, hflags⟩
  rw [SudoersSpec.authorize, ← hflags, ← hskip]
  cases flags with
  | none => simp
  | some t =>
    cases skip
    · simp
    · simp [absTag, absAuthenticate]

/-! ## Equation forms -/

/-- `check_permission` returns `ok r` (no panic, no divergence) with
`r.map absTag = SudoersSpec.checkPermission …`. -/
theorem check_permission_eq (hO : InstOracle uInst eqInst gInst O) (hG : GlobOracle A O)
    (hH : O.SudoRsHosts) (rules : Slice sudo_rs.sudoers.ast.PermissionSpec)
    (aliases : sudo_rs.sudoers.AliasTable) (hpol : PolicyOK rules aliases) (amUser : U)
    (onHost : sudo_rs.system.Hostname) (hhost : Fits onHost.inner)
    (request : sudo_rs.sudoers.Request U G UG) :
    ∃ r, sudo_rs.sudoers.check_permission uInst eqInst gInst rules aliases amUser onHost request =
        ok r ∧
      r.map absTag = SudoersSpec.checkPermission O (absPolicy A rules aliases)
        (absRequest A amUser onHost request) :=
  exists_eq_ok_of_spec
    (check_permission_spec hO hG hH rules aliases hpol amUser onHost hhost request)

/-- `permission_flags` returns `ok r` with `r.map absTag = SudoersSpec.authorize …`. -/
theorem permission_flags_eq (hO : InstOracle uInst eqInst gInst O) (hG : GlobOracle A O)
    (hH : O.SudoRsHosts) (rules : Slice sudo_rs.sudoers.ast.PermissionSpec)
    (aliases : sudo_rs.sudoers.AliasTable) (hpol : PolicyOK rules aliases) (amUser : U)
    (onHost : sudo_rs.system.Hostname) (hhost : Fits onHost.inner)
    (request : sudo_rs.sudoers.Request U G UG) :
    ∃ r, sudo_rs.sudoers.permission_flags uInst eqInst gInst rules aliases amUser onHost request =
        ok r ∧
      r.map absTag = SudoersSpec.authorize O (absPolicy A rules aliases)
        (absRequest A amUser onHost request) :=
  exists_eq_ok_of_spec
    (permission_flags_spec hO hG hH rules aliases hpol amUser onHost hhost request)

end SudoRsProofs
