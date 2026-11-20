import SudoRsProofs.Authorization
import SudoersSpec.Properties

/-!
# The policy-level properties, for the extracted code

`SudoersSpec/Properties.lean` proves properties P1-P9 of `SudoersSpec.authorize`. Through
`permission_flags_eq` they hold for the extracted `sudo_rs.sudoers.permission_flags` (the flags of
`Sudoers::check`), read through the abstraction `absPolicy`/`absRequest`/`absTag`, under the
hypotheses of `permission_flags_eq`: `InstOracle`, `GlobOracle`, `O.SudoRsHosts`, `PolicyOK`, and
a host name that fits in memory. P4, P5 and P6 relate two Rust rule slices that differ as in the
spec statements (same alias table, rules `pre ++ R :: post` against `pre' ++ R :: post` or
`pre ++ post`); their conclusions compare the results through `absTag` (`r₁.map absTag =
r₂.map absTag`, or "`r₂` grants implies `r₁` grants"), which is what the spec determines.

The hypotheses about policy contents (`userMentioned … = false`, the entries of `R`, …) are
stated on the abstracted policy, where the spec defines them.
-/

open Aeneas Aeneas.Std Result

namespace SudoRsProofs

variable {U G UG : Type} {uInst : sudo_rs.system.interface.UnixUser U UG}
  {eqInst : core.cmp.PartialEq U U} {gInst : sudo_rs.system.interface.UnixGroup G}
  {O : SudoersSpec.Oracle U G} {A : GlobAbs}

/-! ## From `permission_flags` to `authorize` -/

theorem permission_flags_some_authorize (hO : InstOracle uInst eqInst gInst O)
    (hG : GlobOracle A O) (hH : O.SudoRsHosts) (rules : Slice sudo_rs.sudoers.ast.PermissionSpec)
    (aliases : sudo_rs.sudoers.AliasTable) (hpol : PolicyOK rules aliases) (amUser : U)
    (onHost : sudo_rs.system.Hostname) (hhost : Fits onHost.inner)
    (request : sudo_rs.sudoers.Request U G UG) (t : sudo_rs.sudoers.ast.Tag)
    (h : sudo_rs.sudoers.permission_flags uInst eqInst gInst rules aliases amUser onHost request =
      ok (some t)) :
    SudoersSpec.authorize O (absPolicy A rules aliases) (absRequest A amUser onHost request) =
      some (absTag t) := by
  obtain ⟨res, hr, habs⟩ := permission_flags_eq hO hG hH rules aliases hpol amUser onHost hhost request
  rw [h] at hr
  have hr' : res = some t := by simpa using hr.symm
  subst hr'
  exact habs.symm

theorem permission_flags_none_authorize (hO : InstOracle uInst eqInst gInst O)
    (hG : GlobOracle A O) (hH : O.SudoRsHosts) (rules : Slice sudo_rs.sudoers.ast.PermissionSpec)
    (aliases : sudo_rs.sudoers.AliasTable) (hpol : PolicyOK rules aliases) (amUser : U)
    (onHost : sudo_rs.system.Hostname) (hhost : Fits onHost.inner)
    (request : sudo_rs.sudoers.Request U G UG)
    (h : sudo_rs.sudoers.permission_flags uInst eqInst gInst rules aliases amUser onHost request =
      ok none) :
    SudoersSpec.authorize O (absPolicy A rules aliases) (absRequest A amUser onHost request) =
      none := by
  obtain ⟨res, hr, habs⟩ := permission_flags_eq hO hG hH rules aliases hpol amUser onHost hhost request
  rw [h] at hr
  have hr' : res = none := by simpa using hr.symm
  subst hr'
  exact habs.symm

theorem permission_flags_eq_none (hO : InstOracle uInst eqInst gInst O)
    (hG : GlobOracle A O) (hH : O.SudoRsHosts) (rules : Slice sudo_rs.sudoers.ast.PermissionSpec)
    (aliases : sudo_rs.sudoers.AliasTable) (hpol : PolicyOK rules aliases) (amUser : U)
    (onHost : sudo_rs.system.Hostname) (hhost : Fits onHost.inner)
    (request : sudo_rs.sudoers.Request U G UG)
    (h : SudoersSpec.authorize O (absPolicy A rules aliases) (absRequest A amUser onHost request) =
      none) :
    sudo_rs.sudoers.permission_flags uInst eqInst gInst rules aliases amUser onHost request =
      ok none := by
  obtain ⟨res, hr, habs⟩ := permission_flags_eq hO hG hH rules aliases hpol amUser onHost hhost request
  rw [h, Option.map_eq_none_iff] at habs
  rw [hr, habs]

/-! ## P1 -/

/-- **P1 for the code.** If `permission_flags` grants `t`, the abstracted policy has an
applicable line, host group and deciding command entry that grants `absTag t`. -/
theorem permission_flags_allow_witness (hO : InstOracle uInst eqInst gInst O)
    (hG : GlobOracle A O) (hH : O.SudoRsHosts) (rules : Slice sudo_rs.sudoers.ast.PermissionSpec)
    (aliases : sudo_rs.sudoers.AliasTable) (hpol : PolicyOK rules aliases) (amUser : U)
    (onHost : sudo_rs.system.Hostname) (hhost : Fits onHost.inner)
    (request : sudo_rs.sudoers.Request U G UG) (t : sudo_rs.sudoers.ast.Tag)
    (h : sudo_rs.sudoers.permission_flags uInst eqInst gInst rules aliases amUser onHost request =
      ok (some t)) :
    let p := absPolicy A rules aliases
    let r := absRequest A amUser onHost request
    ∃ rule ∈ p.rules, SudoersSpec.userListMatches O p r rule.users = true ∧
      ∃ seg ∈ rule.permissions, SudoersSpec.hostListMatches O p r seg.1 = true ∧
        ∃ e ∈ SudoersSpec.distributeTagsSpec seg.2, SudoersSpec.decidingEntry O p r = some e ∧
          SudoersSpec.runasPermits O r (SudoersSpec.runasUserAliases O p r)
            (SudoersSpec.runasGroupAliases O p r) e.1 = true ∧
          SudoersSpec.cmdParticipates O p r e.2 = true ∧
          ∃ t', SudoersSpec.condition (SudoersSpec.cmndAliases O p r) (e.2.2, e.2.1) = some t' ∧
            absTag t = (if SudoersSpec.skipPasswd O r then { t' with authenticate := .nopasswd }
              else t') :=
  SudoersSpec.allow_witness O _ _ _
    (permission_flags_some_authorize hO hG hH rules aliases hpol amUser onHost hhost request t h)

/-! ## P2 -/

/-- **P2 for the code, users.** -/
theorem permission_flags_unmentioned_user (hO : InstOracle uInst eqInst gInst O)
    (hG : GlobOracle A O) (hH : O.SudoRsHosts) (rules : Slice sudo_rs.sudoers.ast.PermissionSpec)
    (aliases : sudo_rs.sudoers.AliasTable) (hpol : PolicyOK rules aliases) (amUser : U)
    (onHost : sudo_rs.system.Hostname) (hhost : Fits onHost.inner)
    (request : sudo_rs.sudoers.Request U G UG)
    (hm : SudoersSpec.userMentioned O (absPolicy A rules aliases)
      (absRequest A amUser onHost request) = false) :
    sudo_rs.sudoers.permission_flags uInst eqInst gInst rules aliases amUser onHost request =
      ok none :=
  permission_flags_eq_none hO hG hH rules aliases hpol amUser onHost hhost request
    (SudoersSpec.unmentioned_user_unmatched O _ _ hm)

/-- **P2 for the code, hosts.** -/
theorem permission_flags_unmentioned_host (hO : InstOracle uInst eqInst gInst O)
    (hG : GlobOracle A O) (hH : O.SudoRsHosts) (rules : Slice sudo_rs.sudoers.ast.PermissionSpec)
    (aliases : sudo_rs.sudoers.AliasTable) (hpol : PolicyOK rules aliases) (amUser : U)
    (onHost : sudo_rs.system.Hostname) (hhost : Fits onHost.inner)
    (request : sudo_rs.sudoers.Request U G UG)
    (hm : SudoersSpec.hostMentioned O (absPolicy A rules aliases)
      (absRequest A amUser onHost request) = false) :
    sudo_rs.sudoers.permission_flags uInst eqInst gInst rules aliases amUser onHost request =
      ok none :=
  permission_flags_eq_none hO hG hH rules aliases hpol amUser onHost hhost request
    (SudoersSpec.unmentioned_host_unmatched O _ _ hm)

/-- **P2 for the code, commands.** -/
theorem permission_flags_unmentioned_command (hO : InstOracle uInst eqInst gInst O)
    (hG : GlobOracle A O) (hH : O.SudoRsHosts) (rules : Slice sudo_rs.sudoers.ast.PermissionSpec)
    (aliases : sudo_rs.sudoers.AliasTable) (hpol : PolicyOK rules aliases) (amUser : U)
    (onHost : sudo_rs.system.Hostname) (hhost : Fits onHost.inner)
    (request : sudo_rs.sudoers.Request U G UG)
    (hm : SudoersSpec.cmdMentioned O (absPolicy A rules aliases)
      (absRequest A amUser onHost request) = false) :
    sudo_rs.sudoers.permission_flags uInst eqInst gInst rules aliases amUser onHost request =
      ok none :=
  permission_flags_eq_none hO hG hH rules aliases hpol amUser onHost hhost request
    (SudoersSpec.unmentioned_command_unmatched O _ _ hm)

/-- **P2 through `Judgement::authorization`**: an unmentioned user, host or command gets
`Authorization::Forbidden`, whatever the Defaults (in range). -/
theorem authorization_unmentioned_forbidden (hO : InstOracle uInst eqInst gInst O)
    (hG : GlobOracle A O) (hH : O.SudoRsHosts) (rules : Slice sudo_rs.sudoers.ast.PermissionSpec)
    (aliases : sudo_rs.sudoers.AliasTable) (hpol : PolicyOK rules aliases) (amUser : U)
    (onHost : sudo_rs.system.Hostname) (hhost : Fits onHost.inner)
    (request : sudo_rs.sudoers.Request U G UG) (settings : sudo_rs.defaults.Settings)
    (hs : SettingsInRange settings)
    (hm : SudoersSpec.userMentioned O (absPolicy A rules aliases)
        (absRequest A amUser onHost request) = false ∨
      SudoersSpec.hostMentioned O (absPolicy A rules aliases)
        (absRequest A amUser onHost request) = false ∨
      SudoersSpec.cmdMentioned O (absPolicy A rules aliases)
        (absRequest A amUser onHost request) = false) :
    ∃ flags a,
      sudo_rs.sudoers.permission_flags uInst eqInst gInst rules aliases amUser onHost request =
        ok flags ∧
      sudo_rs.sudoers.policy.Judgement.authorization ⟨flags, settings⟩ = ok a ∧
      a = .Forbidden := by
  obtain ⟨flags, a, hf, ha, hiff, -⟩ :=
    authorization_permission_flags_props hO hG hH rules aliases hpol amUser onHost hhost request
      settings hs
  refine ⟨flags, a, hf, ha, hiff.2 ?_⟩
  rcases hm with hm | hm | hm
  · exact SudoersSpec.unmentioned_user_unmatched O _ _ hm
  · exact SudoersSpec.unmentioned_host_unmatched O _ _ hm
  · exact SudoersSpec.unmentioned_command_unmatched O _ _ hm

/-! ## P2r -/

/-- **P2r for the code** (the sudo-rs form; the documented form fails, finding F2): a target
other than the invoking user that no runas list or Runas_Alias mentions is granted only if it
is root by `is_root`, and the deciding entry has no runas spec. -/
theorem permission_flags_unmentioned_runas_target (hO : InstOracle uInst eqInst gInst O)
    (hG : GlobOracle A O) (hH : O.SudoRsHosts) (rules : Slice sudo_rs.sudoers.ast.PermissionSpec)
    (aliases : sudo_rs.sudoers.AliasTable) (hpol : PolicyOK rules aliases) (amUser : U)
    (onHost : sudo_rs.system.Hostname) (hhost : Fits onHost.inner)
    (request : sudo_rs.sudoers.Request U G UG) (t : sudo_rs.sudoers.ast.Tag)
    (hm : SudoersSpec.runasUserMentioned O (absPolicy A rules aliases)
      (absRequest A amUser onHost request) = false)
    (hne : O.userEq request.user amUser = false)
    (h : sudo_rs.sudoers.permission_flags uInst eqInst gInst rules aliases amUser onHost request =
      ok (some t)) :
    O.isRoot request.user = true ∧
      ∃ e, SudoersSpec.decidingEntry O (absPolicy A rules aliases)
        (absRequest A amUser onHost request) = some e ∧ e.1 = none :=
  SudoersSpec.unmentioned_runas_target O _ _ _ hm hne
    (permission_flags_some_authorize hO hG hH rules aliases hpol amUser onHost hhost request t h)

/-! ## P3 -/

/-- **P3 for the code.** If some allowed entry of the abstracted policy takes part for the
command and `permission_flags` denies, the final such entry is a negated command spec or a
reference to a `Cmnd_Alias` that explicitly excludes the command (and the `Cmnd_Alias` table
then contains a negated item). -/
theorem permission_flags_deny_needs_cmd_negation (hO : InstOracle uInst eqInst gInst O)
    (hG : GlobOracle A O) (hH : O.SudoRsHosts) (rules : Slice sudo_rs.sudoers.ast.PermissionSpec)
    (aliases : sudo_rs.sudoers.AliasTable) (hpol : PolicyOK rules aliases) (amUser : U)
    (onHost : sudo_rs.system.Hostname) (hhost : Fits onHost.inner)
    (request : sudo_rs.sudoers.Request U G UG)
    (hex : ∃ e ∈ SudoersSpec.allowedSpec O (absPolicy A rules aliases)
        (absRequest A amUser onHost request),
      SudoersSpec.cmdParticipates O (absPolicy A rules aliases)
        (absRequest A amUser onHost request) e = true)
    (h : sudo_rs.sudoers.permission_flags uInst eqInst gInst rules aliases amUser onHost request =
      ok none) :
    let p := absPolicy A rules aliases
    let r := absRequest A amUser onHost request
    ∃ e, SudoersSpec.IsFinalMatch (SudoersSpec.cmdParticipates O p r)
        (SudoersSpec.allowedSpec O p r) e ∧
      ((∃ m, e.2 = .forbid m) ∨
        (∃ n, e.2 = .allow (.alias n) ∧ SudoersSpec.cmndAliases O p r n = some false ∧
          ∃ d ∈ p.aliases.cmnd, ∃ s ∈ d.items, ∃ m, s = .forbid m)) :=
  SudoersSpec.deny_needs_cmd_negation O _ _ hex
    (permission_flags_none_authorize hO hG hH rules aliases hpol amUser onHost hhost request h)

/-! ## P7, P8 -/

/-- **P7 for the code.** When `permission_flags` grants, the deciding entry exists, and if its
runas user list is empty the target user is the invoking user. -/
theorem permission_flags_myself_no_impersonation (hO : InstOracle uInst eqInst gInst O)
    (hG : GlobOracle A O) (hH : O.SudoRsHosts) (rules : Slice sudo_rs.sudoers.ast.PermissionSpec)
    (aliases : sudo_rs.sudoers.AliasTable) (hpol : PolicyOK rules aliases) (amUser : U)
    (onHost : sudo_rs.system.Hostname) (hhost : Fits onHost.inner)
    (request : sudo_rs.sudoers.Request U G UG) (t : sudo_rs.sudoers.ast.Tag)
    (h : sudo_rs.sudoers.permission_flags uInst eqInst gInst rules aliases amUser onHost request =
      ok (some t)) :
    ∃ e, SudoersSpec.decidingEntry O (absPolicy A rules aliases)
        (absRequest A amUser onHost request) = some e ∧
      ((∃ gs, e.1 = some ⟨[], gs⟩) → O.userEq request.user amUser = true) := by
  obtain ⟨e, he, -⟩ := (SudoersSpec.authorize_eq_some_iff_deciding O _ _ _).1
    (permission_flags_some_authorize hO hG hH rules aliases hpol amUser onHost hhost request t h)
  refine ⟨e, he, ?_⟩
  rintro ⟨gs, hgs⟩
  exact SudoersSpec.myself_no_impersonation_decision O _ _ e he gs hgs

/-- **P8 for the code.** When `permission_flags` grants, the target group is one of the target
user's groups or is accepted by the group list of the deciding entry's runas spec. -/
theorem permission_flags_runas_group_justified (hO : InstOracle uInst eqInst gInst O)
    (hG : GlobOracle A O) (hH : O.SudoRsHosts) (rules : Slice sudo_rs.sudoers.ast.PermissionSpec)
    (aliases : sudo_rs.sudoers.AliasTable) (hpol : PolicyOK rules aliases) (amUser : U)
    (onHost : sudo_rs.system.Hostname) (hhost : Fits onHost.inner)
    (request : sudo_rs.sudoers.Request U G UG) (t : sudo_rs.sudoers.ast.Tag)
    (h : sudo_rs.sudoers.permission_flags uInst eqInst gInst rules aliases amUser onHost request =
      ok (some t)) :
    SudoersSpec.inGroup O request.user request.group = true ∨
      ∃ e ra', SudoersSpec.decidingEntry O (absPolicy A rules aliases)
          (absRequest A amUser onHost request) = some e ∧ e.1 = some ra' ∧
        (SudoersSpec.findItemSpec (SudoersSpec.matchGroup O request.group)
          (SudoersSpec.runasGroupAliases O (absPolicy A rules aliases)
            (absRequest A amUser onHost request))
          (SudoersSpec.withUnit ra'.groups)).isSome = true := by
  obtain ⟨e, he, -⟩ := (SudoersSpec.authorize_eq_some_iff_deciding O _ _ _).1
    (permission_flags_some_authorize hO hG hH rules aliases hpol amUser onHost hhost request t h)
  rcases SudoersSpec.runas_group_justified_decision O _ _ e he with h1 | ⟨ra', hra, h2⟩
  · exact Or.inl h1
  · exact Or.inr ⟨e, ra', he, hra, h2⟩

/-! ## P9 -/

/-- **P9 for the code.** A grant whose abstracted tag says NOPASSWD comes from the root/self
exception or from a `NOPASSWD` modifier in the deciding host group at or before the deciding
entry. -/
theorem permission_flags_nopasswd_needs_explicit_tag (hO : InstOracle uInst eqInst gInst O)
    (hG : GlobOracle A O) (hH : O.SudoRsHosts) (rules : Slice sudo_rs.sudoers.ast.PermissionSpec)
    (aliases : sudo_rs.sudoers.AliasTable) (hpol : PolicyOK rules aliases) (amUser : U)
    (onHost : sudo_rs.system.Hostname) (hhost : Fits onHost.inner)
    (request : sudo_rs.sudoers.Request U G UG) (t : sudo_rs.sudoers.ast.Tag)
    (h : sudo_rs.sudoers.permission_flags uInst eqInst gInst rules aliases amUser onHost request =
      ok (some t))
    (hn : (absTag t).authenticate = .nopasswd) :
    let p := absPolicy A rules aliases
    let r := absRequest A amUser onHost request
    SudoersSpec.skipPasswd O r = true ∨
      ∃ rule ∈ p.rules, SudoersSpec.userListMatches O p r rule.users = true ∧
        ∃ seg ∈ rule.permissions, SudoersSpec.hostListMatches O p r seg.1 = true ∧
          ∃ i e, SudoersSpec.decidingEntry O p r = some e ∧
            (SudoersSpec.distributeTagsSpec seg.2)[i]? = some e ∧
            SudoersSpec.Modifier.nopasswd ∈ (seg.2.take (i + 1)).flatMap (·.2.mods) :=
  SudoersSpec.nopasswd_needs_explicit_tag O _ _ _
    (permission_flags_some_authorize hO hG hH rules aliases hpol amUser onHost hhost request t h) hn

/-! ## P4, P5, P6: two rule slices -/

/-- The abstracted policy of a rule slice, written as a policy with explicit rules. -/
theorem absPolicy_eq_with (rules : Slice sudo_rs.sudoers.ast.PermissionSpec)
    (rules' : Slice sudo_rs.sudoers.ast.PermissionSpec) (aliases : sudo_rs.sudoers.AliasTable)
    (l : List sudo_rs.sudoers.ast.PermissionSpec) (h : rules.val = l) :
    absPolicy A rules aliases = { absPolicy A rules' aliases with rules := l.map (absPermissionSpec A) } := by
  simp only [absPolicy, h]

/-- **P4 for the code.** Two rule slices `pre ++ R :: post` and `pre' ++ R :: post` with the same
alias table: if `R` has an entry that takes part and no line of `post` does, `permission_flags`
gives the same abstracted result. -/
theorem permission_flags_last_line_decides (hO : InstOracle uInst eqInst gInst O)
    (hG : GlobOracle A O) (hH : O.SudoRsHosts)
    (rules₁ rules₂ : Slice sudo_rs.sudoers.ast.PermissionSpec)
    (aliases : sudo_rs.sudoers.AliasTable) (hpol₁ : PolicyOK rules₁ aliases)
    (hpol₂ : PolicyOK rules₂ aliases) (amUser : U)
    (onHost : sudo_rs.system.Hostname) (hhost : Fits onHost.inner)
    (request : sudo_rs.sudoers.Request U G UG)
    (pre pre' post : List sudo_rs.sudoers.ast.PermissionSpec) (R : sudo_rs.sudoers.ast.PermissionSpec)
    (h₁ : rules₁.val = pre ++ R :: post) (h₂ : rules₂.val = pre' ++ R :: post)
    (hR : ∃ e ∈ SudoersSpec.ruleCandidates O (absPolicy A rules₁ aliases)
        (absRequest A amUser onHost request) (absPermissionSpec A R),
      SudoersSpec.entryDecides O (absPolicy A rules₁ aliases)
        (absRequest A amUser onHost request) e = true)
    (hpost : ∀ R' ∈ post, ∀ e ∈ SudoersSpec.ruleCandidates O (absPolicy A rules₁ aliases)
        (absRequest A amUser onHost request) (absPermissionSpec A R'),
      SudoersSpec.entryDecides O (absPolicy A rules₁ aliases)
        (absRequest A amUser onHost request) e = false) :
    ∃ f₁ f₂,
      sudo_rs.sudoers.permission_flags uInst eqInst gInst rules₁ aliases amUser onHost request =
        ok f₁ ∧
      sudo_rs.sudoers.permission_flags uInst eqInst gInst rules₂ aliases amUser onHost request =
        ok f₂ ∧
      f₁.map absTag = f₂.map absTag := by
  obtain ⟨f₁, hf₁, ha₁⟩ :=
    permission_flags_eq hO hG hH rules₁ aliases hpol₁ amUser onHost hhost request
  obtain ⟨f₂, hf₂, ha₂⟩ :=
    permission_flags_eq hO hG hH rules₂ aliases hpol₂ amUser onHost hhost request
  refine ⟨f₁, f₂, hf₁, hf₂, ?_⟩
  rw [ha₁, ha₂, absPolicy_eq_with rules₁ rules₁ aliases _ h₁,
    absPolicy_eq_with rules₂ rules₁ aliases _ h₂]
  simp only [List.map_append, List.map_cons]
  apply SudoersSpec.last_line_decides O _ _ _ _ _ _ hR
  intro R' hR' e he
  obtain ⟨R'', hR'', rfl⟩ := List.mem_map.1 hR'
  exact hpost R'' hR'' e he

/-- **P5 for the code.** Two rule slices `pre ++ R :: post` and `pre ++ post` with the same alias
table, where the user list of `R` does not accept the invoking user: `permission_flags` gives the
same abstracted result. -/
theorem permission_flags_insert_other_user_irrelevant (hO : InstOracle uInst eqInst gInst O)
    (hG : GlobOracle A O) (hH : O.SudoRsHosts)
    (rules₁ rules₂ : Slice sudo_rs.sudoers.ast.PermissionSpec)
    (aliases : sudo_rs.sudoers.AliasTable) (hpol₁ : PolicyOK rules₁ aliases)
    (hpol₂ : PolicyOK rules₂ aliases) (amUser : U)
    (onHost : sudo_rs.system.Hostname) (hhost : Fits onHost.inner)
    (request : sudo_rs.sudoers.Request U G UG)
    (pre post : List sudo_rs.sudoers.ast.PermissionSpec) (R : sudo_rs.sudoers.ast.PermissionSpec)
    (h₁ : rules₁.val = pre ++ R :: post) (h₂ : rules₂.val = pre ++ post)
    (hR : SudoersSpec.userListMatches O (absPolicy A rules₁ aliases)
      (absRequest A amUser onHost request) (absPermissionSpec A R).users = false) :
    ∃ f₁ f₂,
      sudo_rs.sudoers.permission_flags uInst eqInst gInst rules₁ aliases amUser onHost request =
        ok f₁ ∧
      sudo_rs.sudoers.permission_flags uInst eqInst gInst rules₂ aliases amUser onHost request =
        ok f₂ ∧
      f₁.map absTag = f₂.map absTag := by
  obtain ⟨f₁, hf₁, ha₁⟩ :=
    permission_flags_eq hO hG hH rules₁ aliases hpol₁ amUser onHost hhost request
  obtain ⟨f₂, hf₂, ha₂⟩ :=
    permission_flags_eq hO hG hH rules₂ aliases hpol₂ amUser onHost hhost request
  refine ⟨f₁, f₂, hf₁, hf₂, ?_⟩
  rw [ha₁, ha₂, absPolicy_eq_with rules₁ rules₁ aliases _ h₁,
    absPolicy_eq_with rules₂ rules₁ aliases _ h₂]
  simp only [List.map_append, List.map_cons]
  exact SudoersSpec.insert_other_user_irrelevant O _ _ _ _ _ hR

/-- **P6 for the code.** Two rule slices `pre ++ R :: post` and `pre ++ post` with the same alias
table, where `R` has no negated command spec and the `Cmnd_Alias` table no negated item: if
`permission_flags` grants on the second, it grants on the first. -/
theorem permission_flags_add_positive_preserves_allow (hO : InstOracle uInst eqInst gInst O)
    (hG : GlobOracle A O) (hH : O.SudoRsHosts)
    (rules₁ rules₂ : Slice sudo_rs.sudoers.ast.PermissionSpec)
    (aliases : sudo_rs.sudoers.AliasTable) (hpol₁ : PolicyOK rules₁ aliases)
    (hpol₂ : PolicyOK rules₂ aliases) (amUser : U)
    (onHost : sudo_rs.system.Hostname) (hhost : Fits onHost.inner)
    (request : sudo_rs.sudoers.Request U G UG)
    (pre post : List sudo_rs.sudoers.ast.PermissionSpec) (R : sudo_rs.sudoers.ast.PermissionSpec)
    (h₁ : rules₁.val = pre ++ R :: post) (h₂ : rules₂.val = pre ++ post)
    (hR : ∀ seg ∈ (absPermissionSpec A R).permissions, ∀ x ∈ seg.2, x.2.cmd.isAllow = true)
    (hA : ∀ d ∈ (absAliasTable A aliases).cmnd, ∀ s ∈ d.items, s.isAllow = true) :
    ∃ f₁ f₂,
      sudo_rs.sudoers.permission_flags uInst eqInst gInst rules₁ aliases amUser onHost request =
        ok f₁ ∧
      sudo_rs.sudoers.permission_flags uInst eqInst gInst rules₂ aliases amUser onHost request =
        ok f₂ ∧
      (f₂.isSome = true → f₁.isSome = true) := by
  obtain ⟨f₁, hf₁, ha₁⟩ :=
    permission_flags_eq hO hG hH rules₁ aliases hpol₁ amUser onHost hhost request
  obtain ⟨f₂, hf₂, ha₂⟩ :=
    permission_flags_eq hO hG hH rules₂ aliases hpol₂ amUser onHost hhost request
  refine ⟨f₁, f₂, hf₁, hf₂, fun h => ?_⟩
  have e₁ : f₁.isSome = (f₁.map absTag).isSome := by cases f₁ <;> rfl
  have e₂ : f₂.isSome = (f₂.map absTag).isSome := by cases f₂ <;> rfl
  rw [e₂, ha₂, absPolicy_eq_with rules₂ rules₁ aliases _ h₂] at h
  rw [e₁, ha₁, absPolicy_eq_with rules₁ rules₁ aliases _ h₁]
  simp only [List.map_append, List.map_cons] at h ⊢
  exact SudoersSpec.add_positive_preserves_allow O _ _ _ _ _ hR hA h

end SudoRsProofs
