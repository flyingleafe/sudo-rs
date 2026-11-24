import SudoRsProofs.Parser.Scoping.Check
import SudoRsProofs.ListValidate
import SudoRsProofs.Authorization
import SudoersSpec.Settings.ListValidate

/-!
# `check_validate_permission` and `check_list_permission`: Defaults, settings and result

`src/sudoers/mod.rs`, as extracted:

* `check_validate_permission` runs the first Defaults pass with the invoking user and no target
  user, computes `validate_flags` on the unchanged rules and aliases, and returns
  `Allowed(self.settings.to_auth(&tag), ())` or `Forbidden` with the policy.
* `check_list_permission` runs, only when the inspected user differs from the invoking user
  (`PartialEq::ne`), the first pass with the inspected user as runas target and the command pass
  for `Path::new("list")` without arguments; then `list_flags` and `to_auth` as above.

The theorems compare the returned `Authorization<()>` (through `absListAuthorization`) and the
settings of the returned policy (through `Defaults.absSettings`) with
`SudoersSpec.Analysis.validateAuthorization` / `listAuthorization` and `validateSettings` /
`listSettings`, for arbitrary initial settings and whatever customisers the policy still holds
(`c` and the customiser correspondences, as in `check_eq`). `to_auth` reads the settings in
place (no clone); the settings of the returned policy are those `to_auth` read.

`search_path_then_check_list_permission_eq` composes the first pass that `Sudoers::search_path`
runs in `run_list` (with the `-u` target) before `check_list_permission`; `search_path` itself is
not extracted (its first statement is that call, its second reads `secure_path`), so the
composition is stated with `specify_host_user_runas` directly.
-/

open Aeneas Aeneas.Std Result
open sudo_rs sudo_rs.sudoers
open SudoersSpec.Analysis (applyModifiers nonCommandModifiers validateSettings listSettings
  validateAuthorization listAuthorization listPipelineSettings listPipelineAuthorization)

namespace SudoRsProofs.Parser.Scoping

/-- `Authorization<()>` as `Option Authentication`: `Forbidden` is `none`. -/
def absListAuthorization : sudoers.policy.Authorization Unit → Option SudoersSpec.Authentication
  | .Allowed a _ => some (absAuthentication a)
  | .Forbidden => none

theorem absListAuthorization_allowed (a : sudoers.policy.Authentication) (u : Unit) :
    absListAuthorization (.Allowed a u) = some (absAuthentication a) := rfl

theorem absListAuthorization_forbidden : absListAuthorization .Forbidden = none := rfl

theorem absPolicy_aliases_eq (A : GlobAbs) (rules : Slice sudoers.ast.PermissionSpec)
    (aliases : sudoers.AliasTable) : (absPolicy A rules aliases).aliases = absAliasTable A aliases :=
  rfl

/-! ## `check_validate_permission` -/

section Validate

variable {U G UG : Type} {uInst : sudo_rs.system.interface.UnixUser U UG}
  {eqInst : core.cmp.PartialEq U U} {gInst : sudo_rs.system.interface.UnixGroup G}
  {O : SudoersSpec.Oracle U G} {A : GlobAbs}

/-- **`check_validate_permission` (`sudo -v`) on a well-formed policy.** It returns `ok`; the
result is `validateAuthorization` (the `validate_flags` tag through `to_auth` of the settings in
force); those settings are `validateSettings` (first pass with the invoking user, no runas
target, no command pass); rules, aliases and the command customisers are unchanged, the
first-pass customisers are consumed. No glob, `UnixUser::group` or command-customiser hypothesis
is needed. -/
theorem check_validate_permission_eq (hO : InstOracle uInst eqInst gInst O)
    (hH : O.SudoRsHosts) (self : sudoers.Sudoers) (amUser : U) (onHost : system.Hostname)
    (c : SudoersSpec.Analysis.Collected)
    (hpol : PolicyOK (alloc.vec.Vec.deref self.rules) self.aliases) (hhost : Fits onHost.inner)
    (hnon : c.nonCommand = Analysis.absNonCommand self.customisers.non_cmnd)
    (hokN : NonCommandEntriesOK self.customisers.non_cmnd.val)
    (hs : SettingsInRange self.settings) :
    ∃ (a : sudoers.policy.Authorization Unit) (self' : sudoers.Sudoers),
      sudoers.Sudoers.check_validate_permission uInst eqInst self amUser onHost = ok (a, self') ∧
      absListAuthorization a =
        validateAuthorization O (absPolicy A (alloc.vec.Vec.deref self.rules) self.aliases) c
          amUser (absSysHostname onHost) (Defaults.absSettings self.settings) ∧
      Defaults.absSettings self'.settings =
        validateSettings O (absAliasTable A self.aliases) c amUser (absSysHostname onHost)
          (Defaults.absSettings self.settings) ∧
      SettingsInRange self'.settings ∧
      self'.rules = self.rules ∧ self'.aliases = self.aliases ∧
      self'.customisers.non_cmnd.val = [] ∧
      self'.customisers.cmnd = self.customisers.cmnd := by
  obtain ⟨self1, hspec1, hset1, hrange1, hrules1, raliases1, hnon1, hcmnd1⟩ :=
    specify_host_user_runas_eq (A := A) hO hH self onHost amUser none hpol.1 hhost hokN hs
  obtain ⟨flags, hflags, hflagsAbs⟩ :=
    validate_flags_eq (A := A) hO hH (alloc.vec.Vec.deref self1.rules) self1.aliases
      (by rw [hrules1, raliases1]; exact hpol) amUser onHost hhost
  rw [hrules1, raliases1] at hflagsAbs
  have hset : Defaults.absSettings self1.settings =
      validateSettings O (absAliasTable A self.aliases) c amUser (absSysHostname onHost)
        (Defaults.absSettings self.settings) := by
    rw [hset1]
    simp only [validateSettings, hnon]
  cases flags with
  | none =>
    refine ⟨.Forbidden, self1, ?_, ?_, hset, hrange1, hrules1, raliases1, hnon1, hcmnd1⟩
    · unfold sudoers.Sudoers.check_validate_permission
      simp only [hspec1, Aeneas.Std.bind_ok, hflags]
    · rw [absListAuthorization_forbidden, validateAuthorization, ← hflagsAbs]
      all_goals rfl
  | some t =>
    obtain ⟨au, hau, habs⟩ := to_auth_eq self1.settings t hrange1.passwd_tries
    refine ⟨.Allowed au (), self1, ?_, ?_, hset, hrange1, hrules1, raliases1, hnon1, hcmnd1⟩
    · unfold sudoers.Sudoers.check_validate_permission
      simp only [hspec1, Aeneas.Std.bind_ok, hflags, hau]
    · rw [absListAuthorization_allowed, habs, validateAuthorization, ← hflagsAbs,
        absPolicy_aliases_eq, ← hset, Defaults.absDefaults_eq]
      all_goals rfl

end Validate

/-! ## `check_list_permission` -/

section ListPermission

variable {U UG : Type} {uInst : sudo_rs.system.interface.UnixUser U UG}
  {eqInst : core.cmp.PartialEq U U} {O : SudoersSpec.Oracle U UG} {A : GlobAbs}

/-- **`sudo -l` for one's own entries.** No Defaults pass runs: the policy is returned
unchanged, and the result is `listAuthorization`, i.e. the `list_flags` tag through `to_auth` of
the settings the policy holds. Only the hypotheses of `list_flags_self_spec` and the
`passwd_tries` range are needed. -/
theorem check_list_permission_self_eq (hO : InstOracle uInst eqInst uInst.UnixGroupInst O)
    (hH : O.SudoRsHosts) (grp : U → UG) (self : sudoers.Sudoers) (amUser : U)
    (onHost : system.Hostname) (request : sudoers.ListRequest U UG UG)
    (c : SudoersSpec.Analysis.Collected)
    (hpol : PolicyOK (alloc.vec.Vec.deref self.rules) self.aliases) (hhost : Fits onHost.inner)
    (hs : SettingsInRange self.settings)
    (hne : O.userEq request.inspected_user amUser = true) :
    ∃ a : sudoers.policy.Authorization Unit,
      sudoers.Sudoers.check_list_permission uInst eqInst uInst.UnixGroupInst self amUser onHost
          request = ok (a, self) ∧
      absListAuthorization a =
        listAuthorization O grp (absPolicy A (alloc.vec.Vec.deref self.rules) self.aliases) c
          (absListRequest amUser onHost request) (Defaults.absSettings self.settings) := by
  obtain ⟨flags, hflags, hflagsAbs⟩ := exists_eq_ok_of_spec
    (list_flags_self_spec (A := A) hO hH grp (alloc.vec.Vec.deref self.rules) self.aliases hpol
      amUser onHost hhost request hne)
  have hset : listSettings O (absAliasTable A self.aliases) c grp
      (absListRequest amUser onHost request) (Defaults.absSettings self.settings) =
      Defaults.absSettings self.settings :=
    SudoersSpec.Analysis.listSettings_self O (absAliasTable A self.aliases) c grp
      (absListRequest amUser onHost request) (Defaults.absSettings self.settings) hne
  cases flags with
  | none =>
    refine ⟨.Forbidden, ?_, ?_⟩
    · unfold sudoers.Sudoers.check_list_permission
      simp only [core.cmp.impls.PartialEqShared.ne, hO.ne, hne, Bool.not_true, Bool.false_eq_true,
        ite_false, Aeneas.Std.bind_ok, hflags]
    · rw [absListAuthorization_forbidden, listAuthorization, ← hflagsAbs]
      all_goals rfl
  | some t =>
    obtain ⟨au, hau, habs⟩ := to_auth_eq self.settings t hs.passwd_tries
    refine ⟨.Allowed au (), ?_, ?_⟩
    · unfold sudoers.Sudoers.check_list_permission
      simp only [core.cmp.impls.PartialEqShared.ne, hO.ne, hne, Bool.not_true, Bool.false_eq_true,
        ite_false, Aeneas.Std.bind_ok, hflags, hau]
    · rw [absListAuthorization_allowed, habs, listAuthorization, ← hflagsAbs,
        absPolicy_aliases_eq, hset, Defaults.absDefaults_eq]
      all_goals rfl

/-- **`sudo -l -U other`.** Both passes run as in `check` for the pseudo-command `list` run as
the inspected user; the result is `listAuthorization` and the settings of the returned policy
are `listSettings` (`listSettings_other`); rules and aliases are unchanged and both customiser
vectors are consumed. Hypotheses: those of `check_eq` and `list_flags_spec`. -/
theorem check_list_permission_other_eq (hO : InstOracle uInst eqInst uInst.UnixGroupInst O)
    (hG : GlobOracle A O) (hH : O.SudoRsHosts) (grp : U → UG) (hgrp : GroupOracle uInst grp)
    (hpath : ListPath A) (self : sudoers.Sudoers) (amUser : U) (onHost : system.Hostname)
    (request : sudoers.ListRequest U UG UG) (c : SudoersSpec.Analysis.Collected)
    (hpol : PolicyOK (alloc.vec.Vec.deref self.rules) self.aliases) (hhost : Fits onHost.inner)
    (hnon : c.nonCommand = Analysis.absNonCommand self.customisers.non_cmnd)
    (hcmd : c.command = Analysis.absCommandCustomisers A self.customisers.cmnd)
    (hokN : NonCommandEntriesOK self.customisers.non_cmnd.val)
    (hokC : CommandEntriesOK self.customisers.cmnd.val)
    (hs : SettingsInRange self.settings)
    (hne : O.userEq request.inspected_user amUser = false) :
    ∃ (a : sudoers.policy.Authorization Unit) (self' : sudoers.Sudoers),
      sudoers.Sudoers.check_list_permission uInst eqInst uInst.UnixGroupInst self amUser onHost
          request = ok (a, self') ∧
      absListAuthorization a =
        listAuthorization O grp (absPolicy A (alloc.vec.Vec.deref self.rules) self.aliases) c
          (absListRequest amUser onHost request) (Defaults.absSettings self.settings) ∧
      Defaults.absSettings self'.settings =
        listSettings O (absAliasTable A self.aliases) c grp (absListRequest amUser onHost request)
          (Defaults.absSettings self.settings) ∧
      SettingsInRange self'.settings ∧
      self'.rules = self.rules ∧ self'.aliases = self.aliases ∧
      self'.customisers.non_cmnd.val = [] ∧ self'.customisers.cmnd.val = [] := by
  obtain ⟨lp, hlp, hlpA⟩ := hpath
  obtain ⟨self1, hspec1, hset1, hrange1, hrules1, raliases1, hnon1, hcmnd1⟩ :=
    specify_host_user_runas_eq (A := A) hO hH self onHost amUser (some request.inspected_user)
      hpol.1 hhost hokN hs
  obtain ⟨self2, hspec2, hset2, hrange2, hrules2, raliases2, hnon2, hcmnd2⟩ :=
    specify_command_eq (A := A) hG self1 lp (Array.to_slice (Std.Array.empty std.ffi.os_str.OsString))
      (by rw [raliases1]; exact hpol.1) (by rw [hcmnd1]; exact hokC) hrange1
  obtain ⟨flags, hflags, hflagsAbs⟩ :=
    list_flags_eq (A := A) hO hG hH grp hgrp ⟨lp, hlp, hlpA⟩ (alloc.vec.Vec.deref self2.rules)
      self2.aliases (by rw [hrules2, hrules1, raliases2, raliases1]; exact hpol) amUser onHost
      hhost request
  rw [hrules2, hrules1, raliases2, raliases1] at hflagsAbs
  have hargs : (Array.to_slice (Std.Array.empty std.ffi.os_str.OsString)).val.map A.os = [] :=
    rfl
  have hset : Defaults.absSettings self2.settings =
      listSettings O (absAliasTable A self.aliases) c grp (absListRequest amUser onHost request)
        (Defaults.absSettings self.settings) := by
    rw [SudoersSpec.Analysis.listSettings_other O (absAliasTable A self.aliases) c grp
        (absListRequest amUser onHost request) (Defaults.absSettings self.settings) hne,
      hset2, raliases1, hcmnd1, hset1, hlpA, hargs, hnon, hcmd]
    all_goals rfl
  have hnonEmpty : self2.customisers.non_cmnd.val = [] := by rw [hnon2]; exact hnon1
  cases flags with
  | none =>
    refine ⟨.Forbidden, self2, ?_, ?_, hset, hrange2, hrules2.trans hrules1,
      raliases2.trans raliases1, hnonEmpty, hcmnd2⟩
    · unfold sudoers.Sudoers.check_list_permission
      simp only [core.cmp.impls.PartialEqShared.ne, hO.ne, hne, Bool.not_false, ite_true,
        Aeneas.Std.bind_ok, hspec1, hlp, lift, hspec2, hflags]
    · rw [absListAuthorization_forbidden, listAuthorization, ← hflagsAbs]
      all_goals rfl
  | some t =>
    obtain ⟨au, hau, habs⟩ := to_auth_eq self2.settings t hrange2.passwd_tries
    refine ⟨.Allowed au (), self2, ?_, ?_, hset, hrange2, hrules2.trans hrules1,
      raliases2.trans raliases1, hnonEmpty, hcmnd2⟩
    · unfold sudoers.Sudoers.check_list_permission
      simp only [core.cmp.impls.PartialEqShared.ne, hO.ne, hne, Bool.not_false, ite_true,
        Aeneas.Std.bind_ok, hspec1, hlp, lift, hspec2, hflags, hau]
    · rw [absListAuthorization_allowed, habs, listAuthorization, ← hflagsAbs,
        absPolicy_aliases_eq, ← hset, Defaults.absDefaults_eq]
      all_goals rfl

/-- **`check_list_permission` on a well-formed policy**, both branches: the result is
`listAuthorization`, the settings of the returned policy are `listSettings`, ranges, rules and
aliases are kept. -/
theorem check_list_permission_eq (hO : InstOracle uInst eqInst uInst.UnixGroupInst O)
    (hG : GlobOracle A O) (hH : O.SudoRsHosts) (grp : U → UG) (hgrp : GroupOracle uInst grp)
    (hpath : ListPath A) (self : sudoers.Sudoers) (amUser : U) (onHost : system.Hostname)
    (request : sudoers.ListRequest U UG UG) (c : SudoersSpec.Analysis.Collected)
    (hpol : PolicyOK (alloc.vec.Vec.deref self.rules) self.aliases) (hhost : Fits onHost.inner)
    (hnon : c.nonCommand = Analysis.absNonCommand self.customisers.non_cmnd)
    (hcmd : c.command = Analysis.absCommandCustomisers A self.customisers.cmnd)
    (hokN : NonCommandEntriesOK self.customisers.non_cmnd.val)
    (hokC : CommandEntriesOK self.customisers.cmnd.val)
    (hs : SettingsInRange self.settings) :
    ∃ (a : sudoers.policy.Authorization Unit) (self' : sudoers.Sudoers),
      sudoers.Sudoers.check_list_permission uInst eqInst uInst.UnixGroupInst self amUser onHost
          request = ok (a, self') ∧
      absListAuthorization a =
        listAuthorization O grp (absPolicy A (alloc.vec.Vec.deref self.rules) self.aliases) c
          (absListRequest amUser onHost request) (Defaults.absSettings self.settings) ∧
      Defaults.absSettings self'.settings =
        listSettings O (absAliasTable A self.aliases) c grp (absListRequest amUser onHost request)
          (Defaults.absSettings self.settings) ∧
      SettingsInRange self'.settings ∧
      self'.rules = self.rules ∧ self'.aliases = self.aliases := by
  cases hne : O.userEq request.inspected_user amUser
  · obtain ⟨a, self', h1, h2, h3, h4, h5, h6, -, -⟩ :=
      check_list_permission_other_eq hO hG hH grp hgrp hpath self amUser onHost request c hpol
        hhost hnon hcmd hokN hokC hs hne
    exact ⟨a, self', h1, h2, h3, h4, h5, h6⟩
  · obtain ⟨a, h1, h2⟩ :=
      check_list_permission_self_eq (A := A) hO hH grp self amUser onHost request c hpol hhost hs
        hne
    exact ⟨a, self, h1, h2,
      (SudoersSpec.Analysis.listSettings_self O (absAliasTable A self.aliases) c grp
        (absListRequest amUser onHost request) (Defaults.absSettings self.settings) hne).symm,
      hs, rfl, rfl⟩

/-- **`run_list` up to authentication.** `Context::from_list_opts` calls `search_path`, whose
first pass uses the invoking user and the `-u` target (`request.target_user`) and consumes the
first-pass customisers; `check_list_permission` follows. The result is
`listPipelineAuthorization` and the settings are `listPipelineSettings`: for one's own entries
the first pass with the `-u` target, for another user's entries additionally the command pass
for `list`; a `Defaults>…` line naming only the inspected user is not applied. -/
theorem search_path_then_check_list_permission_eq
    (hO : InstOracle uInst eqInst uInst.UnixGroupInst O)
    (hG : GlobOracle A O) (hH : O.SudoRsHosts) (grp : U → UG) (hgrp : GroupOracle uInst grp)
    (hpath : ListPath A) (self : sudoers.Sudoers) (amUser : U) (onHost : system.Hostname)
    (request : sudoers.ListRequest U UG UG) (c : SudoersSpec.Analysis.Collected)
    (hpol : PolicyOK (alloc.vec.Vec.deref self.rules) self.aliases) (hhost : Fits onHost.inner)
    (hnon : c.nonCommand = Analysis.absNonCommand self.customisers.non_cmnd)
    (hcmd : c.command = Analysis.absCommandCustomisers A self.customisers.cmnd)
    (hokN : NonCommandEntriesOK self.customisers.non_cmnd.val)
    (hokC : CommandEntriesOK self.customisers.cmnd.val)
    (hs : SettingsInRange self.settings) :
    ∃ (a : sudoers.policy.Authorization Unit) (self' : sudoers.Sudoers),
      (do
        let self1 ← sudoers.Sudoers.specify_host_user_runas uInst eqInst self onHost amUser
          (some request.target_user)
        sudoers.Sudoers.check_list_permission uInst eqInst uInst.UnixGroupInst self1 amUser
          onHost request) = ok (a, self') ∧
      absListAuthorization a =
        listPipelineAuthorization O grp (absPolicy A (alloc.vec.Vec.deref self.rules) self.aliases)
          c (absListRequest amUser onHost request) (Defaults.absSettings self.settings) ∧
      Defaults.absSettings self'.settings =
        listPipelineSettings O (absAliasTable A self.aliases) c grp
          (absListRequest amUser onHost request) (Defaults.absSettings self.settings) ∧
      SettingsInRange self'.settings ∧
      self'.rules = self.rules ∧ self'.aliases = self.aliases := by
  obtain ⟨self1, hspec1, hset1, hrange1, hrules1, raliases1, hnon1, hcmnd1⟩ :=
    specify_host_user_runas_eq (A := A) hO hH self onHost amUser (some request.target_user)
      hpol.1 hhost hokN hs
  obtain ⟨a, self', hrun, hauth, hset', hrange', hrules', haliases'⟩ :=
    check_list_permission_eq hO hG hH grp hgrp hpath self1 amUser onHost request
      { c with nonCommand := [] }
      (by rw [hrules1, raliases1]; exact hpol) hhost
      (by simp [Analysis.absNonCommand, hnon1])
      (by rw [hcmnd1]; exact hcmd)
      (by simp [NonCommandEntriesOK, hnon1])
      (by rw [hcmnd1]; exact hokC)
      hrange1
  refine ⟨a, self', ?_, ?_, ?_, hrange', hrules'.trans hrules1, haliases'.trans raliases1⟩
  · simp only [hspec1, Aeneas.Std.bind_ok, hrun]
  · rw [hauth, hrules1, raliases1, hset1, ← hnon]
    all_goals rfl
  · rw [hset', raliases1, hset1, ← hnon]
    all_goals rfl

end ListPermission

end SudoRsProofs.Parser.Scoping
