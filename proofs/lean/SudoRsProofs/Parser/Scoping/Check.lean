import SudoRsProofs.Parser.Scoping.Functions
import SudoRsProofs.Parser.Scoping.Clone
import SudoRsProofs.Permission

/-!
# `Sudoers::check`: both Defaults passes and the decision

`src/sudoers/mod.rs`: `check` runs the non-command pass with the invoking user and the request's
target user, then the command pass with the request's path and arguments, computes
`permission_flags` on the unchanged policy, clones the effective settings into the judgement, and
returns the judgement with the consumed policy.

The theorem exposes the effective settings as `SudoersSpec.Analysis.settingsInForce` and the
flags as `SudoersSpec.authorize`; `check_authorization_eq` composes `Judgement::authorization`
(`authorization_eq`) to the specification's `Authorization` over the effective Defaults. A
collected configuration is supplied by `c` and the two customiser correspondences, which is the
form PA produces; no initializer equality is assumed (arbitrary initial settings).
-/

open Aeneas Aeneas.Std Result
open sudo_rs sudo_rs.sudoers
open SudoersSpec.Analysis (nonCommandModifiers commandModifiers applyModifiers settingsInForce)

namespace SudoRsProofs.Parser.Scoping

variable {U G UG : Type} {uInst : sudo_rs.system.interface.UnixUser U UG}
  {eqInst : core.cmp.PartialEq U U} {gInst : sudo_rs.system.interface.UnixGroup G}
  {O : SudoersSpec.Oracle U G} {A : GlobAbs}

/-- **`check` on a well-formed policy.** Both passes run (even towards a forbidden decision),
the policy's rules and aliases are unchanged, both customiser vectors are emptied, the judgement
carries the settings in force (clone identity) and the abstract decision. -/
theorem check_eq (hO : InstOracle uInst eqInst gInst O) (hG : GlobOracle A O)
    (hH : O.SudoRsHosts) (self : sudoers.Sudoers) (amUser : U) (onHost : system.Hostname)
    (request : sudoers.Request U G UG) (c : SudoersSpec.Analysis.Collected)
    (hpol : PolicyOK (alloc.vec.Vec.deref self.rules) self.aliases) (hhost : Fits onHost.inner)
    (hnon : c.nonCommand = Analysis.absNonCommand self.customisers.non_cmnd)
    (hcmd : c.command = Analysis.absCommandCustomisers A self.customisers.cmnd)
    (hokN : NonCommandEntriesOK self.customisers.non_cmnd.val)
    (hokC : CommandEntriesOK self.customisers.cmnd.val)
    (hs : SettingsInRange self.settings) :
    ∃ j self', sudoers.Sudoers.check uInst eqInst gInst self amUser onHost request =
        ok (j, self') ∧
      Defaults.absSettings j.settings =
        settingsInForce O (absAliasTable A self.aliases) c
          (absRequest A amUser onHost request) (Defaults.absSettings self.settings) ∧
      j.flags.map absTag =
        SudoersSpec.authorize O (absPolicy A (alloc.vec.Vec.deref self.rules) self.aliases)
          (absRequest A amUser onHost request) ∧
      SettingsInRange j.settings ∧
      self'.rules = self.rules ∧ self'.aliases = self.aliases ∧
      self'.customisers.non_cmnd.val = [] ∧
      self'.customisers.cmnd.val = [] ∧
      j.settings = self'.settings := by
  obtain ⟨self1, hspec1, hset1, hrange1, hrules1, raliases1, hnon1, hcmnd1⟩ :=
    specify_host_user_runas_eq (A := A) hO hH self onHost amUser (some request.user) hpol.1
      hhost hokN hs
  obtain ⟨self2, hspec2, hset2, hrange2, hrules2, raliases2, hnon2, hcmnd2⟩ :=
    specify_command_eq (A := A) hG self1 request.command request.arguments
      (by rw [raliases1]; exact hpol.1) (by rw [hcmnd1]; exact hokC) hrange1
  obtain ⟨flags, hflags, hflagsAbs⟩ :=
    permission_flags_eq (A := A) hO hG hH (alloc.vec.Vec.deref self2.rules) self2.aliases
      (by rw [hrules2, hrules1, raliases2, raliases1]; exact hpol) amUser onHost hhost request
  obtain ⟨s1, hclone, hs1eq⟩ := settings_clone_eq' self2.settings
  refine ⟨{ flags := flags, settings := s1 }, self2, ?_, ?_, ?_, ?_, hrules2.trans hrules1,
    raliases2.trans raliases1, ?_, hcmnd2, hs1eq⟩
  · unfold sudoers.Sudoers.check
    simp only [core.mem.replace, uncurry_apply_pair, hspec1, bind_ok, hspec2, hflags, hclone]
  · rw [hs1eq, hset2, raliases1, hcmnd1, hset1]
    simp only [settingsInForce, absRequest, hnon, hcmd]
  · rw [hrules2, hrules1, raliases2, raliases1] at hflagsAbs
    exact hflagsAbs
  · rw [hs1eq]
    exact hrange2
  · rw [hnon2]
    exact hnon1

/-- **The composed decision.** Under `SettingsInRange` (kept by both passes), the extracted
`Judgement::authorization` of `check` returns `ok a`, and `a` is the specification's
`Authorization` over the effective settings in force and the abstract `authorize` flags. Denial
is `.forbidden` exactly when `authorize` returns `none`; `check` never panics here. -/
theorem check_authorization_eq (hO : InstOracle uInst eqInst gInst O) (hG : GlobOracle A O)
    (hH : O.SudoRsHosts) (self : sudoers.Sudoers) (amUser : U) (onHost : system.Hostname)
    (request : sudoers.Request U G UG) (c : SudoersSpec.Analysis.Collected)
    (hpol : PolicyOK (alloc.vec.Vec.deref self.rules) self.aliases) (hhost : Fits onHost.inner)
    (hnon : c.nonCommand = Analysis.absNonCommand self.customisers.non_cmnd)
    (hcmd : c.command = Analysis.absCommandCustomisers A self.customisers.cmnd)
    (hokN : NonCommandEntriesOK self.customisers.non_cmnd.val)
    (hokC : CommandEntriesOK self.customisers.cmnd.val)
    (hs : SettingsInRange self.settings) :
    ∃ (j : sudoers.Judgement) (self' : sudoers.Sudoers)
      (a : sudoers.policy.Authorization sudoers.policy.Restrictions),
      sudoers.Sudoers.check uInst eqInst gInst self amUser onHost request = ok (j, self') ∧
      sudoers.policy.Judgement.authorization j = ok a ∧
      absAuthorization a =
        SudoersSpec.authorization
          (settingsInForce O (absAliasTable A self.aliases) c
            (absRequest A amUser onHost request) (Defaults.absSettings self.settings)).toDefaults
          (SudoersSpec.authorize O (absPolicy A (alloc.vec.Vec.deref self.rules) self.aliases)
            (absRequest A amUser onHost request)) ∧
      (a = .Forbidden ↔
        SudoersSpec.authorize O (absPolicy A (alloc.vec.Vec.deref self.rules) self.aliases)
          (absRequest A amUser onHost request) = none) ∧
      self'.rules = self.rules ∧ self'.aliases = self.aliases ∧
      self'.customisers.non_cmnd.val = [] ∧ self'.customisers.cmnd.val = [] := by
  obtain ⟨j, self', hcheck, hset, hflags, hrange, hrules, haliases, hnc, hcm, -⟩ :=
    check_eq (A := A) hO hG hH self amUser onHost request c hpol hhost hnon hcmd hokN hokC hs
  obtain ⟨a, hauth, habs⟩ := authorization_eq j hrange
  refine ⟨j, self', a, hcheck, hauth, ?_, ?_, hrules, haliases, hnc, hcm⟩
  · rw [show absAuthorization a = _ from habs, Defaults.absDefaults_eq, hset, hflags]
  · rw [← absAuthorization_eq_forbidden_iff]
    rw [show absAuthorization a =
      SudoersSpec.authorization
        (settingsInForce O (absAliasTable A self.aliases) c
          (absRequest A amUser onHost request) (Defaults.absSettings self.settings)).toDefaults
        (SudoersSpec.authorize O (absPolicy A (alloc.vec.Vec.deref self.rules) self.aliases)
          (absRequest A amUser onHost request)) from by
      rw [show absAuthorization a = _ from habs, Defaults.absDefaults_eq, hset, hflags]]
    exact SudoersSpec.authorization_eq_forbidden_iff _ _

end SudoRsProofs.Parser.Scoping
