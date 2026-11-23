import SudoRsProofs.Parser.Scoping.Command

/-!
# The two scoping passes as functions

`specify_host_user_runas` and `specify_command` as extracted: each `mem::replace`s its customiser
vector with an empty one (single use), builds the matchers and alias verdicts, runs the pass, and
returns the policy with the new settings. The theorems expose the new settings through
`absSettings`, keep `SettingsInRange`, and state that rules, alias tables and the other
customiser vector are unchanged.
-/

open Aeneas Aeneas.Std Result
open sudo_rs sudo_rs.sudoers
open SudoersSpec.Analysis (nonCommandModifiers commandModifiers applyModifiers)

namespace SudoRsProofs.Parser.Scoping

set_option allowUnsafeReducibility true in
attribute [local reducible] sudoers.match_user.closure sudoers.match_token.closure
  sudoers.match_command.closure alloc.vec.into_iter.IntoIter

local notation "matchUserFn" uInst =>
  sudo_rs.sudoers.match_user.closure.Insts.CoreOpsFunctionFnTupleShared1UserSpecifierBool uInst
local notation "matchCommandFn" =>
  sudo_rs.sudoers.match_command.closure.Insts.CoreOpsFunctionFnTupleShared2PairPatternArgsBool

variable {U G UG : Type} {uInst : sudo_rs.system.interface.UnixUser U UG}
  {eqInst : core.cmp.PartialEq U U} {gInst : sudo_rs.system.interface.UnixGroup G}
  {O : SudoersSpec.Oracle U G} {A : GlobAbs}

theorem match_user_self (u : U) : sudoers.match_user uInst u = ok u := rfl

theorem match_token_self (text : Str) :
    sudoers.match_token sudoers.tokens.Hostname.Insts.CoreOpsDerefDerefString text = ok text := rfl

theorem into_iter_self {T : Type} (v : alloc.vec.Vec T) :
    alloc.vec.IntoIteratorVec.into_iter v = ok v := rfl

theorem empty_vec_val {T : Type} : (alloc.vec.Vec.new T).val = [] := rfl

/-- **The first pass**: on a well-formed policy it returns `ok`, the settings are the reference
fold of the matching non-command entries, the ranges survive, and rules, aliases and the command
customisers are untouched; the non-command vector is emptied (single use). -/
theorem specify_host_user_runas_eq (hO : InstOracle uInst eqInst gInst O)
    (hH : O.SudoRsHosts) (self : sudoers.Sudoers) (onHost : system.Hostname) (amUser : U)
    (target : Option U) (hAlias : AliasTableOK self.aliases) (hhost : Fits onHost.inner)
    (hok : NonCommandEntriesOK self.customisers.non_cmnd.val)
    (hs : SettingsInRange self.settings) :
    ∃ self', sudoers.Sudoers.specify_host_user_runas uInst eqInst self onHost amUser target =
        ok self' ∧
      Defaults.absSettings self'.settings = applyModifiers
        (nonCommandModifiers O (absAliasTable A self.aliases) (absSysHostname onHost) amUser target
          (Analysis.absNonCommand self.customisers.non_cmnd))
        (Defaults.absSettings self.settings) ∧
      SettingsInRange self'.settings ∧
      self'.rules = self.rules ∧ self'.aliases = self.aliases ∧
      self'.customisers.non_cmnd.val = [] ∧
      self'.customisers.cmnd = self.customisers.cmnd := by
  obtain ⟨⟨hwfU, hfU, hgU⟩, ⟨hwfH, hfH, hgH⟩, ⟨hwfC, hfC⟩, ⟨hwfR, hfR, hgR⟩⟩ := hAlias
  obtain ⟨text, htextEq, htext⟩ :=
    exists_eq_ok_of_spec (system_hostname_deref_spec onHost hhost)
  obtain ⟨hostAliases, hhostEq, hhostA, hhostFit⟩ := exists_eq_ok_of_spec
    (get_aliases_match_token_spec hH (absSysHostname onHost) text htext self.aliases.host
      hwfH hfH hgH)
  obtain ⟨userAliases, huserEq, huserA, huserFit⟩ := exists_eq_ok_of_spec
    (get_aliases_match_user_spec hO amUser self.aliases.user hwfU hfU hgU)
  cases target with
  | none =>
    obtain ⟨s1, hloop, habs1, hrange1⟩ := specify_host_user_runas_loop_eq hO hH
      self.customisers.non_cmnd.val self.settings text (absSysHostname onHost) htext amUser
      hostAliases userAliases (absAliasTable A self.aliases) hhostA huserA none none
      (by simp) (by intro u h; exact absurd h (by simp)) hhostFit huserFit (by simp)
      self.customisers.non_cmnd rfl hok hs
    refine ⟨{ self with settings := s1, customisers :=
        { self.customisers with non_cmnd := alloc.vec.Vec.new _ } }, ?_, ?_, hrange1, rfl, rfl,
      empty_vec_val, rfl⟩
    · unfold sudoers.Sudoers.specify_host_user_runas
      simp only [core.mem.replace, uncurry_apply_pair, htextEq, bind_ok, match_token_self,
        hhostEq, match_user_self, huserEq, into_iter_self, hloop]
    · show Defaults.absSettings s1 = _
      rw [habs1]
  | some u =>
    obtain ⟨a, ha, haA, haFit⟩ := exists_eq_ok_of_spec
      (get_aliases_match_user_spec hO u self.aliases.runas hwfR hfR hgR)
    have hrunasEq : (do
        let r ← sudoers.match_user uInst u
        let a ← sudoers.get_aliases (matchUserFn uInst) self.aliases.runas r
        ok (some (r, a))) = ok (some (u, a)) := by
      simp [match_user_self, ha]
    obtain ⟨s1, hloop, habs1, hrange1⟩ := specify_host_user_runas_loop_eq hO hH
      self.customisers.non_cmnd.val self.settings text (absSysHostname onHost) htext amUser
      hostAliases userAliases (absAliasTable A self.aliases) hhostA huserA (some u) (some (u, a))
      (by simp)
      (by
        intro v hv
        simp only [Option.some.injEq] at hv
        subst hv
        exact ⟨a, rfl, haA⟩)
      hhostFit huserFit
      (by
        intro c names h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, h2⟩ := h
        subst h2
        exact haFit)
      self.customisers.non_cmnd rfl hok hs
    refine ⟨{ self with settings := s1, customisers :=
        { self.customisers with non_cmnd := alloc.vec.Vec.new _ } }, ?_, ?_, hrange1, rfl, rfl,
      empty_vec_val, rfl⟩
    · unfold sudoers.Sudoers.specify_host_user_runas
      simp only [core.mem.replace, uncurry_apply_pair, htextEq, bind_ok, match_token_self,
        hhostEq, match_user_self, huserEq, ha, into_iter_self, hloop]
    · show Defaults.absSettings s1 = _
      rw [habs1]

/-- **The second pass**: on a well-formed policy it returns `ok`, the settings are the reference
fold of the matching command entries, the ranges survive, and rules, aliases and the non-command
customisers are untouched; the command vector is emptied (single use). -/
theorem specify_command_eq (hG : GlobOracle A O) (self : sudoers.Sudoers)
    (command : std.path.Path) (arguments : Slice std.ffi.os_str.OsString)
    (hAlias : AliasTableOK self.aliases)
    (hok : CommandEntriesOK self.customisers.cmnd.val)
    (hs : SettingsInRange self.settings) :
    ∃ self', sudoers.Sudoers.specify_command self command arguments = ok self' ∧
      Defaults.absSettings self'.settings = applyModifiers
        (commandModifiers O (absAliasTable A self.aliases) (A.path command)
          (arguments.val.map A.os) (Analysis.absCommandCustomisers A self.customisers.cmnd))
        (Defaults.absSettings self.settings) ∧
      SettingsInRange self'.settings ∧
      self'.rules = self.rules ∧ self'.aliases = self.aliases ∧
      self'.customisers.non_cmnd = self.customisers.non_cmnd ∧
      self'.customisers.cmnd.val = [] := by
  obtain ⟨⟨hwfU, hfU, hgU⟩, ⟨hwfH, hfH, hgH⟩, ⟨hwfC, hfC⟩, ⟨hwfR, hfR, hgR⟩⟩ := hAlias
  obtain ⟨c, hcEq, hcpred⟩ := exists_eq_ok_of_spec (match_command_spec (A := A) hG command arguments)
  obtain ⟨hcval, -⟩ := hcpred
  obtain ⟨cmnd_aliases, hcmndEq, hcmndA, hcmndFit⟩ := exists_eq_ok_of_spec
    (get_aliases_match_command_spec (A := A) hG command arguments self.aliases.cmnd hwfC hfC)
  obtain ⟨s1, hloop, habs1, hrange1⟩ := specify_command_loop_eq hG
    self.customisers.cmnd.val self.settings command arguments cmnd_aliases
    (absAliasTable A self.aliases) hcmndA hcmndFit self.customisers.cmnd rfl hok hs
  refine ⟨{ self with settings := s1, customisers :=
    { self.customisers with cmnd := alloc.vec.Vec.new _ } }, ?_, ?_, hrange1, rfl, rfl, rfl,
    empty_vec_val⟩
  · unfold sudoers.Sudoers.specify_command
    simp only [core.mem.replace, uncurry_apply_pair, hcEq, hcval, bind_ok, hcmndEq,
      into_iter_self, hloop]
  · show Defaults.absSettings s1 = _
    rw [habs1]

end SudoRsProofs.Parser.Scoping
