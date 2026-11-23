import SudoRsProofs.Permission

/-!
# `Judgement::authorization` and `Settings::to_auth` refine `SudoersSpec.authorization`

`src/sudoers/policy.rs`: the decision (`Judgement.flags`) and the Defaults in force
(`Judgement.settings`) become `Authorization::{Allowed(Authentication, Restrictions), Forbidden}`.
Both functions are extracted as they are; `Settings` is plain data.

The only hypothesis is `SettingsInRange`: the two integer conversions that `unwrap`/`expect`
(`passwd_tries` to `u16`, `umask` to `mode_t = u32`) succeed. The Defaults DSL establishes it
for every `Settings` value (see `SettingsInRange`). Without it the extracted function panics
(`authorization_panics_of_passwd_tries`, `authorization_panics_of_umask`).
-/

open Aeneas Aeneas.Std Result
open sudo_rs -- the extracted names live in this namespace

namespace SudoRsProofs

/-- The extracted model of `HashSet<String>` (the `env_keep`/`env_check` sets). -/
abbrev RSet :=
  std.collections.hash.set.HashSet String std.hash.random.RandomState alloc.alloc.Global

/-! ## Abstraction functions -/

def absTimestampType : sudo_rs.defaults.enums.timestamp_type → SudoersSpec.TimestampType
  | .tty => .tty
  | .ppid => .ppid

/-- The Defaults values `authorization` reads. `Box<str>` values are read as text. -/
def absDefaults (s : sudo_rs.defaults.Settings) : SudoersSpec.Defaults RSet where
  usePty := s.use_pty
  pwfeedback := s.pwfeedback
  rootpw := s.rootpw
  targetpw := s.targetpw
  noexec := s.noexec
  noninteractiveAuth := s.noninteractive_auth
  logAllowed := s.log_allowed
  setenv := s.setenv
  runcwd := s.runcwd.map sudo_rs.stringOfStr
  umask := s.umask.val
  umaskOverride := s.umask_override
  passwdTries := s.passwd_tries.val
  securePath := s.secure_path.map sudo_rs.stringOfStr
  passwdTimeout := s.passwd_timeout.val
  timestampTimeout := s.timestamp_timeout.val
  timestampType := absTimestampType s.timestamp_type
  envKeep := s.env_keep
  envCheck := s.env_check

def absDuration (d : core.time.Duration) : SudoersSpec.Duration := ⟨d.secs.val, d.nanos.val⟩

def absCredential : sudo_rs.sudoers.policy.AuthenticatingUser → SudoersSpec.AuthenticatingUser
  | .InvokingUser => .invokingUser
  | .Root => .root
  | .TargetUser => .targetUser

def absScope : sudo_rs.sudoers.policy.AuthenticationScope → SudoersSpec.AuthenticationScope
  | .Tty => .tty
  | .PPid => .ppid

def absAuthentication (a : sudo_rs.sudoers.policy.Authentication) :
    SudoersSpec.Authentication where
  mustAuthenticate := a.must_authenticate
  credential := absCredential a.credential
  allowedAttempts := a.allowed_attempts.val
  priorValidity := absDuration a.prior_validity
  pwfeedback := a.pwfeedback
  passwordTimeout := a.password_timeout.map absDuration
  noninteractiveAuth := a.noninteractive_auth
  scope := absScope a.scope

def absDirChange : sudo_rs.sudoers.policy.DirChange → SudoersSpec.DirChange
  | .Strict p => .strict (p.map (·.inner))
  | .Any => .any

def absUmask : sudo_rs.exec.Umask → SudoersSpec.Umask
  | .Preserve => .preserve
  | .Extend m => .extend m.val
  | .Override m => .override m.val

def absLogging : sudo_rs.sudoers.policy.Logging → SudoersSpec.Logging
  | .Auth => .auth
  | .Disabled => .disabled

def absRestrictions (r : sudo_rs.sudoers.policy.Restrictions) : SudoersSpec.Restrictions RSet where
  usePty := r.use_pty
  trustEnvironment := r.trust_environment
  noexec := r.noexec
  envKeep := r.env_keep
  envCheck := r.env_check
  chdir := absDirChange r.chdir
  path := r.path.map sudo_rs.stringOfStr
  umask := absUmask r.umask
  log := absLogging r.log

def absAuthorization :
    sudo_rs.sudoers.policy.Authorization sudo_rs.sudoers.policy.Restrictions →
      SudoersSpec.Authorization RSet
  | .Allowed a r => .allowed (absAuthentication a) (absRestrictions r)
  | .Forbidden => .forbidden

/-! ## The hypothesis -/

/-- **Value ranges of the Defaults that `authorization` converts.**

`Settings` fields are private to `crate::defaults` and change only through `Settings::default`
and the modifiers built by `negate`/`set` (`src/defaults/settings_dsl.rs`):
* `passwd_tries = 3 [0..=1000]` (`src/defaults/mod.rs`): initial value 3; `set` filters the parsed
  `u64` with `(0..=1000).contains` (`modifier_of!`, `=int $first ..= $last` arm); no `!=` clause
  and not a flag or list, so `negate` rejects it (`has_standard_negator!` is `false`). Hence
  `passwd_tries ≤ 1000 ≤ u16::MAX`.
* `umask = 0o022 (!= 0o777) {octal_mode}`: initial value `0o22`, negation `0o777`; `set` stores
  `octal_mode(text)`, which parses a `libc::mode_t` and widens it (`Into<u64>`). Hence
  `umask ≤ mode_t::MAX`; `mode_t` is `u32` on Linux, the platform of the extraction.

The proof does not derive this from the DSL (its modifiers are boxed closures, which do not
extract); it is a hypothesis. -/
structure SettingsInRange (s : sudo_rs.defaults.Settings) : Prop where
  passwd_tries : s.passwd_tries.val ≤ U16.max
  umask : s.umask.val ≤ U32.max

/-! ## Building blocks -/

theorem tryFromUScalar_eq {src : UScalarTy} (tgt : UScalarTy) (i : UScalar src)
    (h : i.val ≤ UScalar.max tgt) :
    core.num.tryFromUScalar tgt i = ok (.Ok (UScalar.cast tgt i)) ∧
      (UScalar.cast tgt i).val = i.val := by
  refine ⟨by simp [core.num.tryFromUScalar, h], ?_⟩
  have := UScalar.cast_inBounds_spec tgt i h
  simpa [lift] using this

theorem tryFromUScalar_err {src : UScalarTy} (tgt : UScalarTy) (i : UScalar src)
    (h : UScalar.max tgt < i.val) :
    core.num.tryFromUScalar tgt i = ok (.Err ()) := by
  simp [core.num.tryFromUScalar, Nat.not_le.2 h]

theorem needs_passwd_eq (t : sudo_rs.sudoers.ast.Tag) :
    sudo_rs.sudoers.ast.Tag.needs_passwd t = ok (absTag t).needsPasswd := by
  rcases t with ⟨a, _, _, _, _, _⟩
  cases a <;> rfl

theorem as_deref_box_eq {T : Type} (o : Option T) :
    core.option.Option.as_deref (core.ops.deref.DerefBoxInst T) o = ok o := by
  cases o <;> simp [core.option.Option.as_deref, core.ops.deref.DerefBoxInst,
    alloc.boxed.Box.deref]

/-- The Rust `ChDir` of a spec `ChDir` (inverse of `absChDir`). -/
def concChDir : SudoersSpec.ChDir → sudo_rs.sudoers.tokens.ChDir
  | .any => .Any
  | .path p => .Path ⟨p⟩

@[simp] theorem absChDir_concChDir (c : SudoersSpec.ChDir) : absChDir (concChDir c) = c := by
  cases c <;> rfl

/-- `ChDir::construct` followed by `.ok()` is `runcwdDir`. -/
theorem construct_ok_eq (s : String) :
    (do
      let r ← sudoers.tokens.ChDir.Insts.Sudo_rsSudoersBasic_parserToken.construct s
      core.result.Result.ok r) = ok ((SudoersSpec.runcwdDir s).map concChDir) := by
  simp only [sudoers.tokens.ChDir.Insts.Sudo_rsSudoersBasic_parserToken.construct,
    sudoers.tokens.classify_chdir, sudoers.tokens.sudo_path, SudoersSpec.runcwdDir,
    core.result.Result.ok, concChDir]
  split_ifs <;> simp_all [core.result.Result.ok, concChDir]

/-- The `runcwd` fallback closure of `authorization`. -/
theorem runcwd_closure_eq (j : sudo_rs.sudoers.Judgement) :
    sudo_rs.sudoers.policy.Judgement.authorization.closure.Insts.CoreOpsFunctionFnOnceTupleOptionChDir.call_once
        j () =
      ok (((absDefaults j.settings).runcwd.bind SudoersSpec.runcwdDir).map concChDir) := by
  simp only [sudo_rs.sudoers.policy.Judgement.authorization.closure.Insts.CoreOpsFunctionFnOnceTupleOptionChDir.call_once,
    sudo_rs.defaults.Settings.impl.runcwd, as_deref_box_eq, bind_ok, absDefaults]
  cases j.settings.runcwd with
  | none => rfl
  | some s =>
    simp only [core.option.Option.and_then,
      sudo_rs.sudoers.policy.Judgement.authorization.closure.closure.Insts.CoreOpsFunctionFnOnceTupleShared1StrOptionChDir.call_once,
      alloc.string.String.Insts.CoreConvertFromShared0Str.from, bind_ok, construct_ok_eq,
      Option.map_some, Option.bind_some]

/-! ## `Settings::to_auth` -/

/-- **`to_auth` refines `toAuth`.** -/
theorem to_auth_eq (s : sudo_rs.defaults.Settings) (t : sudo_rs.sudoers.ast.Tag)
    (h : s.passwd_tries.val ≤ U16.max) :
    ∃ a, sudo_rs.sudoers.policy.Settings.to_auth s t = ok a ∧
      absAuthentication a = SudoersSpec.toAuth (absDefaults s) (absTag t) := by
  obtain ⟨hcast, hval⟩ := tryFromUScalar_eq .U16 s.passwd_tries (by simpa using h)
  simp only [sudo_rs.sudoers.policy.Settings.to_auth, needs_passwd_eq,
    sudo_rs.defaults.Settings.impl.passwd_tries, sudo_rs.defaults.Settings.impl.timestamp_timeout,
    sudo_rs.defaults.Settings.impl.pwfeedback, sudo_rs.defaults.Settings.impl.passwd_timeout,
    sudo_rs.defaults.Settings.impl.timestamp_type,
    sudo_rs.defaults.Settings.impl.noninteractive_auth, sudo_rs.defaults.Settings.impl.rootpw,
    sudo_rs.defaults.Settings.impl.targetpw,
    U16.Insts.CoreConvertTryFromU64TryFromIntError.try_from, hcast,
    core.result.Result.unwrap, core.time.Duration.from_secs, bind_ok]
  have hz : ∀ x : U64, x = 0#uscalar ↔ x.val = 0 := fun x =>
    ⟨fun h => by rw [h]; rfl, fun h => UScalar.val_eq_imp _ _ (by rw [h]; rfl)⟩
  split
  all_goals
    cases hts : s.timestamp_type <;> cases hr : s.rootpw <;> cases ht : s.targetpw <;>
    simp_all [absAuthentication, SudoersSpec.toAuth, SudoersSpec.credentialOf, absDefaults,
      absCredential, absScope, absTimestampType, absDuration, SudoersSpec.Duration.ofSecs]

/-! ## `Judgement::authorization` -/

theorem cwd_clone_eq (t : sudo_rs.sudoers.ast.Tag) :
    core.option.Option.Insts.CoreCloneClone.clone
      sudo_rs.sudoers.tokens.ChDir.Insts.CoreCloneClone t.cwd = ok t.cwd :=
  Option.clone_eq _ (fun d => eq_ok_of_spec (ChDir.clone_spec d)) t.cwd

/-- `tag.cwd.clone().or_else(..runcwd..)`: the tag's `CWD`, else the `runcwd` default. -/
theorem cwd_or_else_eq (t : sudo_rs.sudoers.ast.Tag) (s : sudo_rs.defaults.Settings) :
    core.option.Option.or_else
        sudo_rs.sudoers.policy.Judgement.authorization.closure.Insts.CoreOpsFunctionFnOnceTupleOptionChDir
        t.cwd ⟨some t, s⟩ =
      ok (match t.cwd with
        | some c => some c
        | none => ((absDefaults s).runcwd.bind SudoersSpec.runcwdDir).map concChDir) := by
  cases t.cwd with
  | some c => rfl
  | none =>
    simp only [core.option.Option.or_else]
    exact runcwd_closure_eq ⟨some t, s⟩

/-- **`passwd_tries` beyond `u16::MAX` panics** (`try_into().unwrap()` in `to_auth`): the
`passwd_tries` half of `SettingsInRange` is needed. -/
theorem authorization_panics_of_passwd_tries (t : sudo_rs.sudoers.ast.Tag)
    (s : sudo_rs.defaults.Settings) (h : U16.max < s.passwd_tries.val) :
    sudo_rs.sudoers.policy.Judgement.authorization ⟨some t, s⟩ = fail .panic := by
  simp [sudo_rs.sudoers.policy.Judgement.authorization,
    sudo_rs.defaults.Settings.impl.apparmor_profile, as_deref_box_eq,
    sudo_rs.sudoers.policy.Settings.to_auth, needs_passwd_eq,
    sudo_rs.defaults.Settings.impl.passwd_tries,
    U16.Insts.CoreConvertTryFromU64TryFromIntError.try_from,
    tryFromUScalar_err .U16 s.passwd_tries (by simpa using h), core.result.Result.unwrap]

/-- **`umask` beyond `u32::MAX` panics** (`.expect(..)` in `authorization`): the `umask` half of
`SettingsInRange` is needed. -/
theorem authorization_panics_of_umask (t : sudo_rs.sudoers.ast.Tag)
    (s : sudo_rs.defaults.Settings) (hp : s.passwd_tries.val ≤ U16.max)
    (h : U32.max < s.umask.val) :
    sudo_rs.sudoers.policy.Judgement.authorization ⟨some t, s⟩ = fail .panic := by
  obtain ⟨a, ha, -⟩ := to_auth_eq s t hp
  simp only [sudo_rs.sudoers.policy.Judgement.authorization,
    sudo_rs.defaults.Settings.impl.apparmor_profile, as_deref_box_eq, ha, cwd_clone_eq,
    cwd_or_else_eq, sudo_rs.defaults.Settings.impl.use_pty, sudo_rs.defaults.Settings.impl.setenv,
    sudo_rs.defaults.Settings.impl.noexec, sudo_rs.defaults.Settings.impl.env_keep,
    sudo_rs.defaults.Settings.impl.env_check, sudo_rs.defaults.Settings.impl.secure_path,
    sudo_rs.defaults.Settings.impl.umask,
    U32.Insts.CoreConvertTryFromU64TryFromIntError.try_from,
    tryFromUScalar_err .U32 s.umask (by simpa using h), core.result.Result.expect, bind_ok]
  rcases t with ⟨au, cwd, env, ap, nx, ig⟩
  cases env <;> cases nx <;> rcases cwd with _ | (_ | _) <;> simp
  all_goals
    rcases hr : s.runcwd with _ | r
    · simp [hr, absDefaults]
    · rcases hd : SudoersSpec.runcwdDir (sudo_rs.stringOfStr r) with _ | (_ | _) <;>
      simp [hr, hd, absDefaults, concChDir]

/-- **`authorization` refines `SudoersSpec.authorization`**: it returns `ok` (no panic) and the
result abstracts to the spec of the abstracted decision and Defaults. -/
theorem authorization_eq (j : sudo_rs.sudoers.Judgement) (h : SettingsInRange j.settings) :
    ∃ a, sudo_rs.sudoers.policy.Judgement.authorization j = ok a ∧
      absAuthorization a =
        SudoersSpec.authorization (absDefaults j.settings) (j.flags.map absTag) := by
  rcases hj : j with ⟨flags, s⟩
  rw [hj] at h
  cases flags with
  | none =>
    refine ⟨.Forbidden, ?_, rfl⟩
    simp [sudo_rs.sudoers.policy.Judgement.authorization,
      sudo_rs.defaults.Settings.impl.apparmor_profile, as_deref_box_eq]
  | some t =>
    obtain ⟨a, ha, habs⟩ := to_auth_eq s t h.passwd_tries
    obtain ⟨hcast, hval⟩ := tryFromUScalar_eq .U32 s.umask (by simpa using h.umask)
    have hclone := cwd_clone_eq t
    have hor := cwd_or_else_eq t s
    have hmask : (UScalar.cast .U32 s.umask = 511#u32) ↔ s.umask.val = 0o777 := by
      constructor
      · intro he; rw [← hval, he]; rfl
      · intro he; apply UScalar.val_eq_imp; rw [hval, he]; rfl
    simp only [sudo_rs.sudoers.policy.Judgement.authorization,
      sudo_rs.defaults.Settings.impl.apparmor_profile, as_deref_box_eq, ha, hclone, hor,
      sudo_rs.defaults.Settings.impl.use_pty, sudo_rs.defaults.Settings.impl.setenv,
      sudo_rs.defaults.Settings.impl.noexec, sudo_rs.defaults.Settings.impl.env_keep,
      sudo_rs.defaults.Settings.impl.env_check, sudo_rs.defaults.Settings.impl.secure_path,
      sudo_rs.defaults.Settings.impl.umask, sudo_rs.defaults.Settings.impl.umask_override,
      sudo_rs.defaults.Settings.impl.log_allowed,
      U32.Insts.CoreConvertTryFromU64TryFromIntError.try_from, hcast,
      core.result.Result.expect, bind_ok]
    have hlt : s.umask.val < 4294967296 := by
      have h1 : s.umask.val ≤ U32.max := h.umask
      scalar_tac
    rcases t with ⟨au, cwd, env, ap, nx, ig⟩
    by_cases hm : s.umask.val = 0o777
    all_goals
      cases env <;> cases nx <;> cases hu : s.umask_override <;> cases hl : s.log_allowed <;>
      rcases cwd with _ | (_ | _) <;>
      simp [hm, hmask, hu, hl, absAuthorization, absRestrictions, absDirChange, absUmask,
        absLogging, SudoersSpec.authorization, SudoersSpec.restrictionsOf,
        SudoersSpec.trustEnvironmentOf, SudoersSpec.noexecOf, SudoersSpec.chdirOf,
        SudoersSpec.cwdOf, SudoersSpec.umaskOf, absTag, absEnv, absExec, absChDir, absDefaults,
        habs, hval]
    all_goals
      rcases hr : s.runcwd with _ | r
      · simp [hm, hu, hl, hr, habs, hlt, absTag, absEnv, absExec, absDefaults]
      · rcases hd : SudoersSpec.runcwdDir (sudo_rs.stringOfStr r) with _ | (_ | _) <;>
        simp [hm, hu, hl, hr, hd, habs, hlt, absTag, absEnv, absExec, absDefaults, concChDir]

/-! ## Composition with the decision proof -/

section Composed

variable {U G UG : Type} {uInst : sudo_rs.system.interface.UnixUser U UG}
  {eqInst : core.cmp.PartialEq U U} {gInst : sudo_rs.system.interface.UnixGroup G}
  {O : SudoersSpec.Oracle U G} {A : GlobAbs}

/-- **Decision and terms of execution together.** `Sudoers::check` builds
`Judgement { flags: permission_flags(..), settings }`; for any `settings` in range, the extracted
`authorization` of that judgement returns `ok a`, and `a` is the spec mapping applied to the spec
decision `authorize`. Hypotheses: those of `permission_flags_eq` plus `SettingsInRange`. -/
theorem authorization_permission_flags_eq (hO : InstOracle uInst eqInst gInst O)
    (hG : GlobOracle A O) (hH : O.SudoRsHosts) (rules : Slice sudo_rs.sudoers.ast.PermissionSpec)
    (aliases : sudo_rs.sudoers.AliasTable) (hpol : PolicyOK rules aliases) (amUser : U)
    (onHost : sudo_rs.system.Hostname) (hhost : Fits onHost.inner)
    (request : sudo_rs.sudoers.Request U G UG) (settings : sudo_rs.defaults.Settings)
    (hs : SettingsInRange settings) :
    ∃ flags a,
      sudo_rs.sudoers.permission_flags uInst eqInst gInst rules aliases amUser onHost request =
        ok flags ∧
      sudo_rs.sudoers.policy.Judgement.authorization ⟨flags, settings⟩ = ok a ∧
      absAuthorization a = SudoersSpec.authorization (absDefaults settings)
        (SudoersSpec.authorize O (absPolicy A rules aliases) (absRequest A amUser onHost request)) := by
  obtain ⟨flags, hf, habs⟩ :=
    permission_flags_eq hO hG hH rules aliases hpol amUser onHost hhost request
  obtain ⟨a, ha, haeq⟩ := authorization_eq ⟨flags, settings⟩ hs
  exact ⟨flags, a, hf, ha, haeq.trans (by rw [← habs])⟩

theorem absAuthorization_eq_forbidden_iff
    (a : sudo_rs.sudoers.policy.Authorization sudo_rs.sudoers.policy.Restrictions) :
    absAuthorization a = .forbidden ↔ a = .Forbidden := by
  cases a <;> simp [absAuthorization]

/-- **Rust `Forbidden` iff the spec denies**, and **root never authenticates**: on the composed
path, the extracted result is `Forbidden` exactly when `SudoersSpec.authorize` is `none`, and when
the invoking user is root an `Allowed` result has `must_authenticate = false`, whatever the
Defaults. -/
theorem authorization_permission_flags_props (hO : InstOracle uInst eqInst gInst O)
    (hG : GlobOracle A O) (hH : O.SudoRsHosts) (rules : Slice sudo_rs.sudoers.ast.PermissionSpec)
    (aliases : sudo_rs.sudoers.AliasTable) (hpol : PolicyOK rules aliases) (amUser : U)
    (onHost : sudo_rs.system.Hostname) (hhost : Fits onHost.inner)
    (request : sudo_rs.sudoers.Request U G UG) (settings : sudo_rs.defaults.Settings)
    (hs : SettingsInRange settings) :
    ∃ flags a,
      sudo_rs.sudoers.permission_flags uInst eqInst gInst rules aliases amUser onHost request =
        ok flags ∧
      sudo_rs.sudoers.policy.Judgement.authorization ⟨flags, settings⟩ = ok a ∧
      (a = .Forbidden ↔
        SudoersSpec.authorize O (absPolicy A rules aliases) (absRequest A amUser onHost request) =
          none) ∧
      (O.isRoot amUser = true → ∀ auth res, a = .Allowed auth res →
        auth.must_authenticate = false) := by
  obtain ⟨flags, a, hf, ha, habs⟩ :=
    authorization_permission_flags_eq hO hG hH rules aliases hpol amUser onHost hhost request
      settings hs
  refine ⟨flags, a, hf, ha, ?_, ?_⟩
  · rw [← absAuthorization_eq_forbidden_iff, habs, SudoersSpec.authorization_eq_forbidden_iff]
  · rintro hroot auth res rfl
    exact SudoersSpec.authorization_authorize_root O _ _ (absRequest A amUser onHost request)
      hroot (absAuthentication auth) (absRestrictions res) habs.symm

end Composed

end SudoRsProofs
