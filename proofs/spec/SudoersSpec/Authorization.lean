import SudoersSpec.Theorems

/-!
# From the decision to the terms of execution

Transcribes `src/sudoers/policy.rs` `Judgement::authorization` and `Settings::to_auth`: the
decision (`Judgement.flags`, i.e. `authorize`) and the Defaults values in force turn into
`Authorization::{Allowed(Authentication, Restrictions), Forbidden}`.

The Defaults values come from the `defaults!` table in `src/defaults/mod.rs`; `Defaults` holds
exactly the ones these two functions read, with the same initial values. The type `σ` of the
`env_keep`/`env_check` sets is a parameter: the mapping only passes them through.

The spec follows the code; `docs/man/sudoers.5.md` is not consulted here.
-/

namespace SudoersSpec

/-- `defaults::enums::timestamp_type`. -/
inductive TimestampType where
  | tty
  | ppid
  deriving DecidableEq, Repr

/-- The Defaults values read by `Judgement::authorization` and `Settings::to_auth`. Numbers are
`u64` in Rust. Durations are in seconds (`passwd_timeout`, `timestamp_timeout` are parsed from
fractional minutes); `passwd_timeout = 0` means no timeout. -/
structure Defaults (σ : Type) where
  usePty : Bool := true
  pwfeedback : Bool := true
  rootpw : Bool := false
  targetpw : Bool := false
  noexec : Bool := false
  noninteractiveAuth : Bool := false
  logAllowed : Bool := true
  setenv : Bool := false
  runcwd : Option String := none
  umask : Nat := 0o022
  umaskOverride : Bool := false
  passwdTries : Nat := 3
  securePath : Option String := none
  passwdTimeout : Nat := 5 * 60
  timestampTimeout : Nat := 15 * 60
  timestampType : TimestampType := .tty
  envKeep : σ
  envCheck : σ

/-- `core::time::Duration`. -/
structure Duration where
  secs : Nat
  nanos : Nat
  deriving DecidableEq, Repr

/-- `Duration::from_secs`. -/
def Duration.ofSecs (n : Nat) : Duration := ⟨n, 0⟩

/-- `policy.rs` `AuthenticatingUser`: whose password is asked. -/
inductive AuthenticatingUser where
  | invokingUser
  | root
  | targetUser
  deriving DecidableEq, Repr

/-- `policy.rs` `AuthenticationScope`. -/
inductive AuthenticationScope where
  | tty
  | ppid
  deriving DecidableEq, Repr

/-- `policy.rs` `Authentication`. -/
structure Authentication where
  mustAuthenticate : Bool
  credential : AuthenticatingUser
  allowedAttempts : Nat
  priorValidity : Duration
  pwfeedback : Bool
  passwordTimeout : Option Duration
  noninteractiveAuth : Bool
  scope : AuthenticationScope
  deriving DecidableEq, Repr

/-- `policy.rs` `DirChange`: `strict none` forbids `--chdir` and keeps the working directory,
`strict (some p)` changes to `p`, `any` allows `--chdir`. -/
inductive DirChange where
  | strict (p : Option String)
  | any
  deriving DecidableEq, Repr

/-- `exec::Umask`. -/
inductive Umask where
  | preserve
  | extend (mask : Nat)
  | override (mask : Nat)
  deriving DecidableEq, Repr

/-- `policy.rs` `Logging`. -/
inductive Logging where
  | auth
  | disabled
  deriving DecidableEq, Repr

/-- `policy.rs` `Restrictions` (without the `apparmor` feature). -/
structure Restrictions (σ : Type) where
  usePty : Bool
  trustEnvironment : Bool
  noexec : Bool
  envKeep : σ
  envCheck : σ
  chdir : DirChange
  path : Option String
  umask : Umask
  log : Logging

/-- `policy.rs` `Authorization<Restrictions>`. -/
inductive Authorization (σ : Type) where
  | allowed (auth : Authentication) (restrictions : Restrictions σ)
  | forbidden

variable {σ : Type}

/-! ## The mapping -/

/-- The `credential` of `Settings::to_auth`: `rootpw` first, then `targetpw`. -/
def credentialOf (d : Defaults σ) : AuthenticatingUser :=
  if d.rootpw then .root else if d.targetpw then .targetUser else .invokingUser

/-- `Settings::to_auth`. -/
def toAuth (d : Defaults σ) (t : Tag) : Authentication where
  mustAuthenticate := t.needsPasswd
  credential := credentialOf d
  allowedAttempts := d.passwdTries
  priorValidity := .ofSecs d.timestampTimeout
  pwfeedback := d.pwfeedback
  passwordTimeout := if d.passwdTimeout = 0 then none else some (.ofSecs d.passwdTimeout)
  noninteractiveAuth := d.noninteractiveAuth
  scope := match d.timestampType with
    | .tty => .tty
    | .ppid => .ppid

/-- `trust_environment`: an explicit `SETENV`/`NOSETENV` tag wins over the `setenv` default. -/
def trustEnvironmentOf (d : Defaults σ) (t : Tag) : Bool :=
  match t.env with
  | .implicit => d.setenv
  | .setenv => true
  | .nosetenv => false

/-- `noexec`: an explicit `EXEC`/`NOEXEC` tag wins over the `noexec` default. -/
def noexecOf (d : Defaults σ) (t : Tag) : Bool :=
  match t.noexec with
  | .implicit => d.noexec
  | .exec => false
  | .noexec => true

/-- `ChDir::construct` applied to the `runcwd` text (`tokens.rs`, `path.rs`): `*` is `any`;
other text containing `*` or a NUL character is rejected, and `.ok()` drops the error. -/
def runcwdDir (s : String) : Option ChDir :=
  if s = "*" then some .any
  else if s.toList.contains '*' then none
  else if s.toList.contains (Char.ofNat 0) then none
  else some (.path s)

/-- The `CWD` in force: the tag's, else the `runcwd` default's. -/
def cwdOf (d : Defaults σ) (t : Tag) : Option ChDir :=
  match t.cwd with
  | some c => some c
  | none => d.runcwd.bind runcwdDir

/-- `chdir`. -/
def chdirOf (d : Defaults σ) (t : Tag) : DirChange :=
  match cwdOf d t with
  | none => .strict none
  | some .any => .any
  | some (.path p) => .strict (some p)

/-- `umask`: `0o777` keeps the parent's umask. -/
def umaskOf (d : Defaults σ) : Umask :=
  if d.umask = 0o777 then .preserve
  else if d.umaskOverride then .override d.umask
  else .extend d.umask

/-- The `Restrictions` of `Judgement::authorization`. -/
def restrictionsOf (d : Defaults σ) (t : Tag) : Restrictions σ where
  usePty := d.usePty
  trustEnvironment := trustEnvironmentOf d t
  noexec := noexecOf d t
  envKeep := d.envKeep
  envCheck := d.envCheck
  chdir := chdirOf d t
  path := d.securePath
  umask := umaskOf d
  log := if d.logAllowed then .auth else .disabled

/-- `Judgement::authorization`. -/
def authorization (d : Defaults σ) : Option Tag → Authorization σ
  | none => .forbidden
  | some t => .allowed (toAuth d t) (restrictionsOf d t)

/-! ## Meta-theorems -/

/-- **Forbidden iff denied.** No Defaults value turns a denial into a permission or back. -/
theorem authorization_eq_forbidden_iff (d : Defaults σ) (f : Option Tag) :
    authorization d f = .forbidden ↔ f = none := by
  cases f <;> simp [authorization]

/-- An `Allowed` result comes from a granted tag, and its parts are `toAuth`/`restrictionsOf`
of that tag. -/
theorem authorization_eq_allowed_iff (d : Defaults σ) (f : Option Tag) (a : Authentication)
    (r : Restrictions σ) :
    authorization d f = .allowed a r ↔ ∃ t, f = some t ∧ a = toAuth d t ∧ r = restrictionsOf d t := by
  cases f with
  | none => simp [authorization]
  | some t =>
    simp only [authorization, Authorization.allowed.injEq, Option.some.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩; exact ⟨t, rfl, rfl, rfl⟩
    · rintro ⟨_, rfl, rfl, rfl⟩; exact ⟨rfl, rfl⟩

/-- **Authentication follows the tag only.** `must_authenticate` is `Tag::needs_passwd`; no
Defaults value changes it. -/
theorem authorization_mustAuthenticate (d : Defaults σ) (t : Tag) (a : Authentication)
    (r : Restrictions σ) (h : authorization d (some t) = .allowed a r) :
    a.mustAuthenticate = t.needsPasswd := by
  simp only [authorization, Authorization.allowed.injEq] at h
  rw [← h.1]; rfl

/-- `must_authenticate` is false exactly for `NOPASSWD`. -/
theorem toAuth_mustAuthenticate_eq_false_iff (d : Defaults σ) (t : Tag) :
    (toAuth d t).mustAuthenticate = false ↔ t.authenticate = .nopasswd := by
  simp only [toAuth, Tag.needsPasswd]
  cases t.authenticate <;> simp

/-- **Credential rule**: `rootpw` wins, then `targetpw`, otherwise the invoking user. -/
theorem credentialOf_eq_root_iff (d : Defaults σ) :
    credentialOf d = .root ↔ d.rootpw = true := by
  unfold credentialOf; cases d.rootpw <;> cases d.targetpw <;> simp

theorem credentialOf_eq_targetUser_iff (d : Defaults σ) :
    credentialOf d = .targetUser ↔ d.rootpw = false ∧ d.targetpw = true := by
  unfold credentialOf; cases d.rootpw <;> cases d.targetpw <;> simp

theorem credentialOf_eq_invokingUser_iff (d : Defaults σ) :
    credentialOf d = .invokingUser ↔ d.rootpw = false ∧ d.targetpw = false := by
  unfold credentialOf; cases d.rootpw <;> cases d.targetpw <;> simp

/-- **Explicit tags win** for environment trust, NOEXEC and the working directory; the Defaults
values only fill in what the tag leaves implicit. -/
theorem restrictionsOf_explicit (d : Defaults σ) (t : Tag) :
    (t.env = .setenv → (restrictionsOf d t).trustEnvironment = true) ∧
    (t.env = .nosetenv → (restrictionsOf d t).trustEnvironment = false) ∧
    (t.env = .implicit → (restrictionsOf d t).trustEnvironment = d.setenv) ∧
    (t.noexec = .noexec → (restrictionsOf d t).noexec = true) ∧
    (t.noexec = .exec → (restrictionsOf d t).noexec = false) ∧
    (t.noexec = .implicit → (restrictionsOf d t).noexec = d.noexec) ∧
    (t.cwd = some .any → (restrictionsOf d t).chdir = .any) ∧
    (∀ p, t.cwd = some (.path p) → (restrictionsOf d t).chdir = .strict (some p)) := by
  simp only [restrictionsOf, trustEnvironmentOf, noexecOf, chdirOf, cwdOf]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> simp_all

/-- The NOEXEC/SETENV results do not depend on the Defaults value when the tag is explicit, and
the working directory does not depend on `runcwd` when the tag sets `CWD`. -/
theorem restrictionsOf_tag_independent (d d' : Defaults σ) (t : Tag) :
    (t.env ≠ .implicit → (restrictionsOf d t).trustEnvironment =
      (restrictionsOf d' t).trustEnvironment) ∧
    (t.noexec ≠ .implicit → (restrictionsOf d t).noexec = (restrictionsOf d' t).noexec) ∧
    (t.cwd ≠ none → (restrictionsOf d t).chdir = (restrictionsOf d' t).chdir) := by
  simp only [restrictionsOf, trustEnvironmentOf, noexecOf, chdirOf, cwdOf]
  refine ⟨?_, ?_, ?_⟩ <;> intro h
  · cases he : t.env <;> simp_all
  · cases hx : t.noexec <;> simp_all
  · cases hc : t.cwd <;> simp_all

/-- Without a tag `CWD`, the working directory comes from `runcwd`: `*` allows `--chdir`, an
acceptable path is used, and an absent or rejected value (containing `*` or NUL) leaves
`strict none`. -/
theorem chdirOf_runcwd (d : Defaults σ) (t : Tag) (h : t.cwd = none) :
    chdirOf d t = match d.runcwd.bind runcwdDir with
      | none => .strict none
      | some .any => .any
      | some (.path p) => .strict (some p) := by
  simp [chdirOf, cwdOf, h]

/-- A `runcwd` value with a `*` other than `*` itself is silently ignored. -/
theorem runcwdDir_star (s : String) (h1 : s ≠ "*") (h2 : s.toList.contains '*' = true) :
    runcwdDir s = none := by
  simp only [runcwdDir, h1, h2, ite_false, ite_true]

/-! ## Composition with the decision -/

variable {User Group : Type} (O : Oracle User Group)

/-- **A denial stays a denial**, whatever the Defaults. -/
theorem authorization_authorize_forbidden (d : Defaults σ) (p : Policy) (r : Request User Group) :
    authorization d (authorize O p r) = .forbidden ↔ authorize O p r = none :=
  authorization_eq_forbidden_iff d _

/-- **Root (or a user running as themself with one of their groups) never authenticates**:
`authorize` sets NOPASSWD, so `must_authenticate` is false, whatever the Defaults. -/
theorem authorization_authorize_no_auth (d : Defaults σ) (p : Policy) (r : Request User Group)
    (h : O.isRoot r.invokingUser = true ∨
      (O.userEq r.targetUser r.invokingUser = true ∧ inGroup O r.invokingUser r.targetGroup = true))
    (a : Authentication) (res : Restrictions σ)
    (ha : authorization d (authorize O p r) = .allowed a res) : a.mustAuthenticate = false := by
  obtain ⟨t, ht, rfl, -⟩ := (authorization_eq_allowed_iff d _ a res).1 ha
  exact (toAuth_mustAuthenticate_eq_false_iff d t).2 (authorize_nopasswd O p r t h ht)

/-- The root case on its own. -/
theorem authorization_authorize_root (d : Defaults σ) (p : Policy) (r : Request User Group)
    (h : O.isRoot r.invokingUser = true) (a : Authentication) (res : Restrictions σ)
    (ha : authorization d (authorize O p r) = .allowed a res) : a.mustAuthenticate = false :=
  authorization_authorize_no_auth O d p r (.inl h) a res ha

end SudoersSpec
