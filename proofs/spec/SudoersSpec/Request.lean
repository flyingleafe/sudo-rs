import SudoersSpec.Escape

/-! Request construction for `Context::from_run_opts`, after CLI parsing and resolving the
invoker and hostname. The result supplies the user, group, command and argument fields of
`sudo::pipeline::judge`'s `Request`. It does not model admission, authentication or execution.
`from_run_opts` resolves the targets first, then the shell, then the policy's secure path
(or the environment PATH), then builds the command under `sudo_call`. This specifies the
selection inside that call, not credential changes or its own error paths. An unsuccessful
command resolution still supplies a path and argv for policy matching; `resolved` is checked
later by `Context::try_as_run_options`. Edit's synthetic `sudoedit` and validation's empty
command are outside this model; list with positional arguments uses the direct case.

`NameOrId::parse` supplies `TargetArg.key`; see the separate AArch64 proof
`parseUid_placed_ok` for the UID specialization. The GID specialization uses the same
`u32::from_str` implementation on the supported targets, by source inspection, not a second
machine-code proof. `none` for the key of a *present* option means parse failure, not an
omitted option. Shell escaping is `SudoersSpec.Escape.escapeArgs` and is verified separately by
`SudoRsProofs.Escape.escaped_eq`; we do not model interpretation by a shell. -/

namespace SudoersSpec.Request

inductive NameOrId where
  | name (value : String)
  | id (value : UInt32)
  deriving DecidableEq

structure TargetArg where
  raw : String
  key : Option NameOrId

/-- NSS answers as seen by the Rust wrapper. An ordinary miss (`ok none`) is not an I/O or
account-construction error (`error e`). `primaryGroup` can succeed with an unnamed group:
`User::primary_group` calls `Group::from_gid_unchecked`, not `Group::from_gid`. -/
structure Nss (U G E : Type) where
  user : NameOrId → Except E (Option U)
  group : NameOrId → Except E (Option G)
  primaryGroup : U → Except E G

inductive Lookup (U : Type) where
  | user (key : NameOrId)
  | group (key : NameOrId)
  | primaryGroup (user : U)
  deriving DecidableEq

inductive TargetError (E : Type) where
  | lookup (error : E)
  | userNotFound (arg : String)
  | groupNotFound (arg : String)
  deriving DecidableEq

inductive Fallback where
  | keep
  | currentUser
  | primaryGroupIfFound
  | root
  deriving DecidableEq

def targetFallback : Bool → Bool → Fallback
  | true, true => .keep
  | false, true => .currentUser
  | true, false => .primaryGroupIfFound
  | false, false => .root

inductive Missing where
  | user
  | group
  deriving DecidableEq

def selectTarget (user : Option U) (group : Option G) : Except Missing (U × G) :=
  match user with
  | none => .error .user
  | some u => group.elim (.error .group) (fun g => .ok (u, g))

/-- Ordered observations; an error prevents any later lookups in the same call. -/
abbrev Observed (U E A : Type) := List (Lookup U) × Except (TargetError E) A

private def observedBind (result : Observed U E A) (next : A → Observed U E B) :
    Observed U E B :=
  match result with
  | (log, .error e) => (log, .error e)
  | (log, .ok value) =>
      let (more, out) := next value
      (log ++ more, out)

@[simp] theorem observedBind_result (result : Observed U E A) (next : A → Observed U E B) :
    (observedBind result next).2 = result.2.bind (fun a => (next a).2) := by
  obtain ⟨_, result⟩ := result
  cases result <;> rfl

private def observedLookup (call : Lookup U) (answer : Except E A) : Observed U E A :=
  ([call], answer.mapError TargetError.lookup)

@[simp] theorem observedLookup_result (call : Lookup U) (answer : Except E A) :
    (observedLookup call answer).2 = answer.mapError TargetError.lookup := rfl

private def optionalLookup (arg : Option TargetArg) (call : NameOrId → Lookup U)
    (query : NameOrId → Except E (Option A)) : Observed U E (Option A) :=
  match arg.bind TargetArg.key with
  | none => ([], .ok none)
  | some key => observedLookup (call key) (query key)

/-- The return of the native name-or-ID dispatch on an explicit option. A parse failure
produces an ordinary miss without an NSS call. -/
def lookupAnswer (query : NameOrId → Except E (Option A)) (arg : TargetArg) :
    Except (TargetError E) (Option A) :=
  (arg.key.elim (.ok none) query).mapError TargetError.lookup

@[simp] theorem optionalLookup_result (arg : Option TargetArg) (call : NameOrId → Lookup U)
    (query : NameOrId → Except E (Option A)) :
    (optionalLookup arg call query).2 =
      arg.elim (.ok none) (lookupAnswer query) := by
  cases arg with
  | none => rfl
  | some arg => cases h : arg.key <;> simp [optionalLookup, lookupAnswer, observedLookup, h,
      Except.mapError]

def finishTarget (userArg groupArg : Option TargetArg) (answer : Except Missing (U × G)) :
    Except (TargetError E) (U × G) :=
  match answer with
  | .ok pair => .ok pair
  | .error .user => .error (.userNotFound ((userArg.map TargetArg.raw).getD ""))
  | .error .group => .error (.groupNotFound ((groupArg.map TargetArg.raw).getD ""))

/-- `rootGroupName` is `root` on Linux and `wheel` otherwise. The primary-group lookup is
made only on a found user. Both ordinary explicit lookups precede the fallback, so even a
missing user does not suppress the group lookup. -/
def resolveTarget (nss : Nss U G E) (invoker : U) (rootGroupName : String)
    (userArg groupArg : Option TargetArg) :
    Observed U E (U × G) :=
  let finish (u : Option U) (g : Option G) : Observed U E (U × G) :=
    ([], finishTarget userArg groupArg (selectTarget u g))
  observedBind (optionalLookup userArg .user nss.user) fun u =>
    observedBind (optionalLookup groupArg .group nss.group) fun g =>
      match targetFallback userArg.isSome groupArg.isSome with
      | .keep => finish u g
      | .currentUser => finish (some invoker) g
      | .primaryGroupIfFound =>
          match u with
          | none => finish u g
          | some user =>
              observedBind (observedLookup (.primaryGroup user) (nss.primaryGroup user)) fun group =>
                finish u (some group)
      | .root =>
          observedBind (observedLookup (.user (.name "root")) (nss.user (.name "root"))) fun user =>
            let key := NameOrId.name rootGroupName
            observedBind (observedLookup (.group key) (nss.group key)) fun group => finish user group

/-- A user NSS error, unlike a miss, suppresses the group lookup and every fallback. -/
theorem user_lookup_error (nss : Nss U G E) (invoker : U) (rootGroupName : String)
    (arg : TargetArg) (groupArg : Option TargetArg) (key : NameOrId) (e : E)
    (parsed : arg.key = some key) (answer : nss.user key = .error e) :
    resolveTarget nss invoker rootGroupName (some arg) groupArg =
      ([.user key], .error (.lookup e)) := by
  simp [resolveTarget, optionalLookup, observedLookup, observedBind, parsed,
    answer, Except.mapError]

/-- On an ordinary missing explicit user, the explicit group call still runs. If it errors,
its error is returned; if it returns normally, the original user text is reported missing. -/
theorem ordinary_user_miss (nss : Nss U G E) (invoker : U) (rootGroupName : String)
    (userArg groupArg : TargetArg) (u g : NameOrId)
    (userKey : userArg.key = some u) (groupKey : groupArg.key = some g)
    (missed : nss.user u = .ok none) :
    resolveTarget nss invoker rootGroupName (some userArg) (some groupArg) =
      ([.user u, .group g], match nss.group g with
        | .error e => .error (.lookup e)
        | .ok _ => .error (.userNotFound userArg.raw)) := by
  cases answer : nss.group g <;>
    simp [resolveTarget, optionalLookup, observedLookup, observedBind, userKey,
      groupKey, missed, answer, Except.mapError, targetFallback, finishTarget, selectTarget]

abbrev Bytes := List UInt8

/-- `Path::parent() != Some(Path::new(""))` on Unix. A path is unqualified exactly when it is
relative and has one component, counting a leading `.`. Empty pieces and non-leading `.`
are not components. This characterization of the standard library is a boundary contract. -/
def isQualified (path : Bytes) : Bool :=
  path.isEmpty || path.head? == some 47 ||
    ((path.splitOn 47).drop 1).any (fun p => !p.isEmpty && p != [46])

/-- `Path::join` on an absolute directory and an unqualified command: append the original
command bytes, inserting a `/` if needed. -/
def joinCandidate (dir command : Bytes) : Bytes :=
  dir ++ (if dir.getLast? == some 47 then command else 47 :: command)

/-- The ordered candidates for the remaining PATH entries, before filesystem checks. -/
def pathCandidatesFrom (dirs : List Bytes) (command : Bytes) : List Bytes :=
  (dirs.filter fun dir => dir.head? == some 47).map fun dir => joinCandidate dir command

/-- The candidates `resolve_path` considers, in order, before metadata checks. Empty and
relative PATH entries are skipped. The supplied command is unqualified. -/
def pathCandidates (path command : Bytes) : List Bytes :=
  pathCandidatesFrom (path.splitOn 58) command

/-- Filesystem answers in the context of `sudo_call` with the selected user and group. The
fields are pointwise observations, not software implementations of the filesystem. -/
structure Filesystem where
  /-- `is_valid_executable`: `is_file` succeeds, and the subsequent `metadata` call succeeds
  and returns at least one bit of `mode & 0o111`. This is not `access(X_OK)`. -/
  executable : Bytes → Bool
  /-- `canonicalize`: canonicalize the parent and retain the final filename (if any), then
  check metadata on the reconstructed path. `none` covers any failure. -/
  canonical : Bytes → Option Bytes

def searchPath (fs : Filesystem) (path command : Bytes) : Option Bytes :=
  (pathCandidates path command).find? fs.executable

theorem search_first (fs : Filesystem) (path command found : Bytes) :
    searchPath fs path command = some found ↔
      fs.executable found ∧ ∃ before after, pathCandidates path command = before ++ found :: after ∧
        ∀ earlier ∈ before, !fs.executable earlier :=
  List.find?_eq_some_iff_append

/-- A successful step changes the pathname, not the old success flag. A failure clears
that flag and keeps the old pathname. -/
def selectPath (input : P) (replacement : Option P) (resolved : Bool) : P × Bool :=
  (replacement.getD input, resolved && replacement.isSome)

def commandPath (fs : Filesystem) (search : Bool) (path input : Bytes) : Bytes × Bool :=
  let (candidate, found) :=
    if search then selectPath input (searchPath fs path input) true else (input, true)
  selectPath candidate (fs.canonical candidate) found

/-- Canonicalization still runs after a failed PATH search; even success there cannot set
`resolved` back to `true`. `arg0` is recorded separately before either lookup. -/
theorem path_miss (fs : Filesystem) (path input : Bytes)
    (miss : searchPath fs path input = none) :
    commandPath fs true path input = ((fs.canonical input).getD input, false) := by
  simp [commandPath, selectPath, miss]

inductive Launch where
  | direct
  | shell
  | login
  deriving DecidableEq

def launch (login shell : Bool) : Launch :=
  if login then .login else if shell then .shell else .direct

/-- `envShell` is `some` exactly for a present UTF-8 `SHELL` (possibly empty). -/
def selectShell (envShell : Option Bytes) (currentShell targetShell : Bytes) : Launch → Option Bytes
  | .direct => none
  | .shell => some (envShell.getD currentShell)
  | .login => some targetShell

/-- `securePath` is the result of policy Defaults scoped by hostname, invoker and target; the
UTF-8 environment PATH is read only when it is absent. A missing/non-UTF-8 PATH becomes empty. -/
def effectivePath (securePath envPath : Option Bytes) : Bytes :=
  securePath.getD (envPath.getD [])

structure Command where
  path : Bytes
  arguments : List Bytes
  resolved : Bool
  arg0 : Option Bytes
  deriving DecidableEq

/-- `build_from_args` for run and nonempty-command list mode. `none` means the excluded
empty direct argv (the Rust `Vec::remove(0)` panics); it is not a command lookup failure.
Shell mode does not search PATH. No shell evaluation or credential switching is modeled. -/
def buildCommand (fs : Filesystem) (shell : Option Bytes) (argv : List Bytes) (path : Bytes) :
    Option Command :=
  match shell, argv with
  | some s, _ =>
      let (command, resolved) := commandPath fs false path s
      let args := if argv.isEmpty then [] else [[45, 99], Escape.escapeArgs argv]
      some ⟨command, args, resolved, none⟩
  | none, [] => none
  | none, first :: tail =>
      let (command, resolved) := commandPath fs (!isQualified first) path first
      some ⟨command, tail, resolved, some first⟩

theorem direct_argv (fs : Filesystem) (path first : Bytes) (tail : List Bytes) :
    (buildCommand fs none (first :: tail) path).map (fun c => (c.arg0, c.arguments)) =
      some (some first, tail) := by
  cases h : commandPath fs (!isQualified first) path first <;> simp [buildCommand, h]

/-! Ordinary nonroot examples. These are not authorization requests or policies. -/

private def ordinaryNss : Nss Nat Nat Unit where
  user := fun k => .ok (if k = .name "alice" then some 1000 else none)
  group := fun k => .ok (if k = .name "staff" then some 1001 else none)
  primaryGroup := fun _ => .ok 1000

theorem ordinary_explicit_target :
    resolveTarget ordinaryNss 1002 "root"
      (some ⟨"alice", some (.name "alice")⟩) (some ⟨"staff", some (.name "staff")⟩) =
      ([.user (.name "alice"), .group (.name "staff")], .ok (1000, 1001)) := by
  simp [resolveTarget, optionalLookup, observedLookup, observedBind, ordinaryNss,
    Except.mapError, targetFallback, finishTarget, selectTarget, Option.elim]

theorem ordinary_missing_target :
    resolveTarget ordinaryNss 1002 "root"
      (some ⟨"missing", some (.name "missing")⟩) (some ⟨"staff", some (.name "staff")⟩) =
      ([.user (.name "missing"), .group (.name "staff")], .error (.userNotFound "missing")) := by
  simp [resolveTarget, optionalLookup, observedLookup, observedBind, ordinaryNss,
    Except.mapError, targetFallback, finishTarget, selectTarget, Option.elim]

theorem ordinary_primary_group :
    resolveTarget ordinaryNss 1002 "root" (some ⟨"alice", some (.name "alice")⟩) none =
      ([.user (.name "alice"), .primaryGroup 1000], .ok (1000, 1000)) := by
  simp [resolveTarget, optionalLookup, observedLookup, observedBind, ordinaryNss,
    Except.mapError, targetFallback, finishTarget, selectTarget, Option.elim]

private def ordinaryFs : Filesystem where
  -- Both /a/p and /b/p are available. Canonicalizing /a/p resolves its parent to /c.
  executable := fun p => p == [47, 97, 47, 112] || p == [47, 98, 47, 112]
  canonical := fun p => if p == [47, 97, 47, 112] then some [47, 99, 47, 112] else none

/-- `p` with arguments `"a b"` and `""`, and PATH `.:/a:/b`: choose `/a/p` before `/b/p`,
canonicalize to `/c/p`, and leave both direct arguments intact. -/
theorem ordinary_direct_command :
    buildCommand ordinaryFs none [[112], [97, 32, 98], []] [46, 58, 47, 97, 58, 47, 98] =
      some ⟨[47, 99, 47, 112], [[97, 32, 98], []], true, some [112]⟩ := by decide

end SudoersSpec.Request
