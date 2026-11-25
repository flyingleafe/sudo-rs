import SudoRsProofs.Util
import SudoRsProofs.Parser.Abs
import SudoersSpec.Request

/-! Request construction with the production lookup/selection cores. The native adapters are
left at individual operations: the NSS answer or ordinary miss, `Iterator::next`, path
classification and joining, the executable check, and canonicalization. The wrapper that
parses CLI arguments, converts argv and runs under target credentials is not extracted.
These are statements about the computation under the adapters' contracts, not traces of an
operating system or of a shipped binary. -/

open Aeneas Aeneas.Std Result
open SudoersSpec.Request

namespace SudoRsProofs.Request

open sudo_rs.common.resolve
open sudo_rs.common.command (select_command_path)

def encodeFallback : Fallback → TargetFallback
  | .keep => .Keep
  | .currentUser => .CurrentUser
  | .primaryGroupIfFound => .PrimaryGroupIfFound
  | .root => .Root

def encodeMissing : Missing → TargetMissing
  | .user => .User
  | .group => .Group

def encodeTarget : Except Missing (U × G) → core.result.Result (U × G) TargetMissing
  | .ok pair => .Ok pair
  | .error part => .Err (encodeMissing part)

theorem target_fallback_eq (userGiven groupGiven : Bool) :
    target_fallback userGiven groupGiven = ok (encodeFallback (targetFallback userGiven groupGiven)) := by
  cases userGiven <;> cases groupGiven <;> rfl

theorem select_target_eq (user : Option U) (group : Option G) :
    select_target user group = ok (encodeTarget (selectTarget user group)) := by
  cases user <;> cases group <;> rfl

/-- Read the result of an individual native Rust lookup in the specification's representation. -/
def rustAnswer : Except E A → core.result.Result A E
  | .ok value => .Ok value
  | .error error => .Err error

/-- Per-call obligations on `CurrentUser`'s `TargetLookup` adapter. An explicit call
dispatches to the name/ID NSS operation indicated by the input's parsed key, or returns
`Ok(None)` when the key failed to parse. `TargetArg.raw` is the original option text.
NSS errors have already been converted to the common error type. The invoking user,
if needed, is the already-resolved current user. -/
structure TargetPrimitives (lookup : TargetLookup L TargetArg U G (TargetError E))
    (context : L) (nss : Nss U G E) (invoker : U) (rootGroupName : String) : Prop where
  requestedUser : ∀ arg, lookup.requested_user context arg =
    ok (rustAnswer (lookupAnswer nss.user arg))
  requestedGroup : ∀ arg, lookup.requested_group context arg =
    ok (rustAnswer (lookupAnswer nss.group arg))
  invokingUser : lookup.invoking_user context = ok invoker
  primaryGroup : ∀ u, lookup.primary_group context u =
    ok (rustAnswer ((nss.primaryGroup u).mapError TargetError.lookup))
  rootUser : lookup.root_user context =
    ok (rustAnswer ((nss.user (.name "root")).mapError TargetError.lookup))
  rootGroup : lookup.root_group context =
    ok (rustAnswer ((nss.group (.name rootGroupName)).mapError TargetError.lookup))
  userNotFound : ∀ arg, lookup.user_not_found context arg =
    ok (.userNotFound ((arg.map TargetArg.raw).getD ""))
  groupNotFound : ∀ arg, lookup.group_not_found context arg =
    ok (.groupNotFound ((arg.map TargetArg.raw).getD ""))

local macro "finish_target_case " h:ident : tactic =>
  `(tactic| simp [resolve_target_core, resolveTarget, ($h).requestedUser, ($h).requestedGroup,
    ($h).invokingUser, ($h).primaryGroup, ($h).rootUser, ($h).rootGroup, ($h).userNotFound,
    ($h).groupNotFound, target_fallback, targetFallback, finish_target, select_target,
    selectTarget, finishTarget, Except.bind, Except.mapError, rustAnswer, *])

/-- The actual Rust lookup driver refines the reference's return value. The hypothesis
describes each primitive's result separately, not a completed resolver. The specification's
lookup log documents the call order; that log is not a Rust return value. -/
theorem resolve_target_refines (lookup : TargetLookup L TargetArg U G (TargetError E))
    (context : L) (nss : Nss U G E) (invoker : U) (rootGroupName : String)
    (userArg groupArg : Option TargetArg)
    (h : TargetPrimitives lookup context nss invoker rootGroupName) :
    resolve_target_core lookup context userArg groupArg =
      ok (rustAnswer (resolveTarget nss invoker rootGroupName userArg groupArg).2) := by
  cases userArg with
  | none =>
    cases groupArg with
    | none =>
      cases hu : nss.user (.name "root") with
      | error _ => finish_target_case h
      | ok u =>
        cases hg : nss.group (.name rootGroupName) with
        | error _ => finish_target_case h
        | ok g => cases u <;> cases g <;> finish_target_case h
    | some g =>
      cases hg : lookupAnswer nss.group g with
      | error _ => finish_target_case h
      | ok g' => cases g' <;> finish_target_case h
  | some u =>
    cases hu : lookupAnswer nss.user u with
    | error _ => cases groupArg <;> finish_target_case h
    | ok u' =>
      cases groupArg with
      | none =>
        cases u' with
        | none => finish_target_case h
        | some user => cases hp : nss.primaryGroup user <;> finish_target_case h
      | some g =>
        cases hg : lookupAnswer nss.group g with
        | error _ => finish_target_case h
        | ok g' => cases u' <;> cases g' <;> finish_target_case h

/-- A failed explicit user lookup short-circuits the production core. No contracts
are needed for the group lookup, any fallback, or the not-found diagnostic adapters. -/
theorem target_stops_at_user_error {L A U G E : Type}
    (lookup : TargetLookup L A U G E) (context : L)
    (user : A) (groupArg : Option A) (err : E)
    (hUser : lookup.requested_user context user = ok (.Err err)) :
    resolve_target_core lookup context (some user) groupArg = ok (.Err err) := by
  simp [resolve_target_core, hUser]

/-- A normal user miss, unlike a lookup error, proceeds to the explicit group lookup
and propagates a group lookup error before constructing a not-found diagnostic. -/
theorem target_group_error_after_user_miss {L A U G E : Type}
    (lookup : TargetLookup L A U G E) (context : L)
    (user group : A) (err : E)
    (hUser : lookup.requested_user context user = ok (.Ok none))
    (hGroup : lookup.requested_group context group = ok (.Err err)) :
    resolve_target_core lookup context (some user) (some group) = ok (.Err err) := by
  simp [resolve_target_core, hUser, hGroup]

theorem select_command_path_eq (input : P) (replacement : Option P) (resolved : Bool) :
    select_command_path input replacement resolved = ok (selectPath input replacement resolved) := by
  cases replacement <;> cases resolved <;> rfl

/-! ### Production PATH traversal -/

/-- Per-operation contracts for the native adapters in `resolve_path`. `remaining` describes
the residual `split(':').map(Path::new)` iterator. Each `next` either gives its head and
advances to its tail, or reports exhaustion; no hypothesis prescribes a search answer.
`dirBytes` and `pathBytes` read Unix path bytes; `command` represents the unqualified
spelling `input` when the search runs. Joining is constrained only for an absolute
directory. `fs.executable` is the pointwise answer of the combined `is_file`/`metadata`
test under the target credentials. -/
structure PathPrimitives (C D I P : Type) (fs : Filesystem) (input : Bytes) where
  entry : SearchEntry D C P
  iterator : core.iter.traits.iterator.Iterator I D
  command : C
  remaining : I → List D
  dirBytes : D → Bytes
  pathBytes : P → Bytes
  nextEmpty : ∀ i, remaining i = [] → ∃ i', iterator.next i = ok (none, i')
  nextEntry : ∀ i d ds, remaining i = d :: ds →
    ∃ i', iterator.next i = ok (some d, i') ∧ remaining i' = ds
  absolute : ∀ d, entry.is_absolute d = ok ((dirBytes d).head? == some 47)
  join : ∀ d, ((dirBytes d).head? == some 47) = true →
    ∃ p, entry.join d command = ok p ∧ pathBytes p = joinCandidate (dirBytes d) input
  executable : ∀ p, entry.is_executable p = ok (fs.executable (pathBytes p))

private theorem search_path_loop_refines (prim : PathPrimitives C D I P fs input) (i : I) :
    Aeneas.Std.bind (search_path_core_loop prim.entry prim.iterator i prim.command)
      (fun answer => ok (answer.map prim.pathBytes)) =
        ok ((pathCandidatesFrom ((prim.remaining i).map prim.dirBytes) input).find? fs.executable) := by
  rw [search_path_core_loop]
  cases hEntries : prim.remaining i with
  | nil =>
    obtain ⟨_, hNext⟩ := prim.nextEmpty i hEntries
    simp [hNext, uncurry, pathCandidatesFrom]
  | cons d ds =>
    obtain ⟨i', hNext, hTail⟩ := prim.nextEntry i d ds hEntries
    have hDecr : (prim.remaining i').length < (prim.remaining i).length := by
      simp [hEntries, hTail]
    by_cases hAbs : (prim.dirBytes d).head? = some 47
    · obtain ⟨p, hJoin, hBytes⟩ := prim.join d (by simp [hAbs])
      cases hExec : fs.executable (prim.pathBytes p) with
      | false =>
        have ih := search_path_loop_refines prim i'
        simpa [hNext, uncurry, prim.absolute, hAbs, hJoin, prim.executable, hExec,
          pathCandidatesFrom, ← hBytes, hTail] using ih
      | true =>
        simp [hNext, uncurry, prim.absolute, hAbs, hJoin, prim.executable, hExec,
          pathCandidatesFrom, ← hBytes]
    · have ih := search_path_loop_refines prim i'
      simpa [hNext, uncurry, prim.absolute, hAbs, pathCandidatesFrom, hTail] using ih
termination_by (prim.remaining i).length
decreasing_by all_goals exact hDecr

def runPathSearch (prim : PathPrimitives C D I P fs input) (initial : I) :
    Result (Option Bytes) :=
  Aeneas.Std.bind (search_path_core prim.entry prim.iterator initial prim.command)
    (fun answer => ok (answer.map prim.pathBytes))

/-- The extracted loop implements the ordered first-match search. The split is a single
input-representation contract; all subsequent conditions are local to an iterator step.
The proof follows the next iterator state only when the current entry has not won. -/
theorem search_path_refines (prim : PathPrimitives C D I P fs input) (initial : I) (path : Bytes)
    (hSplit : (prim.remaining initial).map prim.dirBytes = path.splitOn 58) :
    runPathSearch prim initial = ok (searchPath fs path input) := by
  simpa [runPathSearch, search_path_core, searchPath, pathCandidates, hSplit] using
    search_path_loop_refines prim initial

/-- The first-hit branch does not even require an answer from `next` in the successor
state, nor any facts about subsequent entries or filesystem results. -/
theorem search_path_stops_at_hit (entry : SearchEntry D C P)
    (iter : core.iter.traits.iterator.Iterator I D) (command : C) (i i' : I) (d : D) (p : P)
    (hNext : iter.next i = ok (some d, i')) (hAbs : entry.is_absolute d = ok true)
    (hJoin : entry.join d command = ok p) (hExec : entry.is_executable p = ok true) :
    search_path_core entry iter i command = ok (some p) := by
  unfold search_path_core
  rw [search_path_core_loop]
  simp [hNext, uncurry, hAbs, hJoin, hExec]

/-- A relative entry advances directly to its successor: neither path joining nor the
filesystem needs to have a result for it. -/
theorem search_path_skips_relative (entry : SearchEntry D C P)
    (iter : core.iter.traits.iterator.Iterator I D) (command : C) (i i' : I) (d : D)
    (hNext : iter.next i = ok (some d, i')) (hAbs : entry.is_absolute d = ok false) :
    search_path_core entry iter i command = search_path_core entry iter i' command := by
  unfold search_path_core
  rw [search_path_core_loop]
  simp [hNext, uncurry, hAbs]

/-- In `build_from_args`, the first (PATH) selection happens only in direct mode and only
for an unqualified name. The second selection always runs, using the result of canonically
resolving the candidate's directories and checking its existence. `fs.canonical` abstracts
that actual call; canonicalization is not retried on a different PATH entry. -/
def commandPathModel (fs : Filesystem) (search : Bool) (input : Bytes)
    (searched : Result (Option Bytes)) : Result (Bytes × Bool) :=
  Aeneas.Std.bind
    (if search then
      Aeneas.Std.bind searched (fun answer => select_command_path input answer true)
    else ok (input, true))
    (fun (candidate, found) => select_command_path candidate (fs.canonical candidate) found)

theorem command_path_refines (search : Bool) (path : Bytes)
    (prim : PathPrimitives C D I P fs input) (initial : I)
    (hSplit : search = true → (prim.remaining initial).map prim.dirBytes = path.splitOn 58) :
    commandPathModel fs search input (runPathSearch prim initial) =
      ok (commandPath fs search path input) := by
  cases search with
  | false => simp [commandPathModel, commandPath, select_command_path_eq]
  | true =>
      simp [commandPathModel, commandPath, select_command_path_eq, selectPath,
        search_path_refines prim initial path (hSplit rfl)]

/-- For nonempty direct argv, `build_from_args` converts the first word to a path (`first`)
and removes that word in place, leaving `tail`. The qualified-path test is
`Path::parent() != Some(Path::new(""))`; `hQualified` is its Unix byte-list contract. The model
records the original `arg0` and the unmodified tail, irrespective of either filesystem answer.
The direct callers have nonempty argv (run option parsing; explicit list guard). -/
theorem direct_command_refines (path first : Bytes) (tail : List Bytes)
    (prim : PathPrimitives C D I P fs first) (initial : I) (qualified : Bool)
    (hQualified : qualified = isQualified first)
    (hSplit : !qualified = true → (prim.remaining initial).map prim.dirBytes = path.splitOn 58) :
    Aeneas.Std.bind (commandPathModel fs (!qualified) first (runPathSearch prim initial))
        (fun (command, resolved) => ok (some (Command.mk command tail resolved (some first)))) =
      ok (buildCommand fs none (first :: tail) path) := by
  rw [command_path_refines (!qualified) path prim initial hSplit, bind_ok, hQualified]
  cases h : commandPath fs (!isQualified first) path first <;> simp [buildCommand, h]

end SudoRsProofs.Request
