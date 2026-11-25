import SudoRsProofs.Util
import SudoersSpec.Request

/-! These proofs connect three extracted decisions to the request reference. The NSS calls,
Rust `Path` operations, `resolve_path`'s standard-library iterator and filesystem calls,
conversion of direct argv, and the context wrapper are not extracted. The code reading that
identifies their pointwise contracts is given below and in `SudoersSpec.Request`. The
parameterized models are of the ordinary return paths, not of the operating system or of a
shipped executable. -/

open Aeneas Aeneas.Std Result
open SudoersSpec.Request

namespace SudoRsProofs.Request

open sudo_rs.common.resolve (TargetFallback TargetMissing target_fallback select_target)
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

private theorem encodeFallback_injective : Function.Injective encodeFallback := by
  intro x y h
  cases x <;> cases y <;> simp_all [encodeFallback]

private theorem encodeMissing_injective : Function.Injective encodeMissing := by
  intro x y h
  cases x <;> cases y <;> simp_all [encodeMissing]

private theorem encodeTarget_injective : Function.Injective (@encodeTarget U G) := by
  intro x y h
  cases x <;> cases y <;> simp_all [encodeTarget, encodeMissing_injective.eq_iff]

/-- The resolver model with decisions represented by the extracted helpers has the same
answer (including diagnostics) and lookup sequence as the reference. `hFallback` and `hSelect`
are the helper representation contracts, inhabited by `target_fallback_eq` and
`select_target_eq`. `nss` describes the answers of the ordinary name/ID/primary-group lookups;
it does not assert that a missing record or an I/O error is impossible. The caller supplies the
already-resolved invoker, parsed option keys, and the platform's root-group name. -/
theorem resolve_target_refines (nss : Nss U G E) (invoker : U) (rootGroupName : String)
    (userArg groupArg : Option TargetArg)
    (fallback : Bool → Bool → Fallback) (select : Option U → Option G → Except Missing (U × G))
    (hFallback : ∀ u g, target_fallback u g = ok (encodeFallback (fallback u g)))
    (hSelect : ∀ u g, select_target u g = ok (encodeTarget (select u g))) :
    resolveTargetBy fallback select nss invoker rootGroupName userArg groupArg =
      resolveTarget nss invoker rootGroupName userArg groupArg := by
  have hf : fallback = targetFallback := by
    funext u g
    apply encodeFallback_injective
    simpa only [ok.injEq] using (hFallback u g).symm.trans (target_fallback_eq u g)
  have hs : select = selectTarget := by
    funext u g
    apply encodeTarget_injective
    simpa only [ok.injEq] using (hSelect u g).symm.trans (select_target_eq u g)
  simp [resolveTarget, hf, hs]

theorem select_command_path_eq (input : P) (replacement : Option P) (resolved : Bool) :
    select_command_path input replacement resolved = ok (selectPath input replacement resolved) := by
  cases replacement <;> cases resolved <;> rfl

/-- Boundary contract for `resolve_path` when it is called: the ordered absolute entries
of `PATH` are joined with the command, and the first candidate whose observed executable test
succeeds is returned. This is the `split`/`filter`/`map`/`find` chain in `resolve.rs`. The
pointwise `Filesystem` contract assumes one consistent answer per pathname within the call;
no claim is made about concurrent changes or a later execution. -/
def PathSearchAnswer (fs : Filesystem) (search : Bool) (path input : Bytes)
    (answer : Option Bytes) : Prop :=
  search = true → answer = searchPath fs path input

/-- In `build_from_args`, the first (PATH) selection happens only in direct mode and only
for an unqualified name. The second selection always runs, using the result of canonically
resolving the candidate's directories and checking its existence. `fs.canonical` abstracts
that actual call; canonicalization is not retried on a different PATH entry. -/
def commandPathModel (fs : Filesystem) (search : Bool) (input : Bytes) (answer : Option Bytes) :
    Result (Bytes × Bool) :=
  Aeneas.Std.bind
    (if search then select_command_path input answer true else ok (input, true))
    (fun (candidate, found) => select_command_path candidate (fs.canonical candidate) found)

theorem command_path_refines (fs : Filesystem) (search : Bool) (path input : Bytes)
    (answer : Option Bytes) (hSearch : PathSearchAnswer fs search path input answer) :
    commandPathModel fs search input answer = ok (commandPath fs search path input) := by
  cases search with
  | false => simp [commandPathModel, commandPath, select_command_path_eq]
  | true =>
      have h : answer = searchPath fs path input := hSearch rfl
      simp [commandPathModel, commandPath, select_command_path_eq, selectPath, h]

/-- For nonempty direct argv, `build_from_args` converts the first word to a path (`first`)
and removes that word in place, leaving `tail`. The qualified-path test is
`Path::parent() != Some(Path::new(""))`; `hQualified` is its Unix byte-list contract. The model
records the original `arg0` and the unmodified tail, irrespective of either filesystem answer.
The direct callers have nonempty argv (run option parsing; explicit list guard). -/
theorem direct_command_refines (fs : Filesystem) (path first : Bytes) (tail : List Bytes)
    (qualified : Bool) (answer : Option Bytes) (hQualified : qualified = isQualified first)
    (hSearch : PathSearchAnswer fs (!qualified) path first answer) :
    Aeneas.Std.bind (commandPathModel fs (!qualified) first answer)
        (fun (command, resolved) => ok (some (Command.mk command tail resolved (some first)))) =
      ok (buildCommand fs none (first :: tail) path) := by
  subst qualified
  simp only [command_path_refines fs _ path first answer hSearch, bind_ok, buildCommand] <;>
    cases commandPath fs (!isQualified first) path first <;> rfl

end SudoRsProofs.Request
