import SudoersSpec.Syntax.Sudo
import SudoersSpec.Expansion
import SudoersSpec.Settings.Properties
import SudoersSpec.Analysis.AliasOrder

/-!
# From parsed local items to rules, alias definitions and Defaults

The lists in `Collected` are in **file order**, before alias sanitization and before any
request-specific Defaults are applied. This layer does not open files. Includes and a top-level
`Reject` are outside its domain, not comments or silently dropped records.
-/

namespace SudoersSpec.Analysis

open Syntax (Parsed Sudo)
open Settings (SettingsModifier)

/-- A scope that can occur in the first (non-command) Defaults pass. -/
inductive NonCommandScope where
  | generic
  | host (hosts : SpecList Hostname)
  | user (users : SpecList UserSpecifier)
  | runAs (users : SpecList UserSpecifier)
  deriving DecidableEq, Repr

structure Collected where
  rules : List PermissionSpec := []
  written : AliasTable := {}
  nonCommand : List (NonCommandScope × List SettingsModifier) := []
  command : List (SpecList Command × List SettingsModifier) := []
  /-- Reports for this source, before the sanitizer appends its file-independent reports. -/
  diagnostics : List (Span × String) := []
  deriving DecidableEq, Repr

/-- Rule diagnostics are emitted in host, command and modifier order. -/
def ignoredSpans (rule : PermissionSpec) : List Span :=
  rule.permissions.flatMap fun (_, entries) => entries.flatMap fun (_, entry) =>
    entry.mods.filterMap fun | .ignored span => some span | _ => none

/-- Command-scoped Defaults supply no argument restriction, retaining negations and aliases. -/
def commandScope (patterns : SpecList String) : SpecList Command :=
  patterns.map (mapSpec (fun pattern => ⟨pattern, .prefix []⟩))

/-- One iteration of `sudoers::process` with no file I/O. An accepted item preceding a fatal
record stays collected; the two records are processed separately. -/
def collectItem (acc : Collected) : Parsed Sudo → Option Collected
  | .error .reject | .ok (.include ..) | .ok (.includeDir ..) => none
  | .error (.fatal span kind) => some { acc with diagnostics := acc.diagnostics ++ [(span, kind.render)] }
  | .ok .lineComment => some acc
  | .ok (.spec rule) => some { acc with
        rules := acc.rules ++ [rule]
        diagnostics := acc.diagnostics ++ (ignoredSpans rule).map (·, "this tag is ignored by sudo-rs") }
  | .ok (.decl (.userAlias ds)) => some { acc with written.user := acc.written.user ++ ds }
  | .ok (.decl (.hostAlias ds)) => some { acc with written.host := acc.written.host ++ ds }
  | .ok (.decl (.cmndAlias ds)) => some { acc with written.cmnd := acc.written.cmnd ++ ds }
  | .ok (.decl (.runasAlias ds)) => some { acc with written.runas := acc.written.runas ++ ds }
  | .ok (.decl (.defaults mods (.command cmds))) => some { acc with command := acc.command ++ [(commandScope cmds, mods)] }
  | .ok (.decl (.defaults mods .generic)) => some { acc with nonCommand := acc.nonCommand ++ [(.generic, mods)] }
  | .ok (.decl (.defaults mods (.host xs))) => some { acc with nonCommand := acc.nonCommand ++ [(.host xs, mods)] }
  | .ok (.decl (.defaults mods (.user xs))) => some { acc with nonCommand := acc.nonCommand ++ [(.user xs, mods)] }
  | .ok (.decl (.defaults mods (.runAs xs))) => some { acc with nonCommand := acc.nonCommand ++ [(.runAs xs, mods)] }

/-- Accumulator-generalized for the refinement of the extracted item loop. -/
def collectFrom (acc : Collected) (items : List (Parsed Sudo)) : Option Collected :=
  items.foldlM collectItem acc

def collect (items : List (Parsed Sudo)) : Option Collected := collectFrom {} items

/-- This domain allows fatal parse diagnostics; it does not require a clean file. -/
def LocalItem : Parsed Sudo → Prop
  | .error .reject | .ok (.include ..) | .ok (.includeDir ..) => False
  | _ => True

private theorem collectItem_some_iff (acc : Collected) (item : Parsed Sudo) :
    (∃ out, collectItem acc item = some out) ↔ LocalItem item := by
  cases item with
  | error status => cases status <;> simp [LocalItem, collectItem]
  | ok line => cases line with
    | decl d => cases d with
      | defaults mods scope => cases scope <;> simp [LocalItem, collectItem]
      | _ => simp [LocalItem, collectItem]
    | _ => simp [LocalItem, collectItem]

/-- Exactly the local, non-`Reject` inputs can be collected, for **any** starting accumulator. -/
theorem collectFrom_some_iff (acc : Collected) (items : List (Parsed Sudo)) :
    (∃ out, collectFrom acc items = some out) ↔ ∀ item ∈ items, LocalItem item := by
  induction items generalizing acc with
  | nil => simp [collectFrom]
  | cons i is ih =>
    have first := collectItem_some_iff acc i
    cases h : collectItem acc i with
    | none => simp [h] at first; simp [collectFrom, List.foldlM_cons, h, first]
    | some next =>
      have hi : LocalItem i := first.mp ⟨next, h⟩
      simpa [collectFrom, List.foldlM_cons, h, hi] using ih next

/-- When the initial settings and every applied modifier came from the table, all effective
settings are still reachable; later filtering by scope may discard arbitrary modifiers. -/
def applyModifiers (mods : List SettingsModifier) (s : Settings.Settings) : Settings.Settings :=
  mods.foldl (fun current m => m.apply current) s

theorem reachable_applyModifiers {s : Settings.Settings} (hs : Settings.Reachable s)
    {mods : List SettingsModifier} (hm : ∀ m ∈ mods, Settings.Produced m) :
    Settings.Reachable (applyModifiers mods s) := by
  induction mods generalizing s with
  | nil => exact hs
  | cons m ms ih => exact ih (.apply hs (hm m (by simp))) (fun n hn => hm n (List.mem_cons_of_mem _ hn))

/-- The first Defaults pass. No command (and no target group) participates in these matches;
a `runAs` scope cannot match if no target was requested. -/
def nonCommandModifiers (O : Oracle U G) (aliases : AliasTable) (host : Hostname)
    (invoker : U) (target : Option U) (entries : List (NonCommandScope × List SettingsModifier)) : List SettingsModifier :=
  let hostAliases := getAliases aliases.host (matchHost O host)
  let userAliases := getAliases aliases.user (matchUser O invoker)
  let runasAliases := target.map fun u => getAliases aliases.runas (matchUser O u)
  entries.flatMap fun (scope, mods) =>
    let keep := match scope with
      | .generic => true
      | .host xs => (findItem (matchHost O host) hostAliases (withUnit xs)).isSome
      | .user xs => (findItem (matchUser O invoker) userAliases (withUnit xs)).isSome
      | .runAs xs => match target, runasAliases with
        | some u, some names => (findItem (matchUser O u) names (withUnit xs)).isSome
        | _, _ => false
    if keep then mods else []

/-- The second pass. Lookups use the command aliases in sanitizer order. -/
def commandModifiers (O : Oracle U G) (aliases : AliasTable) (path : String) (args : List String)
    (entries : List (SpecList Command × List SettingsModifier)) : List SettingsModifier :=
  let matcher := matchCommand O path args
  let names := getAliases aliases.cmnd matcher
  entries.flatMap fun (scope, mods) => if (findItem matcher names (withUnit scope)).isSome then mods else []

/-- Effective settings of a `check` on a freshly analyzed policy. Command-scoped Defaults
are applied last, even when they precede a generic Defaults line in the source file. -/
def settingsInForce (O : Oracle U G) (aliases : AliasTable) (c : Collected) (req : Request U G)
    (initial : Settings.Settings) : Settings.Settings :=
  let ms := nonCommandModifiers O aliases req.host req.invokingUser (some req.targetUser) c.nonCommand
  applyModifiers (commandModifiers O aliases req.command req.arguments c.command) (applyModifiers ms initial)

/-- The policy on which the reference decision operates, including the actual processing
order for every alias table. It is independent of the extracted analyzer's output. -/
def policyOf (c : Collected) : Policy :=
  { rules := c.rules, aliases := (orderAliases c.written).1 }

/-- Shape used to state include-free E2E: the text parser returns its items, collection
accepts their shape, and the decision and restrictions use those items, not a policy
supplied by the caller. `Option.none` is outside this model; denial is `.some .forbidden`. -/
def authorizationOfText (env : Syntax.Oracles) (O : Oracle U G) (src : List Char)
    (req : Request U G) : Option (Authorization Settings.StrSet) := do
  let items ← (Syntax.parseSudoers env src).toOption
  let c ← collect items
  let policy := policyOf c
  let settings := settingsInForce O policy.aliases c req Settings.Settings.default
  pure (authorization settings.toDefaults (authorize O policy req))

/-- Clean or not, every locally collectable parser result yields a decision. A missing
model result must not be confused with `authorization` returning `Forbidden`. -/
theorem authorizationOfText_defined {env : Syntax.Oracles} {O : Oracle U G} {src : List Char}
    {items : List (Parsed Sudo)} (parsed : Syntax.parseSudoers env src = .ok items)
    (req : Request U G) :
    (∃ a, authorizationOfText env O src req = some a) ↔ ∀ i ∈ items, LocalItem i := by
  have h := collectFrom_some_iff {} items
  change (∃ c, collect items = some c) ↔ _ at h
  rw [← h]
  cases hc : collect items <;> simp [authorizationOfText, parsed, Except.toOption, hc]

end SudoersSpec.Analysis
