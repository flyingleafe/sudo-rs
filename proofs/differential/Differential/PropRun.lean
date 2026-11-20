import Std.Data.HashMap
import Differential.Props

/-!
# The property search

`run P k n seed bin work outDir cap` draws `n` instances of property `P` (instance `i` from the
generator seeded with `(16 * seed + k, i)`), runs their probes on sudo-rs (`Engine.run`, in
batches), checks each instance, and prints how many met the precondition, held, or failed, by
class. The first `cap` failures of every class are shrunk (`Minimize.minimizeBatch`: one run
of the harness per shrinking step, on all candidates of the step), the shrunk instance is run
twice more to confirm it, and both instances are written to `outDir/NAME/CLASS/inst-I.txt`
with the probe records and the results.
-/

namespace Differential.PropRun

open Props

/-- Evaluate a batch of instances: the first-round probes, then the second-round probes (which
may depend on the first-round results), then the checks. -/
def evalAll (P : Prop' I) (bin work : String) (xs : Array I) :
    IO (Array (Outcome × List (Probe × String))) := do
  let s1 : Array (Array Probe) := xs.mapIdx fun i x =>
    (P.stage1 x).toArray.mapIdx fun j p => { p with id := s!"{i}.{j}" }
  let r1 ← Engine.run bin work s1.flatten
  let res1 : Array (List String) := s1.map fun ps => ps.toList.map fun p => r1.getD p.id "missing"
  let s2 : Array (Array Probe) := xs.mapIdx fun i x =>
    (P.stage2 x res1[i]!).toArray.mapIdx fun j p => { p with id := s!"{i}.s{j}" }
  let r2 ← Engine.run bin work s2.flatten
  let res2 : Array (List String) := s2.map fun ps => ps.toList.map fun p => r2.getD p.id "missing"
  return xs.mapIdx fun i x =>
    (P.check x res1[i]! res2[i]!,
     (s1[i]!.toList.zip res1[i]!) ++ (s2[i]!.toList.zip res2[i]!))

def classKey : Outcome → Option String
  | .violated cls => some cls
  | .outside cls true => some s!"outside-{cls}"
  | _ => none

def pathOf (cls : String) : String := (cls.splitOn "/").foldl (fun a b => if a.isEmpty then b else a ++ "__" ++ b) ""

def render (P : Prop' I) (x : I) (o : Outcome) (runs : List (Probe × String)) : String :=
  let o := match o with
    | .vacuous => "precondition false" | .holds => "holds"
    | .outside c f => s!"outside the precondition ({c}), conclusion {if f then "fails" else "holds"}"
    | .violated c => s!"VIOLATED ({c})"
  s!"# property {P.name}: {P.statement}\n# outcome: {o}\n{P.describe x}\n" ++
    "".intercalate (runs.map fun (p, r) => p.record ++ s!"result {r}\n")

def countBy (l : List String) : List (String × Nat) :=
  (l.foldl (fun (m : Std.HashMap String Nat) k => m.insert k (m.getD k 0 + 1)) {}).toList.mergeSort
    (fun a b => a.1 ≤ b.1)

def run (P : Prop' I) [Inhabited I] (k n seed : Nat) (bin work outDir : String) (cap : Nat) :
    IO Unit := do
  let gen (i : Nat) : I := (P.gen i).run' (Rng.forCase (16 * seed + k) i)
  let batch := 2000
  let mut vacuous := 0
  let mut holds := 0
  let mut outsideAll : Array String := #[]
  let mut failures : Array (Nat × String) := #[]
  let mut b := 0
  while b * batch < n do
    let idx := (List.range (min batch (n - b * batch))).map (b * batch + ·)
    let os ← evalAll P bin work (idx.map gen).toArray
    for (i, (o, _)) in idx.zip os.toList do
      match o with
      | .vacuous => vacuous := vacuous + 1
      | .holds => holds := holds + 1
      | .outside c f =>
        outsideAll := outsideAll.push s!"{c}: conclusion {if f then "fails" else "holds"}"
        if f then failures := failures.push (i, s!"outside-{c}")
      | .violated c => failures := failures.push (i, c)
    b := b + 1
  let violated := failures.filter (!·.2.startsWith "outside-")
  IO.println s!"== property {P.name}: {P.statement}"
  IO.println s!"instances: {n} (seed {seed}); precondition met: {n - vacuous - outsideAll.size}; holds: {holds}; violated: {violated.size}"
  for (cls, cnt) in countBy (violated.map (·.2)).toList do
    IO.println s!"  violated, {cls}: {cnt}"
  for (cls, cnt) in countBy outsideAll.toList do
    IO.println s!"  outside the precondition, {cls}: {cnt}"
  -- shrink and confirm the first `cap` failures of every class
  for (cls, _) in countBy (failures.map (·.2)).toList do
    for (i, _) in (failures.filter (·.2 == cls)).toList.take cap do
      let x := gen i
      let keepAll (cands : List I) : IO (Option Nat) := do
        let os ← evalAll P bin work cands.toArray
        return os.toList.findIdx? fun (o, _) => classKey o == some cls
      let m ← Minimize.minimizeBatch P.shrink keepAll x
      let a ← evalAll P bin work #[m]
      let a2 ← evalAll P bin work #[m]
      let confirmed := classKey a[0]!.1 == some cls && classKey a2[0]!.1 == some cls
      let orig ← evalAll P bin work #[x]
      let dir := s!"{outDir}/{P.name}/{pathOf cls}"
      IO.FS.createDirAll dir
      IO.FS.writeFile s!"{dir}/inst-{i}.txt"
        (s!"# seed {seed} instance {i}; shrunk; confirmed twice on sudo-rs: {confirmed}\n" ++
          render P m a[0]!.1 a[0]!.2 ++ "\n# --- original instance\n" ++
          render P x orig[0]!.1 orig[0]!.2)
      IO.println s!"  {cls}: instance {i} shrunk to {dir}/inst-{i}.txt (confirmed: {confirmed})"

end Differential.PropRun
