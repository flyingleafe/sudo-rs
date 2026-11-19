import Differential.Compare
import Differential.Coverage

/-!
`oracle`: the executable side of the differential test.

```
oracle gen N SEED                       case records 0..N-1 (with the spec verdict) on stdout
oracle show SEED I                      the record of case I
oracle paths                            the command paths the generator uses
oracle coverage N SEED                  how many cases exercise each feature
oracle csudo N SEED TESTSUDOERS WORK J  run testsudoers on every case (J workers)
oracle compare N SEED SUDO_RS_OUT C_OUT OUTDIR TESTSUDOERS WORK J MINCAP
                                        compare, save disagreements, minimise
```
-/

open Differential

def usage : IO UInt32 := do
  IO.eprintln "usage: oracle gen N SEED | show SEED I | paths | coverage N SEED | csudo N SEED TS WORK J | compare N SEED RUST C OUTDIR TS WORK J MINCAP"
  return 2

def main (args : List String) : IO UInt32 := do
  match args with
  | ["gen", n, seed] =>
    let some n := n.toNat? | usage
    let some seed := seed.toNat? | usage
    let out ← IO.getStdout
    for i in [0:n] do
      out.putStr (Generate.caseOf seed i).record
    return 0
  | ["show", seed, i] =>
    let some seed := seed.toNat? | usage
    let some i := i.toNat? | usage
    IO.print (Generate.caseOf seed i).record
    return 0
  | ["paths"] =>
    for p in Generate.paths do IO.println p
    return 0
  | ["coverage", n, seed] =>
    let some n := n.toNat? | usage
    let some seed := seed.toNat? | usage
    Coverage.report n seed
    return 0
  | ["csudo", n, seed, ts, work, jobs] =>
    let some n := n.toNat? | usage
    let some seed := seed.toNat? | usage
    let some jobs := jobs.toNat? | usage
    Compare.runCSudo n seed ts work jobs
    return 0
  | ["compare", n, seed, rust, c, outDir, ts, work, jobs, minCap] =>
    let some n := n.toNat? | usage
    let some seed := seed.toNat? | usage
    let some jobs := jobs.toNat? | usage
    let some minCap := minCap.toNat? | usage
    Compare.compare n seed rust c outDir ts work jobs minCap
  | _ => usage
