import Differential.Compare
import Differential.Coverage
import Differential.PropRun

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
oracle prop NAME N SEED BIN OUTDIR CAP  property search on sudo-rs (NAME: a b c d e f g),
                                        BIN: the sudo-rs unit-test binary, CAP: failures
                                        shrunk per class
```
-/

open Differential

def usage : IO UInt32 := do
  IO.eprintln "usage: oracle gen N SEED | show SEED I | paths | coverage N SEED | csudo N SEED TS WORK J | compare N SEED RUST C OUTDIR TS WORK J MINCAP | prop NAME N SEED BIN OUTDIR CAP"
  return 2

def runProp (name : String) (n seed : Nat) (bin outDir : String) (cap : Nat) : IO UInt32 := do
  let work := s!"{outDir}/work-{name}"
  match name with
  | "a" => PropRun.run Props.propA 0 n seed bin work outDir cap
  | "b" => PropRun.run Props.propB 1 n seed bin work outDir cap
  | "c" => PropRun.run Props.propC 2 n seed bin work outDir cap
  | "d" => PropRun.run Props.propD 3 n seed bin work outDir cap
  | "e" => PropRun.run Props.propE 4 n seed bin work outDir cap
  | "f" => PropRun.run Props.propF 5 n seed bin work outDir cap
  | "g" => PropRun.run Props.propG 6 n seed bin work outDir cap
  | _ => return ← usage
  return 0

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
    for p in Generate.paths ++ [Props.unmentionedPath] do IO.println p
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
