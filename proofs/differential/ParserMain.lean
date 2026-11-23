import Differential.ParserCSudo
import Differential.ParserDump

/-!
`parser`: corpus generation and C sudo comparison for the sudoers parser (stage P0,
`proofs/parser/DUMP.md`, `proofs/parser/C-SUDO.md`).

```
parser corpus SEED N                  the corpus (N cases per category and mutation operator) on
                                      stdout, one `<label> <quoted text>` per line
parser categories SEED N              the number of cases per category
parser csudo CORPUS BUILD WORK JOBS   C sudo's visudo, testsudoers, cvtsudoers on every case (stdout)
parser lean-dump CORPUS CHARTABLE     the dump of the Lean reference parser (`SudoersSpec.Syntax`)
                                      in the format of the Rust dump, with the test oracles of
                                      `Differential.ParserOracles` (stdout)
```
-/

open Differential

def usage : IO UInt32 := do
  IO.eprintln ("usage: parser corpus SEED N | categories SEED N | csudo CORPUS BUILD WORK JOBS" ++
    " | lean-dump CORPUS CHARTABLE")
  return 2

def categoryOf (label : String) : String :=
  (label.splitOn ":").headD label

def main (args : List String) : IO UInt32 := do
  match args with
  | ["corpus", seed, n] =>
    let some seed := seed.toNat? | usage
    let some n := n.toNat? | usage
    let out ← IO.getStdout
    for c in ParserCorpus.corpus seed n do out.putStrLn c.line
    return 0
  | ["categories", seed, n] =>
    let some seed := seed.toNat? | usage
    let some n := n.toNat? | usage
    let mut counts : Array (String × Nat) := #[]
    for c in ParserCorpus.corpus seed n do
      let cat := categoryOf c.label
      match counts.findIdx? (·.1 == cat) with
      | some i => counts := counts.modify i fun (k, v) => (k, v + 1)
      | none => counts := counts.push (cat, 1)
    for (k, v) in counts do IO.println s!"{k} {v}"
    return 0
  | ["csudo", corpus, build, work, jobs] =>
    let some jobs := jobs.toNat? | usage
    ParserCSudo.run (← ParserCSudo.readCorpus corpus) build work jobs
    return 0
  | ["lean-dump", corpus, chartable] =>
    let char ← match ParserOracles.charOracleOfTable (← IO.FS.readFile chartable) with
      | .ok c => pure c
      | .error e => throw (IO.userError s!"chartable: {e}")
    let O := ParserOracles.oracles char Quote.quote
    let out ← IO.getStdout
    for c in ← ParserCSudo.readCorpus corpus do
      out.putStr s!"case {c.label}\n{ParserDump.dump O c.text}"
    return 0
  | _ => usage
