import Std.Data.HashMap
import Differential.Case

/-!
# Running probes on sudo-rs

`run bin work probes` writes the records of `probes` to a file under `work`, runs the sudo-rs
unit-test binary `bin` on them (the test `sudoers::test::differential::differential_cases`
with `SUDO_DIFF_CASES` / `SUDO_DIFF_OUT`, see `src/sudoers/test/differential.rs`) and returns
the result line of every probe, by probe id.

A result line is `VERDICT` (`allow auth=… env=… exec=… cwd=… apparmor=…`, `deny`,
`error …`, or `list ENTRY<TAB>ENTRY…`) followed by ` ;; MESSAGE` for every diagnostic of
`Sudoers::read`.
-/

namespace Differential.Engine

/-- The verdict part of a result line (before the first ` ;; `). -/
def verdictOf (line : String) : String := (line.splitOn " ;; ").headD ""

/-- The diagnostics of a result line. -/
def diagnosticsOf (line : String) : List String := (line.splitOn " ;; ").drop 1

def allows (verdict : String) : Bool := verdict.startsWith "allow "

/-- Allowed without a password. -/
def nopasswd (verdict : String) : Bool := verdict.startsWith "allow auth=nopasswd "

/-- What `sudo` does with a request: refuse, ask for a password, or run without one. -/
def authOutcome (verdict : String) : String :=
  if !allows verdict then "deny" else if nopasswd verdict then "nopasswd" else "passwd"

/-- `id rest` lines into a map. -/
def parseResults (text : String) : Std.HashMap String String := Id.run do
  let mut m := {}
  for l in text.splitOn "\n" do
    match l.splitOn " " with
    | i :: rest => if !i.isEmpty then m := m.insert i (" ".intercalate rest)
    | [] => pure ()
  return m

/-- Run the harness on a batch of probes (ids must be distinct). -/
def run (bin work : String) (probes : Array Probe) : IO (Std.HashMap String String) := do
  if probes.isEmpty then return {}
  IO.FS.createDirAll work
  let cases := s!"{work}/probes.txt"
  let out := s!"{work}/results.txt"
  let h ← IO.FS.Handle.mk cases .write
  for p in probes do h.putStr p.record
  h.flush
  let r ← IO.Process.output
    { cmd := bin, args := #["sudoers::test::differential::differential_cases", "--exact", "-q"],
      env := #[("SUDO_DIFF_CASES", some cases), ("SUDO_DIFF_OUT", some out)] }
  if r.exitCode != 0 then
    throw <| IO.userError s!"sudo-rs harness failed ({r.exitCode}):\n{r.stdout}\n{r.stderr}"
  return parseResults (← IO.FS.readFile out)

end Differential.Engine
