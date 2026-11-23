import Differential.ParserCorpus

/-!
# C sudo 1.9.18 on the parser corpus

For every case the text is written to `sudoers` in a private work directory and three tools
built by `build-csudo-tools.sh` run on it, with `LC_ALL=C`:

* `visudo -c -f sudoers`: does C sudo accept the file (exit status 0)?
* `testsudoers -p passwd -P group -d < sudoers`: the parse errors (`sudoers:L:C: ...` on
  standard error) and the entries the parser kept, printed back in sudoers syntax (`-d`);
* `cvtsudoers -f json sudoers` when `visudo` accepted the file: the kept entries as JSON.

Output, per case: `case <label>`, then
`visudo <status> <quoted output>`, `testsudoers <status> <quoted stdout> <quoted stderr>` and
`cvtsudoers <status> <quoted stdout>` (or `cvtsudoers skipped`).
-/

namespace Differential.ParserCSudo

open ParserCorpus Quote

/-- Run `act` on every index in `[0, n)` with `jobs` workers; results in index order. -/
def parallel (n jobs : Nat) (act : Nat → Nat → IO α) [Inhabited α] : IO (Array α) := do
  let jobs := max jobs 1
  let mut tasks := #[]
  for w in [0:jobs] do
    tasks := tasks.push (← IO.asTask (prio := .dedicated) do
      let mut out := #[]
      let mut i := w
      while i < n do
        out := out.push (i, ← act w i)
        i := i + jobs
      return out)
  let mut res : Array α := Array.replicate n default
  for t in tasks do
    for (i, x) in ← IO.ofExcept (← IO.wait t) do
      res := res.set! i x
  return res

structure Run where
  status : UInt32
  out : String
  err : String
  deriving Inhabited

/-- Bytes as text: UTF-8 if valid, else every byte as the code point of the same value
(marked by a leading U+FFFD). -/
def lossy (b : ByteArray) : String :=
  match String.fromUTF8? b with
  | some s => s
  | none => b.toList.foldl (fun s x => s.push (Char.ofNat x.toNat)) "\ufffd"

/-- Run a tool in `dir`, feeding `input` on standard input (closed after it). -/
def runTool (cmd : String) (args : Array String) (dir : String) (input : String := "") :
    IO Run := do
  let child ← IO.Process.spawn
    { cmd, args, cwd := dir, env := #[("LC_ALL", some "C")],
      stdin := .piped, stdout := .piped, stderr := .piped }
  let (stdin, child) ← child.takeStdin
  stdin.putStr input
  stdin.flush
  let errTask ← IO.asTask child.stderr.readBinToEnd .dedicated
  let out ← child.stdout.readBinToEnd
  let err ← IO.ofExcept errTask.get
  let status ← child.wait
  return ⟨status, lossy out, lossy err⟩

def passwd : String :=
  "root:x:0:0::/root:/bin/sh\nalice:x:1000:1000::/home/alice:/bin/sh\nbob:x:1001:1001::/home/bob:/bin/sh\n"
def group : String := "root:x:0:\nwheel:x:10:alice\nalice:x:1000:\nbob:x:1001:\n"

def caseRecord (build dir : String) (c : PCase) : IO String := do
  let bin := build ++ "/plugins/sudoers/"
  IO.FS.writeFile (dir ++ "/sudoers") c.text
  let v ← runTool (bin ++ "visudo") #["-c", "-f", "sudoers"] dir
  let t ← runTool (bin ++ "testsudoers") #["-p", "passwd", "-P", "group", "-d"] dir c.text
  let cv ← if v.status == 0 then
      some <$> runTool (bin ++ "cvtsudoers") #["-f", "json", "sudoers"] dir
    else pure none
  let cvLine := match cv with
    | some r => s!"cvtsudoers {r.status} {quote r.out}"
    | none => "cvtsudoers skipped"
  return s!"case {c.label}\nvisudo {v.status} {quote (v.out ++ v.err)}\n" ++
    s!"testsudoers {t.status} {quote t.out} {quote t.err}\n{cvLine}\n"

/-- Run the three tools on every case of `cases` with `jobs` workers under `work`. -/
def run (cases : Array PCase) (build work : String) (jobs : Nat) : IO Unit := do
  let recs ← parallel cases.size jobs fun w i => do
    let dir := s!"{work}/w{w}"
    IO.FS.createDirAll dir
    IO.FS.writeFile (dir ++ "/passwd") passwd
    IO.FS.writeFile (dir ++ "/group") group
    caseRecord build dir cases[i]!
  let out ← IO.getStdout
  for r in recs do out.putStr r

/-- Read a corpus file (`<label> <quoted text>` per line). -/
def readCorpus (path : String) : IO (Array PCase) := do
  let mut out := #[]
  for l in (← IO.FS.readFile path).splitOn "\n" do
    if l.isEmpty then continue
    match l.splitOn " " with
    | label :: _ =>
      let rest := String.ofList (l.toList.drop (label.length + 1))
      match unquote? rest with
      | some text => out := out.push { label, text }
      | none => throw (IO.userError s!"corpus: malformed line for {label}")
    | [] => pure ()
  return out

end Differential.ParserCSudo
