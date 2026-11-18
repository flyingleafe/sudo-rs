import Std.Data.HashMap
import Differential.Generate
import Differential.CSudo
import Differential.Minimize
import Differential.CModel

/-!
# Running the C engine, comparing the three engines, saving disagreements

Spec vs sudo-rs is compared on the full verdict line (`showVerdict`: allow/deny and every
tag field). Spec vs C sudo is compared on what both express: allow (`Command allowed`) vs
deny (`Command denied` / `Command unmatched`), and for allowed requests whether a password is
asked (`Tag.needsPasswd` vs `CSudo.effectivePasswd`), whether `SETENV` is in effect
(`env = setenv` vs `def_setenv`) and whether `NOEXEC` is in effect (`noexec = noexec` vs
`def_noexec`).
-/

namespace Differential.Compare

open SudoersSpec

/-- Run `act` on every index in `[0, n)` with `jobs` workers; worker `w` gets `w` as its
first argument (to pick a private scratch directory). Results in index order. -/
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

def workDir (work : String) (w : Nat) : IO String := do
  let d := s!"{work}/w{w}"
  IO.FS.createDirAll d
  return d

/-- The C engine over all cases: one line `index status authenticate=. setenv=. noexec=.`. -/
def runCSudo (n seed : Nat) (ts work : String) (jobs : Nat) : IO Unit := do
  let lines ← parallel n jobs fun w i => do
    let (_, r) ← CSudo.run ts (← workDir work w) (Generate.caseOf seed i)
    return s!"{i} {r.show}"
  let out ← IO.getStdout
  for l in lines do out.putStrLn l

/-- `index rest` lines into a map. -/
def readResults (path : String) : IO (Std.HashMap Nat String) := do
  let mut m := {}
  for l in (← IO.FS.readFile path).splitOn "\n" do
    match l.splitOn " " with
    | i :: rest => if let some i := i.toNat? then m := m.insert i (" ".intercalate rest)
    | [] => pure ()
  return m

/-- How spec and C sudo disagree, if they do. -/
def cKind (c : Case) (spec : Option Tag) (r : CSudo.Result) : Option String :=
  match spec, r.status with
  | none, "denied" | none, "unmatched" => none
  | some _, "denied" | some _, "unmatched" => some "spec-allow-c-deny"
  | none, "allowed" => some "spec-deny-c-allow"
  | some t, "allowed" =>
    let diffs :=
      (if t.needsPasswd != CSudo.effectivePasswd c r then ["passwd"] else []) ++
      (if (t.env == .setenv) != r.setenv then ["setenv"] else []) ++
      (if (t.noexec == .noexec) != r.noexec then ["noexec"] else [])
    if diffs.isEmpty then none else some ("tags-" ++ "-".intercalate diffs)
  | _, st => some ("c-" ++ st)

def comment (s : String) : String :=
  "".intercalate ((s.splitOn "\n").filter (!·.isEmpty) |>.map ("# " ++ · ++ "\n"))

def specLine (c : Case) : String :=
  match c.decision with | some d => showVerdict d | none => "unresolved"

/-- The text of one saved disagreement: a comment header with the three outputs and the raw
`testsudoers` output, followed by the case record (which `repro.sh` and the sudo-rs harness
read directly). -/
def report (title : String) (c : Case) (rust : String) (cRes : CSudo.Result) (raw : String) :
    String :=
  comment (title ++ "\n" ++
    s!"spec:        {specLine c}\n" ++
    s!"sudo-rs:     {rust}\n" ++
    s!"testsudoers: {cRes.show} (password asked: {CSudo.effectivePasswd c cRes})\n" ++
    "reproduce: ./repro.sh <this file>\n" ++
    "--- testsudoers output\n" ++ raw) ++ c.record

/-- Sub-causes of a runas disagreement: every candidate entry on which sudo-rs's runas test
(`runasCheck`) and C's (`CModel.runasMatches`) differ is labelled by the situation:

* `default-root`: the entry has no runas spec (sudo-rs: `is_root`, a uid test; C:
  `runas_default` = `root`, a name test);
* `self-own-group`: running as oneself with one's own group via `-g`; sudo-rs requires a
  non-empty user list to contain oneself, C does not;
* `own-group-list`: the target group is one of the target user's groups; sudo-rs ignores the
  group list, C evaluates it (so an explicit `!group` denies);
* `self-foreign-group`: running as oneself with a group one is not in; sudo-rs ignores the
  user list, C evaluates it (so an explicit `!user` denies);
* `other`: none of the above. -/
def runasLabels (c : Case) : List String := Id.run do
  let some rq := c.request | return ["other"]
  let O := oracleOf c.db
  let p := c.policy
  let ctx := CModel.ctxOf c rq
  let self := rq.targetUser == rq.invokingUser
  let own := inGroup O rq.targetUser rq.targetGroup
  let mut labels : List String := []
  for e in (matchingUserSpecs O p rq.invokingUser rq.host).flatten do
    let rs := (runasCheck O rq (runasUserAliases O p rq) (runasGroupAliases O p rq) e.1).isSome
    let cc := CModel.runasMatches ctx p.aliases.runas e.1 == some true
    if rs != cc then
      let l := match e.1, self, own, rs with
        | none, _, _, _ => "default-root"
        | some _, true, true, false => "self-own-group"
        | some _, _, true, true => "own-group-list"
        | some _, true, false, true => "self-foreign-group"
        | _, _, _, _ => "other"
      if !labels.contains l then labels := labels ++ [l]
  return labels.mergeSort (· ≤ ·)

/-- Which C components explain a spec-vs-C disagreement: the first switch set under which
`CModel.decide` agrees with `testsudoers` (`args`, then `runas`, then both), refined for
runas by `runasLabels`. -/
def cause (c : Case) (r : CSudo.Result) : String :=
  let agrees (tg : CModel.Toggles) := cKind c ((CModel.decide tg c).getD none) r == none
  let runas := "runas-" ++ "+".intercalate (runasLabels c)
  if agrees { cArgs := true } then "args-prefix"
  else if agrees { cRunas := true } then runas
  else if agrees { cRunas := true, cArgs := true } then "args-prefix+" ++ runas
  else "unexplained"

def bothC : CModel.Toggles := { cRunas := true, cArgs := true }

def countBy (l : Array String) : List (String × Nat) :=
  (l.foldl (fun (m : Std.HashMap String Nat) k => m.insert k (m.getD k 0 + 1)) {}).toList.mergeSort
    (fun a b => a.1 ≤ b.1)

/-- The comparison step: statistics on stdout, disagreements under `outDir`. The first
`minCap` C disagreements of every (cause, kind) are minimised, keeping kind and cause. -/
def compare (n seed : Nat) (rustOut cOut outDir ts work : String) (jobs minCap : Nat) :
    IO UInt32 := do
  let rust ← readResults rustOut
  let cres ← readResults cOut
  let mut allow := 0
  let mut rustAgree := 0
  let mut cAgree := 0
  let mut modelAgree := 0
  let mut rustBad := #[]
  let mut cBad : Array (Nat × String) := #[]
  let mut modelBad := #[]
  for i in [0:n] do
    let c := Generate.caseOf seed i
    let d := c.decision.getD none
    if d.isSome then allow := allow + 1
    if rust[i]? == some (specLine c) then rustAgree := rustAgree + 1 else rustBad := rustBad.push i
    match cres[i]? >>= CSudo.Result.parse? with
    | some r =>
      if cKind c ((CModel.decide bothC c).getD none) r == none then modelAgree := modelAgree + 1
      else modelBad := modelBad.push i
      match cKind c d r with
      | none => cAgree := cAgree + 1
      | some k => cBad := cBad.push (i, s!"{cause c r}/{k}")
    | none =>
      modelBad := modelBad.push i
      cBad := cBad.push (i, "unexplained/c-missing")
  IO.println s!"cases:                          {n} (seed {seed}; spec allows {allow}, denies {n - allow})"
  IO.println s!"spec vs sudo-rs agree:          {rustAgree} / {n}"
  IO.println s!"spec vs C sudo agree:           {cAgree} / {n}"
  IO.println s!"C model vs C sudo agree:        {modelAgree} / {n}   (spec with C runas and C args)"
  IO.println "spec vs C sudo disagreements by cause/kind:"
  for (k, cnt) in countBy (cBad.map (·.2)) do
    IO.println s!"  {k}: {cnt}"
  -- save every disagreement
  IO.FS.createDirAll outDir
  let save (sub title : String) (i w : Nat) : IO Unit := do
    let c := Generate.caseOf seed i
    let (raw, r) ← CSudo.run ts (← workDir work w) c
    IO.FS.createDirAll s!"{outDir}/{sub}"
    IO.FS.writeFile s!"{outDir}/{sub}/case-{i}.case"
      (report title c (rust[i]?.getD "missing") r raw)
  let _ ← parallel rustBad.size jobs fun w j =>
    save "sudo-rs" s!"spec vs sudo-rs disagreement, seed {seed} case {rustBad[j]!}" rustBad[j]! w
  let _ ← parallel modelBad.size jobs fun w j =>
    save "c-model" s!"C model vs C sudo disagreement, seed {seed} case {modelBad[j]!}" modelBad[j]! w
  let _ ← parallel cBad.size jobs fun w j =>
    let (i, k) := cBad[j]!
    save s!"c-sudo/{k}" s!"spec vs C sudo: {k}, seed {seed} case {i}" i w
  -- minimise the first `minCap` C disagreements of every cause/kind
  let groups := countBy (cBad.map (·.2))
  let mut picked : Array (Nat × String) := #[]
  for (k, _) in groups do
    picked := picked ++ ((cBad.filter (·.2 == k)).toList.take minCap).toArray
  let minimized ← parallel picked.size jobs fun w j => do
    let (i, k) := picked[j]!
    let dir ← workDir work w
    let keep (c : Case) : IO Bool := do
      let (_, r) ← CSudo.run ts dir c
      return match cKind c (c.decision.getD none) r with
        | some kind => s!"{cause c r}/{kind}" == k
        | none => false
    let m ← Minimize.minimize keep (Generate.caseOf seed i)
    let (raw, r) ← CSudo.run ts dir m
    IO.FS.createDirAll s!"{outDir}/c-sudo-minimized/{k}"
    IO.FS.writeFile s!"{outDir}/c-sudo-minimized/{k}/case-{i}.case"
      (report s!"spec vs C sudo: {k}, seed {seed} case {i}, minimised" m "(not run)" r raw)
    return (k, m)
  -- distinct minimised policies per cause/kind
  let mut summary := ""
  for (k, _) in groups do
    let ms := minimized.filter (·.1 == k)
    let mut seen : Std.HashMap String Nat := {}
    for (_, m) in ms do
      let key := "\n".intercalate (m.sudoersLines ++
        [s!"request: {m.invoker}@{m.host} {" ".intercalate m.cli.flags} {" ".intercalate (m.command :: m.args)}"])
      seen := seen.insert key (seen.getD key 0 + 1)
    summary := summary ++ s!"== {k}: {ms.size} minimised, {seen.size} distinct\n"
    for (key, cnt) in seen.toList.mergeSort (fun a b => a.2 ≥ b.2) do
      summary := summary ++ s!"-- x{cnt}\n{key}\n"
  IO.FS.writeFile s!"{outDir}/c-sudo-minimized/summary.txt" summary
  return if rustBad.isEmpty then 0 else 1

end Differential.Compare
