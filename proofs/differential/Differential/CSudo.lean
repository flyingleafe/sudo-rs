import Differential.Case

/-!
# Driver for C sudo's `testsudoers`

`testsudoers` (`plugins/sudoers/testsudoers.c` of the sudo 1.9.18 sources) reads a sudoers
policy on stdin, takes the passwd and group databases from files (`-p`, `-P`), the host from
`-h`, the runas user/group from `-u`/`-g`, then the invoking user, the command and its
arguments, and runs the real `sudoers_lookup`. It prints `Command allowed`, `Command denied`,
`Command unmatched` or `Parse error`, and `Password required` when `def_authenticate` is set.
`build-testsudoers.sh` applies `testsudoers-flags.patch`, which adds one line
`Flags: authenticate=A setenv=S noexec=N` with the values of `def_authenticate`, `def_setenv`
and `def_noexec` after the lookup (`apply_cmndspec`, `lookup.c`); nothing else is changed.

`testsudoers` stops after the lookup. The password exemptions that sudo applies later
(`check_user`, `plugins/sudoers/check.c` lines 166-182) are applied here by
`effectivePasswd`, so that the comparison is with what sudo would actually do.
-/

namespace Differential.CSudo

/-- The parsed outcome of one `testsudoers` run. -/
structure Result where
  /-- `allowed`, `denied`, `unmatched`, `parse-error` or `no-verdict`. -/
  status : String
  authenticate : Bool
  setenv : Bool
  noexec : Bool
  deriving Inhabited, BEq

def Result.show (r : Result) : String :=
  let b (x : Bool) := if x then "1" else "0"
  s!"{r.status} authenticate={b r.authenticate} setenv={b r.setenv} noexec={b r.noexec}"

def Result.parse? (s : String) : Option Result := do
  match s.splitOn " " with
  | [st, a, e, n] =>
    let flag (k v : String) : Option Bool :=
      if v == k ++ "=1" then some true else if v == k ++ "=0" then some false else none
    return ⟨st, ← flag "authenticate" a, ← flag "setenv" e, ← flag "noexec" n⟩
  | _ => none

/-- Parse the output of `testsudoers`. -/
def parseOutput (out : String) : Result := Id.run do
  let lines := out.splitOn "\n" |>.map (·.trimAscii.toString)
  let parsesOk := lines.contains "Parses OK"
  let status :=
    if !parsesOk || lines.contains "Parse error" then "parse-error"
    else if lines.contains "Command allowed" then "allowed"
    else if lines.contains "Command denied" then "denied"
    else if lines.contains "Command unmatched" then "unmatched"
    else "no-verdict"
  let mut r : Result := ⟨status, true, false, false⟩
  for l in lines do
    if l.startsWith "Flags: " then
      for w in (l.drop 7).toString.splitOn " " do
        match w.splitOn "=" with
        | [k, v] =>
          let b := v == "1"
          if k == "authenticate" then r := { r with authenticate := b }
          else if k == "setenv" then r := { r with setenv := b }
          else if k == "noexec" then r := { r with noexec := b }
        | _ => pure ()
  return r

/-- The command line for a case; `dir` holds the case's `passwd` and `group` files. -/
def argv (dir : String) (c : Case) : List String :=
  ["-p", dir ++ "/passwd", "-P", dir ++ "/group", "-h", c.host] ++ c.cli.flags ++
    [c.invoker, c.command] ++ c.args

def sudoersText (c : Case) : String := "".intercalate (c.sudoersLines.map (· ++ "\n"))

def writeDb (dir : String) (c : Case) : IO Unit := do
  IO.FS.writeFile (dir ++ "/passwd") ("".intercalate (c.db.users.map (Db.passwdLine · ++ "\n")))
  IO.FS.writeFile (dir ++ "/group") ("".intercalate (c.db.groups.map (Db.groupLine · ++ "\n")))

/-- Run `testsudoers` on a case; returns the raw output (stdout then stderr) and its parse. -/
def run (ts dir : String) (c : Case) : IO (String × Result) := do
  writeDb dir c
  let child ← IO.Process.spawn
    { cmd := ts, args := (argv dir c).toArray, stdin := .piped, stdout := .piped,
      stderr := .piped }
  let (stdin, child) ← child.takeStdin
  stdin.putStr (sudoersText c)
  stdin.flush
  let errTask ← IO.asTask child.stderr.readToEnd .dedicated
  let out ← child.stdout.readToEnd
  let err ← IO.ofExcept errTask.get
  let _ ← child.wait
  return (out ++ (if err.isEmpty then "" else "--- stderr\n" ++ err), parseOutput out)

/-- The shell command that reproduces a run (with the files written by `writeDb`). -/
def shellCommand (ts dir : String) (c : Case) : String :=
  " ".intercalate (ts :: argv dir c) ++ " <<'EOF'\n" ++ sudoersText c ++ "EOF"

/-- Does sudo ask for a password? `check_user` (`check.c` 166-182) skips authentication if
`def_authenticate` is off, if the invoking user has uid 0, or if `running_as_user` holds
(`check.c` 116-125: same uid as the runas user and, if `-g` was given, the runas group is the
invoking user's primary or a supplementary group, `user_has_gid`, 88-107). The runas user is
`-u`, else the invoking user if only `-g` was given, else `runas_default` = `root`
(`testsudoers.c` 337-342). -/
def effectivePasswd (c : Case) (r : Result) : Bool := Id.run do
  let some inv := c.db.userNamed c.invoker | return r.authenticate
  let runasName := match c.cli.runasUser, c.cli.runasGroup with
    | some u, _ => u
    | none, some _ => c.invoker
    | none, none => "root"
  let some runasPw := c.db.userNamed runasName | return r.authenticate
  let gidOk := match c.cli.runasGroup with
    | none => true
    | some g => match c.db.groupNamed g with
      | some gr => gr.gid == inv.gid || (c.db.gidsOf inv).contains gr.gid
      | none => false
  let runningAsUser := inv.uid == runasPw.uid && gidOk
  return r.authenticate && inv.uid != 0 && !runningAsUser

end Differential.CSudo
