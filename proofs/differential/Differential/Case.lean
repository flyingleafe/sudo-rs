import SudoersSpec.Authorize
import Differential.Db
import Differential.Print
import Differential.Sanitize

/-!
# Test cases, their decision under the spec, and their text form

A case is a policy (the spec AST of its lines and its alias definitions in file order), the
user/group database, and the request as the sudo command line expresses it (invoking user,
host, `-u`/`-g`, command and arguments). The spec decision is `SudoersSpec.authorize` under
`oracleOf db`, for the request that sudo-rs derives from the command line (`Cli.resolve`), on
the policy whose alias tables are in sudo-rs's processing order (`sanitize`).

The text form is line based, one record per probe; the sudo-rs harness
(`src/sudoers/test/differential.rs`) and `repro.sh` read it:

```
case <id>
passwd <passwd(5) line>        (one per user, in passwd order)
group <group(5) line>          (one per group)
host <host name>
user <invoking user>
runas [-u <user>] [-g <group>]
command <path> [<arg> ...]
mode list                      (optional: list the invoking user's entries instead)
sudoers <sudoers line>         (one per line of the policy)
spec <verdict>                 (optional)
end
```
-/

namespace Differential

open SudoersSpec

instance : Inhabited Policy := ⟨{ rules := [] }⟩

/-- What the sudo-rs harness runs: a policy text and a request, identified by `id`. -/
structure Probe where
  id : String
  db : Db
  host : String
  invoker : String
  /-- The `-u`/`-g` options, as words. -/
  flags : List String
  /-- The command path followed by its arguments. -/
  command : List String
  sudoers : List String
  /-- `check` (`Sudoers::check`) or `list` (the entries `sudo -l` prints). -/
  mode : String := "check"
  deriving Inhabited

/-- The record text of a probe, with an optional `spec` line. -/
def Probe.record (p : Probe) (spec : Option String := none) : String :=
  let lines :=
    [s!"case {p.id}"] ++
    p.db.users.map (fun u => "passwd " ++ Db.passwdLine u) ++
    p.db.groups.map (fun g => "group " ++ Db.groupLine g) ++
    [s!"host {p.host}", s!"user {p.invoker}", "runas " ++ " ".intercalate p.flags,
     "command " ++ " ".intercalate p.command] ++
    (if p.mode == "check" then [] else [s!"mode {p.mode}"]) ++
    p.sudoers.map ("sudoers " ++ ·) ++
    (match spec with | some s => [s!"spec {s}"] | none => []) ++ ["end"]
  "\n".intercalate lines ++ "\n"

structure Case where
  index : Nat
  db : Db
  /-- The user specification lines. -/
  rules : List PermissionSpec
  /-- The alias definitions, in the order they are printed (file order). -/
  defs : List AnyDef
  host : String
  invoker : String
  cli : Cli
  command : String
  args : List String
  deriving Inhabited

namespace Case

/-- The policy as the decision sees it: alias tables in sudo-rs's processing order. -/
def policy (c : Case) : Policy := { rules := c.rules, aliases := (sanitize c.defs).1 }

/-- The diagnostics sudo-rs reports for the alias tables (`sanitize`). -/
def diagnostics (c : Case) : List String := (sanitize c.defs).2

/-- The alias tables in file order (what C sudo looks names up in). -/
def written (c : Case) : AliasTable := writtenTables c.defs

/-- The request sudo-rs builds from the command line, if all names resolve. -/
def request (c : Case) : Option (Request UserEnt GroupEnt) := do
  let inv ← c.db.userNamed c.invoker
  let (tu, tg) ← c.cli.resolve c.db inv
  return { invokingUser := inv, host := c.host, targetUser := tu, targetGroup := tg,
           command := c.command, arguments := c.args }

/-- The spec's decision; `none` if the request does not resolve. -/
def decision (c : Case) : Option (Option Tag) :=
  c.request.map (authorize (oracleOf c.db) c.policy)

/-- The alias definitions in print order. -/
def aliasLines (c : Case) : List String := c.defs.map Print.anyDef

/-- The policy as sudoers text, one string per line. -/
def sudoersLines (c : Case) : List String :=
  c.aliasLines ++ c.rules.map Print.permissionSpec

/-- The probe that runs this case on sudo-rs. -/
def probe (c : Case) : Probe :=
  { id := toString c.index, db := c.db, host := c.host, invoker := c.invoker,
    flags := c.cli.flags, command := c.command :: c.args, sudoers := c.sudoersLines }

end Case

def showAuth : Authenticate → String
  | .none => "none" | .passwd => "passwd" | .nopasswd => "nopasswd"

def showEnv : EnvironmentControl → String
  | .implicit => "implicit" | .setenv => "setenv" | .nosetenv => "nosetenv"

def showExec : ExecControl → String
  | .implicit => "implicit" | .exec => "exec" | .noexec => "noexec"

/-- The verdict line shared by the spec and the sudo-rs harness. -/
def showVerdict : Option Tag → String
  | none => "deny"
  | some t =>
    s!"allow auth={showAuth t.authenticate} env={showEnv t.env} exec={showExec t.noexec} " ++
    s!"cwd={if t.cwd.isSome then "set" else "none"} " ++
    s!"apparmor={if t.apparmorProfile.isSome then "set" else "none"}"

/-- The full line the sudo-rs harness prints for a case: the verdict, then each diagnostic
after ` ;; `. -/
def resultLine (verdict : String) (diags : List String) : String :=
  " ;; ".intercalate (verdict :: diags)

namespace Case

/-- The spec's result line: verdict and the predicted diagnostics. -/
def specLine (c : Case) : String :=
  resultLine (match c.decision with | some d => showVerdict d | none => "unresolved")
    c.diagnostics

/-- The case record (see the module documentation). -/
def record (c : Case) : String := c.probe.record (some c.specLine)

end Case

end Differential
