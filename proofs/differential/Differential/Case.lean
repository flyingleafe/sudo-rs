import SudoersSpec.Authorize
import Differential.Db
import Differential.Print

/-!
# Test cases, their decision under the spec, and their text form

A case is a policy (spec AST), the user/group database, and the request as the sudo command
line expresses it (invoking user, host, `-u`/`-g`, command and arguments). The spec decision
is `SudoersSpec.authorize` under `oracleOf db` for the request that sudo-rs derives from the
command line (`Cli.resolve`).

The text form is line based, one record per case; the sudo-rs harness
(`src/sudoers/test/differential.rs`) and the C driver (`c-driver.sh`) read it:

```
case <index>
passwd <passwd(5) line>        (one per user)
group <group(5) line>          (one per group)
host <host name>
user <invoking user>
runas [-u <user>] [-g <group>]
command <path> [<arg> ...]
sudoers <sudoers line>         (one per line of the policy)
spec <verdict>
end
```
-/

namespace Differential

open SudoersSpec

instance : Inhabited Policy := ⟨{ rules := [] }⟩

structure Case where
  index : Nat
  db : Db
  policy : Policy
  /-- Alias names in the order their definitions are printed (a permutation of the
  dependency order the spec's alias table is given in). -/
  aliasOrder : List String
  host : String
  invoker : String
  cli : Cli
  command : String
  args : List String
  deriving Inhabited

namespace Case

/-- The request sudo-rs builds from the command line, if all names resolve. -/
def request (c : Case) : Option (Request UserEnt GroupEnt) := do
  let inv ← c.db.userNamed c.invoker
  let (tu, tg) ← c.cli.resolve c.db inv
  return { invokingUser := inv, host := c.host, targetUser := tu, targetGroup := tg,
           command := c.command, arguments := c.args }

/-- The spec's decision; `none` if the request does not resolve (never generated). -/
def decision (c : Case) : Option (Option Tag) :=
  c.request.map (authorize (oracleOf c.db) c.policy)

/-- The alias definitions in print order. -/
def aliasLines (c : Case) : List String :=
  let t := c.policy.aliases
  let named : List (String × String) :=
    t.user.map (fun d => (d.name, Print.def_ "User_Alias" Print.userSpecifier d)) ++
    t.runas.map (fun d => (d.name, Print.def_ "Runas_Alias" Print.userSpecifier d)) ++
    t.host.map (fun d => (d.name, Print.def_ "Host_Alias" Print.hostname d)) ++
    t.cmnd.map (fun d => (d.name, Print.def_ "Cmnd_Alias" Print.command d))
  let ordered := c.aliasOrder.filterMap fun n => (named.find? (·.1 == n)).map (·.2)
  let rest := (named.filter fun p => !c.aliasOrder.contains p.1).map (·.2)
  ordered ++ rest

/-- The policy as sudoers text, one string per line. -/
def sudoersLines (c : Case) : List String :=
  c.aliasLines ++ c.policy.rules.map Print.permissionSpec

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

namespace Case

/-- The case record (see the module documentation). -/
def record (c : Case) : String :=
  let lines :=
    [s!"case {c.index}"] ++
    c.db.users.map (fun u => "passwd " ++ Db.passwdLine u) ++
    c.db.groups.map (fun g => "group " ++ Db.groupLine g) ++
    [s!"host {c.host}", s!"user {c.invoker}", "runas " ++ " ".intercalate c.cli.flags,
     "command " ++ " ".intercalate (c.command :: c.args)] ++
    c.sudoersLines.map ("sudoers " ++ ·) ++
    [s!"spec {match c.decision with | some d => showVerdict d | none => "unresolved"}", "end"]
  "\n".intercalate lines ++ "\n"

end Case

end Differential
