import Differential.Rng
import Differential.Case

/-!
# Random test cases

The generator covers the fragment of sudoers that the spec models and that both sudo-rs and
C sudo accept:

* user lists with `user`, `#uid`, `%group`, `%#gid`, `ALL`, `User_Alias` references, `!`;
* `User_Alias`, `Runas_Alias`, `Host_Alias`, `Cmnd_Alias`, with nested references (to aliases
  defined earlier in dependency order, printed in a random order) and negated members;
* one to four lines, each with one or two `Host_List = Cmnd_Spec_List` groups;
* runas `(users)`, `(users : groups)`, `(: groups)`, `()` or none;
* tags `NOPASSWD`, `PASSWD`, `SETENV`, `NOSETENV`, `NOEXEC`, `EXEC`;
* commands as exact paths with no argument list, with `""`, with an exact argument list, or
  with a leading argument list followed by `*`; `ALL`; `Cmnd_Alias` references; `!`.

No path contains a glob metacharacter. Paths are chosen not to exist on the test machine
(`run.sh` checks this), so neither sudo-rs (which canonicalises existing paths) nor C sudo
(which compares inodes of existing paths) looks at the file system.

Requests are biased towards the names, hosts and commands that occur in the policy, so that
both allow and deny decisions are frequent.
-/

namespace Differential.Generate

open SudoersSpec Gen

instance : Inhabited Modifier := ⟨.noop⟩
instance : Inhabited Command := ⟨⟨"/", .prefix []⟩⟩

def userNames : List String := ["root", "toor", "alice", "bob", "carol", "dave"]
/-- Names that may occur in a policy; `eve` is not in the database. -/
def policyUserNames : List String := userNames ++ ["eve"]
def groupNames : List String := ["root", "wheel", "staff", "users", "alice", "bob", "carol", "dave"]
def uids : List Nat := [0, 1001, 1002, 1003, 1004, 1005]
def gids : List Nat := [0, 10, 20, 100, 1001, 1002]
def hosts : List String := ["h1", "h2", "h3"]
def paths : List String := ["/bin/ls", "/bin/cat", "/usr/bin/id", "/usr/local/bin/ls"]
def argPool : List String := ["-a", "-l", "x"]

/-- A fresh database: fixed names and ids, random primary groups and memberships. `toor` is
a second account with uid 0. -/
def db : Gen Db := do
  let alice ← pick [1001, 100]
  let bob ← pick [1002, 100]
  let carol ← pick [1003, 20]
  let dave ← pick [1004, 100]
  let users : List UserEnt :=
    [⟨"root", 0, 0⟩, ⟨"toor", 0, 0⟩, ⟨"alice", 1001, alice⟩, ⟨"bob", 1002, bob⟩,
     ⟨"carol", 1003, carol⟩, ⟨"dave", 1004, dave⟩]
  let groupIds : List (String × Nat) :=
    [("root", 0), ("wheel", 10), ("staff", 20), ("users", 100),
     ("alice", 1001), ("bob", 1002), ("carol", 1003), ("dave", 1004)]
  let mut groups := #[]
  for (n, gid) in groupIds do
    let mut members := #[]
    for u in ["root", "alice", "bob", "carol", "dave"] do
      if ← chance 1 4 then members := members.push u
    groups := groups.push { name := n, gid, members := members.toList }
  return { users, groups := groups.toList }

def negate (s : Spec α) : Gen (Spec α) := do
  if ← chance 1 6 then return s.negate else return s

/-- An item of a list: `ALL` (rarely), a reference to an available alias, or a plain item. -/
def item (plain : Gen α) (aliases : List String) : Gen (Spec α) := do
  let m ← weighted [(1, 0), (if aliases.isEmpty then 0 else 3, 1), (8, 2)]
  match m with
  | 0 => negate (.allow .all)
  | 1 => negate (.allow (.alias (← pick aliases)))
  | _ => negate (.allow (.only (← plain)))

def userSpecifier : Gen UserSpecifier := do
  match ← weighted [(6, 0), (2, 1), (3, 2), (1, 3)] with
  | 0 => return .user (.name (← pick policyUserNames))
  | 1 => return .user (.id (← pick uids))
  | 2 => return .group (.name (← pick groupNames))
  | _ => return .group (.id (← pick gids))

def groupIdentifier : Gen Identifier := do
  if ← chance 4 5 then return .name (← pick groupNames) else return .id (← pick gids)

def args : Gen Args := do
  match ← weighted [(5, 0), (2, 1), (3, 2), (1, 3)] with
  | 0 => return .prefix []
  | 1 => return .exact []
  | 2 => return .exact (← listOf 1 2 (pick argPool))
  | _ => return .prefix (← listOf 1 1 (pick argPool))

def command : Gen Command := do
  return ⟨← pick paths, ← args⟩

/-- Alias definitions of one kind: names `PREFIX0`, `PREFIX1`, ...; definition `i` may refer
to definitions `0 .. i-1`, so the list is in dependency order. -/
def defs (pfx : String) (plain : Gen α) : Gen (List (Def α)) := do
  let n ← weighted [(3, 0), (3, 1), (2, 2), (1, 3)]
  let mut out := #[]
  for i in [0:n] do
    let earlier := (List.range i).map (s!"{pfx}{·}")
    let items ← listOf 1 3 (item plain earlier)
    out := out.push { name := s!"{pfx}{i}", items }
  return out.toList

def runAs (runasAliases : List String) : Gen (Option RunAs) := do
  let users := listOf 1 2 (item userSpecifier runasAliases)
  let groups := listOf 1 2 (item groupIdentifier runasAliases)
  match ← weighted [(5, 0), (4, 1), (2, 2), (2, 3), (1, 4)] with
  | 0 => return none
  | 1 => return some ⟨← users, []⟩
  | 2 => return some ⟨← users, ← groups⟩
  | 3 => return some ⟨[], ← groups⟩
  | _ => return some ⟨[], []⟩

def modifier : Gen Modifier :=
  pick [.nopasswd, .passwd, .setenv, .nosetenv, .noexec, .exec]

def cmndSpecItem (cmndAliases : List String) : Gen (Spec Command) := do
  match ← weighted [(2, 0), (if cmndAliases.isEmpty then 0 else 2, 1), (7, 2)] with
  | 0 => negate (.allow .all)
  | 1 => negate (.allow (.alias (← pick cmndAliases)))
  | _ => negate (.allow (.only (← command)))

def entry (t : AliasTable) : Gen (Option RunAs × CommandSpec) := do
  let r ← runAs (t.runas.map (·.name))
  let mods ← weighted [(5, 0), (3, 1), (1, 2)] >>= fun n => listOf n n modifier
  return (r, ⟨mods, ← cmndSpecItem (t.cmnd.map (·.name))⟩)

def hostGroup (t : AliasTable) : Gen (SpecList Hostname × List (Option RunAs × CommandSpec)) := do
  let hs ← listOf 1 2 (item (pick hosts) (t.host.map (·.name)))
  return (hs, ← listOf 1 3 (entry t))

def rule (t : AliasTable) : Gen PermissionSpec := do
  let users ← listOf 1 3 (item userSpecifier (t.user.map (·.name)))
  return ⟨users, ← listOf 1 2 (hostGroup t)⟩

def policy : Gen Policy := do
  let user ← defs "UA" userSpecifier
  let runas ← defs "RA" userSpecifier
  let host ← defs "HA" (pick hosts)
  let cmnd ← defs "CA" command
  let t : AliasTable := { user, host, cmnd, runas }
  return { rules := ← listOf 1 4 (rule t), aliases := t }

/-- Plain names occurring in a user specifier list (for biasing the request). -/
def namesIn (l : SpecList UserSpecifier) : List String :=
  l.filterMap fun s => match s.who with
    | .only (.user (.name n)) => if userNames.contains n then some n else none
    | _ => none

def commandsIn (p : Policy) : List Command :=
  let fromRules := p.rules.flatMap fun r => r.permissions.flatMap fun g => g.2.filterMap
    fun e => match e.2.cmd.who with | .only c => some c | _ => none
  let fromAliases := p.aliases.cmnd.flatMap fun d => d.items.filterMap
    fun s => match s.who with | .only c => some c | _ => none
  fromRules ++ fromAliases

/-- Arguments that a command pattern accepts, sometimes perturbed. -/
def requestArgs (c : Option Command) : Gen (List String) := do
  match c, ← chance 3 4 with
  | some ⟨_, .prefix as⟩, true =>
    return as ++ (← listOf 0 1 (pick argPool))
  | some ⟨_, .exact as⟩, true => return as
  | _, _ => listOf 0 2 (pick argPool)

def groupNamesIn (l : SpecList Identifier) : List String :=
  l.filterMap fun s => match s.who with
    | .only (.name n) => if groupNames.contains n then some n else none
    | _ => none

/-- A command line that a given runas spec is likely to accept. -/
def cliFor : Option RunAs → Gen Cli
  | none => return ⟨none, none⟩
  | some ra => do
    let us := namesIn ra.users
    let gs := groupNamesIn ra.groups
    let u ← if us.isEmpty then pure none else some <$> pick us
    let g ← if gs.isEmpty || (← chance 1 3) then pure none else some <$> pick gs
    return ⟨u, g⟩

def cli (p : Policy) : Gen Cli := do
  let runases := p.rules.flatMap fun r => r.permissions.flatMap fun g => g.2.map (·.1)
  if !runases.isEmpty && (← chance 1 2) then return ← cliFor (← pick runases)
  match ← weighted [(3, 0), (4, 1), (2, 2), (2, 3)] with
  | 0 => return ⟨none, none⟩
  | 1 => return ⟨some (← pick userNames), none⟩
  | 2 => return ⟨none, some (← pick groupNames)⟩
  | _ => return ⟨some (← pick userNames), some (← pick groupNames)⟩

def case_ (index : Nat) : Gen Case := do
  let db ← db
  let p ← policy
  let t := p.aliases
  let order ← shuffle (t.user.map (·.name) ++ t.runas.map (·.name) ++
    t.host.map (·.name) ++ t.cmnd.map (·.name))
  let lineUsers := p.rules.flatMap (namesIn ·.users) ++ t.user.flatMap (namesIn ·.items)
  let invoker ← if !lineUsers.isEmpty && (← chance 4 5) then pick lineUsers
    else pick userNames
  let lineHosts := p.rules.flatMap fun r => r.permissions.flatMap fun g => g.1.filterMap
    fun s => match s with | .allow (.only h) => some h | _ => none
  let host ← if !lineHosts.isEmpty && (← chance 4 5) then pick lineHosts else pick hosts
  let cli ← cli p
  let cmds := commandsIn p
  let c ← if !cmds.isEmpty && (← chance 4 5) then some <$> pick cmds else pure none
  let path ← match c with | some c => pure c.pattern | none => pick paths
  let args ← requestArgs c
  return { index, db, policy := p, aliasOrder := order, host, invoker, cli,
           command := path, args }

/-- Case `index` of the run with seed `seed`. -/
def caseOf (seed index : Nat) : Case :=
  (case_ index).run' (Rng.forCase seed index)

end Differential.Generate
