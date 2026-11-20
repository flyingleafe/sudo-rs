import Std.Data.HashMap
import Differential.Generate

/-!
# Feature coverage of a run

For every feature of the generated fragment, the number of cases whose policy or request
contains it.
-/

namespace Differential.Coverage

open SudoersSpec

def isNeg : Qualified α → Bool | .forbid _ => true | .allow _ => false

def anyRule (p : Policy) (f : PermissionSpec → Bool) : Bool := p.rules.any f

def entries (p : Policy) : List (Option RunAs × CommandSpec) :=
  p.rules.flatMap fun r => r.permissions.flatMap (·.2)

def userItems (p : Policy) : List (Spec UserSpecifier) :=
  p.rules.flatMap (·.users) ++ p.aliases.user.flatMap (·.items)

def runasItems (p : Policy) : List (Spec UserSpecifier) :=
  (entries p).flatMap (fun e => match e.1 with | some ra => ra.users | none => []) ++
    p.aliases.runas.flatMap (·.items)

def cmds (p : Policy) : List (Spec Command) :=
  (entries p).map (·.2.cmd) ++ p.aliases.cmnd.flatMap (·.items)

def hasUserSpec (l : List (Spec UserSpecifier)) (f : UserSpecifier → Bool) : Bool :=
  l.any fun s => match s.who with | .only u => f u | _ => false

def nested (ds : List (Def α)) : Bool :=
  ds.any fun d => d.items.any fun s => match s.who with | .alias _ => true | _ => false

/-- Some command (in a rule or a `Cmnd_Alias`) has an argument pattern satisfying `f`. -/
def argsForm (f : Args → Bool) (p : Policy) : Bool :=
  (cmds p).any fun s => match s.who with | .only c => f c.args | _ => false

def noArgs : Args → Bool
  | .prefix [] => true
  | _ => false

def emptyArgs : Args → Bool
  | .exact [] => true
  | _ => false

def exactArgs : Args → Bool
  | .exact [] => false
  | .exact _ => true
  | _ => false

def prefixArgs : Args → Bool
  | .prefix [] => false
  | .prefix _ => true
  | _ => false

def P (f : Policy → Bool) (c : Case) : Bool := f c.policy

/-- Every alias reference of the policy (rules and definitions), with the table it is looked
up in. -/
def aliasRefs (c : Case) : List (String × String) :=
  let tagged (k : String) (l : List String) := l.map (k, ·)
  let runasRefs (e : Option RunAs × CommandSpec) : List String :=
    match e.1 with
    | some ra => aliasRefsOf ra.users ++ aliasRefsOf ra.groups
    | none => []
  let w := c.written
  c.rules.flatMap (fun r => tagged "user" (aliasRefsOf r.users) ++ r.permissions.flatMap fun g =>
      tagged "host" (aliasRefsOf g.1) ++ g.2.flatMap fun e =>
        tagged "cmnd" (aliasRefsOf [e.2.cmd]) ++ tagged "runas" (runasRefs e)) ++
    w.user.flatMap (tagged "user" <| aliasRefsOf ·.items) ++
    w.runas.flatMap (tagged "runas" <| aliasRefsOf ·.items) ++
    w.host.flatMap (tagged "host" <| aliasRefsOf ·.items) ++
    w.cmnd.flatMap (tagged "cmnd" <| aliasRefsOf ·.items)

def definedIn (c : Case) (k n : String) : Bool :=
  let w := c.written
  match k with
  | "user" => w.user.any (·.name == n)
  | "runas" => w.runas.any (·.name == n)
  | "host" => w.host.any (·.name == n)
  | _ => w.cmnd.any (·.name == n)

def dbName (c : Case) (n : String) : Bool :=
  c.db.users.any (·.name == n) || c.db.groups.any (·.name == n) || Generate.hosts.contains n

def hasDiag (pfx : String) (c : Case) : Bool := c.diagnostics.any (·.startsWith pfx)

def features : List (String × (Case → Bool)) :=
  [ ("user list: name", P fun p => hasUserSpec (userItems p) fun | .user (.name _) => true | _ => false),
    ("user list: #uid", P fun p => hasUserSpec (userItems p) fun | .user (.id _) => true | _ => false),
    ("user list: %group", P fun p => hasUserSpec (userItems p) fun | .group (.name _) => true | _ => false),
    ("user list: %#gid", P fun p => hasUserSpec (userItems p) fun | .group (.id _) => true | _ => false),
    ("user list: ALL", P fun p => (userItems p).any (·.who == .all)),
    ("negated item (any list)", P fun p => (userItems p).any isNeg || (runasItems p).any isNeg ||
      (cmds p).any isNeg || p.rules.any (·.permissions.any (·.1.any isNeg)) ||
      p.aliases.host.any (·.items.any isNeg)),
    ("User_Alias", P fun p => !p.aliases.user.isEmpty),
    ("Runas_Alias", P fun p => !p.aliases.runas.isEmpty),
    ("Host_Alias", P fun p => !p.aliases.host.isEmpty),
    ("Cmnd_Alias", P fun p => !p.aliases.cmnd.isEmpty),
    ("nested alias", P fun p => nested p.aliases.user || nested p.aliases.runas ||
      nested p.aliases.host || nested p.aliases.cmnd),
    ("negated alias member", P fun p => p.aliases.user.any (·.items.any isNeg) ||
      p.aliases.runas.any (·.items.any isNeg) || p.aliases.host.any (·.items.any isNeg) ||
      p.aliases.cmnd.any (·.items.any isNeg)),
    ("negated alias reference", P fun p => (userItems p ++ runasItems p).any (fun s =>
      isNeg s && match s.who with | .alias _ => true | _ => false) ||
      (cmds p).any (fun s => isNeg s && match s.who with | .alias _ => true | _ => false)),
    ("two or more lines", P fun p => p.rules.length ≥ 2),
    ("two host groups in a line", P fun p => anyRule p (·.permissions.length ≥ 2)),
    ("runas omitted", P fun p => (entries p).any (·.1.isNone)),
    ("runas (users)", P fun p => (entries p).any fun e => match e.1 with
      | some ra => !ra.users.isEmpty && ra.groups.isEmpty | none => false),
    ("runas (users : groups)", P fun p => (entries p).any fun e => match e.1 with
      | some ra => !ra.users.isEmpty && !ra.groups.isEmpty | none => false),
    ("runas (: groups)", P fun p => (entries p).any fun e => match e.1 with
      | some ra => ra.users.isEmpty && !ra.groups.isEmpty | none => false),
    ("runas ()", P fun p => (entries p).any fun e => match e.1 with
      | some ra => ra.users.isEmpty && ra.groups.isEmpty | none => false),
    ("NOPASSWD", P fun p => (entries p).any (·.2.mods.contains .nopasswd)),
    ("PASSWD", P fun p => (entries p).any (·.2.mods.contains .passwd)),
    ("SETENV", P fun p => (entries p).any (·.2.mods.contains .setenv)),
    ("NOSETENV", P fun p => (entries p).any (·.2.mods.contains .nosetenv)),
    ("NOEXEC", P fun p => (entries p).any (·.2.mods.contains .noexec)),
    ("EXEC", P fun p => (entries p).any (·.2.mods.contains .exec)),
    ("command without arguments", P (argsForm noArgs)),
    ("command \"\"", P (argsForm emptyArgs)),
    ("command with exact arguments", P (argsForm exactArgs)),
    ("command with arguments and *", P (argsForm prefixArgs)),
    ("command ALL", P fun p => (cmds p).any (·.who == .all)),
    ("request: no -u/-g", fun c => c.cli == ⟨none, none⟩),
    ("request: -u only", fun c => c.cli.runasUser.isSome && c.cli.runasGroup.isNone),
    ("request: -g only", fun c => c.cli.runasUser.isNone && c.cli.runasGroup.isSome),
    ("request: -u and -g", fun c => c.cli.runasUser.isSome && c.cli.runasGroup.isSome),
    ("request: invoked by toor (uid 0)", fun c => c.invoker == "toor"),
    ("request: runs as toor (uid 0)", fun c => c.cli.runasUser == some "toor"),
    ("hazard: upper-case name of an account, group or host referenced",
      fun c => (aliasRefs c).any fun (_, n) => dbName c n),
    ("hazard: same, and also defined as an alias of that table",
      fun c => (aliasRefs c).any fun (k, n) => dbName c n && definedIn c k n),
    ("hazard: reference to an undefined alias", fun c => (aliasRefs c).any fun (k, n) => !definedIn c k n),
    ("hazard: duplicate definition", hasDiag "multiple occurrences"),
    ("hazard: cyclic definition", hasDiag "recursive alias"),
    ("hazard: undefined alias in a definition", hasDiag "undefined alias"),
    ("request: invoked by an upper-case account", fun c => Generate.capsUsers.contains c.invoker),
    ("request: upper-case host", fun c => Generate.capsHosts.contains c.host),
    ("request: -u/-g with an upper-case name", fun c =>
      (c.cli.runasUser.any Generate.capsUsers.contains) ||
      (c.cli.runasGroup.any Generate.capsGroups.contains)) ]

def report (n seed : Nat) : IO Unit := do
  let mut counts := Array.replicate features.length 0
  for i in [0:n] do
    let c := Generate.caseOf seed i
    for (j, (_, f)) in features.zipIdx.map (fun (x, j) => (j, x)) do
      if f c then counts := counts.modify j (· + 1)
  IO.println s!"feature coverage ({n} cases, seed {seed}):"
  for ((name, _), k) in features.zip counts.toList do
    IO.println s!"  {name}: {k}"

end Differential.Coverage
