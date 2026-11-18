import SudoersSpec.Oracle

/-!
# The user/group database of a test case, and the oracle it induces

A case carries its own passwd/group database. Users are passwd entries; a user's group
vector is its primary gid followed by the gids of every group that lists it as a member,
which is what `getgrouplist(3)` returns and what both sudo-rs (`User::groups`,
`src/system/mod.rs`) and C sudo (`sudo_get_gidlist`) work with.

`oracleOf db` instantiates `SudoersSpec.Oracle` exactly the way the real sudo-rs types behave
(`impl UnixUser for User`, `impl UnixGroup for Group`, `src/system/interface.rs`): names and
ids are compared literally, `is_root` is `uid == 0`, `in_group_by_name` resolves the group
name through the database (`Group::from_name`, the first entry wins) and then tests the gid,
user equality is equality of the whole passwd entry (`#[derive(PartialEq)] struct User`), the
host matcher is string equality (`match_token`), and the glob matcher is string equality,
which is what `glob::Pattern::matches_path_with` does on patterns without metacharacters (the
generator never produces any).
-/

namespace Differential

open SudoersSpec

/-- A passwd entry (home and shell are fixed when printed). -/
structure UserEnt where
  name : String
  uid : Nat
  gid : Nat
  deriving DecidableEq, Repr, Inhabited

/-- A group entry with its member list. -/
structure GroupEnt where
  name : String
  gid : Nat
  members : List String
  deriving DecidableEq, Repr, Inhabited

structure Db where
  users : List UserEnt
  groups : List GroupEnt
  deriving DecidableEq, Repr, Inhabited

namespace Db

def userNamed (db : Db) (n : String) : Option UserEnt := db.users.find? (·.name == n)
def groupNamed (db : Db) (n : String) : Option GroupEnt := db.groups.find? (·.name == n)
def groupWithGid (db : Db) (gid : Nat) : Option GroupEnt := db.groups.find? (·.gid == gid)

/-- `getgrouplist(name, primary gid)`: the primary gid and the gid of every group listing the
user as a member. -/
def gidsOf (db : Db) (u : UserEnt) : List Nat :=
  u.gid :: (db.groups.filter (·.members.contains u.name)).map (·.gid)

/-- `/etc/passwd` line. -/
def passwdLine (u : UserEnt) : String :=
  s!"{u.name}:x:{u.uid}:{u.gid}::/home/{u.name}:/bin/sh"

/-- `/etc/group` line. -/
def groupLine (g : GroupEnt) : String :=
  s!"{g.name}:x:{g.gid}:{",".intercalate g.members}"

end Db

/-- The oracle of the real sudo-rs `User`/`Group` types over database `db`. -/
def oracleOf (db : Db) : Oracle UserEnt GroupEnt where
  hasName u n := u.name == n
  hasUid u n := u.uid == n
  isRoot u := u.uid == 0
  inGroupByName u n := match db.groupNamed n with
    | some g => (db.gidsOf u).contains g.gid
    | none => false
  inGroupByGid u n := (db.gidsOf u).contains n
  userEq u v := u == v
  asGid g := g.gid
  tryAsName g := some g.name
  globMatches pat path := pat == path
  hostMatches pat host := pat == host

/-- The `-u` / `-g` options of the sudo command line. -/
structure Cli where
  runasUser : Option String
  runasGroup : Option String
  deriving DecidableEq, Repr, Inhabited

/-- The command-line flags as `testsudoers` (and `sudo`) take them. -/
def Cli.flags (c : Cli) : List String :=
  (match c.runasUser with | some u => ["-u", u] | none => []) ++
  (match c.runasGroup with | some g => ["-g", g] | none => [])

/-- `resolve_target_user_and_group` (`src/common/resolve.rs`): `-g` alone runs as the
invoking user, `-u` alone uses the target user's primary group, neither means `root:root`. -/
def Cli.resolve (db : Db) (invoker : UserEnt) (c : Cli) : Option (UserEnt × GroupEnt) :=
  match c.runasUser, c.runasGroup with
  | none, none => do return (← db.userNamed "root", ← db.groupNamed "root")
  | some u, none => do
    let u ← db.userNamed u
    return (u, ← db.groupWithGid u.gid)
  | none, some g => do return (invoker, ← db.groupNamed g)
  | some u, some g => do return (← db.userNamed u, ← db.groupNamed g)

end Differential
