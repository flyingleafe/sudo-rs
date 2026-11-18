import SudoersSpec.Ast

/-!
# Printing the spec AST as sudoers text

One printer per AST node of `SudoersSpec.Ast`, following the grammar of `sudoers(5)`
(`docs/man/sudoers.5.md`) and of the sudo-rs parser (`src/sudoers/ast.rs`). Every printer is
the inverse of one parser production:

| AST node | text |
|---|---|
| `Meta.all` / `.only x` / `.alias n` | `ALL` / `x` / `n` |
| `Qualified.allow x` / `.forbid x` | `x` / `!x` |
| `Identifier.name n` / `.id n` | `n` / `#n` |
| `UserSpecifier.user i` / `.group i` / `.nonunixGroup i` | `i` / `%i` / `%:i` |
| `Args.prefix []` / `.prefix as` / `.exact []` / `.exact as` | `` / ` as *` / ` ""` / ` as` |
| `RunAs ⟨us, []⟩` / `⟨[], gs⟩` / `⟨us, gs⟩` | `(us)` / `(: gs)` / `(us : gs)` |
| `Modifier` | `EXEC:`, `NOEXEC:`, `SETENV:`, `NOSETENV:`, `PASSWD:`, `NOPASSWD:` |
| `CommandSpec ⟨mods, cmd⟩` | `mods cmd` |
| `PermissionSpec ⟨users, groups⟩` | `users hosts = entries : hosts = entries` |
| `Def` | `Kind_Alias NAME = items` |

Only the fragment the generator produces is printable: `CWD=`, `APPARMOR_PROFILE=`, ignored
tags and no-op tags have no printer (`printModifier` returns `none`), and the generator
never produces names or arguments that would need quoting.
-/

namespace Differential.Print

open SudoersSpec

def metaItem (f : α → String) : Meta α → String
  | .all => "ALL"
  | .only x => f x
  | .alias n => n

def qualified (f : α → String) : Qualified α → String
  | .allow x => f x
  | .forbid x => "!" ++ f x

def spec (f : α → String) (s : Spec α) : String := qualified (metaItem f) s

def specList (f : α → String) (l : SpecList α) : String := ", ".intercalate (l.map (spec f))

def identifier : Identifier → String
  | .name n => n
  | .id n => s!"#{n}"

def userSpecifier : UserSpecifier → String
  | .user i => identifier i
  | .group i => "%" ++ identifier i
  | .nonunixGroup i => "%:" ++ identifier i

def hostname (h : Hostname) : String := h

def args : Args → String
  | .prefix [] => ""
  | .prefix as => " " ++ " ".intercalate as ++ " *"
  | .exact [] => " \"\""
  | .exact as => " " ++ " ".intercalate as

def command (c : Command) : String := c.pattern ++ args c.args

def runAs (r : RunAs) : String :=
  match r.users, r.groups with
  | us, [] => "(" ++ specList userSpecifier us ++ ")"
  | [], gs => "(: " ++ specList identifier gs ++ ")"
  | us, gs => "(" ++ specList userSpecifier us ++ " : " ++ specList identifier gs ++ ")"

def modifier : Modifier → Option String
  | .exec => some "EXEC:"
  | .noexec => some "NOEXEC:"
  | .setenv => some "SETENV:"
  | .nosetenv => some "NOSETENV:"
  | .passwd => some "PASSWD:"
  | .nopasswd => some "NOPASSWD:"
  | _ => none

def commandSpec (c : CommandSpec) : String :=
  " ".intercalate (c.mods.filterMap modifier ++ [spec command c.cmd])

/-- One `Cmnd_Spec`: optional runas followed by the command spec. -/
def entry : Option RunAs × CommandSpec → String
  | (some r, c) => runAs r ++ " " ++ commandSpec c
  | (none, c) => commandSpec c

/-- One `Host_List = Cmnd_Spec_List` group. -/
def hostGroup (g : SpecList Hostname × List (Option RunAs × CommandSpec)) : String :=
  specList hostname g.1 ++ " = " ++ ", ".intercalate (g.2.map entry)

def permissionSpec (p : PermissionSpec) : String :=
  specList userSpecifier p.users ++ " " ++ " : ".intercalate (p.permissions.map hostGroup)

def def_ (kind : String) (f : α → String) (d : Def α) : String :=
  s!"{kind} {d.name} = {specList f d.items}"

/-- All alias definitions of a table, one line each. -/
def aliasLines (t : AliasTable) : List String :=
  t.user.map (def_ "User_Alias" userSpecifier) ++
  t.runas.map (def_ "Runas_Alias" userSpecifier) ++
  t.host.map (def_ "Host_Alias" hostname) ++
  t.cmnd.map (def_ "Cmnd_Alias" command)

end Differential.Print
