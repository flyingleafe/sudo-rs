import Differential.Case

/-!
# Textual alias expansion

`Case.inlined` replaces every alias reference by the body of the alias, recursively, with the
negations of the body flipped when the reference is negated, and deletes the alias
definitions. This is the expansion a reader of a policy performs by hand:

* user lists (`User_Alias`), host lists (`Host_Alias`) and runas user lists (`Runas_Alias`):
  the members take the place of the reference;
* runas group lists (`Runas_Alias` used as a group list): a member `name` or `#id` becomes the
  group `name` or `#id`; a member `%group` (or `%:group`) is written as it stands, i.e. the
  text `%group` in a group list (the expansion is textual, whether or not the result parses);
* command lists (`Cmnd_Alias`): the entry `runas tags ALIAS` becomes the entries
  `runas tags m1, m2, …`, so that the runas spec and the tags carry over to every member as
  they do in a `Cmnd_Spec_List`.

References to aliases that the policy does not define stay as they are. The expansion is
meaningful for alias tables without diagnostics (no duplicates, no cycles); `fuel` bounds the
nesting otherwise.
-/

namespace Differential.Inline

open SudoersSpec

/-- The first definition of a name. -/
def lookup (t : List (Def α)) (n : String) : Option (SpecList α) :=
  (t.find? (·.name == n)).map (·.items)

/-- Expansion of a list whose members have the alias's own type. -/
def expandSame (t : List (Def α)) : Nat → SpecList α → SpecList α
  | 0, l => l
  | fuel + 1, l => l.flatMap fun s =>
    match s.who with
    | .alias n => match lookup t n with
      | some body =>
        let b := expandSame t fuel body
        match s with | .allow _ => b | .forbid _ => b.map Qualified.negate
      | none => [s]
    | _ => [s]

/-- A `Runas_Alias` member read as a member of a group list. -/
def asGroup : Spec UserSpecifier → Spec Identifier
  | .allow m => .allow (conv m)
  | .forbid m => .forbid (conv m)
where
  conv : Meta UserSpecifier → Meta Identifier
    | .all => .all
    | .alias n => .alias n
    | .only (.user i) => .only i
    | .only (.group i) => .only (.name ("%" ++ SudoersSpec.Grammar.PermissionPrint.identifier i))
    | .only (.nonunixGroup i) =>
      .only (.name ("%:" ++ SudoersSpec.Grammar.PermissionPrint.identifier i))

/-- Expansion of a runas group list with the (already fully expanded) `Runas_Alias` table. -/
def expandGroups (t : List (Def UserSpecifier)) (fuel : Nat) (l : SpecList Identifier) :
    SpecList Identifier :=
  l.flatMap fun s =>
    match s.who with
    | .alias n => match lookup t n with
      | some body =>
        let b := (expandSame t fuel body).map asGroup
        match s with | .allow _ => b | .forbid _ => b.map Qualified.negate
      | none => [s]
    | _ => [s]

/-- Expansion of one command entry into one or more entries. -/
def expandEntry (t : List (Def Command)) (fuel : Nat) (e : Option RunAs × CommandSpec) :
    List (Option RunAs × CommandSpec) :=
  match (expandSame t fuel [e.2.cmd]) with
  | [] => [e]
  | first :: rest => (e.1, { e.2 with cmd := first }) :: rest.map fun s => (none, ⟨[], s⟩)

def expandRunAs (t : AliasTable) (fuel : Nat) (r : RunAs) : RunAs :=
  { users := expandSame t.runas fuel r.users, groups := expandGroups t.runas fuel r.groups }

def expandRule (t : AliasTable) (fuel : Nat) (r : PermissionSpec) : PermissionSpec :=
  { users := expandSame t.user fuel r.users,
    permissions := r.permissions.map fun (hs, es) =>
      (expandSame t.host fuel hs,
        es.flatMap fun e => expandEntry t.cmnd fuel ((e.1.map (expandRunAs t fuel)), e.2)) }

end Inline

/-- The policy with every alias expanded and the definitions deleted. Aliases are looked up in
the tables as written (first definition of a name). -/
def Case.inlined (c : Case) : Case :=
  let t := c.written
  let fuel := c.defs.length + 1
  { c with rules := c.rules.map (Inline.expandRule t fuel), defs := [] }

end Differential
