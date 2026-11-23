import SudoersSpec.Analysis.AliasOrder

/-!
# Alias definitions as written, and sudo-rs's processing order

A policy text defines aliases in some order, possibly with duplicate names, cycles and
references to undefined aliases. `AnyDef` is one definition line of any of the four kinds, in
the order of the text.

The shared spec orders the four tables and reports the sanitizer diagnostics.
-/

namespace Differential

open SudoersSpec

instance : Inhabited (Def α) := ⟨⟨"", []⟩⟩

/-- One alias definition line, of one of the four kinds. -/
inductive AnyDef where
  | user (d : Def UserSpecifier)
  | runas (d : Def UserSpecifier)
  | host (d : Def Hostname)
  | cmnd (d : Def Command)
  deriving DecidableEq, Repr, Inhabited

namespace AnyDef

def name : AnyDef → String
  | user d | runas d | host d | cmnd d => d.name

end AnyDef

/-- The tables in file order (duplicates and all). -/
def writtenTables (defs : List AnyDef) : AliasTable where
  user := defs.filterMap fun | .user d => some d | _ => none
  runas := defs.filterMap fun | .runas d => some d | _ => none
  host := defs.filterMap fun | .host d => some d | _ => none
  cmnd := defs.filterMap fun | .cmnd d => some d | _ => none

/-- Does a table define the name? -/
def definesName (t : List (Def α)) (n : String) : Bool := t.any (·.name == n)

/-- The alias table in sudo-rs's processing order, and the diagnostics of the four
`sanitize_alias_table` calls (user, host, command, runas). -/
def sanitize (defs : List AnyDef) : AliasTable × List String :=
  SudoersSpec.Analysis.orderAliases (writtenTables defs)

end Differential
