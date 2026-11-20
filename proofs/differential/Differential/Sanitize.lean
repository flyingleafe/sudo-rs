import SudoersSpec.Ast

/-!
# Alias definitions as written, and sudo-rs's processing order

A policy text defines aliases in some order, possibly with duplicate names, cycles and
references to undefined aliases. `AnyDef` is one definition line of any of the four kinds, in
the order of the text.

`sanitize` transcribes `sanitize_alias_table` (`src/sudoers/mod.rs`): a depth-first visit of
every definition in file order that skips duplicate names, pushes a definition after the
definitions it refers to, and reports `undefined alias: 'X'`, `recursive alias: 'X'` and
`multiple occurrences of 'X'`. `sanitize` applies it to the four tables in the order of
`sanitize_alias_tables` (user, host, command, runas), which is also the order of the
diagnostics.

The spec (`SudoersSpec`) takes alias tables in processing order and leaves the sort out of
scope, so this module is part of the test oracle, not of the specification: the differential
test compares its diagnostics with the ones sudo-rs reports.
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

/-- The alias names a spec list refers to, in order. -/
def aliasRefsOf (l : SpecList α) : List String :=
  l.filterMap fun s => match s.who with | .alias n => some n | _ => none

/-- Does a table define the name? -/
def definesName (t : List (Def α)) (n : String) : Bool := t.any (·.name == n)

namespace Sanitize

/-- The visitor state: `seen`, `order` and the diagnostics. -/
structure St where
  seen : List Nat := []
  order : Array Nat := #[]
  diags : Array String := #[]

/-- The alias names a definition body refers to, in order. -/
def refs (d : Def α) : List String :=
  d.items.filterMap fun s => match s.who with | .alias n => some n | _ => none

/-- `Visitor::visit`. `fuel` bounds the nesting; every nested call inserts a new position into
`seen`, so `t.size + 1` is enough. -/
def visit (t : Array (Def α)) : Nat → Nat → StateM St Unit
  | 0, _ => pure ()
  | fuel + 1, pos => do
    let s ← get
    if s.seen.contains pos then
      if !s.order.contains pos then
        modify fun s => { s with diags := s.diags.push s!"recursive alias: '{t[pos]!.name}'" }
    else
      set { s with seen := pos :: s.seen }
      for name in refs t[pos]! do
        match t.findIdx? (·.name == name) with
        | none => modify fun s => { s with diags := s.diags.push s!"undefined alias: '{name}'" }
        | some dep => visit t fuel dep
      modify fun s => { s with order := s.order.push pos }

/-- `sanitize_alias_table`: the processing order and the diagnostics. -/
def table (defs : List (Def α)) : List (Def α) × List String := Id.run do
  let t := defs.toArray
  let mut st : St := {}
  let mut dupe : List String := []
  for i in [0:t.size] do
    let name := t[i]!.name
    if dupe.contains name then
      st := { st with diags := st.diags.push s!"multiple occurrences of '{name}'" }
    else
      dupe := name :: dupe
      st := ((visit t (t.size + 1) i).run st).2
  return (st.order.toList.map (t[·]!), st.diags.toList)

end Sanitize

/-- The alias table in sudo-rs's processing order, and the diagnostics of the four
`sanitize_alias_table` calls (user, host, command, runas). -/
def sanitize (defs : List AnyDef) : AliasTable × List String :=
  let w := writtenTables defs
  let (user, d1) := Sanitize.table w.user
  let (host, d2) := Sanitize.table w.host
  let (cmnd, d3) := Sanitize.table w.cmnd
  let (runas, d4) := Sanitize.table w.runas
  ({ user, host, cmnd, runas }, d1 ++ d2 ++ d3 ++ d4)

end Differential
