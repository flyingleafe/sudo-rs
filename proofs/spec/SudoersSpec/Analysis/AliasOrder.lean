import SudoersSpec.Ast

/-!
# Alias preprocessing

Visit the definitions in file order, and each definition's references in member order.
A reference resolves to the first definition of its name. A definition is emitted after
its dependencies, even when a dependency was missing or a cycle was reported. A duplicate
root reports a diagnostic instead of starting a visit.
-/

namespace SudoersSpec.Analysis

/-- The alias names a spec list refers to, in member order. -/
def aliasRefsOf (l : SpecList α) : List String :=
  l.filterMap fun s => match s.who with | .alias n => some n | _ => none

namespace AliasOrder

local instance : Inhabited (Def α) := ⟨⟨"", []⟩⟩

/-- Positions entered, positions finished, and diagnostics emitted. -/
structure State where
  seen : List Nat := []
  order : Array Nat := #[]
  diags : Array String := #[]

def State.emit (s : State) (message : String) : State := { s with diags := s.diags.push message }

def undefinedMessage (name : String) : String := s!"undefined alias: '{name}'"
def recursiveMessage (name : String) : String := s!"recursive alias: '{name}'"
def duplicateMessage (name : String) : String := s!"multiple occurrences of '{name}'"

def visitRefs (t : Array (Def α)) (descend : Nat → State → State) (refs : List String)
    (s : State) : State :=
  refs.foldl (fun s name =>
    match t.findIdx? (·.name == name) with
    | none => s.emit (undefinedMessage name)
    | some dep => descend dep s) s

/-- A fresh position enters `seen` before descending; at most `t.size + 1` levels
are needed (including the final check of a previously visited position). -/
def visit (t : Array (Def α)) : Nat → Nat → State → State
  | 0, _, s => s
  | fuel + 1, pos, s =>
    if pos ∈ s.seen then
      if pos ∈ s.order then s else s.emit (recursiveMessage t[pos]!.name)
    else
      let s' := visitRefs t (visit t fuel) (aliasRefsOf t[pos]!.items) { s with seen := pos :: s.seen }
      { s' with order := s'.order.push pos }

/-- Visit successive roots starting at `i`; `names` records roots encountered so far. -/
def roots (t : Array (Def α)) : Nat → Nat → List String → State → State
  | 0, _, _, s => s
  | left + 1, i, names, s =>
    let name := t[i]!.name
    if name ∈ names then
      roots t left (i + 1) names (s.emit (duplicateMessage name))
    else
      roots t left (i + 1) (name :: names) (visit t (t.size + 1) i s)

/-- One table, from file order to processing order and diagnostics. -/
def table (defs : List (Def α)) : List (Def α) × List String :=
  let t := defs.toArray
  let s := roots t t.size 0 [] {}
  (s.order.toList.map (t[·]!), s.diags.toList)

end AliasOrder

/-- Tables in processing order, with messages appended in user, host, command, runas order. -/
def orderAliases (written : AliasTable) : AliasTable × List String :=
  let (user, d1) := AliasOrder.table written.user
  let (host, d2) := AliasOrder.table written.host
  let (cmnd, d3) := AliasOrder.table written.cmnd
  let (runas, d4) := AliasOrder.table written.runas
  ({ user, host, cmnd, runas }, d1 ++ d2 ++ d3 ++ d4)

end SudoersSpec.Analysis
