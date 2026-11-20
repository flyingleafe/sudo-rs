import Differential.Case

/-!
# Shrinking a case

`shrinks c` lists the cases one step smaller than `c`: one rule, host group, command entry,
list item, tag, alias definition, argument, `-u`/`-g` flag or group membership fewer, or a
runas spec dropped. `minimize` greedily takes the first shrink that keeps a property until
none does, so the result is 1-minimal with respect to these steps; `minimizeBatch` does the
same with one call of the property on all shrinks of a step (one run of the sudo-rs harness).
Lists that the grammar requires to be non-empty (user lists, host lists, command lists, alias
bodies) are never emptied.
-/

namespace Differential.Minimize

open SudoersSpec

/-- All ways to remove one element (keeping at least `keep` elements). -/
def drops (l : List α) (keep : Nat := 1) : List (List α) :=
  if l.length ≤ keep then [] else (List.range l.length).map l.eraseIdx

/-- All ways to replace one element by one of its shrinks. -/
def shrinkEach (l : List α) (f : α → List α) : List (List α) :=
  (List.range l.length).flatMap fun i => match l[i]? with
    | some x => (f x).map (l.set i)
    | none => []

def shrinkRunAs (r : RunAs) : List (Option RunAs) :=
  none :: ((drops r.users 0).map fun us => some { r with users := us }) ++
    ((drops r.groups 0).map fun gs => some { r with groups := gs })

def shrinkEntry (e : Option RunAs × CommandSpec) : List (Option RunAs × CommandSpec) :=
  (match e.1 with | some r => (shrinkRunAs r).map (·, e.2) | none => []) ++
  (drops e.2.mods 0).map fun ms => (e.1, { e.2 with mods := ms })

def shrinkGroup (g : SpecList Hostname × List (Option RunAs × CommandSpec)) :
    List (SpecList Hostname × List (Option RunAs × CommandSpec)) :=
  (drops g.1).map (·, g.2) ++ (drops g.2).map (g.1, ·) ++
    (shrinkEach g.2 shrinkEntry).map (g.1, ·)

def shrinkRule (r : PermissionSpec) : List PermissionSpec :=
  (drops r.users).map ({ r with users := · }) ++
  (drops r.permissions).map ({ r with permissions := · }) ++
  (shrinkEach r.permissions shrinkGroup).map ({ r with permissions := · })

def shrinkDef (d : Def α) : List (Def α) := (drops d.items).map ({ d with items := · })

def shrinkAnyDef : AnyDef → List AnyDef
  | .user d => (shrinkDef d).map .user
  | .runas d => (shrinkDef d).map .runas
  | .host d => (shrinkDef d).map .host
  | .cmnd d => (shrinkDef d).map .cmnd

/-- One rule fewer, a smaller rule, one definition fewer, or a smaller definition. -/
def shrinkPolicy (rules : List PermissionSpec) (defs : List AnyDef) :
    List (List PermissionSpec × List AnyDef) :=
  (drops rules 0).map (·, defs) ++
  (shrinkEach rules shrinkRule).map (·, defs) ++
  (drops defs 0).map (rules, ·) ++
  (shrinkEach defs shrinkAnyDef).map (rules, ·)

def shrinkDb (db : Db) : List Db :=
  (shrinkEach db.groups fun g => (drops g.members 0).map ({ g with members := · })).map
    ({ db with groups := · })

def shrinks (c : Case) : List Case :=
  (shrinkPolicy c.rules c.defs).map (fun (r, d) => { c with rules := r, defs := d }) ++
  (drops c.args 0).map ({ c with args := · }) ++
  (match c.cli with
    | ⟨some u, some g⟩ => [{ c with cli := ⟨some u, none⟩ }, { c with cli := ⟨none, some g⟩ }]
    | ⟨some _, none⟩ | ⟨none, some _⟩ => [{ c with cli := ⟨none, none⟩ }]
    | _ => []) ++
  (shrinkDb c.db).map ({ c with db := · })

/-- Greedy 1-minimisation under `keep` (which must hold for `c`). -/
partial def minimize (keep : Case → IO Bool) (c : Case) : IO Case := do
  for c' in shrinks c do
    if ← keep c' then return ← minimize keep c'
  return c

/-- Greedy 1-minimisation of any value with a shrinker, where `keepAll` evaluates the property
on a whole list of candidates at once and returns the index of the first that keeps it. -/
partial def minimizeBatch [Inhabited β] (shrink : β → List β) (keepAll : List β → IO (Option Nat))
    (x : β) : IO β := do
  let cands := shrink x
  if cands.isEmpty then return x
  match ← keepAll cands with
  | some i => minimizeBatch shrink keepAll cands[i]!
  | none => return x

end Differential.Minimize
