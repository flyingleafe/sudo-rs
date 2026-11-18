import Differential.Case

/-!
# Shrinking a case

`shrinks c` lists the cases one step smaller than `c`: one rule, host group, command entry,
list item, tag, alias definition (if unreferenced), argument, `-u`/`-g` flag or group
membership fewer, or a runas spec dropped. `minimize` greedily takes the first shrink that
keeps a property until none does, so the result is 1-minimal with respect to these steps.
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

/-- Alias names referenced by a spec list. -/
def refs (l : SpecList α) : List String :=
  l.filterMap fun s => match s.who with | .alias n => some n | _ => none

def referenced (p : Policy) : List String :=
  let t := p.aliases
  p.rules.flatMap (fun r => refs r.users ++ r.permissions.flatMap fun g => refs g.1 ++
      g.2.flatMap fun e => refs [e.2.cmd] ++
        (match e.1 with | some ra => refs ra.users ++ refs ra.groups | none => [])) ++
    t.user.flatMap (refs ·.items) ++ t.runas.flatMap (refs ·.items) ++
    t.host.flatMap (refs ·.items) ++ t.cmnd.flatMap (refs ·.items)

def shrinkDefs (used : List String) (ds : List (Def α)) : List (List (Def α)) :=
  ((List.range ds.length).filter (fun i => match ds[i]? with
    | some d => !used.contains d.name
    | none => false)).map ds.eraseIdx ++
  shrinkEach ds fun d => (drops d.items).map ({ d with items := · })

def shrinkPolicy (p : Policy) : List Policy :=
  let t := p.aliases
  let used := referenced p
  (drops p.rules 0).map ({ p with rules := · }) ++
  (shrinkEach p.rules shrinkRule).map ({ p with rules := · }) ++
  (shrinkDefs used t.user).map (fun d => { p with aliases := { t with user := d } }) ++
  (shrinkDefs used t.runas).map (fun d => { p with aliases := { t with runas := d } }) ++
  (shrinkDefs used t.host).map (fun d => { p with aliases := { t with host := d } }) ++
  (shrinkDefs used t.cmnd).map (fun d => { p with aliases := { t with cmnd := d } })

def shrinkDb (db : Db) : List Db :=
  (shrinkEach db.groups fun g => (drops g.members 0).map ({ g with members := · })).map
    ({ db with groups := · })

def shrinks (c : Case) : List Case :=
  (shrinkPolicy c.policy).map ({ c with policy := · }) ++
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

end Differential.Minimize
