import SudoRs
import SudoersSpec
import SudoRsProofs.Util

/-!
# Abstraction functions: extracted Rust types → specification types

The extracted types live in namespace `sudo_rs` (`sudo_rs.sudoers.ast.Qualified`, …), the
specification types in `SudoersSpec`. Element types are abstracted by a function `f`; for the
alias/lookup core the element type is kept (`f = id`).

Besides the abstractions this file defines the side conditions that the Rust data structures
satisfy but the Lean types do not enforce:
* string sizes (`Fits`): a Rust `String` fits in memory;
* `TableWF`: the processing order of a `VecOrd` only holds valid positions (established by
  `sanitize_alias_table`).
-/

open Aeneas Aeneas.Std Result

namespace SudoRsProofs

/-- Rust `Spec<T> = Qualified<Meta<T>>`. -/
abbrev RSpec (T : Type) := sudo_rs.sudoers.ast.Qualified (sudo_rs.sudoers.tokens.Meta T)

/-- Rust `Def<T> = (String, SpecList<T>)`. -/
abbrev RDef (T : Type) := sudo_rs.sudoers.ast.Def T

/-! ## Spec lists -/

def absQualified {α β : Type} (f : α → β) :
    sudo_rs.sudoers.ast.Qualified α → SudoersSpec.Qualified β
  | .Allow x => .allow (f x)
  | .Forbid x => .forbid (f x)

def absMeta {α β : Type} (f : α → β) : sudo_rs.sudoers.tokens.Meta α → SudoersSpec.Meta β
  | .All => .all
  | .Only x => .only (f x)
  | .Alias n => .alias n

def absSpec {α β : Type} (f : α → β) (s : RSpec α) : SudoersSpec.Spec β :=
  absQualified (absMeta f) s

def absSpecList {α β : Type} (f : α → β) (l : List (RSpec α)) : SudoersSpec.SpecList β :=
  l.map (absSpec f)

/-- The alias a spec refers to, if any. -/
def aliasName {α : Type} : RSpec α → Option String
  | .Allow (.Alias n) | .Forbid (.Alias n) => some n
  | _ => none

/-- Every alias name a spec list mentions fits in memory. -/
def ItemsFit {α : Type} (l : List (RSpec α)) : Prop :=
  ∀ s ∈ l, ∀ n, aliasName s = some n → Fits n

/-- The item a spec names directly (`Meta::Only`), if any. -/
def onlyItem {α : Type} : RSpec α → Option α
  | .Allow (.Only x) | .Forbid (.Only x) => some x
  | _ => none

/-- Every item a spec list names directly satisfies `Good`: the domain on which the matcher
closure passed to `find_item` is known to be pure and total. -/
def ItemsGood {α : Type} (Good : α → Prop) (l : List (RSpec α)) : Prop :=
  ∀ s ∈ l, ∀ x, onlyItem s = some x → Good x

/-! ## `FoundAliases` -/

/-- The Rust `FoundAliases(Vec<(String, bool)>)` is a list of insertions; later entries win. -/
def absFound (v : sudo_rs.sudoers.FoundAliases) : SudoersSpec.FoundAliases :=
  v.val.foldl (fun m p => m.insert p.1 p.2) SudoersSpec.FoundAliases.empty

/-- Every alias name stored in a `FoundAliases` fits in memory. -/
def FoundFits (v : sudo_rs.sudoers.FoundAliases) : Prop := ∀ p ∈ v.val, Fits p.1

/-! ## Alias tables -/

def absDef {α β : Type} (f : α → β) (d : RDef α) : SudoersSpec.Def β :=
  ⟨d.1, absSpecList f d.2.val⟩

/-- The definitions of a `VecOrd` in processing order (`VecOrd::iter`). Positions out of range
are dropped; `TableWF` rules them out. -/
def tableDefs {α : Type} (t : sudo_rs.sudoers.VecOrd (RDef α)) : List (RDef α) :=
  t.1.val.filterMap fun i => t.2.val[i.val]?

def absTable {α β : Type} (f : α → β) (t : sudo_rs.sudoers.VecOrd (RDef α)) :
    List (SudoersSpec.Def β) :=
  (tableDefs t).map (absDef f)

/-- Every position in the processing order is a valid index (`sanitize_alias_table`). -/
def TableWF {α : Type} (t : sudo_rs.sudoers.VecOrd (RDef α)) : Prop :=
  ∀ i ∈ t.1.val, i.val < t.2.val.length

/-- Every name in an alias table fits in memory: definition names and referenced aliases. -/
def TableFits {α : Type} (t : sudo_rs.sudoers.VecOrd (RDef α)) : Prop :=
  ∀ d ∈ t.2.val, Fits d.1 ∧ ItemsFit d.2.val

/-- Every directly named item of every definition satisfies `Good` (see `ItemsGood`). -/
def TableGood {α : Type} (Good : α → Prop) (t : sudo_rs.sudoers.VecOrd (RDef α)) : Prop :=
  ∀ d ∈ t.2.val, ItemsGood Good d.2.val

/-! ## Basic lemmas -/

@[simp] theorem absSpecList_nil {α β : Type} (f : α → β) : absSpecList f [] = [] := rfl

@[simp] theorem absSpecList_cons {α β : Type} (f : α → β) (s : RSpec α) (l : List (RSpec α)) :
    absSpecList f (s :: l) = absSpec f s :: absSpecList f l := rfl

theorem absSpecList_append {α β : Type} (f : α → β) (l₁ l₂ : List (RSpec α)) :
    absSpecList f (l₁ ++ l₂) = absSpecList f l₁ ++ absSpecList f l₂ := List.map_append

/-- `absFound` from an arbitrary starting map. -/
theorem foldl_insert_apply (l : List (String × Bool)) (m : SudoersSpec.FoundAliases)
    (k : String) :
    l.foldl (fun m p => m.insert p.1 p.2) m k =
      l.foldl (fun r p => if p.1 = k then some p.2 else r) (m k) := by
  induction l generalizing m with
  | nil => rfl
  | cons p l ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp only [SudoersSpec.FoundAliases.insert]
    by_cases h : p.1 = k
    · simp [h]
    · simp [h, Ne.symm h]

/-- `absFound v k` is the last entry of `v` named `k`. -/
theorem absFound_apply (v : sudo_rs.sudoers.FoundAliases) (k : String) :
    absFound v k = v.val.foldl (fun r p => if p.1 = k then some p.2 else r) none := by
  rw [absFound, foldl_insert_apply]; rfl

theorem absFound_push (v : sudo_rs.sudoers.FoundAliases) (v' : sudo_rs.sudoers.FoundAliases)
    (k : String) (b : Bool) (h : v'.val = v.val ++ [(k, b)]) :
    absFound v' = (absFound v).insert k b := by
  simp [absFound, h, List.foldl_append]

theorem absFound_empty (v : sudo_rs.sudoers.FoundAliases) (h : v.val = []) :
    absFound v = SudoersSpec.FoundAliases.empty := by
  simp [absFound, h]

end SudoRsProofs
