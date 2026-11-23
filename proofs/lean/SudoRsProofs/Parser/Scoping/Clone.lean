import SudoRsProofs.Defaults.Range
import SudoRsProofs.Tags

/-!
# `Settings::clone` is the identity

`Sudoers::check` stores a clone of the effective settings in the judgement. In the model every
component clone is the identity: `bool`/`u64` clones, the `Defaults` enumerations, `Box<str>`
(the bytes are copied, boxes erased), and `HashSet<String>` (the key list is cloned element by
element). This file proves the identity so the judgement's settings abstract to the same
`SudoersSpec.Settings` and keep `SettingsInRange`.
-/

open Aeneas Aeneas.Std Result
open sudo_rs
open SudoersSpec.Settings (StrSet)

namespace SudoRsProofs.Parser.Scoping

/-- `mapM` of the identity over `Result` is the identity. -/
theorem mapM_ok_id (l : List String) :
    l.mapM (m := Result) (fun x => ok x) = ok l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.mapM_cons, ih, Functor.map]

/-- The model `HashSet<String>` clones to the same key list. -/
theorem hashSet_clone_eq (keys : RSet) :
    std.collections.hash.set.HashSet.Insts.CoreCloneClone.clone
        alloc.string.String.Insts.CoreCloneClone
        std.hash.random.RandomState.Insts.CoreCloneClone core.clone.CloneGlobal keys =
      ok keys := by
  simp only [std.collections.hash.set.HashSet.Insts.CoreCloneClone.clone]
  change List.mapM (fun x => ok x) keys = ok keys
  exact mapM_ok_id keys

/-- `Option<Box<str>>` clones to itself. -/
@[simp] theorem option_boxstr_clone_eq (o : Option Str) :
    core.option.Option.Insts.CoreCloneClone.clone
        (BoxStr.Insts.CoreCloneClone core.clone.CloneGlobal) o = ok o :=
  Option.clone_eq _ (fun _ => rfl) o

/-- **`Settings::clone` is the identity.** -/
theorem settings_clone_eq (s : defaults.Settings) :
    defaults.Settings.Insts.CoreCloneClone.clone s = ok s := by
  simp [defaults.Settings.Insts.CoreCloneClone.clone,
    core.clone.impls.CloneBool.clone, core.clone.impls.CloneU64.clone,
    defaults.enums.lecture.Insts.CoreCloneClone.clone,
    defaults.enums.verifypw.Insts.CoreCloneClone.clone,
    defaults.enums.timestamp_type.Insts.CoreCloneClone.clone,
    BoxStr.Insts.CoreCloneClone.clone, alloc.string.String.Insts.CoreCloneClone.clone,
    option_boxstr_clone_eq, hashSet_clone_eq, lift]

theorem settings_clone_eq' (s : defaults.Settings) :
    ∃ s', defaults.Settings.Insts.CoreCloneClone.clone s = ok s' ∧ s' = s :=
  ⟨s, settings_clone_eq s, rfl⟩

end SudoRsProofs.Parser.Scoping
