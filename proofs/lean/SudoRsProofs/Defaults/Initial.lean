import SudoRsProofs.Defaults.Apply

/-!
# `Settings::default()`

The extracted initializer reserves space and inserts the table entries in order. The external
`HashSet` model prepends new keys, so the three list representatives are the reverse of the
spec's declaration-order defaults. As sets they have exactly the same members.
-/

open Aeneas Aeneas.Std Result sudo_rs

namespace SudoRsProofs.Defaults

private abbrev d := SudoersSpec.Settings.Settings.default

/-- `Settings.default` in the list order produced by the extracted hash-set model. -/
def initialModel : SudoersSpec.Settings.Settings :=
  { d with env_keep := d.env_keep.reverse, env_check := d.env_check.reverse,
           env_delete := d.env_delete.reverse }

private theorem intMul300 : 5#u64 * 60#u64 = ok 300#u64 := rfl
private theorem intMul900 : 15#u64 * 60#u64 = ok 900#u64 := rfl

private theorem small_succ (i : Usize) (hi : i.val ≤ 36) :
    i + 1#usize = ok (UScalar.ofNatCore (i.val + 1) (by scalar_tac)) := by
  obtain ⟨j, hj, hv⟩ := exists_eq_ok_of_spec (Usize.add_spec (x := i) (y := 1#usize)
    (by scalar_tac))
  rw [hj]
  congr 1
  apply UScalar.val_eq_imp
  simpa using hv

private theorem lenKeep : defaults.DefaultSettings.default.LEN = ok 11#usize := by
  simp [defaults.DefaultSettings.default.LEN, small_succ]

private theorem lenCheck : defaults.DefaultSettings.default.LEN_1 = ok 7#usize := by
  simp [defaults.DefaultSettings.default.LEN_1, small_succ]

private theorem lenDelete : defaults.DefaultSettings.default.LEN_2 = ok 37#usize := by
  simp [defaults.DefaultSettings.default.LEN_2, small_succ]

private theorem model_insert (s : RSet) (k : String) :
    std.collections.hash.set.HashSet.insert alloc.string.String.Insts.CoreCmpEq
      alloc.string.String.Insts.CoreHashHash
      std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher s k =
      ok (!s.contains k, SudoersSpec.Settings.StrSet.insert s k) := by
  rw [Sanitize.hashSet_insert_eq _ _ _ (fun _ _ => rfl), strSet_insert_eq]
  by_cases h : k ∈ s <;> simp [h]

private theorem decodeLiteral (s : String) (h) :
    stringOfStr (toStr s h) = s := stringOfStr_of_val (toStr_val s h)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
/-- The constructor returns the settings of the table, with the extracted list representatives. -/
theorem default_eq : ∃ s, defaults.Settings.Insts.CoreDefaultDefault.default = ok s ∧
    absSettings s = initialModel := by
  simp only [defaults.Settings.Insts.CoreDefaultDefault.default, intMul300, intMul900,
    core.convert.IntoFrom.into, BoxStr.Insts.CoreConvertFromShared0Str.from, lenKeep, lenCheck,
    lenDelete, std.collections.hash.set.HashSetTRandomStateGlobal.with_capacity,
    std.collections.hash.set.HashSetTRandomStateGlobal.new,
    alloc.string.String.Insts.CoreConvertFromShared0Str.from, decodeLiteral, model_insert,
    Aeneas.Std.bind_ok, Aeneas.Std.uncurry]
  refine ⟨_, rfl, ?_⟩
  simp only [absSettings, initialModel, SudoersSpec.Settings.Settings.default,
    defaults.SYSTEM_EDITOR, decodeLiteral, absLecture, absVerifypw, absTimestampType]
  rfl

/-- The defaults' list fields agree with the specification as sets. -/
theorem initialModel_sets :
    SudoersSpec.Settings.StrSet.Equiv initialModel.env_keep d.env_keep ∧
    SudoersSpec.Settings.StrSet.Equiv initialModel.env_check d.env_check ∧
    SudoersSpec.Settings.StrSet.Equiv initialModel.env_delete d.env_delete := by
  exact ⟨fun _ => List.mem_reverse, fun _ => List.mem_reverse, fun _ => List.mem_reverse⟩

theorem default_inRange {s : defaults.Settings}
    (h : defaults.Settings.Insts.CoreDefaultDefault.default = ok s) : SettingsInRange s := by
  obtain ⟨v, hv, ha⟩ := default_eq
  have e : v = s := by simpa only [Result.ok.injEq] using hv.symm.trans h
  subst v
  have hp := congrArg SudoersSpec.Settings.Settings.passwd_tries ha
  have hu := congrArg SudoersSpec.Settings.Settings.umask ha
  have hp' : s.passwd_tries.val = 3 := hp
  have hu' : s.umask.val = 18 := hu
  constructor
  · rw [hp', U16.max_eq]; decide
  · rw [hu', U32.max_eq]; decide

end SudoRsProofs.Defaults
