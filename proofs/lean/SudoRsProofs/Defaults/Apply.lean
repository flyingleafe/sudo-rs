import SudoRsProofs.Defaults.Abs
import SudoRsProofs.SanitizeOrder

/-!
# `SettingsModifier::apply` and `build_list` refine the settings model

`apply_list` is proved against `SudoersSpec.Settings.applyList` with list equality: the list
model of `HashSet` (`insert` prepends a new key, `remove` filters) is exactly the spec's
`StrSet.insert`/`StrSet.remove`. No hypothesis.
-/

open Aeneas Aeneas.Std Result
open sudo_rs
open SudoersSpec.Settings (StrSet)

namespace SudoRsProofs.Defaults

/-! ## The set operations -/

theorem filterAuxM_ok {α : Type} (p : α → Bool) (l acc : List α) :
    List.filterAuxM (m := Result) (fun x => ok (p x)) l acc = ok ((l.filter p).reverse ++ acc) := by
  induction l generalizing acc with
  | nil => rfl
  | cons a l ih =>
    simp only [List.filterAuxM, ih, List.filter_cons]
    cases p a <;> simp

theorem filterM_ok {α : Type} (p : α → Bool) (l : List α) :
    l.filterM (m := Result) (fun x => ok (p x)) = ok (l.filter p) := by
  simp only [List.filterM, filterAuxM_ok, List.append_nil, bind_tc_ok, List.reverse_reverse]
  rfl

theorem strSet_insert_eq (s : StrSet) (x : String) :
    StrSet.insert s x = if x ∈ s then s else x :: s := by
  simp [StrSet.insert]

theorem insert_eq (set : RSet) (k : String) :
    ∃ b, std.collections.hash.set.HashSet.insert alloc.string.String.Insts.CoreCmpEq
      alloc.string.String.Insts.CoreHashHash
      std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher set k =
      ok (b, StrSet.insert set k) := by
  rw [Sanitize.hashSet_insert_eq _ _ _ (fun a b => by
    simp [alloc.string.String.Insts.CoreCmpPartialEqString.eq]), strSet_insert_eq]
  by_cases h : k ∈ set <;> simp [h]

theorem remove_eq (set : RSet) (k : String) :
    ∃ b, std.collections.hash.set.HashSet.remove alloc.string.String.Insts.CoreCmpEq
      alloc.string.String.Insts.CoreHashHash
      std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher
      (core.borrow.Borrow.Blanket String) alloc.string.String.Insts.CoreHashHash
      alloc.string.String.Insts.CoreCmpEq set k =
      ok (b, StrSet.remove set k) := by
  unfold std.collections.hash.set.HashSet.remove
  have : (fun x : String => do
      let q ← (core.borrow.Borrow.Blanket String).borrow x
      let same ← alloc.string.String.Insts.CoreCmpEq.partialEqInst.eq q k
      ok (!same)) = fun x => ok (!(x == k)) := by
    funext x
    simp [core.borrow.Borrow.Blanket.borrow, alloc.string.String.Insts.CoreCmpPartialEqString.eq]
  rw [this, filterM_ok]
  exact ⟨(List.filter (fun x => !x == k) set).length != set.length, by
    simp [StrSet.remove]⟩

/-! ## The loops of `apply_list` -/

theorem next_nil {T : Type} (it : alloc.vec.into_iter.IntoIter T) (h : it.val = []) :
    alloc.vec.into_iter.IteratorIntoIter.next it = ok (none, it) := by
  unfold alloc.vec.into_iter.IteratorIntoIter.next
  split
  · rfl
  · rename_i h'; rw [h] at h'; cases h'

theorem next_cons {T : Type} (it : alloc.vec.into_iter.IntoIter T) (hd : T) (tl : List T)
    (h : it.val = hd :: tl) :
    ∃ it' : alloc.vec.into_iter.IntoIter T, it'.val = tl ∧
      alloc.vec.into_iter.IteratorIntoIter.next it = ok (some hd, it') := by
  unfold alloc.vec.into_iter.IteratorIntoIter.next
  split
  · rename_i h'; rw [h] at h'; cases h'
  · rename_i hd' tl' h'
    rw [h] at h'
    simp only [List.cons.injEq] at h'
    obtain ⟨rfl, rfl⟩ := h'
    exact ⟨_, by simp, rfl⟩

theorem loop0_eq (l : List String) : ∀ (it : alloc.vec.into_iter.IntoIter String) (s : RSet),
    it.val = l → sudo_rs.defaults.apply_list_loop0 it s = ok (l.foldl StrSet.insert s) := by
  induction l with
  | nil =>
    intro it s h
    unfold sudo_rs.defaults.apply_list_loop0
    simp [next_nil it h]
  | cons a l ih =>
    intro it s h
    unfold sudo_rs.defaults.apply_list_loop0
    obtain ⟨b, hb⟩ := insert_eq s a
    obtain ⟨it', hit', hn⟩ := next_cons it a l h
    simp [hn, hb, ih it' _ hit']

theorem loop1_eq (l : List String) : ∀ (it : alloc.vec.into_iter.IntoIter String) (s : RSet),
    it.val = l → sudo_rs.defaults.apply_list_loop1 it s = ok (l.foldl StrSet.insert s) := by
  induction l with
  | nil =>
    intro it s h
    unfold sudo_rs.defaults.apply_list_loop1
    simp [next_nil it h]
  | cons a l ih =>
    intro it s h
    unfold sudo_rs.defaults.apply_list_loop1
    obtain ⟨b, hb⟩ := insert_eq s a
    obtain ⟨it', hit', hn⟩ := next_cons it a l h
    simp [hn, hb, ih it' _ hit']

theorem loop2_eq (l : List String) : ∀ (it : alloc.vec.into_iter.IntoIter String) (s : RSet),
    it.val = l → sudo_rs.defaults.apply_list_loop2 it s = ok (l.foldl StrSet.remove s) := by
  induction l with
  | nil =>
    intro it s h
    unfold sudo_rs.defaults.apply_list_loop2
    simp [next_nil it h]
  | cons a l ih =>
    intro it s h
    unfold sudo_rs.defaults.apply_list_loop2
    obtain ⟨b, hb⟩ := remove_eq s a
    obtain ⟨it', hit', hn⟩ := next_cons it a l h
    simp [hn, hb, ih it' _ hit']

/-- **`apply_list` is `applyList`.** -/
theorem apply_list_eq (s : RSet) (mode : sudo_rs.defaults.ListMode)
    (items : alloc.vec.Vec String) :
    sudo_rs.defaults.apply_list s mode items =
      ok (SudoersSpec.Settings.applyList s (absChange (mode, items))) := by
  cases mode
  · have h : sudo_rs.defaults.apply_list s .Set items =
        sudo_rs.defaults.apply_list_loop0 items [] := by
      unfold sudo_rs.defaults.apply_list
      simp only [std.collections.hash.set.HashSetTRandomStateGlobal.new,
        alloc.vec.IntoIteratorVec.into_iter, bind_ok]
      exact bind_ok _ _
    rw [h, loop0_eq items.val items _ rfl]; rfl
  · have h : sudo_rs.defaults.apply_list s .Add items =
        sudo_rs.defaults.apply_list_loop1 items s := by
      unfold sudo_rs.defaults.apply_list
      simp only [alloc.vec.IntoIteratorVec.into_iter]
      exact bind_ok _ _
    rw [h, loop1_eq items.val items _ rfl]; rfl
  · have h : sudo_rs.defaults.apply_list s .Del items =
        sudo_rs.defaults.apply_list_loop2 items s := by
      unfold sudo_rs.defaults.apply_list
      simp only [alloc.vec.IntoIteratorVec.into_iter]
      exact bind_ok _ _
    rw [h, loop2_eq items.val items _ rfl]; rfl

/-! ## `apply` -/

/-- **`SettingsModifier::apply` refines `SettingsModifier.apply`**: it returns `ok`, and the
result abstracts to the spec's effect of the abstracted modifier. -/
theorem apply_eq (m : sudo_rs.defaults.SettingsModifier) (s : sudo_rs.defaults.Settings) :
    ∃ s', sudo_rs.defaults.SettingsModifier.apply m s = ok s' ∧
      absSettings s' = (absModifier m).apply (absSettings s) := by
  cases m with
  | env_keep v =>
    rcases v with ⟨mode, items⟩
    let c := SudoersSpec.Settings.applyList s.env_keep (absChange (mode, items))
    refine ⟨{ s with env_keep := c }, ?_, rfl⟩
    simp only [sudo_rs.defaults.SettingsModifier.apply, apply_list_eq, bind_ok]; rfl
  | env_check v =>
    rcases v with ⟨mode, items⟩
    let c := SudoersSpec.Settings.applyList s.env_check (absChange (mode, items))
    refine ⟨{ s with env_check := c }, ?_, rfl⟩
    simp only [sudo_rs.defaults.SettingsModifier.apply, apply_list_eq, bind_ok]; rfl
  | env_delete v =>
    rcases v with ⟨mode, items⟩
    let c := SudoersSpec.Settings.applyList s.env_delete (absChange (mode, items))
    refine ⟨{ s with env_delete := c }, ?_, rfl⟩
    simp only [sudo_rs.defaults.SettingsModifier.apply, apply_list_eq, bind_ok]; rfl
  | _ => exact ⟨_, rfl, rfl⟩

/-- **`build_list` refines `buildList`.** -/
theorem build_list_eq (id : sudo_rs.defaults.ListSetting) (mode : sudo_rs.defaults.ListMode)
    (items : alloc.vec.Vec String) :
    ∃ m, sudo_rs.defaults.build_list id mode items = ok m ∧
      absModifier m = SudoersSpec.Settings.buildList (absListSetting id) (absListMode mode)
        items.val := by
  cases id <;> exact ⟨_, rfl, rfl⟩

end SudoRsProofs.Defaults
