import SudoRsProofs.Parser.P2Oracle
import SudoRsProofs.Parser.Words

/-! The indexed loops used by `Command::construct` after splitting the input into word
ranges. The bounds use natural lengths; the postconditions describe the logical words, not
another scanner. -/

open Aeneas Aeneas.Std Result
open SudoersSpec.Syntax (Oracles utf8Len)

namespace SudoRsProofs.Parser

abbrev WordRange := Usize × Usize

def rangeChars (text : Slice Char) (r : WordRange) : List Char :=
  (text.val.drop r.1.val).take (r.2.val - r.1.val)

private theorem utf8Len_ofList (cs : List Char) :
    (String.ofList cs).utf8ByteSize = utf8Len cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [String.ofList_cons, String.utf8ByteSize_append, String.utf8ByteSize_singleton, ih,
      utf8Len_cons]

theorem utf8Len_toList (s : String) : s.utf8ByteSize = utf8Len s.toList := by
  simpa only [String.ofList_toList] using utf8Len_ofList s.toList

/-- Slicing at character boundaries cannot increase the UTF-8 byte length. -/
theorem rangeChars_utf8ByteSize_le (text : Slice Char) (r : WordRange) :
    (String.ofList (rangeChars text r)).utf8ByteSize ≤ utf8Len text.val := by
  have budget (xs : List Char) (n : Nat) :
      utf8Len (xs.take n) ≤ utf8Len xs ∧ utf8Len (xs.drop n) ≤ utf8Len xs := by
    have he := congrArg utf8Len (List.take_append_drop n xs)
    rw [utf8Len_append] at he
    omega
  rw [utf8Len_ofList]
  exact (budget _ _).1.trans (budget _ _).2

def WordInBounds (text : Slice Char) (r : WordRange) : Prop :=
  r.1.val < r.2.val ∧ r.2.val ≤ text.val.length

def argGlobChar (c : Char) : Bool := c == '?' || c == '*' || c == '['

theorem rangeChars_length {text : Slice Char} {r : WordRange} (h : WordInBounds text r) :
    (rangeChars text r).length = r.2.val - r.1.val := by
  rw [rangeChars, List.length_take_of_le]
  simpa [List.length_drop] using Nat.sub_le_sub_right h.2 r.1.val

theorem rangeChars_nonempty {text : Slice Char} {r : WordRange} (h : WordInBounds text r) :
    rangeChars text r ≠ [] := by
  intro he
  have hl := rangeChars_length h
  rw [he] at hl
  have := h.1
  simp at hl
  omega

theorem rangeChars_eq_cons (text : Slice Char) (start stop : Usize)
    (h : WordInBounds text (start, stop)) :
    rangeChars text (start, stop) = text.val[start.val]'(Nat.lt_of_lt_of_le h.1 h.2) ::
      (text.val.drop (start.val + 1)).take (stop.val - (start.val + 1)) := by
  unfold rangeChars
  rw [List.drop_eq_getElem_cons (Nat.lt_of_lt_of_le h.1 h.2 : start.val < text.val.length)]
  have hlt : start.val < stop.val := h.1
  have he : stop.val - start.val = stop.val - (start.val + 1) + 1 := by omega
  rw [he, List.take_succ_cons]

theorem sliceIndex_eq {α : Type} (s : Slice α) (i : Usize) (hi : i.val < s.val.length) :
    Slice.index_usize s i = ok s.val[i.val] := eq_ok_of_spec (Slice.index_usize_spec s i hi)

theorem vecIndex_eq {α : Type} (s : alloc.vec.Vec α) (i : Usize) (hi : i.val < s.val.length) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) s i = ok s.val[i.val] := by
  rw [alloc.vec.Vec.index_slice_index]
  exact eq_ok_of_spec (alloc.vec.Vec.index_usize_spec s i hi)

theorem usizeAdd_eq (a b : Usize) (h : a.val + b.val ≤ Usize.max) :
    ∃ r : Usize, a + b = ok r ∧ r.val = a.val + b.val :=
  exists_eq_ok_of_spec (UScalar.add_spec (by scalar_tac))

theorem usizeSub_eq (a b : Usize) (h : b.val ≤ a.val) :
    ∃ r : Usize, a - b = ok r ∧ r.val = a.val - b.val :=
  by
    obtain ⟨r, hr, he, _⟩ := exists_eq_ok_of_spec (UScalar.sub_spec (x := a) (y := b) h)
    exact ⟨r, hr, he⟩

private theorem has_glob_char_loop_eq (text : Slice Char) (i stop : Usize)
    (hstop : stop.val ≤ text.val.length) (found : Bool) :
    sudo_rs.sudoers.tokens.has_glob_char_loop text i stop found =
      ok (found || (rangeChars text (i, stop)).any argGlobChar) := by
  rw [sudo_rs.sudoers.tokens.has_glob_char_loop]
  cases found
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_or]
    by_cases hi : i < stop
    · have hi' : i.val < stop.val := by scalar_tac
      have htxt := Nat.lt_of_lt_of_le hi' hstop
      obtain ⟨j, hj, hjv⟩ := usizeAdd_eq i 1#usize (by have := text.property; scalar_tac)
      have hstep : j.val = i.val + 1 := by simpa using hjv
      have step := rangeChars_eq_cons text i stop ⟨hi', hstop⟩
      rw [step]
      simp only [hi, ↓reduceIte, sliceIndex_eq text i htxt, bind_ok, hj]
      have hpred : (if text.val[i.val] = '?' then true else if text.val[i.val] = '*' then true
          else if text.val[i.val] = '[' then true else false) = argGlobChar text.val[i.val] := by
        unfold argGlobChar
        split_ifs <;> simp_all
      have hbind : (if text.val[i.val] = '?' then ok true else if text.val[i.val] = '*' then ok true
          else if text.val[i.val] = '[' then ok true else ok false) =
          ok (argGlobChar text.val[i.val]) := by
        rw [← hpred]; split_ifs <;> rfl
      rw [hbind, bind_ok, has_glob_char_loop_eq text j stop hstop]
      simp [rangeChars, hstep]
    · have : stop.val ≤ i.val := by scalar_tac
      simp [hi, rangeChars, Nat.sub_eq_zero_of_le this]
  · simp
termination_by stop.val - i.val
decreasing_by omega

theorem has_glob_char_eq (text : Slice Char) (r : WordRange) (h : r.2.val ≤ text.val.length) :
    sudo_rs.sudoers.tokens.has_glob_char text r.1 r.2 =
      ok ((rangeChars text r).any argGlobChar) := by
  simpa [sudo_rs.sudoers.tokens.has_glob_char] using has_glob_char_loop_eq text r.1 r.2 h false

/-- The interval of logical words selected by the argument loops. -/
def rangeWords (text : Slice Char) (words : Slice WordRange) (start stop : Usize) :
    List (List Char) :=
  ((words.val.drop start.val).take (stop.val - start.val)).map (rangeChars text)

private theorem rangeWords_eq_cons {text : Slice Char} {words : Slice WordRange}
    {i j stop : Usize} (hi : i.val < stop.val) (hs : stop.val ≤ words.val.length)
    (hj : j.val = i.val + 1) :
    rangeWords text words i stop = rangeChars text (words.val[i.val]'(Nat.lt_of_lt_of_le hi hs)) ::
      rangeWords text words j stop := by
  unfold rangeWords
  rw [List.drop_eq_getElem_cons (Nat.lt_of_lt_of_le hi hs : i.val < words.val.length)]
  have he : stop.val - i.val = (stop.val - j.val) + 1 := by omega
  rw [he, List.take_succ_cons, List.map_cons, hj]

private theorem any_glob_loop_eq (text : Slice Char) (words : Slice WordRange) (i stop : Usize)
    (hs : stop.val ≤ words.val.length) (hw : ∀ r ∈ words.val, WordInBounds text r)
    (found : Bool) :
    sudo_rs.sudoers.tokens.any_glob_loop text words stop found i =
      ok (found || (rangeWords text words i stop).any (·.any argGlobChar)) := by
  rw [sudo_rs.sudoers.tokens.any_glob_loop]
  cases found
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_or]
    by_cases hi : i < stop
    · have hi' : i.val < stop.val := by scalar_tac
      have hib := Nat.lt_of_lt_of_le hi' hs
      let r := words.val[i.val]
      have hr := hw r (List.getElem_mem hib)
      obtain ⟨j, hj, hjv⟩ := usizeAdd_eq i 1#usize (by have := words.property; scalar_tac)
      have hstep : j.val = i.val + 1 := by simpa using hjv
      have e := has_glob_char_eq text r hr.2
      rw [rangeWords_eq_cons hi' hs hstep]
      simp only [hi, ↓reduceIte, sliceIndex_eq words i hib, bind_ok,
        ← show r = words.val[i.val] from rfl, List.any_cons]
      change Aeneas.Std.bind (sudo_rs.sudoers.tokens.has_glob_char text r.1 r.2)
        (fun found1 => Aeneas.Std.bind (i + 1#usize)
          (fun next => sudo_rs.sudoers.tokens.any_glob_loop text words stop found1 next)) = _
      simp only [e, bind_ok, hj, any_glob_loop_eq text words j stop hs hw]
    · have : stop.val ≤ i.val := by scalar_tac
      simp [hi, rangeWords, Nat.sub_eq_zero_of_le this]
  · simp
termination_by stop.val - i.val
decreasing_by omega

theorem any_glob_eq (text : Slice Char) (words : Slice WordRange) (stop : Usize)
    (hs : stop.val ≤ words.val.length) (hw : ∀ r ∈ words.val, WordInBounds text r) :
    sudo_rs.sudoers.tokens.any_glob text words stop =
      ok ((rangeWords text words 1#usize stop).any (·.any argGlobChar)) := by
  simpa [sudo_rs.sudoers.tokens.any_glob] using any_glob_loop_eq text words 1#usize stop hs hw false

private theorem os_strings_loop_eq {A : GlobAbs} {O : Oracles} (hO : P2Oracle A O)
    (text : Slice Char) (htext : utf8Len text.val ≤ Usize.max)
    (words : Slice WordRange) (stop : Usize)
    (hs : stop.val ≤ words.val.length) (hw : ∀ r ∈ words.val, WordInBounds text r)
    (acc : alloc.vec.Vec std.ffi.os_str.OsString) (i : Usize)
    (hb : acc.val.length + (stop.val - i.val) ≤ Usize.max) :
    ∃ v, sudo_rs.sudoers.tokens.os_strings_loop text words stop acc i = ok v ∧
      v.val.map A.os = acc.val.map A.os ++ (rangeWords text words i stop).map String.ofList := by
  rw [sudo_rs.sudoers.tokens.os_strings_loop]
  by_cases hi : i < stop
  · have hi' : i.val < stop.val := by scalar_tac
    have hib := Nat.lt_of_lt_of_le hi' hs
    let r := words.val[i.val]
    have hr := hw r (List.getElem_mem hib)
    have he : sudo_rs.sudoers.tokens.word_text text r.1 r.2 =
        ok (String.ofList (rangeChars text r)) := word_text_eq text r.1 r.2 hr.2
    obtain ⟨os, hos, _, ha⟩ := hO.os_string (String.ofList (rangeChars text r))
      ((rangeChars_utf8ByteSize_le text r).trans htext)
    obtain ⟨acc', hpush, hpv⟩ := exists_eq_ok_of_spec
      (alloc.vec.Vec.push_spec acc os (by omega))
    obtain ⟨j, hj, hjv⟩ := usizeAdd_eq i 1#usize (by have := words.property; scalar_tac)
    have hstep : j.val = i.val + 1 := by simpa using hjv
    have hb' : acc'.val.length + (stop.val - j.val) ≤ Usize.max := by simp [hpv]; omega
    obtain ⟨v, ev, hv⟩ := os_strings_loop_eq hO text htext words stop hs hw acc' j hb'
    refine ⟨v, ?_, ?_⟩
    · simp only [hi, ↓reduceIte, sliceIndex_eq words i hib, bind_ok]
      change (do
        let w ← sudo_rs.sudoers.tokens.word_text text r.1 r.2
        let bytes ← sudoers.tokens.os_string w
        let xs ← alloc.vec.Vec.push acc bytes
        let j' ← i + 1#usize
        sudo_rs.sudoers.tokens.os_strings_loop text words stop xs j') = ok v
      simpa only [he, hos, hpush, hj, bind_ok] using ev
    · rw [hv, hpv, rangeWords_eq_cons hi' hs hstep]
      simp [ha, r]
  · have hge : stop.val ≤ i.val := by scalar_tac
    exact ⟨acc, by simp [hi], by simp [rangeWords, Nat.sub_eq_zero_of_le hge]⟩
termination_by stop.val - i.val
decreasing_by omega

theorem os_strings_eq {A : GlobAbs} {O : Oracles} (hO : P2Oracle A O)
    (text : Slice Char) (htext : utf8Len text.val ≤ Usize.max)
    (words : Slice WordRange) (stop : Usize)
    (hpos : 1 ≤ stop.val) (hs : stop.val ≤ words.val.length)
    (hw : ∀ r ∈ words.val, WordInBounds text r) :
    ∃ v, sudo_rs.sudoers.tokens.os_strings text words stop = ok v ∧
      v.val.map A.os = (rangeWords text words 1#usize stop).map String.ofList := by
  obtain ⟨n, hn, _⟩ := usizeSub_eq stop 1#usize (by simpa using hpos)
  let v := alloc.vec.Vec.with_capacity std.ffi.os_str.OsString n
  have hv : v.val = [] := rfl
  obtain ⟨v', e, h⟩ := os_strings_loop_eq hO text htext words stop hs hw v 1#usize (by
    have := words.property
    simp [hv]; omega)
  exact ⟨v', by simpa [sudo_rs.sudoers.tokens.os_strings, hn, v] using e, by simpa [hv] using h⟩

end SudoRsProofs.Parser
