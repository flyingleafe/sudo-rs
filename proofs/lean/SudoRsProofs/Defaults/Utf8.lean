import SudoRsProofs.Defaults.Abs

/-!
# UTF-8 facts for the value parsers

The bytes of a `&str` made from a `String` (`t.val = stringBytes s`) are the spec's `bytes s`,
the concatenation of the encodings of the characters. In such an encoding the byte after an
ASCII byte starts a character or is the end, so `str::split_at` just after an ASCII byte does
not panic (`strIsCharBoundary_after_ascii`). Proved from Lean's definition of the encoding
(`String.utf8EncodeChar`), no hypothesis.
-/

open Aeneas Aeneas.Std Result

namespace SudoRsProofs.Defaults

/-- The byte values of the encoding of a character. -/
def encNat (c : Char) : List Nat := (String.utf8EncodeChar c).map UInt8.toNat

theorem bytes_eq_flatMap (s : String) :
    SudoersSpec.Settings.bytes s = s.toList.flatMap encNat := by
  conv => lhs; rw [← String.ofList_toList (s := s)]
  simp only [SudoersSpec.Settings.bytes, String.toByteArray_ofList, List.utf8Encode,
    List.toList_data_toByteArray, List.map_flatMap]
  rfl

/-- The bytes of a `&str` holding a string's encoding, as numbers, are `bytes`. -/
theorem val_map_eq_bytes {t : Str} {s : String} (h : t.val = sudo_rs.stringBytes s) :
    t.val.map (·.val) = SudoersSpec.Settings.bytes s := by
  rw [h]
  simp only [sudo_rs.stringBytes, SudoersSpec.Settings.bytes, List.map_map]
  apply List.map_congr_left
  intro b _
  rfl

/-- The shape of a character's encoding: a first byte that is not a continuation byte, the
other bytes continuation bytes (`≥ 0x80`), and a single byte exactly when it is ASCII. -/
theorem encNat_shape (c : Char) : ∃ b rest, encNat c = b :: rest ∧ (b < 0x80 ∨ 0xC0 ≤ b) ∧
    (b < 0x80 → rest = []) ∧ ∀ x ∈ rest, 0x80 ≤ x := by
  unfold encNat String.utf8EncodeChar
  generalize c.val.toNat = v
  dsimp only
  split
  · exact ⟨_, _, rfl, by simp; omega, by simp, by simp⟩
  · split
    · refine ⟨_, _, rfl, ?_, ?_, ?_⟩ <;> simp [UInt8.toNat_ofNat] <;> omega
    · split
      · refine ⟨_, _, rfl, ?_, ?_, ?_⟩ <;> simp [UInt8.toNat_ofNat] <;> omega
      · refine ⟨_, _, rfl, ?_, ?_, ?_⟩ <;> simp [UInt8.toNat_ofNat] <;> omega

theorem flatMap_head (c : Char) (l : List Char) :
    ∃ h : 0 < ((c :: l).flatMap encNat).length,
      ((c :: l).flatMap encNat)[0] < 0x80 ∨ 0xC0 ≤ ((c :: l).flatMap encNat)[0] := by
  obtain ⟨b, rest, he, hb, -, -⟩ := encNat_shape c
  simp only [List.flatMap_cons, he, List.cons_append, List.length_cons,
    List.getElem_cons_zero]
  exact ⟨by omega, hb⟩

/-- After an ASCII byte comes the end or a byte that starts a character. -/
theorem next_after_ascii (l : List Char) (i : Nat) (hi : i < (l.flatMap encNat).length)
    (hb : (l.flatMap encNat)[i] < 0x80) :
    i + 1 = (l.flatMap encNat).length ∨ ∃ h : i + 1 < (l.flatMap encNat).length,
      (l.flatMap encNat)[i + 1] < 0x80 ∨ 0xC0 ≤ (l.flatMap encNat)[i + 1] := by
  induction l generalizing i with
  | nil => simp at hi
  | cons c l ih =>
    obtain ⟨b, rest, he, hfirst, hsingle, hrest⟩ := encNat_shape c
    have hB : (c :: l).flatMap encNat = b :: (rest ++ l.flatMap encNat) := by
      simp [List.flatMap_cons, he]
    simp only [hB] at hi hb ⊢
    rcases i with _ | i
    · -- the ASCII byte is the first byte of `c`
      simp only [List.getElem_cons_zero] at hb
      have hr := hsingle hb
      subst hr
      simp only [List.nil_append, List.length_cons, Nat.zero_add]
      rcases l with _ | ⟨c', l'⟩
      · simp
      · obtain ⟨h0, hh⟩ := flatMap_head c' l'
        right
        exact ⟨by omega, by simpa using hh⟩
    · simp only [List.getElem_cons_succ, List.length_cons] at hb hi ⊢
      by_cases hir : i < rest.length
      · rw [List.getElem_append_left hir] at hb
        have := hrest _ (List.getElem_mem hir)
        omega
      · have hj : i - rest.length < (l.flatMap encNat).length := by
          simp only [List.length_append] at hi; omega
        rw [List.getElem_append_right (by omega)] at hb
        rcases ih (i - rest.length) hj hb with e | ⟨h1, h2⟩
        · left; simp only [List.length_append]; omega
        · right
          refine ⟨by simp only [List.length_append]; omega, ?_⟩
          rw [List.getElem_append_right (by omega)]
          have : i + 1 - rest.length = i - rest.length + 1 := by omega
          simpa [this] using h2

/-- **`str::split_at` just after an ASCII byte of a string's encoding does not panic.** -/
theorem strIsCharBoundary_after_ascii {t : Str} {s : String}
    (h : t.val = sudo_rs.stringBytes s) (i : Nat) (hi : i < t.val.length)
    (hb : (t.val[i]'hi).val < 0x80) : sudo_rs.strIsCharBoundary t (i + 1) = true := by
  have hm := val_map_eq_bytes h
  rw [bytes_eq_flatMap] at hm
  have hlen : t.val.length = (s.toList.flatMap encNat).length := by
    rw [← hm, List.length_map]
  have hget : ∀ j (hj : j < t.val.length), (t.val[j]'hj).val =
      (s.toList.flatMap encNat)[j]'(hlen ▸ hj) := by
    intro j hj
    have := congrArg (·[j]?) hm
    simp only [List.getElem?_map, List.getElem?_eq_getElem hj,
      List.getElem?_eq_getElem (hlen ▸ hj), Option.map_some, Option.some.injEq] at this
    exact this
  have hb' := hget i hi ▸ hb
  unfold sudo_rs.strIsCharBoundary
  rcases next_after_ascii s.toList i (hlen ▸ hi) hb' with e | ⟨h1, h2⟩
  · have : i + 1 = t.length := by simp only [Slice.length]; omega
    simp [this]
  · have h1' : i + 1 < t.val.length := by omega
    rw [List.getElem?_eq_getElem h1']
    rw [← hget (i + 1) h1'] at h2
    rcases h2 with h2 | h2 <;> simp [h2]

end SudoRsProofs.Defaults
