import SudoRsProofs.Authorization
import SudoersSpec.EnvFilter

/-!
# The environment policy (`src/sudo/env/filter.rs`) refines `SudoersSpec.EnvFilter`

The extraction of `wildcard_match`, `should_keep` and `keep_inherited` (and of every helper
they call) is proved equal to the specification, for every input:

* `wildcard_match_eq`: `wildcard_match test pattern` returns `wildcard starByte` of the bytes;
  it never panics, never overflows and terminates (the greedy loop refines
  `SudoersSpec.EnvFilter.greedy`, which `greedy_correct` proves equal to `wildcard`);
* `in_table_eq`: the loop over the table visits every entry once (`table_next` model) and
  returns whether some entry matches;
* `is_safe_tz_eq`, `should_keep_eq`, `keep_inherited_eq`: the decision, for the zoneinfo
  directory `z` and the `PATH_MAX` value `pm` the system gives (`zoneinfo_path = ok z`,
  `path_max = ok pm`; both opaque, see `ASSUMPTIONS.md`), and for tables whose entries are
  Rust strings (`Fits`: at most `usize::MAX` bytes, true of every Rust `String`).

The decision is stated on `configOf (absRestrictions r)`: the `Restrictions` of the
authorization (`Authorization.lean`) read as policy input, so the chain from the sudoers text to
the authorization continues to the environment decision.

Bytes are read as `Nat`s (`vals`).
-/

open Aeneas Aeneas.Std Result
open sudo_rs
open SudoersSpec.EnvFilter

namespace SudoRsProofs.EnvFilter

/-! ## Abstraction and helpers -/

/-- The bytes of a Rust byte slice. -/
def vals (s : Slice U8) : Bytes := s.val.map (·.val)

@[simp] theorem length_vals (s : Slice U8) : (vals s).length = s.val.length := by
  simp [vals]

theorem u8_val_injective : Function.Injective (fun c : U8 => c.val) :=
  fun _ _ h => UScalar.eq_of_val_eq h

theorem u8_eq_iff_val {a b : U8} : a = b ↔ a.val = b.val :=
  ⟨fun h => h ▸ rfl, fun h => UScalar.eq_of_val_eq h⟩

private theorem add_one (i : Usize) (h : i.val < Usize.max) :
    ∃ j, i + 1#usize = ok j ∧ j.val = i.val + 1 := by
  obtain ⟨j, hj, hv⟩ := exists_eq_ok_of_spec
    (Usize.add_spec (x := i) (y := 1#usize) (by simp; omega))
  exact ⟨j, hj, by simpa using hv⟩

private theorem slice_len_le (s : Slice U8) : s.val.length ≤ Usize.max := s.property

/-- The bytes of a Rust `String`, as the specification reads them. -/
theorem vals_strOf (s : String) (h : Fits s) : vals (strOf s h) = utf8 s := by
  simp only [vals, strOf_val, sudo_rs.stringBytes, utf8, List.map_map]
  rfl

/-! ## `wildcard_match` -/

theorem wildcard_match_loop_done (test pattern : Slice U8)
    (s : sudo.env.wildcard_match.MatchState) (h : s.more = false) :
    sudo.env.wildcard_match.wildcard_match_loop test pattern s = ok s.matched := by
  unfold sudo.env.wildcard_match.wildcard_match_loop
  simp [h]

/-- The loop over `wildcard_step` refines `greedy` (on `U8`, with `*` = `42#u8`), state for
state, for every undecided state. -/
theorem wildcard_match_loop_eq (test pattern : Slice U8) (t p st sp : Usize) (star : Bool)
    (tn pn stn spn : Nat) (htn : t.val = tn) (hpn : p.val = pn) (hstn : st.val = stn)
    (hspn : sp.val = spn) (hst : stn ≤ tn) (ht : tn ≤ test.val.length) :
    sudo.env.wildcard_match.wildcard_match_loop test pattern
        (sudo.env.wildcard_match.MatchState.mk t p star st sp false true) =
      ok (greedy 42#u8 test.val pattern.val tn pn star stn spn hst ht) := by
  subst htn hpn hstn hspn
  have hT := slice_len_le test
  have hP := slice_len_le pattern
  unfold sudo.env.wildcard_match.wildcard_match_loop
  unfold sudo.env.wildcard_match.wildcard_step
  unfold greedy
  by_cases hp : p.val < pattern.val.length
  · have hpl : p < Slice.len pattern := by scalar_tac
    have hidxP := eq_ok_of_spec (Slice.index_usize_spec pattern p hp)
    obtain ⟨p1, hp1, hp1v⟩ := add_one p (by omega)
    by_cases htn : t.val < test.val.length
    · have htl : t < Slice.len test := by scalar_tac
      have hidxT := eq_ok_of_spec (Slice.index_usize_spec test t htn)
      obtain ⟨t1, ht1, ht1v⟩ := add_one t (by omega)
      by_cases hs : pattern.val[p.val] = 42#u8
      · -- a `*`: remember it
        have ih := wildcard_match_loop_eq test pattern t p1 t p1 true t.val (p.val + 1) t.val
          (p.val + 1) rfl hp1v rfl hp1v (Nat.le_refl _) ht
        simp only [hpl, htl, hidxP, hp1, hp, htn, bind_ok, ↓reduceIte, and_self]
        erw [ite_eq_left hs, bind_ok, ih]
        simp only [_root_.dite_true]
        erw [ite_eq_left hs]
      · by_cases hc : pattern.val[p.val] = test.val[t.val]
        · -- a literal match
          have ih := wildcard_match_loop_eq test pattern t1 p1 st sp star (t.val + 1)
            (p.val + 1) st.val sp.val ht1v hp1v rfl rfl (by omega) (by omega)
          simp only [hpl, htl, hidxP, hidxT, hp1, ht1, hp, htn, bind_ok, ↓reduceIte, and_self]
          erw [ite_eq_right hs, ite_eq_left hc, bind_ok, ih]
          simp only [_root_.dite_true]
          erw [ite_eq_right hs, ite_eq_left hc]
        · cases star with
          | false =>
            simp only [hpl, htl, hidxP, hidxT, hp, htn, bind_ok, ↓reduceIte, and_self]
            erw [ite_eq_right hs, ite_eq_right hc, bind_ok]
            simp only [_root_.dite_true]
            erw [ite_eq_right hs, ite_eq_right hc]
            simp [wildcard_match_loop_done]
          | true =>
            -- restart after the most recent `*`
            obtain ⟨s1, hs1, hs1v⟩ := add_one st (by omega)
            have ih := wildcard_match_loop_eq test pattern s1 sp s1 sp true (st.val + 1) sp.val
              (st.val + 1) sp.val hs1v rfl hs1v rfl (Nat.le_refl _) (by omega)
            simp only [hpl, htl, hidxP, hidxT, hs1, hp, htn, bind_ok, ↓reduceIte, and_self]
            erw [ite_eq_right hs, ite_eq_right hc, bind_ok, ih]
            simp only [_root_.dite_true]
            erw [ite_eq_right hs, ite_eq_right hc] <;> rfl
    · -- the input is exhausted
      have htl : ¬ t < Slice.len test := by scalar_tac
      by_cases hs : pattern.val[p.val] = 42#u8
      · have ih := wildcard_match_loop_eq test pattern t p1 st sp star t.val (p.val + 1) st.val
          sp.val rfl hp1v rfl rfl hst ht
        simp only [hpl, htl, hidxP, hp1, hp, htn, bind_ok, ↓reduceIte, and_false]
        erw [ite_eq_left hs, bind_ok, ih]
        simp only [_root_.dite_false, _root_.dite_true]
        erw [ite_eq_left hs]
      · simp only [hpl, htl, hidxP, hp, htn, bind_ok, ↓reduceIte, and_false]
        erw [ite_eq_right hs, bind_ok]
        simp only [_root_.dite_false, _root_.dite_true]
        erw [ite_eq_right hs]
        simp [wildcard_match_loop_done]
  · have hpl : ¬ p < Slice.len pattern := by scalar_tac
    by_cases htn : t.val < test.val.length
    · -- the pattern is exhausted, the input is not
      have htl : t < Slice.len test := by scalar_tac
      cases star with
      | false => simp [hpl, htl, hp, htn, wildcard_match_loop_done]
      | true =>
        obtain ⟨s1, hs1, hs1v⟩ := add_one st (by omega)
        have ih := wildcard_match_loop_eq test pattern s1 sp s1 sp true (st.val + 1) sp.val
          (st.val + 1) sp.val hs1v rfl hs1v rfl (Nat.le_refl _) (by omega)
        simp [hpl, htl, hs1, ih, hp, htn]
    · -- both exhausted: a match
      have htl : ¬ t < Slice.len test := by scalar_tac
      simp [hpl, htl, hp, htn, wildcard_match_loop_done]
termination_by (test.val.length + 1 - stn, test.val.length - tn + (pattern.val.length - pn))
decreasing_by
  all_goals
    first
    | (apply lex_lt; omega)
    | (simp_wf; apply lex_lt; omega)
    | (simp only [Prod.lex_def]; omega)
    | (simp_wf; simp only [Prod.lex_def]; omega)

/-- **`wildcard_match` is the wildcard match of the specification**, on `U8`. -/
theorem wildcard_match_eq_u8 (test pattern : Slice U8) :
    sudo.env.wildcard_match.wildcard_match test pattern =
      ok (wildcard 42#u8 test.val pattern.val) := by
  unfold sudo.env.wildcard_match.wildcard_match
  rw [wildcard_match_loop_eq test pattern 0#usize 0#usize 0#usize 0#usize false 0 0 0 0
    (by simp) (by simp) (by simp) (by simp) (Nat.le_refl 0) (Nat.zero_le _), greedy_correct]

/-- **`wildcard_match` is the wildcard match of the specification**, on the bytes. -/
theorem wildcard_match_eq (test pattern : Slice U8) :
    sudo.env.wildcard_match.wildcard_match test pattern =
      ok (wildcard starByte (vals test) (vals pattern)) := by
  rw [wildcard_match_eq_u8]
  have h := wildcard_map (fun c : U8 => c.val) u8_val_injective 42#u8 test.val pattern.val
  have hs : (42#u8 : U8).val = starByte := by simp [starByte]
  simp only [hs] at h
  simp only [vals]
  rw [h]

/-! ## Byte helpers -/

theorem starts_with_bytes_loop_eq (text pre : Slice U8)
    (hlen : pre.val.length ≤ text.val.length) (b : Bool) (i : Usize) :
    sudo.env.filter.starts_with_bytes_loop text pre b i =
      ok (b && ((vals pre).drop i.val).isPrefixOf ((vals text).drop i.val)) := by
  have hP := slice_len_le pre
  unfold sudo.env.filter.starts_with_bytes_loop
  cases b with
  | false => simp
  | true =>
    by_cases hi : i.val < pre.val.length
    · have hil : i < Slice.len pre := by scalar_tac
      have ht : i.val < text.val.length := by omega
      obtain ⟨j, hj, hjv⟩ := add_one i (by omega)
      have ih := starts_with_bytes_loop_eq text pre hlen
        (decide (text.val[i.val] = pre.val[i.val])) j
      have hd : ((vals pre).drop i.val).isPrefixOf ((vals text).drop i.val) =
          (decide (text.val[i.val] = pre.val[i.val]) &&
            ((vals pre).drop j.val).isPrefixOf ((vals text).drop j.val)) := by
        rw [hjv]
        simp only [vals, ← List.map_drop, List.drop_eq_getElem_cons hi,
          List.drop_eq_getElem_cons ht, List.map_cons, List.isPrefixOf_cons_cons]
        have hb : (pre.val[i.val].val == text.val[i.val].val) =
            decide (text.val[i.val] = pre.val[i.val]) := by
          by_cases he : text.val[i.val] = pre.val[i.val]
          · have hv : pre.val[i.val].val = text.val[i.val].val :=
              (congrArg UScalar.val he).symm
            rw [beq_iff_eq.mpr hv, decide_eq_true he]
          · have hv : pre.val[i.val].val ≠ text.val[i.val].val :=
              fun e => he (UScalar.eq_of_val_eq e).symm
            rw [beq_eq_false_iff_ne.mpr hv, decide_eq_false he]
        erw [hb]
      rw [hd]
      simp only [hil, eq_ok_of_spec (Slice.index_usize_spec text i ht),
        eq_ok_of_spec (Slice.index_usize_spec pre i hi), hj, bind_ok, ↓reduceIte, Bool.true_and]
      refine Eq.trans ?_ ih
      congr 1
    · have hil : ¬ i < Slice.len pre := by scalar_tac
      have hnil : (vals pre).drop i.val = [] :=
        List.drop_eq_nil_of_le (by rw [length_vals]; omega)
      simp [hil, hnil]
termination_by pre.val.length - i.val
decreasing_by all_goals scalar_tac

theorem starts_with_bytes_eq (text pre : Slice U8) :
    sudo.env.filter.starts_with_bytes text pre = ok ((vals pre).isPrefixOf (vals text)) := by
  unfold sudo.env.filter.starts_with_bytes
  by_cases h : pre.val.length ≤ text.val.length
  · have hl : Slice.len pre ≤ Slice.len text := by scalar_tac
    simp [hl, starts_with_bytes_loop_eq text pre h]
  · have hl : ¬ Slice.len pre ≤ Slice.len text := by scalar_tac
    have hf : (vals pre).isPrefixOf (vals text) = false := by
      cases hp : (vals pre).isPrefixOf (vals text)
      · rfl
      · have := (List.isPrefixOf_iff_prefix.mp hp).length_le
        simp only [length_vals] at this
        omega
    unfold sudo.env.filter.starts_with_bytes_loop
    simp [hl, hf]

theorem isPrefixOf_eq_beq {a b : Bytes} (h : a.length = b.length) :
    a.isPrefixOf b = (b == a) := by
  apply Bool.eq_iff_iff.mpr
  rw [List.isPrefixOf_iff_prefix, beq_iff_eq]
  constructor
  · intro hp
    exact (hp.eq_of_length h).symm
  · intro e
    rw [e]

theorem equals_bytes_eq (text word : Slice U8) :
    sudo.env.filter.equals_bytes text word = ok (vals text == vals word) := by
  unfold sudo.env.filter.equals_bytes
  by_cases h : text.val.length = word.val.length
  · have hl : Slice.len text = Slice.len word := UScalar.eq_of_val_eq (by simpa using h)
    have e := isPrefixOf_eq_beq (a := vals word) (b := vals text) (by simp [h])
    simp [hl, starts_with_bytes_eq, e]
  · have hl : ¬ Slice.len text = Slice.len word := fun e => h (by simpa using congrArg UScalar.val e)
    have hne : (vals text == vals word) = false := by
      simp only [beq_eq_false_iff_ne]
      intro e
      exact h (by simpa using congrArg List.length e)
    simp [hl, hne]

/-! ### `find_equals` -/

theorem find_equals_loop_done (t : Slice U8) (pos i : Usize) (h : pos.val ≠ t.length) :
    sudo.env.filter.find_equals_loop t pos i = ok pos := by
  unfold sudo.env.filter.find_equals_loop
  have h' : pos ≠ Slice.len t := by
    intro e
    exact h (by rw [e, Slice.len_val])
  simp [h']

theorem find_equals_loop_eq (t : Slice U8) :
    ∀ (d : Nat) (i : Usize), t.length - i.val = d → i.val ≤ t.length →
      ∃ j, sudo.env.filter.find_equals_loop t (Slice.len t) i = ok j ∧
        j.val = i.val + firstEq ((t.val.drop i.val).map (·.val)) := by
  intro d
  induction d with
  | zero =>
    intro i hd hi
    have h : i.val = t.length := by omega
    refine ⟨Slice.len t, ?_, ?_⟩
    · unfold sudo.env.filter.find_equals_loop
      simp [UScalar.lt_equiv, h]
    · rw [Slice.len_val, h]
      simp [Slice.length, firstEq]
  | succ d ih =>
    intro i hd hi
    have hlt : i.val < t.length := by omega
    obtain ⟨j, hj, hjv⟩ := add_one i (Nat.lt_of_lt_of_le hlt t.property)
    have hidx := eq_ok_of_spec (Slice.index_usize_spec t i hlt)
    have hdrop := List.drop_eq_getElem_cons hlt
    have hlt' : i < Slice.len t := by simpa [UScalar.lt_equiv] using hlt
    have hr :
        sudo.env.filter.find_equals_loop t (Slice.len t) i =
          sudo.env.filter.find_equals_loop t
            (if t.val[i.val] = 61#u8 then i else Slice.len t) j := by
      conv => lhs; unfold sudo.env.filter.find_equals_loop
      simp only [hlt', ↓reduceIte, hidx, bind_ok]
      by_cases h : t.val[i.val] = 61#u8
      · rw [ite_eq_left h]
        split
        · simp only [bind_ok, hj]
        · contradiction
      · rw [ite_eq_right h]
        split
        · contradiction
        · simp only [bind_ok, hj]
    rw [hr, hdrop, List.map_cons, firstEq]
    by_cases hb : t.val[i.val] = 61#u8
    · have hv : t.val[i.val].val = 61 := congrArg UScalar.val hb
      refine ⟨i, by simp [hb, find_equals_loop_done t i j (by omega)], ?_⟩
      split <;> omega
    · have hv : t.val[i.val].val ≠ 61 := fun h => hb (UScalar.val_eq_imp _ _ h)
      obtain ⟨k, hk, hkv⟩ := ih j (by omega) (by omega)
      refine ⟨k, by simpa [hb] using hk, ?_⟩
      rw [hkv, hjv]
      split <;> omega

theorem find_equals_eq (t : Slice U8) :
    ∃ j, sudo.env.filter.find_equals t = ok j ∧ j.val = firstEq (vals t) := by
  obtain ⟨j, h, hv⟩ := find_equals_loop_eq t _ 0#usize rfl (by simp)
  exact ⟨j, h, by simpa [vals] using hv⟩

theorem firstEq_le (l : Bytes) : firstEq l ≤ l.length := by
  induction l with
  | nil => simp [firstEq]
  | cons c r ih =>
    simp only [firstEq, List.length_cons]
    split <;> omega

/-! ### `contains_dotdot` -/

theorem hasDotDot_short (l : Bytes) (h : l.length ≤ 1) : hasDotDot l = false := by
  match l, h with
  | [], _ => rfl
  | [_], _ => rfl

theorem hasDotDot_drop (l : Bytes) (k : Nat) (h : k + 1 < l.length) :
    hasDotDot (l.drop k) =
      ((l[k] == 46 && l[k + 1] == 46) || hasDotDot (l.drop (k + 1))) := by
  rw [List.drop_eq_getElem_cons (by omega : k < l.length),
    List.drop_eq_getElem_cons (by omega : k + 1 < l.length), hasDotDot,
    ← List.drop_eq_getElem_cons (by omega : k + 1 < l.length)]

theorem contains_dotdot_loop_true (value : Slice U8) (i : Usize) :
    sudo.env.filter.contains_dotdot_loop value true i = ok true := by
  unfold sudo.env.filter.contains_dotdot_loop
  simp

theorem contains_dotdot_loop_eq (value : Slice U8) (i : Usize) (hi : 1 ≤ i.val) :
    sudo.env.filter.contains_dotdot_loop value false i =
      ok (hasDotDot ((vals value).drop (i.val - 1))) := by
  have hV := slice_len_le value
  unfold sudo.env.filter.contains_dotdot_loop
  by_cases hlt : i.val < value.val.length
  · have hil : i < Slice.len value := by scalar_tac
    obtain ⟨k, hk, hkv⟩ := exists_eq_ok_of_spec
      (Usize.sub_spec (x := i) (y := 1#usize) (by simp; omega))
    have hkv' : k.val = i.val - 1 := by simpa using hkv.1
    have hk' : k.val < value.val.length := by omega
    obtain ⟨j, hj, hjv⟩ := add_one i (by omega)
    have hidxK := eq_ok_of_spec (Slice.index_usize_spec value k hk')
    have hidxI := eq_ok_of_spec (Slice.index_usize_spec value i hlt)
    have e : i.val - 1 = k.val := by omega
    have hik : i.val = k.val + 1 := by omega
    rw [e, hasDotDot_drop (vals value) k.val (by simp only [length_vals]; omega)]
    simp only [List.getElem_map, vals]
    have hidxI' : value.val[k.val + 1] = value.val[i.val] := by simp [hik]
    have hd : (vals value).drop (j.val - 1) =
        (value.val.map (·.val)).drop (k.val + 1) := by
      rw [hjv, show i.val + 1 - 1 = k.val + 1 by omega]
      rfl
    have hhead (x : U8) : x = 46#u8 ↔ x.val = 46 := u8_eq_iff_val
    simp only [Bool.false_eq_true, if_false, hil, if_true, hk, hidxK, bind_ok, hj]
    by_cases d1 : value.val[k.val] = 46#u8
    · have v1 := (hhead _).mp d1
      simp only [d1, if_true, hidxI, bind_ok, hidxI', v1, beq_self_eq_true, Bool.true_and]
      by_cases d2 : value.val[i.val] = 46#u8
      · have v2 := (hhead _).mp d2
        erw [ite_eq_left d2, bind_ok]
        rw [contains_dotdot_loop_true]
        simp only [v2, show (46#u8 : U8).val = 46 from rfl, beq_self_eq_true,
          Bool.true_and, Bool.true_or]
      · have ih := contains_dotdot_loop_eq value j (by omega)
        rw [hd] at ih
        have v2 := mt (hhead _).mpr d2
        erw [ite_eq_right d2, bind_ok, ih]
        simp only [beq_eq_false_iff_ne.mpr v2, Bool.and_false, Bool.false_or]
    · have ih := contains_dotdot_loop_eq value j (by omega)
      rw [hd] at ih
      have v1 := mt (hhead _).mpr d1
      erw [ite_eq_right d1, bind_ok, ih]
      simp only [beq_eq_false_iff_ne.mpr v1, Bool.false_and, Bool.false_or]
  · have hil : ¬ i < Slice.len value := by scalar_tac
    have hs : hasDotDot ((vals value).drop (i.val - 1)) = false :=
      hasDotDot_short _ (by simp; omega)
    simp only [Bool.false_eq_true, ↓reduceIte, hil, hs]
termination_by value.val.length - i.val
decreasing_by all_goals omega

theorem contains_dotdot_eq (value : Slice U8) :
    sudo.env.filter.contains_dotdot value = ok (hasDotDot (vals value)) := by
  unfold sudo.env.filter.contains_dotdot
  rw [contains_dotdot_loop_eq value 1#usize (by simp)]
  simp

/-! ### Byte classes -/

/-- The byte class of the code, as a predicate on bytes. -/
def classPred : sudo.env.filter.ByteClass → Nat → Bool
  | .NotPrintable => notPrintable
  | .PercentOrSlash => percentOrSlash

theorem in_class_eq (c : U8) (k : sudo.env.filter.ByteClass) :
    sudo.env.filter.in_class c k = ok (classPred k c.val) := by
  have e1 : (33#u8 ≤ c) ↔ 33 ≤ c.val := by rw [UScalar.le_equiv]; simp
  have e2 : (c ≤ 126#u8) ↔ c.val ≤ 126 := by rw [UScalar.le_equiv]; simp
  have e3 : c = 37#u8 ↔ c.val = 37 := by rw [u8_eq_iff_val]; simp
  have e4 : c = 47#u8 ↔ c.val = 47 := by rw [u8_eq_iff_val]; simp
  cases k with
  | NotPrintable =>
    unfold sudo.env.filter.in_class
    simp only [e1, e2, classPred, notPrintable]
    by_cases a : 33 ≤ c.val <;> by_cases b : c.val ≤ 126 <;> simp [a, b]
  | PercentOrSlash =>
    unfold sudo.env.filter.in_class
    simp only [e3, e4, classPred, percentOrSlash]
    by_cases a : c.val = 37 <;> by_cases b : c.val = 47 <;> simp [a, b] <;> omega

theorem contains_class_loop_true (input : Slice U8) (k : sudo.env.filter.ByteClass)
    (i : Usize) : sudo.env.filter.contains_class_loop input k true i = ok true := by
  unfold sudo.env.filter.contains_class_loop
  simp

theorem contains_class_loop_eq (input : Slice U8) (k : sudo.env.filter.ByteClass) (i : Usize) :
    sudo.env.filter.contains_class_loop input k false i =
      ok (((vals input).drop i.val).any (classPred k)) := by
  have hV := slice_len_le input
  unfold sudo.env.filter.contains_class_loop
  by_cases hlt : i.val < input.val.length
  · have hil : i < Slice.len input := by scalar_tac
    obtain ⟨j, hj, hjv⟩ := add_one i (by omega)
    have hidx := eq_ok_of_spec (Slice.index_usize_spec input i hlt)
    have hd : (vals input).drop i.val =
        input.val[i.val].val :: (vals input).drop j.val := by
      rw [hjv]
      simp only [vals, ← List.map_drop, List.drop_eq_getElem_cons hlt, List.map_cons]
      rfl
    rw [hd, List.any_cons]
    simp only [Bool.false_eq_true, if_false, hil, if_true, hidx, bind_ok, in_class_eq, hj]
    by_cases hc : classPred k input.val[i.val].val = true
    · erw [ite_eq_left hc, bind_ok, contains_class_loop_true]
      simp only [hc, Bool.true_or]
    · have ih := contains_class_loop_eq input k j
      have hc' : classPred k input.val[i.val].val = false :=
        Bool.eq_false_of_not_eq_true hc
      erw [ite_eq_right hc, bind_ok, ih]
      simp only [hc', Bool.false_or]
  · have hil : ¬ i < Slice.len input := by scalar_tac
    have hnil : (vals input).drop i.val = [] :=
      List.drop_eq_nil_of_le (by rw [length_vals]; omega)
    simp [hil, hnil]
termination_by input.val.length - i.val
decreasing_by all_goals scalar_tac

theorem contains_class_eq (input : Slice U8) (k : sudo.env.filter.ByteClass) :
    sudo.env.filter.contains_class input k = ok ((vals input).any (classPred k)) := by
  unfold sudo.env.filter.contains_class
  rw [contains_class_loop_eq]
  simp

/-! ## `is_safe_tz` -/

theorem isPrefixOf_single (c : Nat) (l : Bytes) : [c].isPrefixOf l = (l.head? == some c) := by
  cases l <;> simp [List.isPrefixOf, eq_comm]

/-- The value the TZ check examines: without one leading `:`. -/
theorem strip_colon (value : Slice U8) :
    ∃ c : Slice U8,
      (if (vals value).head? = some 58 then
          (do let (_, rest) ← core.slice.Slice.split_at value 1#usize; ok rest)
        else ok value) = ok c ∧ vals c = stripColon (vals value) := by
  by_cases h : (vals value).head? = some 58
  · have hne : 1 ≤ value.val.length := by
      cases hv : value.val with
      | nil => simp [vals, hv] at h
      | cons _ _ => simp
    refine ⟨Slice.from (value.val.drop 1) (by have := slice_len_le value; simp; omega), ?_, ?_⟩
    · simp [h, core.slice.Slice.split_at, hne, List.splitAt_eq]
    · rw [stripColon, ite_eq_left h]
      simp only [vals, Slice.from_val, List.map_drop]
      cases value.val <;> rfl
  · exact ⟨value, by simp [h], by simp [stripColon, h]⟩

/-- **`is_safe_tz` is `tzSafe`**, for the zoneinfo directory `z` and `PATH_MAX` `pm`. -/
theorem is_safe_tz_eq (value : Slice U8) (z : Option Str) (pm : Usize)
    (hz : system.audit.zoneinfo_path = ok z) (hpm : sudo.env.filter.path_max = ok pm) :
    sudo.env.filter.is_safe_tz value = ok (tzSafe ⟨z.map vals, pm.val⟩ (vals value)) := by
  obtain ⟨c, hc, hcv⟩ := strip_colon value
  have hcolon : vals (Array.to_slice (Array.make 1#usize [58#u8])) = [58] := by
    simp [vals, Array.to_slice, Array.make]
  have hslash : vals (Array.to_slice (Array.make 1#usize [47#u8])) = [47] := by
    simp [vals, Array.to_slice, Array.make]
  unfold sudo.env.filter.is_safe_tz
  simp only [lift, bind_ok, starts_with_bytes_eq, hcolon, isPrefixOf_single, beq_iff_eq]
  rw [hc]
  simp only [bind_ok, hslash, isPrefixOf_single, beq_iff_eq, tzSafe, ← hcv]
  by_cases habs : (vals c).head? = some 47
  · have ha : ((vals c).head? != some 47) = false := by rw [habs] <;> rfl
    simp only [habs, ↓reduceIte, hz, bind_ok, ha, Bool.false_or]
    cases z with
    | none => rfl
    | some zs =>
      change Slice U8 at zs
      simp only [core.str.Str.as_bytes, bind_ok, starts_with_bytes_eq]
      change _ = ok
        (((vals zs).isPrefixOf (vals c) && ((vals c).drop (vals zs).length).head? == some 47) &&
          !hasDotDot (vals c) && !(vals c).any notPrintable && decide ((vals c).length < pm.val))
      cases hpre : (vals zs).isPrefixOf (vals c) with
      | false => simp only [hpre, Bool.false_eq_true, ↓reduceIte, Bool.false_and]
      | true =>
        simp only [hpre, ↓reduceIte, Bool.true_and]
        by_cases hl : c.val.length ≤ zs.val.length
        · have hl' : Slice.len c ≤ Slice.len zs := by scalar_tac
          have hd : (vals c).drop (vals zs).length = [] :=
            List.drop_eq_nil_of_le (by simpa only [length_vals] using hl)
          rw [ite_eq_left hl', hd] <;> rfl
        · have hl' : ¬ Slice.len c ≤ Slice.len zs := by scalar_tac
          have hiNat : zs.val.length < c.val.length := Nat.lt_of_not_ge hl
          have hi : (Slice.len zs).val < c.val.length := by
            simpa only [Slice.len_val, Slice.length] using hiNat
          have hidx := eq_ok_of_spec (Slice.index_usize_spec c (Slice.len zs) hi)
          have hd : ((vals c).drop (vals zs).length).head? =
              some c.val[(Slice.len zs).val].val := by
            simp only [length_vals, Slice.len_val, Slice.length, vals, List.length_map,
              ← List.map_drop, List.drop_eq_getElem_cons hiNat, List.map_cons, List.head?_cons] <;> rfl
          rw [ite_eq_right hl', hidx, bind_ok, hd]
          have hslashEq :
              c.val[(Slice.len zs).val] = 47#u8 ↔ c.val[(Slice.len zs).val].val = 47 :=
            u8_eq_iff_val
          by_cases h47 : c.val[(Slice.len zs).val] = 47#u8
          · have v := hslashEq.mp h47
            simp only [bne_iff_ne]
            erw [ite_eq_right (show ¬ (c.val[(Slice.len zs).val] ≠ 47#u8) from fun h => h h47), v]
            simp only [beq_self_eq_true, Bool.true_and, contains_dotdot_eq, contains_class_eq,
              classPred, hpm, bind_ok, UScalar.lt_equiv, Slice.len_val, Slice.length, length_vals]
            cases hasDotDot (vals c) <;> cases (vals c).any notPrintable <;> rfl
          · have v := mt hslashEq.mpr h47
            simp only [bne_iff_ne]
            erw [ite_eq_left h47]
            simp only [Option.some_beq_some, beq_eq_false_iff_ne.mpr v, Bool.false_and]
  · have ha : ((vals c).head? != some 47) = true := by simpa using habs
    simp only [habs, ↓reduceIte, ha, Bool.true_or, Bool.true_and, contains_dotdot_eq,
      contains_class_eq, classPred, hpm, bind_ok, UScalar.lt_equiv, Slice.len_val, length_vals]
    cases hasDotDot (vals c) <;> cases (vals c).any notPrintable <;> rfl

/-! ## Tables -/

theorem entry_matches_eq (key value entry : Slice U8) :
    sudo.env.filter.entry_matches key value entry =
      ok (entryMatches (vals key) (vals value) (vals entry)) := by
  obtain ⟨j, hj, hjv⟩ := find_equals_eq entry
  have hE := slice_len_le entry
  unfold sudo.env.filter.entry_matches
  simp only [hj, bind_ok, entryMatches, ← hjv]
  by_cases hlt : j.val < entry.val.length
  · have hl : j < Slice.len entry := by scalar_tac
    have hlt' : j.val < (vals entry).length := by simpa using hlt
    let keyPat := Slice.from (entry.val.take j.val) (by
      exact (List.length_take_le' _ _).trans hE)
    let rest := Slice.from (entry.val.drop j.val) (by simp only [List.length_drop]; omega)
    have hrest : 1 ≤ rest.val.length := by
      change 1 ≤ (Slice.from (entry.val.drop j.val) _).val.length
      simp only [Slice.from_val, List.length_drop]
      omega
    let sep := Slice.from (rest.val.take 1) (by
      exact (List.length_take_le' _ _).trans rest.property)
    let suffix := Slice.from (rest.val.drop 1) (by
      have := rest.property
      simp only [List.length_drop]
      omega)
    have hsplit1 : core.slice.Slice.split_at entry j = ok (keyPat, rest) := by
      simp [keyPat, rest, core.slice.Slice.split_at, Nat.le_of_lt hlt, List.splitAt_eq]
    have hsplit2 : core.slice.Slice.split_at rest 1#usize = ok (sep, suffix) := by
      simp [sep, suffix, core.slice.Slice.split_at, hrest, List.splitAt_eq]
    have hk : vals keyPat = (vals entry).take j.val := by
      simp [keyPat, vals, Slice.from_val, List.map_take]
    have hv : vals suffix = (vals entry).drop (j.val + 1) := by
      simp [suffix, rest, vals, Slice.from_val, List.map_drop, List.drop_drop, Nat.add_comm]
    simp only [hl, hlt', ↓reduceIte, hsplit1, bind_ok]
    change Aeneas.Std.bind (core.slice.Slice.split_at rest 1#usize)
      (fun p => Aeneas.Std.bind (sudo.env.wildcard_match.wildcard_match key keyPat)
        (fun b => if b then sudo.env.wildcard_match.wildcard_match value p.2 else ok false)) = _
    rw [hsplit2, bind_ok]
    simp only [wildcard_match_eq, bind_ok, hk, hv]
    cases wildcard starByte (vals key) ((vals entry).take j.val) <;> rfl
  · have hl : ¬ j < Slice.len entry := by scalar_tac
    have hlt' : ¬ j.val < (vals entry).length := by simpa using hlt
    simp only [hl, hlt', ↓reduceIte, wildcard_match_eq]

theorem in_table_loop_done (key value : Slice U8) (it : sudo.env.filter.TableIter)
    (found : Bool) : sudo.env.filter.in_table_loop key value it found false = ok found := by
  unfold sudo.env.filter.in_table_loop
  simp

/-- The loop over the table visits every entry, in order, until one matches. -/
theorem in_table_loop_eq (key value : Slice U8) :
    ∀ (l : List String), (∀ e ∈ l, Fits e) →
      sudo.env.filter.in_table_loop key value l false true =
        ok ((l.map utf8).any (entryMatches (vals key) (vals value)))
  | [], _ => by
    unfold sudo.env.filter.in_table_loop
    simp [sudo.env.filter.table_next, in_table_loop_done]
  | e :: rest, h => by
    have he : Fits e := h e (by simp)
    have ih := in_table_loop_eq key value rest (fun x hx => h x (by simp [hx]))
    unfold sudo.env.filter.in_table_loop
    cases hm : entryMatches (vals key) (vals value) (utf8 e)
    · simp [sudo.env.filter.table_next, strOfString_eq he, entry_matches_eq, vals_strOf, hm, ih]
    · simp [sudo.env.filter.table_next, strOfString_eq he, entry_matches_eq, vals_strOf, hm,
        in_table_loop_done]

theorem in_table_eq (key value : Slice U8) (table : SudoRsProofs.RSet)
    (h : ∀ e ∈ table, Fits e) :
    sudo.env.filter.in_table key value table =
      ok (inTable (vals key) (vals value) (table.map utf8)) := by
  unfold sudo.env.filter.in_table
  simp [sudo.env.filter.table_iter, in_table_loop_eq key value table h, inTable]

/-! ## The decision -/

/-- The policy inputs: the `Restrictions` of the authorization (as the specification of the
authorization reads them) and what the TZ check reads from the system. -/
def cfgOf (r : sudo_rs.sudoers.policy.Restrictions) (z : Option Str) (pm : Usize) : Config :=
  configOf (absRestrictions r) ⟨z.map vals, pm.val⟩

theorem cfgOf_keep (r : sudo_rs.sudoers.policy.Restrictions) (z : Option Str) (pm : Usize) :
    (cfgOf r z pm).keep = r.env_keep.map utf8 := rfl

theorem cfgOf_check (r : sudo_rs.sudoers.policy.Restrictions) (z : Option Str) (pm : Usize) :
    (cfgOf r z pm).check = r.env_check.map utf8 := rfl

theorem cfgOf_securePath (r : sudo_rs.sudoers.policy.Restrictions) (z : Option Str)
    (pm : Usize) : (cfgOf r z pm).securePath = r.path.isSome := by
  simp [cfgOf, configOf, absRestrictions]

theorem cfgOf_tz (r : sudo_rs.sudoers.policy.Restrictions) (z : Option Str) (pm : Usize) :
    (cfgOf r z pm).tz = ⟨z.map vals, pm.val⟩ := rfl

/-- The tables hold Rust strings (each at most `usize::MAX` bytes). -/
def TablesFit (r : sudo_rs.sudoers.policy.Restrictions) : Prop :=
  (∀ e ∈ r.env_keep, Fits e) ∧ (∀ e ∈ r.env_check, Fits e)

theorem vals_path :
    vals (Array.to_slice (Array.make 4#usize [80#u8, 65#u8, 84#u8, 72#u8])) = pathName := by
  simp [vals, Array.to_slice, Array.make, pathName]

theorem vals_tz : vals (Array.to_slice (Array.make 2#usize [84#u8, 90#u8])) = tzName := by
  simp [vals, Array.to_slice, Array.make, tzName]

theorem vals_function :
    vals (Array.to_slice (Array.make 2#usize [40#u8, 41#u8])) = functionPrefix := by
  simp [vals, Array.to_slice, Array.make, functionPrefix]

theorem is_secured_path_eq (key : Slice U8) (path : Option Str) :
    sudo.env.filter.is_secured_path key path = ok (path.isSome && (vals key == pathName)) := by
  unfold sudo.env.filter.is_secured_path
  cases path <;> simp [lift, equals_bytes_eq, vals_path]

private theorem decide_not_bool (b : Bool) [Decidable (¬ b = true)] :
    decide (¬ b = true) = !b := by
  cases b <;> simp

/-- **`should_keep` is `shouldKeep`**, on the authorization's `Restrictions`. -/
theorem should_keep_eq (key value : Slice U8) (r : sudo_rs.sudoers.policy.Restrictions)
    (z : Option Str) (pm : Usize) (hz : system.audit.zoneinfo_path = ok z)
    (hpm : sudo.env.filter.path_max = ok pm) (hfit : TablesFit r) :
    sudo.env.filter.should_keep key value r =
      ok (shouldKeep (cfgOf r z pm) (vals key) (vals value)) := by
  unfold sudo.env.filter.should_keep
  simp only [lift, bind_ok, starts_with_bytes_eq, equals_bytes_eq, vals_function,
    is_secured_path_eq, vals_tz, in_table_eq key value r.env_keep hfit.1,
    in_table_eq key value r.env_check hfit.2, is_safe_tz_eq value z pm hz hpm,
    contains_class_eq, classPred, decide_not_bool]
  unfold shouldKeep
  rw [cfgOf_keep, cfgOf_check, cfgOf_securePath, cfgOf_tz]
  split_ifs <;> simp_all

theorem is_login_variable_eq (key : Slice U8) :
    sudo.env.filter.is_login_variable key = ok (loginNames.contains (vals key)) := by
  unfold sudo.env.filter.is_login_variable
  simp only [lift, bind_ok, equals_bytes_eq]
  have e1 : vals (Array.to_slice (Array.make 4#usize [72#u8, 79#u8, 77#u8, 69#u8])) =
      [72, 79, 77, 69] := by simp [vals, Array.to_slice, Array.make]
  have e2 : vals (Array.to_slice (Array.make 5#usize [83#u8, 72#u8, 69#u8, 76#u8, 76#u8])) =
      [83, 72, 69, 76, 76] := by simp [vals, Array.to_slice, Array.make]
  have e3 : vals (Array.to_slice (Array.make 4#usize [85#u8, 83#u8, 69#u8, 82#u8])) =
      [85, 83, 69, 82] := by simp [vals, Array.to_slice, Array.make]
  have e4 : vals (Array.to_slice (Array.make 7#usize
      [76#u8, 79#u8, 71#u8, 78#u8, 65#u8, 77#u8, 69#u8])) =
      [76, 79, 71, 78, 65, 77, 69] := by simp [vals, Array.to_slice, Array.make]
  simp only [e1, e2, e3, e4, loginNames, List.contains, List.elem]
  generalize (vals key == [72, 79, 77, 69]) = home,
    (vals key == [83, 72, 69, 76, 76]) = shell,
    (vals key == [85, 83, 69, 82]) = user,
    (vals key == [76, 79, 71, 78, 65, 77, 69]) = logname
  cases home <;> cases shell <;> cases user <;> cases logname <;> rfl

/-- **`keep_inherited` is `keepInherited`**, on the authorization's `Restrictions`. -/
theorem keep_inherited_eq (key value : Slice U8) (login : Bool)
    (r : sudo_rs.sudoers.policy.Restrictions) (z : Option Str) (pm : Usize)
    (hz : system.audit.zoneinfo_path = ok z) (hpm : sudo.env.filter.path_max = ok pm)
    (hfit : TablesFit r) :
    sudo.env.filter.keep_inherited key value login r =
      ok (keepInherited (cfgOf r z pm) login (vals key) (vals value)) := by
  unfold sudo.env.filter.keep_inherited
  cases login <;>
    simp [is_login_variable_eq, should_keep_eq key value r z pm hz hpm hfit, keepInherited] <;>
    split_ifs <;> simp_all

/-- What a kept variable satisfies, for the code: the safety part of `shouldKeep_sound`. -/
theorem should_keep_sound (key value : Slice U8) (r : sudo_rs.sudoers.policy.Restrictions)
    (z : Option Str) (pm : Usize) (hz : system.audit.zoneinfo_path = ok z)
    (hpm : sudo.env.filter.path_max = ok pm) (hfit : TablesFit r)
    (h : sudo.env.filter.should_keep key value r = ok true) :
    functionPrefix.isPrefixOf (vals value) = false ∧
      ¬ (r.path.isSome = true ∧ vals key = pathName) ∧
      (inTable (vals key) (vals value) (r.env_keep.map utf8) = true ∨
        (inTable (vals key) (vals value) (r.env_check.map utf8) = true ∧
          (vals key = tzName → tzSafe ⟨z.map vals, pm.val⟩ (vals value) = true) ∧
          (vals key ≠ tzName → (vals value).any percentOrSlash = false))) := by
  rw [should_keep_eq key value r z pm hz hpm hfit] at h
  have hs := shouldKeep_sound (cfgOf r z pm) (vals key) (vals value) (Result.ok_injective h)
  rw [cfgOf_keep, cfgOf_check, cfgOf_securePath, cfgOf_tz] at hs
  exact hs

end SudoRsProofs.EnvFilter
