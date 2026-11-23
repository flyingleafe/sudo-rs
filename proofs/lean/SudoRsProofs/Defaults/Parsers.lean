import SudoRsProofs.Defaults.Utf8

/-!
# The value parsers refine `SudoersSpec.Settings.Values`

The external model `sudo_rs.fromStrRadix` (`FunsExternal.lean`) is related to the spec's
`fromStrRadix` (both transcribe `from_ascii_bytes_radix_impl`), then `decimal`,
`integer_in_range`, `octal_mode`, `find_dot` and `fractional_minutes`.

Hypothesis (the string model): the `&str` argument holds the UTF-8 bytes of a spec text
(`t.val = stringBytes s`).
-/

open Aeneas Aeneas.Std Result
open sudo_rs

namespace SudoRsProofs.Defaults

set_option allowUnsafeReducibility true in
attribute [local reducible] Str

namespace Spec
export SudoersSpec.Settings (bytes u32Max u64Max asciiDigit parseDigits fromStrRadix decimal
  integerInRange octalMode findDot fractionalMinutesRun Outcome)
end Spec

/-! ## Scalars -/

theorem tryMk_ok {ty : UScalarTy} {n : Nat} (h : n ≤ UScalar.max ty) :
    ∃ x, UScalar.tryMk ty n = ok x ∧ x.val = n := by
  have := UScalar.tryMkOpt_eq ty n
  unfold UScalar.tryMk
  rcases ho : UScalar.tryMkOpt ty n with _ | y
  · rw [ho] at this
    exfalso; apply this
    simp only [UScalar.inBounds]
    have := UScalar.max_def ty
    have := Nat.one_le_two_pow (n := ty.numBits)
    omega
  · rw [ho] at this
    exact ⟨y, rfl, this.1⟩

theorem max_u64 : UScalar.max .U64 = Spec.u64Max := by
  rw [UScalar.max_UScalarTy_U64_eq, U64.max_eq]; rfl

theorem max_u32 : UScalar.max .U32 = Spec.u32Max := by
  rw [UScalar.max_UScalarTy_U32_eq, U32.max_eq]; rfl

/-! ## `from_str_radix` -/

/-- The error kinds of the model, from the spec's. -/
def concKind : SudoersSpec.Settings.IntErrorKind → core.num.error.IntErrorKind
  | .Empty => .Empty | .InvalidDigit => .InvalidDigit | .PosOverflow => .PosOverflow
  | .NegOverflow => .NegOverflow | .Zero => .Zero

theorem parseDigits_eq (r m : Nat) (l : List Nat) (acc : Nat) :
    sudo_rs.parseDigits r m l acc =
      match Spec.parseDigits r m l acc with
      | .ok v => .Ok v
      | .error k => .Err (concKind k) := by
  induction l generalizing acc with
  | nil => rfl
  | cons b rest ih =>
    simp only [sudo_rs.parseDigits, Spec.parseDigits]
    show (match sudo_rs.asciiDigit b r with
      | none => _ | some x => _) = _
    rw [show sudo_rs.asciiDigit b r = Spec.asciiDigit b r from rfl]
    cases Spec.asciiDigit b r with
    | none => rfl
    | some x =>
      simp only
      split
      · exact ih _
      · rfl

/-- The digit part of the model is the spec's `fromStrRadix`. -/
theorem digitsOf_eq (r m : Nat) (L : List Nat) :
    sudo_rs.digitsOf r m L =
      match Spec.fromStrRadix m r L with
      | .ok v => .Ok v
      | .error k => .Err (concKind k) := by
  unfold sudo_rs.digitsOf Spec.fromStrRadix
  split <;> split <;> simp_all [parseDigits_eq, concKind]
  all_goals (subst_vars; rfl)

/-- `Ok` values of a parse result. -/
def okVal {ty : UScalarTy} {E : Type} : core.result.Result (UScalar ty) E → Option Nat
  | .Ok x => some x.val
  | .Err _ => none

/-- **The model of `from_str_radix` is the spec's `fromStrRadix` on the bytes.** -/
theorem fromStrRadix_eq (ty : UScalarTy) (t : Slice U8) (radix : U32)
    (hr : 2 ≤ radix.val ∧ radix.val ≤ 36) :
    ∃ r, sudo_rs.fromStrRadix ty t radix = ok r ∧
      okVal r = (Spec.fromStrRadix (UScalar.max ty) radix.val (t.val.map (·.val))).toOption := by
  unfold sudo_rs.fromStrRadix
  simp only [show ¬ (radix.val < 2 ∨ 36 < radix.val) by omega, ↓reduceIte]
  simp only [digitsOf_eq]
  generalize hs : SudoersSpec.Settings.fromStrRadix
    (UScalar.max ty) radix.val (t.val.map (·.val)) = parsed
  cases parsed with
  | error k => exact ⟨_, rfl, rfl⟩
  | ok v =>
    have hle := SudoersSpec.Settings.fromStrRadix_le _ _ _ _ hs
    obtain ⟨x, hx, hxv⟩ := tryMk_ok hle
    exact ⟨.Ok x, by simp only [hx, bind_ok], congrArg some hxv⟩

theorem toOption_ok_iff {ε : Type} {e : Except ε Nat} {v : Nat} :
    e.toOption = some v ↔ e = .ok v := by
  cases e <;> simp [Except.toOption]

/-! ## `decimal`, `integer_in_range` -/

/-- **`decimal` is `decimal`.** -/
theorem decimal_eq (t : Str) :
    ∃ r, defaults.decimal t = ok r ∧
      r.map (·.val) = Spec.decimal (t.val.map (·.val)) := by
  obtain ⟨r, hr, hv⟩ := fromStrRadix_eq .U64 t 10#u32 (by simp)
  have h10 : (10#u32).val = 10 := by simp
  rw [max_u64, h10] at hv
  unfold defaults.decimal Spec.decimal
  simp only [core.num.U64.from_str_radix, hr, bind_ok, core.result.Result.ok]
  cases r with
  | Ok x =>
    refine ⟨some x, rfl, ?_⟩
    simp only [okVal] at hv
    rw [toOption_ok_iff.mp hv.symm]
    rfl
  | Err e =>
    refine ⟨none, rfl, ?_⟩
    simp only [okVal] at hv
    cases hs : Spec.fromStrRadix Spec.u64Max 10 (t.val.map (·.val)) with
    | error k => rfl
    | ok v => rw [hs] at hv; simp [Except.toOption] at hv

theorem integer_in_range_eq (t : Str) (s : String) (ht : t.val = stringBytes s)
    (radix : U32) (first last : U64) (hr : 2 ≤ radix.val ∧ radix.val ≤ 36) :
    ∃ r, defaults.integer_in_range t radix first last = ok r ∧
      r.map (·.val) = Spec.integerInRange s radix.val first.val last.val := by
  obtain ⟨r, he, hv⟩ := fromStrRadix_eq .U64 t radix hr
  rw [max_u64, val_map_eq_bytes ht] at hv
  simp only [defaults.integer_in_range, core.num.U64.from_str_radix, he, bind_ok,
    Spec.integerInRange]
  cases r with
  | Ok v =>
    simp only [okVal] at hv
    rw [toOption_ok_iff.mp hv.symm]
    simp only [UScalar.le_equiv]
    by_cases h₁ : first.val ≤ v.val <;> by_cases h₂ : v.val ≤ last.val <;>
      simp [h₁, h₂]
  | Err e =>
    cases hs : Spec.fromStrRadix Spec.u64Max radix.val (Spec.bytes s) with
    | error k => exact ⟨none, rfl, rfl⟩
    | ok v => simp [okVal, hs, Except.toOption] at hv

theorem split_at_eq (t : Slice U8) (mid : Usize) (h : strIsCharBoundary t mid.val = true) :
    ∃ a b : Slice U8, core.str.Str.split_at t mid = ok (a, b) ∧
      a.val = t.val.take mid.val ∧ b.val = t.val.drop mid.val := by
  simp only [core.str.Str.split_at, h, ↓reduceIte]
  exact ⟨_, _, rfl, Slice.from_val _ _, Slice.from_val _ _⟩

theorem octal_mode_eq (t : Slice U8) (s : String) (ht : t.val = stringBytes s) :
    ∃ r, defaults.octal_mode t = ok r ∧ r.map (·.val) = Spec.octalMode s := by
  generalize hb : t.val = l
  cases l with
  | nil =>
    simp only [defaults.octal_mode, Spec.octalMode, ← val_map_eq_bytes ht,
      core.str.Str.as_bytes, bind_ok, core.slice.Slice.is_empty, Slice.length, hb]
    exact ⟨none, rfl, rfl⟩
  | cons b rest =>
    have h0 : (0#usize).val < t.length := by simp [Slice.length, hb]
    have h0' : 0 < t.val.length := by rw [hb]; simp
    have hhead : t.val[0] = b := by
      have h := congrArg (fun l : List U8 => l[0]?) hb
      simpa only [List.getElem?_eq_getElem h0', List.getElem?_cons_zero, Option.some.injEq] using h
    have hi : t.index_usize 0#usize = ok t.val[(0#usize).val] :=
      eq_ok_of_spec (Slice.index_usize_spec t 0#usize h0)
    change t.index_usize 0#usize = ok t.val[0] at hi
    rw [hhead] at hi
    simp only [defaults.octal_mode, Spec.octalMode, ← val_map_eq_bytes ht,
      core.str.Str.as_bytes, bind_ok, core.slice.Slice.is_empty, Slice.length, hb,
      List.length_cons, Nat.succ_ne_zero, decide_false, Bool.false_eq_true,
      ↓reduceIte, hi, List.map_cons]
    by_cases hz : b = 48#u8
    · have hb' : t.val[0].val < 0x80 := by rw [hhead, hz]; decide
      have hc := strIsCharBoundary_after_ascii ht 0 h0 hb'
      obtain ⟨a, digits, hs, _, hd⟩ := split_at_eq t 1#usize hc
      obtain ⟨r, hr, hv⟩ := fromStrRadix_eq .U32 digits 8#u32 (by simp)
      have h8 : (8#u32).val = 8 := rfl
      have hd' : digits.val = rest := by
        change digits.val = t.val.drop 1 at hd
        simpa only [hb, List.drop_succ_cons, List.drop_zero] using hd
      rw [max_u32, h8, hd'] at hv
      simp only [hz, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hs, bind_ok, uncurry,
        core.num.U32.from_str_radix, hr]
      change ∃ r' : Option U64, _ = ok r' ∧ r'.map (·.val) =
        (match Spec.fromStrRadix Spec.u32Max 8 (rest.map (·.val)) with
         | .ok v => some v | .error _ => none)
      cases r with
      | Ok x =>
        simp only [okVal] at hv
        rw [toOption_ok_iff.mp hv.symm]
        refine ⟨some (core.convert.num.FromU64U32.from x), ?_, ?_⟩
        · simp [lift]
        · simp [core.convert.num.FromU64U32.from_val_eq]
      | Err e =>
        cases hp : Spec.fromStrRadix Spec.u32Max 8 (rest.map (·.val)) with
        | error k => exact ⟨none, rfl, rfl⟩
        | ok v => simp [okVal, hp, Except.toOption] at hv
    · have hv : b.val ≠ 48 := fun h => hz (UScalar.val_eq_imp b 48#u8 h)
      simp [hz, hv]

theorem usize_add_one (i : Usize) (h : i.val < Usize.max) :
    ∃ j, i + 1#usize = ok j ∧ j.val = i.val + 1 := by
  obtain ⟨j, hj, hv⟩ := exists_eq_ok_of_spec
    (Usize.add_spec (x := i) (y := 1#usize) (by simp; omega))
  exact ⟨j, hj, by simpa using hv⟩

theorem find_dot_loop_done (t : Slice U8) (dot i : Usize) (h : dot.val ≠ t.length) :
    defaults.find_dot_loop t dot i = ok dot := by
  unfold defaults.find_dot_loop
  have h' : dot ≠ Slice.len t := by
    intro e
    exact h (by rw [e, Slice.len_val])
  simp [h']

theorem find_dot_loop_eq (t : Slice U8) :
    ∀ (d : Nat) (i : Usize), t.length - i.val = d → i.val ≤ t.length →
      ∃ j, defaults.find_dot_loop t (Slice.len t) i = ok j ∧
        j.val = i.val + Spec.findDot ((t.val.drop i.val).map (·.val)) := by
  intro d
  induction d with
  | zero =>
    intro i hd hi
    have h : i.val = t.length := by omega
    refine ⟨Slice.len t, ?_, ?_⟩
    · unfold defaults.find_dot_loop
      simp [UScalar.lt_equiv, h]
    · rw [Slice.len_val, h]
      simp [Slice.length, Spec.findDot]
  | succ d ih =>
    intro i hd hi
    have hlt : i.val < t.length := by omega
    obtain ⟨j, hj, hjv⟩ := usize_add_one i (Nat.lt_of_lt_of_le hlt t.property)
    have hidx := eq_ok_of_spec (Slice.index_usize_spec t i hlt)
    have hdrop := List.drop_eq_getElem_cons hlt
    have hlt' : i < Slice.len t := by simpa [UScalar.lt_equiv] using hlt
    have hr :
        defaults.find_dot_loop t (Slice.len t) i =
          defaults.find_dot_loop t
            (if t.val[i.val] = 46#u8 then i else Slice.len t) j := by
      conv => lhs; unfold defaults.find_dot_loop
      simp only [hlt', ↓reduceIte, hidx, bind_ok]
      by_cases h : t.val[i.val] = 46#u8
      · rw [ite_eq_left h]
        split
        · simp only [bind_ok, hj]
        · contradiction
      · rw [ite_eq_right h]
        split
        · contradiction
        · simp only [bind_ok, hj]
    rw [hr, hdrop, List.map_cons, Spec.findDot]
    by_cases hb : t.val[i.val] = 46#u8
    · have hv : t.val[i.val].val = 46 := congrArg UScalar.val hb
      refine ⟨i, by simp [hb, find_dot_loop_done t i j (by omega)], ?_⟩
      split <;> omega
    · have hv : t.val[i.val].val ≠ 46 := fun h =>
        hb (UScalar.val_eq_imp _ _ h)
      obtain ⟨k, hk, hkv⟩ := ih j (by omega) (by omega)
      refine ⟨k, by simpa [hb] using hk, ?_⟩
      rw [hkv, hjv]
      split <;> omega

theorem find_dot_eq (t : Slice U8) :
    ∃ j, defaults.find_dot t = ok j ∧ j.val = Spec.findDot (t.val.map (·.val)) := by
  obtain ⟨j, h, hv⟩ := find_dot_loop_eq t _ 0#usize rfl (by simp)
  exact ⟨j, h, by simpa using hv⟩

theorem findDot_byte {l : List Nat} (h : Spec.findDot l < l.length) :
    l[Spec.findDot l] = 46 := by
  induction l with
  | nil => simp [Spec.findDot] at h
  | cons a l ih =>
    by_cases ha : a = 46
    · subst a; rfl
    · have hl : Spec.findDot l < l.length := by
        simp only [Spec.findDot, ha, ↓reduceIte, List.length_cons] at h
        omega
      have e : Spec.findDot (a :: l) = Spec.findDot l + 1 := by simp [Spec.findDot, ha]
      have he : (a :: l)[Spec.findDot (a :: l)]? = some 46 := by
        rw [e, List.getElem?_cons_succ, List.getElem?_eq_getElem hl, ih hl]
      simpa only [List.getElem?_eq_getElem h, Option.some.injEq] using he

theorem split_at_dot (t : Slice U8) (s : String) (ht : t.val = stringBytes s)
    (j : Usize) (hj : j.val < t.length) (hdot : t.val[j.val].val = 46) :
    ∃ a b f : Slice U8, core.str.Str.split_at t j = ok (a, b) ∧
      (∃ skip, core.str.Str.split_at b 1#usize = ok (skip, f)) ∧
      a.val = t.val.take j.val ∧ f.val = t.val.drop (j.val + 1) := by
  have h₁ : strIsCharBoundary t j.val = true := by
    simp [strIsCharBoundary, List.getElem?_eq_getElem hj, hdot]
  have h₂ := strIsCharBoundary_after_ascii ht j.val hj (by omega)
  obtain ⟨a, b, hab, ha, hb⟩ := split_at_eq t j h₁
  have h₃ : strIsCharBoundary b (1#usize).val = true := by
    change strIsCharBoundary b 1 = true
    simp only [strIsCharBoundary, Slice.length, hb, List.length_drop, List.getElem?_drop] at h₂ ⊢
    have e : t.val.length - j.val = 1 ↔ j.val + 1 = t.val.length := by omega
    simpa [e] using h₂
  obtain ⟨skip, f, hsf, _, hf⟩ := split_at_eq b 1#usize h₃
  exact ⟨a, b, f, hab, ⟨skip, hsf⟩, ha, by simpa [hb, List.drop_drop] using hf⟩

theorem tryMk_overflow {ty : UScalarTy} {n : Nat} (h : UScalar.max ty < n) :
    UScalar.tryMk ty n = fail .integerOverflow := by
  have hopt := UScalar.tryMkOpt_eq ty n
  unfold UScalar.tryMk
  cases hp : UScalar.tryMkOpt ty n with
  | none => rfl
  | some x =>
    rw [hp] at hopt
    have hb := hopt.2
    have := UScalar.max_def ty
    simp only [UScalar.inBounds] at hb
    omega

theorem checked_mul_eq (x y : U64) :
    (U64.checked_mul x y).map (·.val) =
      if x.val * y.val ≤ Spec.u64Max then some (x.val * y.val) else none := by
  have h := U64.checked_mul_bv_spec x y
  simp only [← UScalar.max_UScalarTy_U64_eq, max_u64] at h
  cases hc : U64.checked_mul x y <;> simp only [hc] at h
  · simp [Nat.not_le.mpr h]
  · simp [h.1, h.2.1]

/-- The fractional calculation after the string splits. -/
theorem fractional_parts_eq (integral fractional : Slice U8) :
    (do
      let r ← core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from (Slice.len fractional)
      let o ← match r with
        | .Ok digits => do
          let shift ← core.num.U64.pow 10#u64 digits
          let i ← defaults.decimal integral
          match i with
          | none => ok none
          | some i =>
            let scaled ← i * shift
            let f ← defaults.decimal fractional
            match f with
            | none => ok none
            | some f =>
              let seconds ← scaled + f
              let total ← seconds * 60#u64
              let quot ← total / shift
              ok (some quot)
        | .Err _ => ok none
      ok (o.map (·.val))) =
    (let ig := integral.val.map (·.val)
     let fr := fractional.val.map (·.val)
     if Spec.u32Max < fr.length then ok none
     else
       let shift := 10 ^ fr.length
       if Spec.u64Max < shift then fail .integerOverflow
       else
         match Spec.decimal ig with
         | none => ok none
         | some i =>
           if Spec.u64Max < i * shift then fail .integerOverflow
           else
             match Spec.decimal fr with
             | none => ok none
             | some f =>
               if Spec.u64Max < i * shift + f then fail .integerOverflow
               else if Spec.u64Max < (i * shift + f) * 60 then fail .integerOverflow
               else ok (some ((i * shift + f) * 60 / shift))) := by
  simp only [List.length_map]
  set n := fractional.val.length
  have hn : (Slice.len fractional).val = n := Slice.len_val _
  change _ = (if Spec.u32Max < n then _ else _)
  by_cases hlen : n ≤ Spec.u32Max
  · obtain ⟨hc, hcv⟩ := tryFromUScalar_eq .U32 (Slice.len fractional) (by rwa [max_u32, hn])
    simp only [core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from, hc, bind_ok,
      hcv, hn, Nat.not_lt.mpr hlen, ↓reduceIte, core.num.U64.pow]
    have h10 : (10#u64).val = 10 := rfl
    simp only [h10]
    by_cases hp : Spec.u64Max < 10 ^ n
    · rw [tryMk_overflow (by rwa [max_u64]), ite_eq_left hp]
      simp
    · obtain ⟨shift, hs, hsv⟩ := tryMk_ok (ty := .U64) (n := 10 ^ n)
        (by rw [max_u64]; omega)
      simp only [hs, bind_ok, hp, ↓reduceIte]
      obtain ⟨i, hi, hiv⟩ := decimal_eq integral
      rw [← hiv]
      simp only [hi, bind_ok]
      cases i with
      | none => simp only [Option.map_none, bind_ok]
      | some i =>
        have mulDef : i * shift = UScalar.tryMk .U64 (i.val * shift.val) := rfl
        simp only [Option.map_some, mulDef, hsv]
        by_cases hm : Spec.u64Max < i.val * 10 ^ n
        · rw [tryMk_overflow (by rwa [max_u64]), ite_eq_left hm]
          simp
        · obtain ⟨scaled, hsc, hscv⟩ := tryMk_ok (ty := .U64) (n := i.val * 10 ^ n)
            (by rw [max_u64]; omega)
          simp only [hsc, bind_ok, hm, ↓reduceIte]
          obtain ⟨f, hf, hfv⟩ := decimal_eq fractional
          simp only [← hfv, hf, bind_ok]
          cases f with
          | none => simp only [Option.map_none, bind_ok]
          | some f =>
            have addDef : scaled + f = UScalar.tryMk .U64 (scaled.val + f.val) := rfl
            simp only [Option.map_some, addDef, hscv]
            by_cases ha : Spec.u64Max < i.val * 10 ^ n + f.val
            · rw [tryMk_overflow (by rwa [max_u64]), ite_eq_left ha]
              simp
            · obtain ⟨seconds, hsec, hsecv⟩ :=
                tryMk_ok (ty := .U64) (n := i.val * 10 ^ n + f.val) (by rw [max_u64]; omega)
              have mul60 : seconds * 60#u64 = UScalar.tryMk .U64 (seconds.val * 60) := rfl
              simp only [hsec, bind_ok, ha, ↓reduceIte, mul60, hsecv]
              by_cases htot : Spec.u64Max < (i.val * 10 ^ n + f.val) * 60
              · rw [tryMk_overflow (by rwa [max_u64]), ite_eq_left htot]
                simp
              · obtain ⟨total, ht, htv⟩ := tryMk_ok (ty := .U64)
                  (n := (i.val * 10 ^ n + f.val) * 60) (by rw [max_u64]; omega)
                obtain ⟨quot, hq, hqv⟩ := UScalar.div_spec total
                  (y := shift) (by rw [hsv]; positivity)
                simp only [ht, hq, bind_ok, htot, ↓reduceIte, Option.map_some, hqv, htv, hsv]
  · have hc := tryFromUScalar_err .U32 (Slice.len fractional) (by rw [max_u32, hn]; omega)
    simp only [core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from, hc, bind_ok,
      show Spec.u32Max < n by omega, ↓reduceIte]
    rfl

/-- Fractional minutes agrees with the spec even on the overflow path. -/
theorem fractional_minutes_run_eq (t : Slice U8) (s : String) (ht : t.val = stringBytes s) :
    (do
      let r ← defaults.fractional_minutes t
      ok (r.map (·.val))) =
      match Spec.fractionalMinutesRun s with
      | .ok r => ok r
      | .panic => fail .integerOverflow := by
  obtain ⟨j, hj, hjv⟩ := find_dot_eq t
  have hb := val_map_eq_bytes ht
  have hl : (Spec.bytes s).length = t.length := by rw [← hb, List.length_map]
  have hjs : j.val = Spec.findDot (Spec.bytes s) := hjv.trans (congrArg Spec.findDot hb)
  by_cases hd : j.val < t.length
  · have hbyte := findDot_byte (l := t.val.map (·.val)) (by rwa [← hjv, List.length_map])
    have hdot : t.val[j.val].val = 46 := by
      let l := t.val.map (·.val)
      have hget : l[Spec.findDot l]? = some 46 := by
        rw [List.getElem?_eq_getElem (by rwa [← hjv, List.length_map]), hbyte]
      rw [← hjv, List.getElem?_map, List.getElem?_eq_getElem hd] at hget
      exact Option.some.inj hget
    obtain ⟨a, b, f, hab, ⟨skip, hsf⟩, ha, hf⟩ := split_at_dot t s ht j hd hdot
    have htake : a.val.map (·.val) = (Spec.bytes s).take j.val := by
      rw [ha, List.map_take, hb]
    have hdrop : f.val.map (·.val) = (Spec.bytes s).drop (j.val + 1) := by
      rw [hf, List.map_drop, hb]
    simp only [defaults.fractional_minutes, core.str.Str.as_bytes, core.str.Str.len, hj, bind_ok,
      UScalar.lt_equiv, Slice.len_val, hd, ↓reduceIte, hab, hsf, uncurry]
    simp only [Aeneas.Std.bind_assoc]
    refine (fractional_parts_eq a f).trans ?_
    rw [htake, hdrop]
    simp only [Spec.fractionalMinutesRun, ← hjs, hl, hd, ↓reduceIte]
    generalize Spec.decimal ((Spec.bytes s).take j.val) = i
    generalize Spec.decimal ((Spec.bytes s).drop (j.val + 1)) = f'
    cases i <;> cases f' <;> simp only <;> split_ifs <;> rfl
  · have hd' : ¬ Spec.findDot (Spec.bytes s) < (Spec.bytes s).length := by rwa [← hjs, hl]
    obtain ⟨r, hr, hv⟩ := decimal_eq t
    rw [hb] at hv
    simp only [defaults.fractional_minutes, core.str.Str.as_bytes, core.str.Str.len, hj, bind_ok,
      UScalar.lt_equiv, Slice.len_val, hd, ↓reduceIte, hr, Spec.fractionalMinutesRun, hd', ← hv]
    cases r with
    | none => simp
    | some m =>
      simp only [bind_ok, Option.map_some, checked_mul_eq]
      rfl

theorem fractional_minutes_eq (t : Slice U8) (s : String) (ht : t.val = stringBytes s)
    (hlen : (Spec.bytes s).length ≤ 18) :
    ∃ r, defaults.fractional_minutes t = ok r ∧
      r.map (·.val) = SudoersSpec.Settings.fractionalMinutes s := by
  have h := fractional_minutes_run_eq t s ht
  rw [SudoersSpec.Settings.fractionalMinutesRun_eq s hlen] at h
  cases hf : defaults.fractional_minutes t <;> simp_all

end SudoRsProofs.Defaults

