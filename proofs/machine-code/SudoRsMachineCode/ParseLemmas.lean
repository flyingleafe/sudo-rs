module

public import Arm64
public import ProofLib.AsciiNum
public import ProofLib.BV.MaskLemmas
public import SudoRsMachineCode.Spec

/-!
# Pure lemmas about the specification

Facts about `nameOrIdParseUid`, `rustParseU32` and the engine's `parseDecimalU32` that the
machine-code proof (`SudoRsMachineCode.Proof`) uses at the loop cut points. The digit loops of the
compiled code keep a running value `prefixValue D i` of the first `i` digits; the lemmas below
turn the three ways a loop can stop (all digits read, a non-digit byte, a value `≥ 2 ^ 32`) into
the value of `parseDecimalU32 D`.
-/

@[expose] public section

namespace SudoRsMachineCode

open Arm64
open ProofLib.AsciiNum

theorem nameOrIdParseUid_cons (c : BitVec 8) (rest : List (BitVec 8)) :
    nameOrIdParseUid (c :: rest) =
      if c = 0x23#8 then (rustParseU32 rest).map ParsedUser.id else some .name := by
  unfold nameOrIdParseUid
  split <;> simp_all

theorem rustParseU32_nil : rustParseU32 [] = none := rfl

theorem rustParseU32_cons (c : BitVec 8) (rest : List (BitVec 8)) :
    rustParseU32 (c :: rest) =
      if c = 0x2b#8 then parseDecimalU32 rest else parseDecimalU32 (c :: rest) := by
  unfold rustParseU32
  split <;> simp_all

theorem parseDecimalU32_nil' : parseDecimalU32 [] = none := rfl

theorem parseDecimalU32_minus : parseDecimalU32 [0x2d#8] = none := by decide

/-- One digit step of the unbounded fold. -/
theorem parseDecimalNatFold_single (a : Nat) (b : BitVec 8) :
    parseDecimalNatFold a [b] =
      if (0x30#8 ≤ b && b ≤ 0x39#8) = true then some (a * 10 + (b.toNat - 0x30)) else none := by
  unfold parseDecimalNatFold
  cases hc : (0x30#8 ≤ b && b ≤ 0x39#8) <;>
    simp only [List.foldlM_cons, List.foldlM_nil, hc, ↓reduceIte, Bool.false_eq_true] <;> rfl

theorem take_succ_getD {D : List (BitVec 8)} {i : Nat} (hi : i < D.length) :
    D.take (i + 1) = D.take i ++ [D.getD i 0#8] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

/-- The compiled digit test `w - 0x30 >u 9` (on the zero-extended byte) is false on digits. -/
theorem digit_ult_false (b : BitVec 8) (h : (0x30#8 ≤ b && b ≤ 0x39#8) = true) :
    BitVec.ult 9#32 (BitVec.zeroExtend 32 b - 48#32) = false := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have h1 := BitVec.le_def.mp h.1
  have h2 := BitVec.le_def.mp h.2
  simp only [BitVec.ult, decide_eq_false_iff_not, Nat.not_lt]
  rw [BitVec.toNat_sub, BitVec.toNat_setWidth]
  simp at h1 h2 ⊢
  omega

/-- ... and true on every other byte. -/
theorem digit_ult_true (b : BitVec 8) (h : ¬ (0x30#8 ≤ b && b ≤ 0x39#8) = true) :
    BitVec.ult 9#32 (BitVec.zeroExtend 32 b - 48#32) = true := by
  simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at h
  simp only [BitVec.le_def] at h
  simp only [BitVec.ult, decide_eq_true_eq]
  rw [BitVec.toNat_sub, BitVec.toNat_setWidth]
  have := b.isLt
  simp at h ⊢
  omega

/-- The compiled digit test `w - 0x30 <u 10` of the overflow exit is true on digits. -/
theorem digit_ult10_true (b : BitVec 8) (h : (0x30#8 ≤ b && b ≤ 0x39#8) = true) :
    BitVec.ult (BitVec.zeroExtend 32 b - 48#32) 10#32 = true := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have h1 := BitVec.le_def.mp h.1
  have h2 := BitVec.le_def.mp h.2
  simp only [BitVec.ult, decide_eq_true_eq]
  rw [BitVec.toNat_sub, BitVec.toNat_setWidth]
  simp at h1 h2 ⊢
  omega

/-- ... and false on every other byte. -/
theorem digit_ult10_false (b : BitVec 8) (h : ¬ (0x30#8 ≤ b && b ≤ 0x39#8) = true) :
    BitVec.ult (BitVec.zeroExtend 32 b - 48#32) 10#32 = false := by
  simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at h
  simp only [BitVec.le_def] at h
  simp only [BitVec.ult, decide_eq_false_iff_not, Nat.not_lt]
  rw [BitVec.toNat_sub, BitVec.toNat_setWidth]
  have := b.isLt
  simp at h ⊢
  omega

/-! ## Register arithmetic of the digit loops -/

/-- One step of the unchecked loop (`madd w10, w10, w11, w12` with `w11 = 10`). -/
theorem madd_digit (d : BitVec 8) (p : Nat) (hd : (0x30#8 ≤ d && d ≤ 0x39#8) = true) :
    BitVec.zeroExtend 32 d - 48#32 + BitVec.truncate 32 (BitVec.ofNat 64 p) * 10#32 =
      BitVec.ofNat 32 (p * 10 + (d.toNat - 0x30)) := by
  simp only [Bool.and_eq_true, decide_eq_true_eq, BitVec.le_def] at hd
  have h1 : 48 ≤ d.toNat := hd.1
  have h2 : d.toNat ≤ 57 := hd.2
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat, BitVec.truncate_eq_setWidth]
  omega

/-- `lsl x8, x10, #32` then `lsr x8, x8, #32` and a 32-bit store keep the low word. -/
theorem trunc_shl_shr (x : BitVec 64) :
    BitVec.truncate 32 (x <<< 32 >>> 32) = BitVec.truncate 32 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
    BitVec.truncate_eq_setWidth]
  have := x.isLt
  omega

theorem trunc_zext (x : BitVec 32) : BitVec.truncate 32 (BitVec.zeroExtend 64 x) = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.truncate_eq_setWidth]
  have := x.isLt
  omega

theorem trunc_ofNat (v : Nat) : BitVec.truncate 32 (BitVec.ofNat 64 v) = BitVec.ofNat 32 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.truncate_eq_setWidth, BitVec.toNat_ofNat]
  omega

theorem zext_ofNat (v : Nat) (hv : v < 2 ^ 32) :
    BitVec.zeroExtend 64 (BitVec.ofNat 32 v) = BitVec.ofNat 64 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- `umull x10, w10, w11` with `w11 = 10` on a value below `2 ^ 32`. -/
theorem umull_ten (p : Nat) (hp : p < 2 ^ 32) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 p)) * 10#64 =
      BitVec.ofNat 64 (p * 10) := by
  apply BitVec.eq_of_toNat_eq
  have h64 : p < 2 ^ 64 := by omega
  have h10 : p * 10 < 2 ^ 64 := by omega
  simp only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    BitVec.truncate_eq_setWidth, Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt hp,
    Nat.mod_eq_of_lt h10]

/-- `tst x10, #0xffffffff00000000`: the high word is zero iff the value is below `2 ^ 32`. -/
theorem hiMask_beq_zero (v : Nat) (hv : v < 2 ^ 64) :
    (BitVec.ofNat 64 v &&& -4294967296#64 == 0#64) = decide (v < 2 ^ 32) := by
  have h : (BitVec.ofNat 64 v &&& -4294967296#64).toNat = v / 4294967296 * 4294967296 := by
    rw [BitVec.toNat_and_compl_eq_div_mul (BitVec.ofNat 64 v) (-4294967296#64) 4294967295#64]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro h0
    rw [h0] at h
    simp only [BitVec.toNat_ofNat, Nat.zero_mod] at h
    omega
  · intro hlt
    apply BitVec.eq_of_toNat_eq
    rw [h]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod]
    have : v / 4294967296 = 0 := Nat.div_eq_of_lt (by omega)
    rw [this]

/-- `adds w10, w13, w10` of the checked loop (`w13 = byte - 0x30`, `w10 = 10 * value`). -/
theorem adds_digit (d : BitVec 8) (q : Nat) (hd : (0x30#8 ≤ d && d ≤ 0x39#8) = true) :
    BitVec.zeroExtend 32 d - 48#32 + BitVec.truncate 32 (BitVec.ofNat 64 q) =
      BitVec.ofNat 32 (q + (d.toNat - 0x30)) := by
  simp only [Bool.and_eq_true, decide_eq_true_eq, BitVec.le_def] at hd
  have h1 : 48 ≤ d.toNat := hd.1
  have h2 : d.toNat ≤ 57 := hd.2
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat, BitVec.truncate_eq_setWidth]
  omega

/-- The carry of that `adds` (`cset w12, hs`) is set iff the sum reaches `2 ^ 32`. -/
theorem adds_digit_carry (d : BitVec 8) (q : Nat) (hd : (0x30#8 ≤ d && d ≤ 0x39#8) = true)
    (hq : q < 2 ^ 32) :
    BitVec.ult (BitVec.zeroExtend 32 d - 48#32 + BitVec.truncate 32 (BitVec.ofNat 64 q))
        (BitVec.zeroExtend 32 d - 48#32) = decide (2 ^ 32 ≤ q + (d.toNat - 0x30)) := by
  simp only [Bool.and_eq_true, decide_eq_true_eq, BitVec.le_def] at hd
  have h1 : 48 ≤ d.toNat := hd.1
  have h2 : d.toNat ≤ 57 := hd.2
  simp only [BitVec.ult, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat, BitVec.truncate_eq_setWidth]
  apply decide_eq_decide.mpr
  omega

/-- The same carry in the form the engine normalises `cset w12, hs` to: no carry iff the digit
    value is at most the (wrapped) sum. -/
theorem carry_ule (d : BitVec 8) (q v : Nat) (hd : (0x30#8 ≤ d && d ≤ 0x39#8) = true)
    (hq : q < 2 ^ 32) (hv : v = q + (d.toNat - 0x30)) :
    (BitVec.zeroExtend 32 d - 48#32).ule (BitVec.ofNat 32 v) = decide (v < 2 ^ 32) := by
  simp only [Bool.and_eq_true, decide_eq_true_eq, BitVec.le_def] at hd
  have h1 : 48 ≤ d.toNat := hd.1
  have h2 : d.toNat ≤ 57 := hd.2
  subst hv
  simp only [BitVec.ule, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  apply decide_eq_decide.mpr
  omega

/-- Value of the first `i` bytes of `D` read as decimal digits (`0` if one is not a digit). -/
def prefixValue (D : List (BitVec 8)) (i : Nat) : Nat :=
  (parseDecimalNatFold 0 (D.take i)).getD 0

/-- The first `i` bytes of `D` are decimal digits. -/
def DigitsUpTo (D : List (BitVec 8)) (i : Nat) : Prop :=
  parseDecimalNatFold 0 (D.take i) = some (prefixValue D i)

theorem digitsUpTo_zero (D : List (BitVec 8)) : DigitsUpTo D 0 := by
  simp [DigitsUpTo, prefixValue]

theorem prefixValue_zero (D : List (BitVec 8)) : prefixValue D 0 = 0 := by
  simp [prefixValue]

/-- Reading digit `i`: the prefix grows by one digit. -/
theorem digitsUpTo_succ {D : List (BitVec 8)} {i : Nat} (hi : i < D.length)
    (h : DigitsUpTo D i) (hd : (0x30#8 ≤ D.getD i 0#8 && D.getD i 0#8 ≤ 0x39#8) = true) :
    DigitsUpTo D (i + 1) ∧
      prefixValue D (i + 1) = prefixValue D i * 10 + ((D.getD i 0#8).toNat - 0x30) := by
  have ht := take_succ_getD hi
  have hf : parseDecimalNatFold 0 (D.take (i + 1)) =
      some (prefixValue D i * 10 + ((D.getD i 0#8).toNat - 0x30)) := by
    rw [ht, parseDecimalNatFold_append]
    unfold DigitsUpTo at h
    rw [h, Option.bind_some, parseDecimalNatFold_single]
    simp only [hd, ↓reduceIte]
  have hv : prefixValue D (i + 1) = prefixValue D i * 10 + ((D.getD i 0#8).toNat - 0x30) := by
    unfold prefixValue
    rw [hf]
    rfl
  exact ⟨by unfold DigitsUpTo; rw [hf, hv], hv⟩

/-- All digits read, value below `2 ^ 32`: the parse succeeds with that value. -/
theorem parseDecimalU32_of_digits {D : List (BitVec 8)} (hne : D ≠ [])
    (h : DigitsUpTo D D.length) (hlt : prefixValue D D.length < 2 ^ 32) :
    parseDecimalU32 D = some (BitVec.ofNat 32 (prefixValue D D.length)) := by
  unfold DigitsUpTo at h
  rw [List.take_length] at h
  unfold parseDecimalU32 parseDecimalUInt
  rw [parseDecimalNat_of_nonempty hne, h]
  simp [hlt]

/-- A non-digit byte at position `i` after `i` digits: the parse fails. -/
theorem parseDecimalU32_of_nondigit {D : List (BitVec 8)} {i : Nat} (hi : i < D.length)
    (h : DigitsUpTo D i) (hd : ¬ (0x30#8 ≤ D.getD i 0#8 && D.getD i 0#8 ≤ 0x39#8) = true) :
    parseDecimalU32 D = none := by
  have hne : D ≠ [] := by
    intro h0; subst h0; simp at hi
  have hf : parseDecimalNatFold 0 (D.take (i + 1)) = none := by
    rw [take_succ_getD hi, parseDecimalNatFold_append]
    unfold DigitsUpTo at h
    rw [h, Option.bind_some, parseDecimalNatFold_single]
    simp only [hd, ↓reduceIte, Bool.false_eq_true]
  unfold parseDecimalU32 parseDecimalUInt
  rw [parseDecimalNat_of_nonempty hne]
  have hsplit := List.take_append_drop (i + 1) D
  rw [← hsplit, parseDecimalNatFold_append, hf]
  rfl

/-- `j` digits whose value is at least `2 ^ 32`: the parse fails (the value only grows). -/
theorem parseDecimalU32_of_big {D : List (BitVec 8)} {j : Nat} (hne : D ≠ [])
    (h : DigitsUpTo D j) (hbig : 2 ^ 32 ≤ prefixValue D j) :
    parseDecimalU32 D = none := by
  unfold parseDecimalU32 parseDecimalUInt
  rw [parseDecimalNat_of_nonempty hne]
  have hsplit := List.take_append_drop j D
  rw [← hsplit, parseDecimalNatFold_append]
  unfold DigitsUpTo at h
  rw [h, Option.bind_some]
  cases hr : parseDecimalNatFold (prefixValue D j) (D.drop j) with
  | none => rfl
  | some n =>
    have := parseDecimalNatFold_ge_acc _ hr
    have hn : ¬ n < 2 ^ 32 := by omega
    simp [hn]

/-- Bound on the value of `i` digits. -/
theorem prefixValue_lt {D : List (BitVec 8)} {i : Nat} (h : DigitsUpTo D i) :
    prefixValue D i < 10 ^ i := by
  induction i with
  | zero => simp [prefixValue_zero]
  | succ i ih =>
    by_cases hi : i < D.length
    · have hstep : parseDecimalNatFold 0 (D.take (i + 1)) =
          (parseDecimalNatFold 0 (D.take i)).bind (parseDecimalNatFold · [D.getD i 0#8]) := by
        rw [take_succ_getD hi, parseDecimalNatFold_append]
      unfold DigitsUpTo at h
      rw [hstep] at h
      have hprev : DigitsUpTo D i := by
        unfold DigitsUpTo
        cases hp : parseDecimalNatFold 0 (D.take i) with
        | none => rw [hp] at h; simp at h
        | some a => simp [prefixValue, hp]
      have hd : (0x30#8 ≤ D.getD i 0#8 && D.getD i 0#8 ≤ 0x39#8) = true := by
        cases hdd : (0x30#8 ≤ D.getD i 0#8 && D.getD i 0#8 ≤ 0x39#8)
        · exfalso
          unfold DigitsUpTo at hprev
          rw [hprev, Option.bind_some, parseDecimalNatFold_single, hdd] at h
          simp at h
        · rfl
      have ⟨_, hv⟩ := digitsUpTo_succ hi hprev hd
      have := ih hprev
      have hd' : (D.getD i 0#8).toNat ≤ 57 := by
        simp only [Bool.and_eq_true, decide_eq_true_eq, BitVec.le_def] at hd
        exact hd.2
      rw [hv, Nat.pow_succ]
      omega
    · have hle : D.length ≤ i := by omega
      have hti : D.take (i + 1) = D.take i := by
        rw [List.take_of_length_le (by omega), List.take_of_length_le hle]
      have hv : prefixValue D (i + 1) = prefixValue D i := by
        simp [prefixValue, hti]
      have hprev : DigitsUpTo D i := by
        unfold DigitsUpTo at h ⊢
        rw [hti] at h
        rw [h, hv]
      rw [hv, Nat.pow_succ]
      have := ih hprev
      omega

theorem prefixValue_lt_of_le {D : List (BitVec 8)} {i n : Nat} (h : DigitsUpTo D i)
    (hi : i ≤ n) : prefixValue D i < 10 ^ n :=
  Nat.lt_of_lt_of_le (prefixValue_lt h) (Nat.pow_le_pow_right (by decide) hi)

end SudoRsMachineCode
