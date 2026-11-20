module

public import Arm64
public import ProofLib.SepLogic.WP
public import ProofLib.SepLogic.Entry
public import ProofLib.SepLogic.LoopTactics
public meta import ProofLib.SepLogic.LoopTactics
public import SudoRsMachineCode.ParseLemmas

@[expose] public section

namespace SudoRsMachineCode

open Arm64
open ProofLib
open ProofLib.AsciiNum

/-- The first 81 instruction words (`+0x000` to `+0x140`) of `sudo_rs_name_or_id_parse_uid` as
    compiled by rustc 1.98.1. The function's remaining five words (`+0x144` to `+0x154`) set up
    and call `core::str::slice_error_fail` (the panic of `&self.inner[..num_bytes - 1]` in
    `SudoString::deref`); the proof shows that they are never reached, so they need not be
    fetched. -/
def parseUidWords : List (BitVec 32) := [
  0xa9bf7bfd#32, 0x910003fd#32, 0xf9400808#32, 0xf1000503#32,
  0x540005c0#32, 0xaa0003e9#32, 0xf9400400#32, 0xb4000948#32,
  0x38e3680a#32, 0x3101055f#32, 0x540008ed#32, 0x3940000a#32,
  0x71008d5f#32, 0x540001c1#32, 0xf1000909#32, 0x54000460#32,
  0xf1000d1f#32, 0x91000408#32, 0x540001a1#32, 0x3940010a#32,
  0x2a1f03e0#32, 0x7100ad5f#32, 0x54000060#32, 0x7100b55f#32,
  0x54000101#32, 0xa8c17bfd#32, 0xd65f03c0#32, 0xf9000029#32,
  0x52800020#32, 0xa8c17bfd#32, 0xd65f03c0#32, 0x3940010a#32,
  0x7100ad5f#32, 0x1a9f17ea#32, 0x9a881508#32, 0xcb0a0129#32,
  0xf100253f#32, 0x54000202#32, 0x2a1f03ea#32, 0xb4000129#32,
  0x5280014b#32, 0x3840150c#32, 0x5100c18c#32, 0x7100259f#32,
  0x540000c8#32, 0x1b0b314a#32, 0xf1000529#32, 0x54ffff41#32,
  0xd3607d48#32, 0x36000368#32, 0x2a1f03e0#32, 0xa8c17bfd#32,
  0xd65f03c0#32, 0x2a1f03ea#32, 0x5280014b#32, 0xb4ffff29#32,
  0x9bab7d4a#32, 0xf2607d5f#32, 0x54000161#32, 0x3840150c#32,
  0x2a1f03e0#32, 0x5100c18d#32, 0x2b0a01aa#32, 0x1a9f37ec#32,
  0x710025bf#32, 0x54fffb08#32, 0xd1000529#32, 0x3607fe8c#32,
  0x17ffffd5#32, 0x39400108#32, 0x52804029#32, 0x5100c108#32,
  0x7100291f#32, 0x52802028#32, 0x9a883128#32, 0x3707fce8#32,
  0xd360fd08#32, 0xb9000048#32, 0x52800040#32, 0xa8c17bfd#32,
  0xd65f03c0#32]

/-
The unchecked digit loop (`+0x0a4` to `+0x0bc`), taken when the digit string has fewer than nine
bytes, from its header to the return. `small_loop_proof off` expects in context: the digit
string `D` of length `L` (`hLD : D.length = L`, `0 < L < 9`) starting at byte `off` (a literal)
of the buffer image `bs` (`hbsD`, `hoffL`), and the goal's result already rewritten to
`(parseDecimalU32 D).map ParsedUser.id`. In the loop body `i` is the index of the byte read.
-/
set_option hygiene false in
local macro "small_loop_proof " off:term:max : tactic => `(tactic| (
  wp_loop_measure frame L (fun k st => 0 < k ∧ k ≤ L ∧
    st.readReg64 .x9 = BitVec.ofNat 64 k ∧
    st.readReg64 .x8 = buf + BitVec.ofNat 64 ($off + (L - k)) ∧
    st.readReg64 .x11 = 10#64 ∧
    st.readReg64 .x2 = idOut ∧
    st.readReg64 .x10 = BitVec.ofNat 64 (prefixValue D (L - k)) ∧
    DigitsUpTo D (L - k))
  case step =>
    have hsucc : L - (m' + 1) + 1 = L - m' := by omega
    have hi : L - (m' + 1) < L := by omega
    have hi7 : L - (m' + 1) ≤ 7 := by omega
    generalize hidef : L - (m' + 1) = i at *
    have hdig : DigitsUpTo D i := by assumption
    have hbyte := hbsD i hi
    have hpv : prefixValue D i < 10000000 := by
      have := prefixValue_lt_of_le hdig hi7
      simpa using this
    by_cases hd : (0x30#8 ≤ D.getD i 0#8 && D.getD i 0#8 ≤ 0x39#8) = true
    · have hdb := digit_ult_false _ hd
      have ⟨hdig', hval'⟩ := digitsUpTo_succ (by omega) hdig hd
      have hacc := madd_digit (D.getD i 0#8) (prefixValue D i) hd
      rw [← hval'] at hacc
      have hpv' : prefixValue D (i + 1) < 2 ^ 32 := by rw [hval']; omega
      have hz64 := zext_ofNat _ hpv'
      have hx9' : BitVec.ofNat 64 (m' + 1) - 1#64 = BitVec.ofNat 64 m' := by bv_omega
      by_cases hm0 : m' = 0
      · left
        have hz : (BitVec.ofNat 64 m' != 0#64) = false := by subst hm0; decide
        have hz' : (BitVec.ofNat 64 m' == 0#64) = true := by subst hm0; decide
        have hL1 : i + 1 = L := by omega
        rw [hL1] at hdig' hval' hacc hz64 hpv'
        have hne : D ≠ [] := by intro h0; rw [h0] at hLD; simp at hLD; omega
        have hres := parseDecimalU32_of_digits (D := D) hne (by rw [hLD]; exact hdig')
          (by rw [hLD]; exact hpv')
        rw [hLD] at hres
        rw [hres]
        simp only [Option.map_some, resultCode, nameOutAfter, idOutAfter]
        wp_steps
        try simp only [hacc, hz64, trunc_shl_shr, trunc_ofNat]
        wp_done
      · right
        have hz : (BitVec.ofNat 64 m' != 0#64) = true := by
          simp only [bne_iff_ne, ne_eq]; bv_omega
        have hz' : (BitVec.ofNat 64 m' == 0#64) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; bv_omega
        rw [hsucc] at hdig' hval' hacc hz64 hpv'
        have hx8 : buf + BitVec.ofNat 64 ($off + i) + 1#64 =
            buf + BitVec.ofNat 64 ($off + (L - m')) := by
          rw [← hsucc]; bv_omega
        wp_steps
        try simp only [hacc, hz64]
        wp_done
    · have hdb := digit_ult_true _ hd
      left
      rw [parseDecimalU32_of_nondigit (by omega) hdig hd]
      simp only [Option.map_none, resultCode, nameOutAfter, idOutAfter]
      wp_steps
      wp_done
  all_goals first
    | (exfalso; omega)
    | omega
    | (simp [prefixValue_zero, digitsUpTo_zero]; done)
    | bv_omega))

/-
The checked digit loop (`+0x0dc` to `+0x10c`, overflow exits at `+0x0e8` and `+0x10c`), taken
when the digit string has at least nine bytes, from its header to the return. Same context as
`small_loop_proof`.
-/
set_option hygiene false in
local macro "checked_loop_proof " off:term:max : tactic => `(tactic| (
  wp_loop_measure frame L (fun k st => k ≤ L ∧
    st.readReg64 .x9 = BitVec.ofNat 64 k ∧
    st.readReg64 .x8 = buf + BitVec.ofNat 64 ($off + (L - k)) ∧
    st.readReg64 .x11 = 10#64 ∧
    st.readReg64 .x2 = idOut ∧
    st.readReg64 .x10 = BitVec.ofNat 64 (prefixValue D (L - k)) ∧
    DigitsUpTo D (L - k) ∧ prefixValue D (L - k) < 2 ^ 32)
  case base =>
    have hdig : DigitsUpTo D L := by
      first | assumption | simpa using (‹DigitsUpTo D (L - 0)›)
    have hlt : prefixValue D L < 2 ^ 32 := by
      first | assumption | simpa using (‹prefixValue D (L - 0) < 2 ^ 32›)
    have hne : D ≠ [] := by intro h0; rw [h0] at hLD; simp at hLD; omega
    have hres := parseDecimalU32_of_digits (D := D) hne (by rw [hLD]; exact hdig)
      (by rw [hLD]; exact hlt)
    rw [hLD] at hres
    rw [hres]
    simp only [Option.map_some, resultCode, nameOutAfter, idOutAfter]
    wp_steps
    try simp only [Nat.sub_zero, trunc_shl_shr, trunc_ofNat]
    wp_done
  case step =>
    have hsucc : L - (m' + 1) + 1 = L - m' := by omega
    have hi : L - (m' + 1) < L := by omega
    generalize hidef : L - (m' + 1) = i at *
    have hdig : DigitsUpTo D i := by assumption
    have hlt : prefixValue D i < 2 ^ 32 := by assumption
    have hbyte := hbsD i hi
    have hne : D ≠ [] := by intro h0; rw [h0] at hLD; simp at hLD; omega
    have hz : (BitVec.ofNat 64 (m' + 1) == 0#64) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; bv_omega
    have hz0 : BitVec.ofNat 64 (m' + 1) ≠ 0#64 := by bv_omega
    have hmul := umull_ten _ hlt
    have htst := hiMask_beq_zero (prefixValue D i * 10) (by omega)
    by_cases hov : 2 ^ 32 ≤ prefixValue D i * 10
    · left
      have htst' : (BitVec.ofNat 64 (prefixValue D i * 10) &&& -4294967296#64 == 0#64) = false := by
        rw [htst]; simp only [decide_eq_false_iff_not]; omega
      have htst'' : (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 (prefixValue D i))) *
          10#64 &&& -4294967296#64 == 0#64) = false := by
        rw [hmul]; exact htst'
      by_cases hd : (0x30#8 ≤ D.getD i 0#8 && D.getD i 0#8 ≤ 0x39#8) = true
      · have hdc := digit_ult10_true _ hd
        have ⟨hdig', hval'⟩ := digitsUpTo_succ (by omega) hdig hd
        rw [parseDecimalU32_of_big hne hdig' (by rw [hval']; omega)]
        simp only [Option.map_none, resultCode, nameOutAfter, idOutAfter]
        wp_steps
        wp_done
      · have hdc := digit_ult10_false _ hd
        rw [parseDecimalU32_of_nondigit (by omega) hdig hd]
        simp only [Option.map_none, resultCode, nameOutAfter, idOutAfter]
        wp_steps
        wp_done
    · have htst' : (BitVec.ofNat 64 (prefixValue D i * 10) &&& -4294967296#64 == 0#64) = true := by
        rw [htst]; simp only [decide_eq_true_eq]; omega
      have htst'' : (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 (prefixValue D i))) *
          10#64 &&& -4294967296#64 == 0#64) = true := by
        rw [hmul]; exact htst'
      by_cases hd : (0x30#8 ≤ D.getD i 0#8 && D.getD i 0#8 ≤ 0x39#8) = true
      · have hdb := digit_ult_false _ hd
        have ⟨hdig', hval'⟩ := digitsUpTo_succ (by omega) hdig hd
        have hadd := adds_digit (D.getD i 0#8) (prefixValue D i * 10) hd
        have hcarry := adds_digit_carry (D.getD i 0#8) (prefixValue D i * 10) hd (by omega)
        rw [← hval'] at hadd hcarry
        have hx9' : BitVec.ofNat 64 (m' + 1) - 1#64 = BitVec.ofNat 64 m' := by bv_omega
        by_cases hcy : 2 ^ 32 ≤ prefixValue D (i + 1)
        · left
          have hc1 : BitVec.ult (BitVec.zeroExtend 32 (D.getD i 0#8) - 48#32 +
              BitVec.truncate 32 (BitVec.ofNat 64 (prefixValue D i * 10)))
              (BitVec.zeroExtend 32 (D.getD i 0#8) - 48#32) = true := by
            rw [hcarry]; simp only [decide_eq_true_eq]; exact hcy
          have hc2 : BitVec.ult (BitVec.ofNat 32 (prefixValue D (i + 1)))
              (BitVec.zeroExtend 32 (D.getD i 0#8) - 48#32) = true := by
            rw [← hadd]; exact hc1
          have hu1 : (BitVec.zeroExtend 32 (D.getD i 0#8) - 48#32).ule
              (BitVec.ofNat 32 (prefixValue D i * 10 + ((D.getD i 0#8).toNat - 48))) = false := by
            rw [carry_ule _ _ _ hd (by omega) rfl]; simp only [decide_eq_false_iff_not]; omega
          have hu2 : (BitVec.zeroExtend 32 (D.getD i 0#8) - 48#32).ule
              (BitVec.ofNat 32 (prefixValue D (i + 1))) = false := by
            rw [carry_ule _ (prefixValue D i * 10) _ hd (by omega) hval']
            simp only [decide_eq_false_iff_not]; omega
          have hu3 : (BitVec.zeroExtend 32 (D.getD i 0#8) - 48#32).ule
              (BitVec.ofNat 32 (prefixValue D (L - m'))) = false := by
            rw [← hsucc]; exact hu2
          have hbr : ((if (BitVec.zeroExtend 32 (D.getD i 0#8) - 48#32).ule
              (BitVec.ofNat 32 (prefixValue D (L - m'))) = true then 0#64 else 1#64).getLsbD 0
              == false) = false := by
            rw [hu3]; rfl
          rw [parseDecimalU32_of_big hne hdig' hcy]
          simp only [Option.map_none, resultCode, nameOutAfter, idOutAfter]
          wp_steps
          wp_done
        · right
          have hc1 : BitVec.ult (BitVec.zeroExtend 32 (D.getD i 0#8) - 48#32 +
              BitVec.truncate 32 (BitVec.ofNat 64 (prefixValue D i * 10)))
              (BitVec.zeroExtend 32 (D.getD i 0#8) - 48#32) = false := by
            rw [hcarry]; simp only [decide_eq_false_iff_not]; exact hcy
          have hc2 : BitVec.ult (BitVec.ofNat 32 (prefixValue D (i + 1)))
              (BitVec.zeroExtend 32 (D.getD i 0#8) - 48#32) = false := by
            rw [← hadd]; exact hc1
          have hz64 := zext_ofNat _ (show prefixValue D (i + 1) < 2 ^ 32 by omega)
          have hu1 : (BitVec.zeroExtend 32 (D.getD i 0#8) - 48#32).ule
              (BitVec.ofNat 32 (prefixValue D i * 10 + ((D.getD i 0#8).toNat - 48))) = true := by
            rw [carry_ule _ _ _ hd (by omega) rfl]; simp only [decide_eq_true_eq]; omega
          have hu2 : (BitVec.zeroExtend 32 (D.getD i 0#8) - 48#32).ule
              (BitVec.ofNat 32 (prefixValue D (i + 1))) = true := by
            rw [carry_ule _ (prefixValue D i * 10) _ hd (by omega) hval']
            simp only [decide_eq_true_eq]; omega
          have hu3 := hu2
          rw [hsucc] at hdig' hval' hadd hz64 hcy hc2 hu3
          have hx8 : buf + BitVec.ofNat 64 ($off + i) + 1#64 =
              buf + BitVec.ofNat 64 ($off + (L - m')) := by
            rw [← hsucc]; bv_omega
          have hbr : ((if (BitVec.zeroExtend 32 (D.getD i 0#8) - 48#32).ule
              (BitVec.ofNat 32 (prefixValue D (L - m'))) = true then 0#64 else 1#64).getLsbD 0
              == false) = true := by
            rw [hu3]; rfl
          clear hval' hcarry hc1 hu1 hu2
          wp_steps
          try simp only [hadd, hz64]
          wp_done
      · have hdb := digit_ult_true _ hd
        left
        rw [parseDecimalU32_of_nondigit (by omega) hdig hd]
        simp only [Option.map_none, resultCode, nameOutAfter, idOutAfter]
        wp_steps
        wp_done
  all_goals first
    | (exfalso; omega)
    | omega
    | (simp [prefixValue_zero, digitsUpTo_zero]; done)
    | bv_omega))

set_option maxHeartbeats 20000000 in
theorem parseUid_codeAt_ok (prog : Program) (a : BitVec 64)
    (hc : prog.hasWords a parseUidWords) :
    subroutine_ok prog a parseUidSpec := by
  wp_init x s0
  rcases x with ⟨input, nameOut, idOut, cap, buf, content, oldName, oldId⟩
  dsimp only at *
  cases content with
  | nil =>
    simp only [nameOrIdParseUid, resultCode, nameOutAfter, idOutAfter] at *
    wp_steps
    wp_done
  | cons c rest =>
    simp only [List.length_cons] at *
    have hL : rest.length + 1 + 1 < 2 ^ 64 := h_1
    have hbs_len : (c :: rest ++ [0#8]).length = rest.length + 1 + 1 := by simp
    have hbs_nul : (c :: rest ++ [0#8]).getD (rest.length + 1) 0#8 = 0#8 := by
      simp [List.getD_eq_getElem?_getD]
    have hbs_0 : (c :: rest ++ [0#8]).getD 0 0#8 = c := rfl
    have hbs_rest : ∀ j, j < rest.length →
        (c :: rest ++ [0#8]).getD (j + 1) 0#8 = rest.getD j 0#8 := by
      intro j hj
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
    generalize (c :: rest ++ [0#8]) = bs at *
    have hne1 : BitVec.ofNat 64 (rest.length + 1 + 1) ≠ 1#64 := by bv_omega
    have hne0 : (BitVec.ofNat 64 (rest.length + 1 + 1) == 0#64) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; bv_omega
    have hx3 : BitVec.ofNat 64 (rest.length + 1 + 1) - 1#64 =
        BitVec.ofNat 64 (rest.length + 1) := by
      bv_omega
    have hle : ConditionHolds CondCode.LE (addsPState32 0#32 65#32) = false := by
      with_unfolding_all decide
    rw [nameOrIdParseUid_cons]
    by_cases hc : c = 0x23#8
    · subst hc
      simp only [↓reduceIte]
      rcases rest with _ | ⟨c1, rest⟩
      · -- `"#"`: empty digit string
        simp only [rustParseU32_nil, Option.map_none, resultCode, nameOutAfter, idOutAfter]
        simp only [List.length_nil] at *
        wp_steps
        wp_done
      · simp only [List.length_cons] at *
        have hbs_1 : bs.getD 1 0#8 = c1 := hbs_rest 0 (by omega)
        have hn2 : (BitVec.ofNat 64 (rest.length + 1 + 1 + 1) == 2#64) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; bv_omega
        have hx9 : BitVec.ofNat 64 (rest.length + 1 + 1 + 1) - 2#64 =
            BitVec.ofNat 64 (rest.length + 1) := by bv_omega
        rcases rest with _ | ⟨c2, rest⟩
        · -- `"#c1"`: one byte after `'#'`
          simp only [List.length_nil] at *
          simp only [rustParseU32_cons]
          by_cases hp : c1 = 0x2b#8
          · subst hp
            simp only [↓reduceIte, parseDecimalU32_nil', Option.map_none, resultCode,
              nameOutAfter, idOutAfter]
            wp_steps
            wp_done
          have hpb : (BitVec.zeroExtend 32 c1 == 43#32) = false := by
            simp only [beq_eq_false_iff_ne, ne_eq]; bv_omega
          have hpb' : (BitVec.zeroExtend 32 c1 != 43#32) = true := by
            simp only [bne_iff_ne, ne_eq]; bv_omega
          simp only [hp, ↓reduceIte]
          by_cases hm : c1 = 0x2d#8
          · subst hm
            simp only [parseDecimalU32_minus, Option.map_none, resultCode, nameOutAfter,
              idOutAfter]
            wp_steps
            wp_done
          have hmb : (BitVec.zeroExtend 32 c1 == 45#32) = false := by
            simp only [beq_eq_false_iff_ne, ne_eq]; bv_omega
          wp_steps 34
          -- the unchecked loop with the one-byte digit string `[c1]` at byte 1
          obtain ⟨D, hD⟩ : ∃ D, D = [c1] := ⟨_, rfl⟩
          obtain ⟨L, hLD⟩ : ∃ L, D.length = L := ⟨_, rfl⟩
          have hbsD : ∀ i, i < L → bs.getD (1 + i) 0#8 = D.getD i 0#8 := by
            intro i hi; subst hD hLD
            simp at hi; subst hi; exact hbs_1
          have hLpos : 0 < L := by subst hD hLD; simp
          have hL9 : L < 9 := by subst hD hLD; simp
          have hoffL : 1 + L + 1 = bs.length := by subst hD hLD; simp [hbs_len]
          have hx9L : BitVec.ofNat 64 L = 1#64 := by subst hD hLD; rfl
          rw [show parseDecimalU32 [c1] = parseDecimalU32 D by rw [hD]]
          clear hD
          small_loop_proof 1
        · -- at least two bytes after `'#'`
          simp only [List.length_cons] at *
          simp only [rustParseU32_cons]
          have hn3 : (BitVec.ofNat 64 (rest.length + 1 + 1 + 1 + 1) == 3#64) = false := by
            simp only [beq_eq_false_iff_ne, ne_eq]; bv_omega
          have hn3' : (BitVec.ofNat 64 (rest.length + 1 + 1 + 1 + 1) != 3#64) = true := by
            simp only [bne_iff_ne, ne_eq]; bv_omega
          by_cases hp : c1 = 0x2b#8
          · -- `'+'`: the digits are `c2 :: rest`, from byte 2
            subst hp
            simp only [↓reduceIte]
            by_cases hL9 : rest.length + 1 < 9
            · have hcs : (9#64).ule (BitVec.ofNat 64 (rest.length + 1 + 1) - 1#64) = false := by
                simp only [BitVec.ule, decide_eq_false_iff_not]; bv_omega
              wp_steps 29
              obtain ⟨D, hD⟩ : ∃ D, D = c2 :: rest := ⟨_, rfl⟩
              obtain ⟨L, hLr⟩ : ∃ L, rest.length + 1 = L := ⟨_, rfl⟩
              have hLD : D.length = L := by subst hD hLr; simp
              have hbsD : ∀ i, i < L → bs.getD (2 + i) 0#8 = D.getD i 0#8 := by
                intro i hi; subst hD hLr
                rw [show 2 + i = (i + 1) + 1 by omega, hbs_rest (i + 1) (by omega)]
                simp
              have hLpos : 0 < L := by omega
              have hoffL : 2 + L + 1 = bs.length := by omega
              have hx9L : BitVec.ofNat 64 (rest.length + 1 + 1) - 1#64 = BitVec.ofNat 64 L := by
                subst hLr; bv_omega
              rw [show parseDecimalU32 (c2 :: rest) = parseDecimalU32 D by rw [hD]]
              clear hD
              replace hL9 : L < 9 := by omega
              small_loop_proof 2
            · have hcs : (9#64).ule (BitVec.ofNat 64 (rest.length + 1 + 1) - 1#64) = true := by
                simp only [BitVec.ule, decide_eq_true_eq]; bv_omega
              wp_steps 28
              obtain ⟨D, hD⟩ : ∃ D, D = c2 :: rest := ⟨_, rfl⟩
              obtain ⟨L, hLr⟩ : ∃ L, rest.length + 1 = L := ⟨_, rfl⟩
              have hLD : D.length = L := by subst hD hLr; simp
              have hbsD : ∀ i, i < L → bs.getD (2 + i) 0#8 = D.getD i 0#8 := by
                intro i hi; subst hD hLr
                rw [show 2 + i = (i + 1) + 1 by omega, hbs_rest (i + 1) (by omega)]
                simp
              have hLpos : 0 < L := by omega
              have hoffL : 2 + L + 1 = bs.length := by omega
              have hx9L : BitVec.ofNat 64 (rest.length + 1 + 1) - 1#64 = BitVec.ofNat 64 L := by
                subst hLr; bv_omega
              rw [show parseDecimalU32 (c2 :: rest) = parseDecimalU32 D by rw [hD]]
              clear hD
              checked_loop_proof 2
          · -- no sign: the digits are `c1 :: c2 :: rest`, from byte 1
            have hpb : (BitVec.zeroExtend 32 c1 == 43#32) = false := by
              simp only [beq_eq_false_iff_ne, ne_eq]; bv_omega
            have hpb' : (BitVec.zeroExtend 32 c1 != 43#32) = true := by
              simp only [bne_iff_ne, ne_eq]; bv_omega
            simp only [hp, ↓reduceIte]
            by_cases hL9 : rest.length + 1 + 1 < 9
            · have hcs : (9#64).ule (BitVec.ofNat 64 (rest.length + 1 + 1)) = false := by
                simp only [BitVec.ule, decide_eq_false_iff_not]; bv_omega
              have hcs' : (9#64).ule (BitVec.ofNat 64 (rest.length + 1 + 1) - 0#64) = false := by
                simp only [BitVec.ule, decide_eq_false_iff_not]; bv_omega
              wp_steps 29
              obtain ⟨D, hD⟩ : ∃ D, D = c1 :: c2 :: rest := ⟨_, rfl⟩
              obtain ⟨L, hLr⟩ : ∃ L, rest.length + 1 + 1 = L := ⟨_, rfl⟩
              have hLD : D.length = L := by subst hD hLr; simp
              have hbsD : ∀ i, i < L → bs.getD (1 + i) 0#8 = D.getD i 0#8 := by
                intro i hi; subst hD hLr
                rw [show 1 + i = i + 1 by omega, hbs_rest i (by omega)]
              have hLpos : 0 < L := by omega
              have hoffL : 1 + L + 1 = bs.length := by omega
              rw [show parseDecimalU32 (c1 :: c2 :: rest) = parseDecimalU32 D by rw [hD]]
              clear hD
              replace hL9 : L < 9 := by omega
              small_loop_proof 1
            · have hcs : (9#64).ule (BitVec.ofNat 64 (rest.length + 1 + 1)) = true := by
                simp only [BitVec.ule, decide_eq_true_eq]; bv_omega
              have hcs' : (9#64).ule (BitVec.ofNat 64 (rest.length + 1 + 1) - 0#64) = true := by
                simp only [BitVec.ule, decide_eq_true_eq]; bv_omega
              wp_steps 28
              obtain ⟨D, hD⟩ : ∃ D, D = c1 :: c2 :: rest := ⟨_, rfl⟩
              obtain ⟨L, hLr⟩ : ∃ L, rest.length + 1 + 1 = L := ⟨_, rfl⟩
              have hLD : D.length = L := by subst hD hLr; simp
              have hbsD : ∀ i, i < L → bs.getD (1 + i) 0#8 = D.getD i 0#8 := by
                intro i hi; subst hD hLr
                rw [show 1 + i = i + 1 by omega, hbs_rest i (by omega)]
              have hLpos : 0 < L := by omega
              have hoffL : 1 + L + 1 = bs.length := by omega
              rw [show parseDecimalU32 (c1 :: c2 :: rest) = parseDecimalU32 D by rw [hD]]
              clear hD
              checked_loop_proof 1
    · have hcb : (BitVec.zeroExtend 32 c != 35#32) = true := by
        simp only [bne_iff_ne, ne_eq]; bv_omega
      simp only [hc, ↓reduceIte, resultCode, nameOutAfter, idOutAfter]
      wp_steps
      wp_done

end SudoRsMachineCode
