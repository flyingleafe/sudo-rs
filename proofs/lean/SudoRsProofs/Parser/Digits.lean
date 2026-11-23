import SudoRsProofs.Parser.Ast

/-!
# `DigitsU32`

The extracted decimal loop checks the bound at every step; the reference digit fold checks the
bound after the last digit. An overflowing prefix cannot become in range again. The reference
constructor additionally handles a leading `+`, which the extracted constructor and the token
scanner do not accept.
-/

open Aeneas Aeneas.Std Result
open SudoersSpec.Syntax (charToDigit digitsU32Token fromStrRadix isAsciiDigit token)
open sudo_rs.sudoers.tokens (parse_u32 parse_u32_loop)
open sudo_rs.sudoers.tokens.DigitsU32.Insts

namespace SudoRsProofs.Parser

private theorem charToDigit_decimal (c : Char) :
    charToDigit 10 c = if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then some (c.toNat - 48) else none := by
  simp only [charToDigit, Char.le_def, UInt32.le_iff_toNat_le, Char.toNat_val,
    ← Bool.decide_and, decide_eq_true_eq]
  change (match (if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then some (c.toNat - 48)
    else if 97 ≤ c.toNat ∧ c.toNat ≤ 122 then some (c.toNat - 97 + 10)
    else if 65 ≤ c.toNat ∧ c.toNat ≤ 90 then some (c.toNat - 65 + 10)
    else none) with
    | some d => if d < 10 then some d else none
    | none => none) = _
  by_cases h : 48 ≤ c.toNat ∧ c.toNat ≤ 57
  · have hd : c.toNat - 48 < 10 := by omega
    simp [h, hd]
  · by_cases ha : 97 ≤ c.toNat ∧ c.toNat ≤ 122
    · simp [h, ha]
    · by_cases hA : 65 ≤ c.toNat ∧ c.toNat ≤ 90
      · simp [h, ha, hA]
      · simp [h, ha, hA]

private theorem asciiDigit_decimal (c : Char) : sudo_rs.asciiDigit c.toNat 10 = charToDigit 10 c := by
  rw [charToDigit_decimal]
  unfold sudo_rs.asciiDigit
  by_cases h : 48 ≤ c.toNat ∧ c.toNat ≤ 57
  · have hd : c.toNat - 48 < 10 := by omega
    simp [h, hd]
  · by_cases ha : 97 ≤ c.toNat ∧ c.toNat ≤ 122
    · have hd : 10 ≤ c.toNat - 87 := by omega
      simp [h, ha, hd]
    · by_cases hA : 65 ≤ c.toNat ∧ c.toNat ≤ 90
      · have hd : 10 ≤ c.toNat - 55 := by omega
        simp [h, ha, hA, hd]
      · simp [h, ha, hA]

private def digitU32 (d : Nat) : U32 := ⟨BitVec.ofNat 32 d⟩

private theorem to_digit_decimal (c : Char) :
    core.char.methods.Char.to_digit c 10#u32 = ok ((charToDigit 10 c).map digitU32) := by
  have hten : (10#u32).val = 10 := by simp
  simp only [core.char.methods.Char.to_digit, hten, asciiDigit_decimal]
  rfl

private theorem digitU32_val {c : Char} {d : Nat} (h : charToDigit 10 c = some d) :
    (digitU32 d).val = d := by
  rw [charToDigit_decimal] at h
  split at h
  · rename_i hd
    have e := Option.some.inj h
    subst d
    change (BitVec.ofNat 32 (c.toNat - 48)).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · cases h

private def appendDigit (acc digit : U32) : Option U32 :=
  (U32.checked_mul acc 10#u32).bind (fun shifted => U32.checked_add shifted digit)

/-- The two checked operations succeed exactly when the full decimal step fits. -/
private theorem appendDigit_spec (acc digit : U32) :
    match appendDigit acc digit with
    | none => 4294967296 ≤ acc.val * 10 + digit.val
    | some sum => acc.val * 10 + digit.val < 4294967296 ∧ sum.val = acc.val * 10 + digit.val := by
  have hten : (10#u32).val = 10 := by simp
  have hmul := U32.checked_mul_bv_spec acc 10#u32
  cases hm : U32.checked_mul acc 10#u32 with
  | none =>
    simp only [hm, hten, U32.max_eq] at hmul
    simp only [appendDigit, hm, Option.bind_none]
    omega
  | some shifted =>
    simp only [hm, hten, U32.max_eq] at hmul
    have hadd := U32.checked_add_bv_spec shifted digit
    cases ha : U32.checked_add shifted digit with
    | none =>
      simp only [ha, U32.max_eq] at hadd
      simp only [appendDigit, hm, Option.bind_some, ha]
      omega
    | some sum =>
      simp only [ha, U32.max_eq] at hadd
      simp only [appendDigit, hm, Option.bind_some, ha]
      exact ⟨by omega, by omega⟩

private def decimalStep (acc : Option Nat) (c : Char) : Option Nat :=
  match acc, charToDigit 10 c with
  | some v, some d => some (v * 10 + d)
  | _, _ => none

private def fitU32 : Option Nat → Option Nat
  | some v => if v < 4294967296 then some v else none
  | none => none

private def decimalFold (cs : List Char) (acc : Option Nat) : Option Nat :=
  fitU32 (cs.foldl decimalStep acc)

private theorem foldl_decimal_none (cs : List Char) : cs.foldl decimalStep none = none := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have hn : decimalStep none c = none := by cases charToDigit 10 c <;> rfl
    simpa only [List.foldl_cons, hn] using ih

private theorem decimalFold_overflow (cs : List Char) (n : Nat) (h : 4294967296 ≤ n) :
    decimalFold cs (some n) = none := by
  induction cs generalizing n with
  | nil => simp [decimalFold, fitU32, Nat.not_lt.mpr h]
  | cons c cs ih =>
    simp only [decimalFold, List.foldl_cons]
    cases hd : charToDigit 10 c with
    | none => simp [decimalStep, hd, foldl_decimal_none, fitU32]
    | some d =>
      simp only [decimalStep, hd]
      exact ih (n * 10 + d) (by omega)

private theorem parse_u32_loop_stop (text : Slice Char) (acc : U32) (i : Usize) :
    parse_u32_loop text acc false i = ok (acc, false) := by
  rw [parse_u32_loop]; simp

private theorem parse_u32_loop_next (text : Slice Char) (acc : U32) (i j : Usize)
    (hi : i.val < text.val.length) (hj : i + 1#usize = ok j) :
    parse_u32_loop text acc true i =
      match ((charToDigit 10 text.val[i.val]).map digitU32).bind (appendDigit acc) with
      | none => ok (acc, false)
      | some sum => parse_u32_loop text sum true j := by
  have hlt : i < Slice.len text := (UScalar.lt_equiv _ _).2 (by simpa using hi)
  have hix : Slice.index_usize text i = ok text.val[i.val] :=
    eq_ok_of_spec (Slice.index_usize_spec text i hi)
  rw [parse_u32_loop]
  simp only [↓reduceIte, ite_eq_left hlt, hix, to_digit_decimal, bind_ok]
  cases hd : charToDigit 10 text.val[i.val] with
  | none => simp [hj, parse_u32_loop_stop]
  | some d =>
    cases hm : U32.checked_mul acc 10#u32 with
    | none => simp [appendDigit, hm, lift, hj, parse_u32_loop_stop]
    | some shifted =>
      cases ha : U32.checked_add shifted (digitU32 d) <;>
        simp [appendDigit, hm, ha, lift, hj, parse_u32_loop_stop]

private theorem parse_u32_loop_spec (text : Slice Char) (acc : U32) (good : Bool) (i : Usize) :
    ∃ r, parse_u32_loop text acc good i = ok r ∧
      (if r.2 then some r.1.val else none) =
        (if good then decimalFold (text.val.drop i.val) (some acc.val) else none) := by
  cases good with
  | false => exact ⟨(acc, false), parse_u32_loop_stop text acc i, rfl⟩
  | true =>
    by_cases hi : i.val < text.val.length
    · have hinc : i.val + (1#usize).val ≤ Usize.max := by
        have := Slice.length_ineq text
        simp
        omega
      obtain ⟨j, hj, hjv⟩ := exists_eq_ok_of_spec (Usize.add_spec hinc)
      have hj' : j.val = i.val + 1 := by simpa using hjv
      have hdrop : text.val.drop i.val = text.val[i.val] :: text.val.drop (i.val + 1) :=
        List.drop_eq_getElem_cons hi
      rw [parse_u32_loop_next text acc i j hi hj, hdrop]
      simp only [↓reduceIte, decimalFold, List.foldl_cons]
      cases hd : charToDigit 10 text.val[i.val] with
      | none =>
        refine ⟨(acc, false), by simp, ?_⟩
        simp [decimalStep, hd, foldl_decimal_none, fitU32]
      | some d =>
        have hstep := appendDigit_spec acc (digitU32 d)
        have hdv := digitU32_val hd
        cases hsum : appendDigit acc (digitU32 d) with
        | none =>
          have hover : 4294967296 ≤ acc.val * 10 + d := by simpa only [hsum, hdv] using hstep
          refine ⟨(acc, false), by simp [hsum], ?_⟩
          simp only [decimalStep, hd]
          exact (decimalFold_overflow _ _ hover).symm
        | some sum =>
          have hval : acc.val * 10 + d < 4294967296 ∧ sum.val = acc.val * 10 + d := by
            simpa only [hsum, hdv] using hstep
          obtain ⟨r, hr, hrv⟩ := parse_u32_loop_spec text sum true j
          refine ⟨r, by simp [hsum, hr], ?_⟩
          simpa only [decimalStep, hd, ↓reduceIte, decimalFold, hj', hval.2] using hrv
    · have hlt : ¬ i < Slice.len text := fun h => hi (by simpa using (UScalar.lt_equiv _ _).1 h)
      have hdrop := List.drop_eq_nil_of_le (Nat.le_of_not_gt hi)
      have hacc : acc.val < 4294967296 := UScalar.hBounds acc
      refine ⟨(acc, true), ?_, ?_⟩
      · rw [parse_u32_loop]; simp [hlt]
      · simp [hdrop, decimalFold, fitU32, hacc]
termination_by text.val.length - i.val
decreasing_by omega

private def decimal : List Char → Option Nat
  | [] => none
  | c :: cs => decimalFold (c :: cs) (some 0)

private theorem parse_u32_spec (text : Slice Char) :
    ∃ o, parse_u32 text = ok o ∧ o.map (fun x => x.val) = decimal text.val := by
  cases h : text.val with
  | nil =>
    have he : core.slice.Slice.is_empty text = ok true := by
      simp [core.slice.Slice.is_empty, h]
    refine ⟨none, ?_, rfl⟩
    unfold parse_u32
    simp only [he, bind_ok]
    simp [parse_u32_loop_stop, uncurry_apply_pair]
  | cons c cs =>
    have he : core.slice.Slice.is_empty text = ok false := by
      simp [core.slice.Slice.is_empty, h]
    obtain ⟨⟨v, good⟩, hr, hv⟩ := parse_u32_loop_spec text 0#u32 true 0#usize
    cases good
    · refine ⟨none, ?_, by simpa [decimal, h] using hv⟩
      unfold parse_u32
      simp only [he, bind_ok]
      simp [hr, uncurry_apply_pair]
    · refine ⟨some v, ?_, by simpa [decimal, h] using hv⟩
      unfold parse_u32
      simp only [he, bind_ok]
      simp [hr, uncurry_apply_pair]

/-! The reference `fromStrRadix` accepts one leading `+`; the extracted constructor does not.
The exact condition for the two constructors to agree is therefore the equality of the two
decimal readings. -/

private theorem digitsValue_eq_foldl (ds : List Char) :
    SudoersSpec.Syntax.digitsValue 10 ds = ds.foldl decimalStep (some 0) := rfl

private theorem isAsciiDigit_charToDigit {c : Char} (h : isAsciiDigit c = true) :
    charToDigit 10 c = some (c.toNat - 48) := by
  simp only [isAsciiDigit, Char.le_def, Bool.and_eq_true, decide_eq_true_eq] at h
  have h1 : 48 ≤ c.toNat := by
    have := (UInt32.le_iff_toNat_le (a := '0'.val) (b := c.val)).mp h.1
    show 48 ≤ c.val.toNat
    simpa using this
  have h2 : c.toNat ≤ 57 := by
    have := (UInt32.le_iff_toNat_le (a := c.val) (b := '9'.val)).mp h.2
    show c.val.toNat ≤ 57
    simpa using this
  rw [charToDigit_decimal]
  simp [h1, h2]

private theorem charToDigit_ne_none {c : Char} (h : charToDigit 10 c ≠ none) :
    c ≠ '+' ∧ c ≠ '-' := by
  constructor
  · intro e; subst e
    exact h (show charToDigit 10 '+' = none from by decide)
  · intro e; subst e
    exact h (show charToDigit 10 '-' = none from by decide)

/-- Texts whose characters are all decimal digits read the same in the two constructs. -/
private theorem decimal_eq_fromStrRadix_digits (cs : List Char)
    (h : ∀ c ∈ cs, isAsciiDigit c = true) : decimal cs = fromStrRadix 10 32 cs := by
  cases cs with
  | nil => rfl
  | cons c rest =>
    have hc : charToDigit 10 c ≠ none := by
      rw [isAsciiDigit_charToDigit (h c (by simp))]
      simp
    obtain ⟨hplus, hminus⟩ := charToDigit_ne_none hc
    unfold decimal decimalFold fitU32 fromStrRadix
    cases rest with
    | nil =>
      simp [decimalStep, digitsValue_eq_foldl, Nat.reducePow, hplus, hminus]; rfl
    | cons d rest =>
      simp [decimalStep, digitsValue_eq_foldl, Nat.reducePow, hplus]; rfl

/-- The exact constructor domain: the extracted constructor refines the reference one on the
texts on which the two decimal readings agree. A leading `+` (which the reference skips) is the
only way for the reference to succeed where the extracted constructor reports `ValueTooLarge`,
so no larger precondition works for those texts. -/
def DigitsU32Pre (cs : List Char) : Prop :=
  decimal cs = fromStrRadix 10 32 cs

/-- `DigitsU32` refines the reference token on its exact constructor domain. -/
theorem digits_u32_token_refines :
    TokenRefines sudo_rs.sudoers.tokens.DigitsU32.Insts.Sudo_rsSudoersBasic_parserToken
      (fun x : U32 => x.val) digitsU32Token DigitsU32Pre where
  max_len := ⟨_, rfl, by simp [Sudo_rsSudoersBasic_parserToken.MAX_LEN, digitsU32Token]⟩
  max_len_le := by
    simp only [digitsU32Token]
    scalar_tac
  allow_escape := by simp [sudo_rs.sudoers.basic_parser.Token.ALLOW_ESCAPE.default, digitsU32Token]
  accept c := by
    simp only [Sudo_rsSudoersBasic_parserToken.accept, core.char.methods.Char.is_ascii_digit,
      digitsU32Token, isAsciiDigit, Char.isDigit, Char.le_def, ge_iff_le]
  accept_1st c := by
    simp only [Sudo_rsSudoersBasic_parserToken.accept, core.char.methods.Char.is_ascii_digit,
      digitsU32Token, isAsciiDigit, Char.isDigit, Char.le_def, ge_iff_le]
  escaped _ := rfl
  construct s hs h := by
    obtain ⟨v, hv, hd⟩ := chars_of_eq s hs
    obtain ⟨o, ho, hov⟩ := parse_u32_spec (alloc.vec.Vec.deref v)
    rw [hd] at hov
    cases o with
    | none =>
      have hcons : Sudo_rsSudoersBasic_parserToken.construct s = ok (.Err .ValueTooLarge) := by
        simp only [Sudo_rsSudoersBasic_parserToken.construct, hv, bind_ok, ho]
      refine ⟨_, hcons, ?_⟩
      change ConstructRel (fun x : U32 => x.val) (.Err .ValueTooLarge)
        (match fromStrRadix 10 32 s.toList with
         | some v => .ok v
         | none => .error .valueTooLarge)
      simp only [Option.map_none] at hov
      cases hfs : fromStrRadix 10 32 s.toList with
      | none => exact KindRel.valueTooLarge
      | some n =>
        have he : (none : Option Nat) = some n := (hov.trans h).trans hfs
        exact absurd he (by simp)
    | some x =>
      have hcons : Sudo_rsSudoersBasic_parserToken.construct s = ok (.Ok x) := by
        simp only [Sudo_rsSudoersBasic_parserToken.construct, hv, bind_ok, ho]
      refine ⟨_, hcons, ?_⟩
      change ConstructRel (fun x : U32 => x.val) (.Ok x)
        (match fromStrRadix 10 32 s.toList with
         | some v => .ok v
         | none => .error .valueTooLarge)
      simp only [Option.map_some] at hov
      cases hfs : fromStrRadix 10 32 s.toList with
      | none =>
        have he : (some x.val : Option Nat) = none := (hov.trans h).trans hfs
        exact absurd he (by simp)
      | some a =>
        have he : (some x.val : Option Nat) = some a := (hov.trans h).trans hfs
        exact Option.some.inj he

/-- The constructor agreement predicate is necessary as well as sufficient. -/
theorem digits_u32_construct_iff (s : String) (hs : s.utf8ByteSize ≤ Usize.max) :
    (∃ r, Sudo_rsSudoersBasic_parserToken.construct s = ok r ∧
      ConstructRel (fun x : U32 => x.val) r (digitsU32Token.construct s.toList)) ↔
      DigitsU32Pre s.toList := by
  constructor
  · rintro ⟨r, er, hr⟩
    obtain ⟨v, hv, hd⟩ := chars_of_eq s hs
    obtain ⟨o, ho, hov⟩ := parse_u32_spec (alloc.vec.Vec.deref v)
    rw [hd] at hov
    have hcon : Sudo_rsSudoersBasic_parserToken.construct s =
        ok (match o with
          | some x => core.result.Result.Ok x
          | none => core.result.Result.Err .ValueTooLarge) := by
      simp only [Sudo_rsSudoersBasic_parserToken.construct, hv, bind_ok, ho]
      cases o <;> rfl
    rw [hcon, ok.injEq] at er
    subst r
    change ConstructRel _ _ (match fromStrRadix 10 32 s.toList with
      | some x => .ok x
      | none => .error .valueTooLarge) at hr
    unfold DigitsU32Pre
    rw [← hov]
    cases o <;> cases hread : fromStrRadix 10 32 s.toList <;>
      simp only [hread, ConstructRel] at hr <;>
      first | rfl | exact congrArg some hr
  · exact digits_u32_token_refines.construct s hs

/-- The scanner only emits digit texts, so the blanket parser needs no extra hypothesis. -/
theorem digits_u32_parse_refines :
    ParseRefines (sudo_rs.sudoers.basic_parser.Parse.Blanket
      sudo_rs.sudoers.tokens.DigitsU32.Insts.Sudo_rsSudoersBasic_parserToken)
      (fun x : U32 => x.val) (token digitsU32Token) := by
  apply token_refines digits_u32_token_refines
  intro cs ht
  match cs with
  | [] => cases ht
  | c :: rest =>
    apply decimal_eq_fromStrRadix_digits
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · have := ht.1
      simpa only [Produces, digitsU32Token, Bool.false_eq_true, false_and, or_false] using this
    · have := ht.2 d hd
      simpa only [Produces, digitsU32Token, Bool.false_eq_true, false_and, or_false] using this

/-- `DigitsU32::DESCRIPTION` is the release description `"number"`. -/
theorem digits_u32_description :
    DescRel sudo_rs.sudoers.tokens.DigitsU32.Insts.Sudo_rsSudoersAst_namesUserFriendly
      SudoersSpec.Syntax.Descriptions.release.digitsU32 :=
  ⟨_, rfl, by
    simp only [Sudo_rsSudoersAst_namesUserFriendly.DESCRIPTION]
    exact toStr_val _ _⟩

end SudoRsProofs.Parser
