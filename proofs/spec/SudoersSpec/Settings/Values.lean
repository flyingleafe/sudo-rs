/-!
# Value parsers of the `Defaults` settings

Transcribes the parsers behind `check_integer` (`src/defaults/mod.rs`): `integer_in_range`,
`octal_mode`, `fractional_minutes` (with `find_dot` and `decimal`), and the `u32`/`u64`
`from_str_radix` of the Rust core library they call (`from_ascii_bytes_radix_impl` in
`core/src/num/mod.rs`, Charon toolchain `1.100.0-nightly-2026-09-17`).

A Rust `&str` is its UTF-8 bytes, and these parsers work on bytes (`as_bytes`, `split_at`,
`len`), so the spec does too: `bytes s` are the UTF-8 bytes of `s` as numbers. Integers are
`Nat`; the bounds of `u32`/`u64` are explicit.

`fractional_minutes` can panic (an arithmetic overflow) on inputs longer than any `Numeric`
token; `fractionalMinutesRun` says exactly when, and `fractionalMinutes` is the panic-free value
(`fractionalMinutesRun_eq` relates them for inputs of at most 18 bytes).

Everything is total and reduces in the kernel.
-/

namespace SudoersSpec.Settings

/-- The UTF-8 bytes of a text, i.e. the bytes of the Rust `&str` with that text. -/
def bytes (s : String) : List Nat := s.toByteArray.data.toList.map (·.toNat)

/-- `u32::MAX`. -/
def u32Max : Nat := 2 ^ 32 - 1

/-- `u64::MAX`. -/
def u64Max : Nat := 2 ^ 64 - 1

/-- The outcome of a Rust computation that can panic. -/
inductive Outcome (α : Type) where
  | ok (a : α)
  | panic
  deriving DecidableEq, Repr

/-- `core::num::IntErrorKind` (`core/src/num/error.rs`): why parsing an integer failed. Unsigned
parsing produces `Empty`, `InvalidDigit` and `PosOverflow`. -/
inductive IntErrorKind where
  | Empty
  | InvalidDigit
  | PosOverflow
  | NegOverflow
  | Zero
  deriving DecidableEq, Repr

/-- `(b as char).to_digit(radix)` for a byte `b` and `2 ≤ radix ≤ 36`
(`core/src/char/methods.rs`): `0`-`9`, then `a`-`z` and `A`-`Z` from 10, if below `radix`. -/
def asciiDigit (b radix : Nat) : Option Nat :=
  let d :=
    if 48 ≤ b ∧ b ≤ 57 then some (b - 48)
    else if 97 ≤ b ∧ b ≤ 122 then some (b - 87)
    else if 65 ≤ b ∧ b ≤ 90 then some (b - 55)
    else none
  match d with
  | some x => if x < radix then some x else none
  | none => none

/-- The digit loop of `from_ascii_bytes_radix_impl` for an unsigned type with maximum `max`: the
first byte that is not a digit is `InvalidDigit`; a value above `max` is `PosOverflow`. (Rust has
an unchecked loop, used only where no overflow is possible, and a checked one that tests the
digit before the overflow of the multiplication; both give these results.) -/
def parseDigits (radix max : Nat) : List Nat → Nat → Except IntErrorKind Nat
  | [], acc => .ok acc
  | b :: rest, acc =>
    match asciiDigit b radix with
    | none => .error .InvalidDigit
    | some x =>
      if acc * radix + x ≤ max then parseDigits radix max rest (acc * radix + x)
      else .error .PosOverflow

/-- `u32::from_str_radix` / `u64::from_str_radix` (`max` is the type's maximum) on the bytes of
the text: the empty input is `Empty`; a lone `+` or `-` is `InvalidDigit`; one leading `+` is
skipped (a leading `-` is not a digit of an unsigned type); then the digits. Rust panics unless
`2 ≤ radix ≤ 36`; every caller passes 8 or 10. -/
def fromStrRadix (max radix : Nat) (b : List Nat) : Except IntErrorKind Nat :=
  match b with
  | [] => .error .Empty
  | [43] => .error .InvalidDigit
  | [45] => .error .InvalidDigit
  | 43 :: rest => parseDigits radix max rest 0
  | b => parseDigits radix max b 0

/-- `decimal` (`src/defaults/mod.rs`): `u64::from_str_radix(input, 10).ok()`, which is
`input.parse::<u64>().ok()`. -/
def decimal (b : List Nat) : Option Nat :=
  match fromStrRadix u64Max 10 b with
  | .ok v => some v
  | .error _ => none

/-- `integer_in_range` (`src/defaults/mod.rs`): the `u64` denoted by `text` in base `radix`, if
it lies in `first..=last`. -/
def integerInRange (text : String) (radix first last : Nat) : Option Nat :=
  match fromStrRadix u64Max radix (bytes text) with
  | .ok v => if first ≤ v ∧ v ≤ last then some v else none
  | .error _ => none

/-- `octal_mode` (`src/defaults/mod.rs`): a leading `0`, then a `libc::mode_t` (`u32` on Linux)
in base 8, widened to `u64`. So `0` alone is rejected and `00` is 0. -/
def octalMode (text : String) : Option Nat :=
  match bytes text with
  | 48 :: digits =>
    match fromStrRadix u32Max 8 digits with
    | .ok v => some v
    | .error _ => none
  | _ => none

/-- `find_dot` (`src/defaults/mod.rs`): the position of the first `.`, or the length. -/
def findDot : List Nat → Nat
  | [] => 0
  | b :: rest => if b = 46 then 0 else findDot rest + 1

/-- `fractional_minutes` (`src/defaults/mod.rs`) with its panics: without `.`, `n * 60` for a
decimal `n`, `None` on overflow (`checked_mul`). With a first `.` at byte `k`: `integral` the
bytes before, `fractional` the bytes after; `shift = 10 ^ fractional.len()` (`None` if the
length does not fit `u32`, a panic if the power exceeds `u64`); `integral * shift`, `+
fractional`, `* 60` panic on `u64` overflow; the value is `(integral * shift + fractional) * 60 /
shift`. The parses are tried in this order: `shift`, `integral`, the multiplication,
`fractional`. -/
def fractionalMinutesRun (text : String) : Outcome (Option Nat) :=
  let b := bytes text
  let dot := findDot b
  if dot < b.length then
    let integral := b.take dot
    let fractional := b.drop (dot + 1)
    if u32Max < fractional.length then .ok none
    else
      let shift := 10 ^ fractional.length
      if u64Max < shift then .panic
      else
        match decimal integral with
        | none => .ok none
        | some i =>
          if u64Max < i * shift then .panic
          else
            match decimal fractional with
            | none => .ok none
            | some f =>
              if u64Max < i * shift + f then .panic
              else if u64Max < (i * shift + f) * 60 then .panic
              else .ok (some ((i * shift + f) * 60 / shift))
  else
    match decimal b with
    | none => .ok none
    | some m => .ok (if m * 60 ≤ u64Max then some (m * 60) else none)

/-- `fractional_minutes` without its panics: the value in unbounded arithmetic. Equal to the Rust
result on inputs of at most 18 bytes (`fractionalMinutesRun_eq`), which is every `Numeric` token
(`MAX_LEN = 18`, the UTF-8 length). -/
def fractionalMinutes (text : String) : Option Nat :=
  let b := bytes text
  let dot := findDot b
  if dot < b.length then
    let shift := 10 ^ (b.drop (dot + 1)).length
    match decimal (b.take dot), decimal (b.drop (dot + 1)) with
    | some i, some f => some ((i * shift + f) * 60 / shift)
    | _, _ => none
  else
    match decimal b with
    | none => none
    | some m => if m * 60 ≤ u64Max then some (m * 60) else none

/-! ## No panic on short inputs -/

theorem parseDigits_lt (radix max : Nat) (l : List Nat) (acc v : Nat)
    (h : parseDigits radix max l acc = .ok v) : v < (acc + 1) * radix ^ l.length := by
  induction l generalizing acc with
  | nil =>
    simp only [parseDigits, Except.ok.injEq] at h
    subst h; simp
  | cons b rest ih =>
    simp only [parseDigits] at h
    split at h
    · cases h
    · rename_i x hx
      split at h
      · have hx' : x < radix := by
          simp only [asciiDigit] at hx
          split at hx <;> (try split at hx) <;> (try split at hx) <;> simp_all
          all_goals (split at hx <;> simp_all)
        have := ih _ h
        have e : (acc * radix + x + 1) * radix ^ rest.length ≤
            (acc + 1) * radix ^ (rest.length + 1) := by
          rw [Nat.pow_succ', ← Nat.mul_assoc]
          apply Nat.mul_le_mul_right
          rw [Nat.add_mul, Nat.one_mul]
          omega
        simp only [List.length_cons]
        omega
      · cases h

theorem fromStrRadix_digits (max radix : Nat) (b : List Nat) (v : Nat)
    (h : fromStrRadix max radix b = .ok v) :
    ∃ l, parseDigits radix max l 0 = .ok v ∧ l.length ≤ b.length := by
  unfold fromStrRadix at h
  split at h
  · cases h
  · cases h
  · cases h
  · exact ⟨_, h, by simp⟩
  · exact ⟨_, h, Nat.le_refl _⟩

theorem fromStrRadix_lt (max radix : Nat) (b : List Nat) (v : Nat) (hr : 0 < radix)
    (h : fromStrRadix max radix b = .ok v) : v < radix ^ b.length := by
  obtain ⟨l, hl, hlen⟩ := fromStrRadix_digits _ _ _ _ h
  have := parseDigits_lt _ _ _ _ _ hl
  have := Nat.pow_le_pow_right hr hlen
  simp only [Nat.zero_add, Nat.one_mul] at *
  omega

theorem decimal_lt (b : List Nat) (v : Nat) (h : decimal b = some v) : v < 10 ^ b.length := by
  unfold decimal at h
  split at h
  · rename_i hv; simp only [Option.some.injEq] at h; subst h
    exact fromStrRadix_lt _ _ _ _ (by decide) hv
  · cases h

theorem findDot_le (b : List Nat) : findDot b ≤ b.length := by
  induction b with
  | nil => simp [findDot]
  | cons x rest ih => simp only [findDot]; split <;> simp <;> omega

/-- **`fractional_minutes` does not panic on a `Numeric` token**: on at most 18 bytes the Rust
outcome is the panic-free value. -/
theorem fractionalMinutesRun_eq (text : String) (h : (bytes text).length ≤ 18) :
    fractionalMinutesRun text = .ok (fractionalMinutes text) := by
  simp only [fractionalMinutesRun, fractionalMinutes]
  generalize bytes text = b at h ⊢
  split
  · rename_i hdot
    have hlen : (b.drop (findDot b + 1)).length + (b.take (findDot b)).length + 1 ≤ 18 := by
      simp only [List.length_drop, List.length_take]; omega
    generalize b.drop (findDot b + 1) = fr at hlen ⊢
    generalize b.take (findDot b) = ig at hlen ⊢
    have hF : fr.length ≤ 17 := by omega
    have hpow : 10 ^ fr.length ≤ 10 ^ 17 := Nat.pow_le_pow_right (by omega) hF
    have h32 : ¬ u32Max < fr.length := by simp only [u32Max]; omega
    have h64 : ¬ u64Max < 10 ^ fr.length := by
      have : (10 : Nat) ^ 17 ≤ u64Max := by decide
      omega
    simp only [h32, h64, ↓reduceIte]
    rcases hi : decimal ig with _ | i <;> rcases hf : decimal fr with _ | f
    · rfl
    · rfl
    · have hi' := decimal_lt _ _ hi
      have : i * 10 ^ fr.length < 10 ^ (ig.length + fr.length) := by
        rw [Nat.pow_add]; exact Nat.mul_lt_mul_of_pos_right hi' (Nat.pow_pos (by omega))
      have hb : 10 ^ (ig.length + fr.length) ≤ 10 ^ 17 :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have : (10 : Nat) ^ 17 ≤ u64Max := by decide
      simp only [show ¬ u64Max < i * 10 ^ fr.length by omega, ↓reduceIte]
    · have hi' := decimal_lt _ _ hi
      have hf' := decimal_lt _ _ hf
      have hsum : i * 10 ^ fr.length + f < 10 ^ (ig.length + fr.length) := by
        rw [Nat.pow_add]
        have : (i + 1) * 10 ^ fr.length ≤ 10 ^ ig.length * 10 ^ fr.length :=
          Nat.mul_le_mul_right _ hi'
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
      have hb : 10 ^ (ig.length + fr.length) ≤ 10 ^ 17 :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have : (10 : Nat) ^ 17 * 60 ≤ u64Max := by decide
      simp only [show ¬ u64Max < i * 10 ^ fr.length by omega,
        show ¬ u64Max < i * 10 ^ fr.length + f by omega,
        show ¬ u64Max < (i * 10 ^ fr.length + f) * 60 by omega, ↓reduceIte]
  · cases decimal b <;> rfl

end SudoersSpec.Settings
