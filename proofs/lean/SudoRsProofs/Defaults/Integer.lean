import SudoRsProofs.Defaults.Parsers

/-! `check_integer` refines `checkInteger`: names and text are ordinary data, with the input
`&str` related to the spec text by its bytes. The timeout cases require the lexer bound of 18
bytes; the other two cases have no length bound. -/

open Aeneas Aeneas.Std Result
open sudo_rs

namespace SudoRsProofs.Defaults

/-- **`check_integer` returns `ok` and refines `checkInteger`**. The length hypothesis applies
only to the timeouts. -/
theorem check_integer_eq (id : defaults.IntegerSetting) (t : Str) (s : String)
    (ht : t.val = stringBytes s)
    (hlen : (id = .passwd_timeout ∨ id = .timestamp_timeout) → (Spec.bytes s).length ≤ 18) :
    ∃ r, defaults.check_integer id t = ok r ∧
      r.map absModifier = SudoersSpec.Settings.checkInteger (absIntegerSetting id) s := by
  cases id with
  | umask =>
    obtain ⟨r, hr, hv⟩ := octal_mode_eq t s ht
    simp only [defaults.check_integer, hr, bind_ok, absIntegerSetting,
      SudoersSpec.Settings.checkInteger, ← hv]
    cases r <;> exact ⟨_, rfl, rfl⟩
  | passwd_tries =>
    obtain ⟨r, hr, hv⟩ := integer_in_range_eq t s ht 10#u32 0#u64 1000#u64 (by simp)
    have hv' : r.map (·.val) = Spec.integerInRange s 10 0 1000 := hv
    simp only [defaults.check_integer, hr, bind_ok, absIntegerSetting,
      SudoersSpec.Settings.checkInteger, ← hv']
    cases r <;> exact ⟨_, rfl, rfl⟩
  | passwd_timeout =>
    obtain ⟨r, hr, hv⟩ := fractional_minutes_eq t s ht (hlen (.inl rfl))
    simp only [defaults.check_integer, hr, bind_ok, absIntegerSetting,
      SudoersSpec.Settings.checkInteger, ← hv]
    cases r <;> exact ⟨_, rfl, rfl⟩
  | timestamp_timeout =>
    obtain ⟨r, hr, hv⟩ := fractional_minutes_eq t s ht (hlen (.inr rfl))
    simp only [defaults.check_integer, hr, bind_ok, absIntegerSetting,
      SudoersSpec.Settings.checkInteger, ← hv]
    cases r <;> exact ⟨_, rfl, rfl⟩

end SudoRsProofs.Defaults
