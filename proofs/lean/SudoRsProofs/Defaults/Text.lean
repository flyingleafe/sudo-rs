import SudoRsProofs.Defaults.Abs

/-! `check_text` returns the modifier of `checkText`, with an explicit UTF-8 representation
hypothesis on the input. -/

open Aeneas Aeneas.Std Result
open sudo_rs

namespace SudoRsProofs.Defaults

/-- **`check_text` refines `checkText`.** -/
theorem check_text_eq (id : defaults.TextSetting) (t : Str) (s : String)
    (ht : t.val = stringBytes s) :
    ∃ r, defaults.check_text id t = ok r ∧
      r.map absModifier = SudoersSpec.Settings.checkText (absTextSetting id) s := by
  have hstr := stringOfStr_of_val ht
  cases id <;> simp only [defaults.check_text, absTextSetting, SudoersSpec.Settings.checkText,
    core.convert.IntoFrom.into,
    BoxStr.Insts.CoreConvertFromShared0Str.from, Str.Insts.CoreCmpPartialEqStr.eq, bind_ok]
  all_goals try (exact ⟨_, rfl, by simp [absModifier, hstr]⟩)
  all_goals
    split <;> simp_all [str_eq_toStr_iff ht, absModifier, absLecture, absVerifypw, absTimestampType]
  all_goals split_ifs <;> simp_all [absModifier, absLecture, absVerifypw, absTimestampType]

end SudoRsProofs.Defaults
