import SudoRsProofs.Parser.Token
import SudoRsProofs.Defaults.Range
import SudoersSpec.Settings.FromParser
import SudoersSpec.Grammar.Token

/-! Successful reference tokens are small enough for the arguments of their extracted string
operations. The bounds come from the token loop, not from the assumption on the input cursor. -/

open Aeneas Aeneas.Std Result SudoersSpec

namespace SudoRsProofs.Parser.DefaultsParse

open Syntax Syntax.Parser

private theorem lenOK_bound {max : Nat} {cs : List Char} (h : Grammar.LenOK max cs xs)
    (hb : utf8Len cs ≤ max + 4) : utf8Len (cs ++ xs) ≤ max + 4 := by
  induction xs generalizing cs with
  | nil => simpa using hb
  | cons c tail ih =>
    obtain ⟨hlen, h⟩ := h
    have hpush : utf8Len (cs ++ [c]) ≤ max + 4 := by
      rw [Grammar.utf8Len_append]
      have hc := Char.utf8Size_le_four c
      simp only [utf8Len, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at *
      omega
    simpa only [List.append_assoc, List.singleton_append] using ih h hpush

private theorem ofList_utf8ByteSize (cs : List Char) :
    (String.ofList cs).utf8ByteSize = utf8Len cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [String.ofList_cons, String.utf8ByteSize_append, String.utf8ByteSize_singleton, ih]
    rfl

/-- Invert the successful return of a `tryNonterminal`: trailing whitespace cannot change its
value. -/
theorem token_before_ws {p : Syntax.Parser α} {s t : Stream} {v : α}
    (h : (tryNonterminal p).run s = (.ok v, t)) : ∃ mid, p.run s = (.ok v, mid) := by
  obtain ⟨a, mid, ha, h⟩ := run_bind_eq_ok.mp h
  obtain ⟨_, _, _, h⟩ := run_bind_eq_ok.mp h
  have he := Except.ok.inj (Prod.mk.inj h).1
  cases he
  exact ⟨mid, ha⟩

/-- A token whose constructor preserves its text cannot return a string beyond the loop's byte
budget. The extra four bytes cover the last character, checked before it is appended. -/
theorem token_size_le (T : TokenSpec String)
    (hT : ∀ cs, T.construct cs = .ok (String.ofList cs))
    {s t : Stream} {v : String} (h : (token T).run s = (.ok v, t)) :
    v.utf8ByteSize ≤ T.maxLen + 4 := by
  obtain ⟨_, _, hg⟩ := Grammar.token_sound T s v t h
  cases hg with
  | @mk _ first _ rest _ _ _ _ hlen hvalue =>
    rw [hT] at hvalue
    cases hvalue
    rw [ofList_utf8ByteSize]
    exact lenOK_bound hlen (by
      have h4 := Char.utf8Size_le_four first
      simp only [utf8Len, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      omega)

/-- The `&str` view's byte budget is exactly that of its source string. -/
theorem fits_of_utf8ByteSize (s : String) (h : s.utf8ByteSize ≤ Usize.max) : Fits s := by
  unfold Fits sudo_rs.stringBytes
  rw [List.length_map, Array.length_toList]
  exact h

/-- `String::as_str` returns the actual byte encoding for the settings lookup/checkers. -/
theorem as_str_bytes (s : String) (h : s.utf8ByteSize ≤ Usize.max) :
    ∃ t, alloc.string.String.as_str s = ok t ∧ t.val = sudo_rs.stringBytes s :=
  exists_eq_ok_of_spec (String.as_str_spec s (fits_of_utf8ByteSize s h))

end SudoRsProofs.Parser.DefaultsParse
