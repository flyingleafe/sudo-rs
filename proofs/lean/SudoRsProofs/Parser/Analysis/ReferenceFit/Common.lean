import SudoRsProofs.Parser.Analysis.Input
import SudoersSpec.Grammar.SudoFile

/-! Inspecting successful grammar outcomes for machine representability. -/

open Aeneas Aeneas.Std SudoersSpec SudoersSpec.Syntax SudoersSpec.Grammar

namespace SudoRsProofs.Parser.Analysis.Ref

/-- The value of every derivation satisfies the given predicate. -/
def GrammarGood (good : α → Prop) (G : Gram α) : Prop := ∀ ⦃c a r⦄, G c a r → good a

theorem nonterm_good {good : α → Prop} {G : Gram α} (h : GrammarGood good G) :
    GrammarGood good (NontermG G) := by
  rintro _ _ _ ⟨_, _, _, hd, _⟩
  exact h hd

private theorem tail_good {good : α → Prop} {G : Gram α} (h : GrammarGood good G)
    {sep c xs r} (ht : ListTail G sep c xs r) : ∀ x ∈ xs, good x := by
  induction ht with
  | nil => simp
  | cons _ he _ ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact nonterm_good (G := G) h he
    · exact ih _ hx

theorem list_good {good : α → Prop} {G : Gram α} {sep : Char} {max : Nat}
    (h : GrammarGood good G) : GrammarGood (fun xs => ∀ x ∈ xs, good x) (ListG G sep max) := by
  intro c xs r hl
  cases hl with
  | mk he ht _ =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact nonterm_good (G := G) h he
    · exact tail_good (G := G) h ht _ hx

theorem list_length_bound {G : Gram α} {sep : Char} {max : Nat} {c xs r}
    (h : ListG G sep max c xs r) (hmax : 0 < max) : xs.length ≤ max := by
  cases h with
  | mk _ _ hl =>
    rcases hl with he | he
    · simp [he]; omega
    · simp only [List.length_cons]; omega

/-- Only names and aliases that survive into the AST need to fit the matcher model. -/
def MetaFit (good : α → Prop) : Meta α → Prop
  | .all => True
  | .only x => good x
  | .alias nm => Fits nm

theorem qual_good {good : α → Prop} {G : Gram (Meta α)}
    (h : GrammarGood (MetaFit good) G) : GrammarGood (specFits good) (QualG G) := by
  intro c a r hd
  cases hd with
  | mk _ _ ha =>
    have hm := nonterm_good (G := G) h ha
    unfold Qualified.ofBangs
    split <;> (cases ‹Meta α› <;> exact hm)

theorem spec_list_good {good : α → Prop} {G : Gram (Meta α)} {m : Many}
    (h : GrammarGood (MetaFit good) G) : GrammarGood (listFits good) (SpecListG G m) :=
  list_good (G := QualG G) (qual_good (G := G) h)

private theorem token_length_bound (limit : Nat) (cs acc : List Char)
    (ha : utf8Len acc ≤ limit + 4) (hl : LenOK limit acc cs) :
    utf8Len (acc ++ cs) ≤ limit + 4 := by
  induction cs generalizing acc with
  | nil => simpa using ha
  | cons c cs ih =>
    have hpush : utf8Len (acc ++ [c]) ≤ limit + 4 := by
      have hcut := hl.1
      have hsize := Char.utf8Size_le_four c
      simp [utf8Len, List.sum_append] at *
      omega
    simpa only [List.append_assoc, List.singleton_append] using ih (acc ++ [c]) hpush hl.2

theorem token_construct_good {good : α → Prop} {T : TokenSpec α}
    (h : ∀ cs, utf8Len cs ≤ T.maxLen + 4 → ∀ a, T.construct cs = .ok a → good a) :
    GrammarGood good (TokenG T) := by
  intro _ _ _ hg
  cases hg with
  | mk _ _ hl hc =>
    apply h _ _ _ hc
    rename_i u x c' xs a rest
    change utf8Len ([x] ++ xs) ≤ T.maxLen + 4
    apply token_length_bound _ _ _ _ hl
    have := Char.utf8Size_le_four x
    simp [utf8Len]
    omega

theorem ofList_fits {cs : List Char} (h : utf8Len cs ≤ Usize.max) : Fits (String.ofList cs) := by
  have heq : (String.ofList cs).utf8ByteSize = utf8Len cs := by
    clear h
    induction cs with
    | nil => rfl
    | cons c cs ih =>
      rw [String.ofList_cons, String.utf8ByteSize_append, String.utf8ByteSize_singleton, ih]
      simp [utf8Len]
  change (sudo_rs.stringBytes (String.ofList cs)).length ≤ Usize.max
  simp only [sudo_rs.stringBytes, List.length_map, Array.length_toList]
  change (String.ofList cs).utf8ByteSize ≤ Usize.max
  rwa [heq]

theorem token_text_fits {cs : List Char} {limit : Nat}
    (h : utf8Len cs ≤ limit + 4) (hb : limit + 4 ≤ Usize.max) : Fits (String.ofList cs) :=
  ofList_fits (h.trans hb)

end SudoRsProofs.Parser.Analysis.Ref
