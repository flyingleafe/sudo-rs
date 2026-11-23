import SudoersSpec.Grammar.SudoInclude

/-! Exact stream boundaries for `parseList`, including whitespace after each element and
separator. The element grammar need not characterize failures: only the separator can end a
successful list, and it does so by rejecting without consuming. -/

namespace SudoersSpec.Grammar

open SudoersSpec.Syntax SudoersSpec.Syntax.Parser

/-- An element and its trailing whitespace. The intermediate cursor is the one returned by
the element itself, before the nonterminal wrapper skips whitespace. -/
def CursorNontermG (G : Stream → α → Stream → Prop) (s : Stream) (a : α) (t : Stream) : Prop :=
  ∃ u, G s a u ∧ AtCursor WsG u () t

/-- Each further element is preceded by a separator and its trailing whitespace. The nil
production leaves the cursor unchanged and requires the separator to be absent. -/
inductive CursorListTailG (G : Stream → α → Stream → Prop) (sep : Char) :
    Stream → List α → Stream → Prop
  | nil {s : Stream} : NextNot (· = sep) s.rest → CursorListTailG G sep s [] s
  | cons {s u v t : Stream} {a : α} {as : List α} :
      AtCursor (SynG sep) s () u → CursorNontermG G u a v → CursorListTailG G sep v as t →
      CursorListTailG G sep s (a :: as) t

/-- A nonempty list, with exact cursors throughout. A singleton can succeed even if `max = 0`:
the parser checks the bound only when it finds a separator. -/
inductive CursorListG (G : Stream → α → Stream → Prop) (sep : Char) (max : Nat) :
    Stream → List α → Stream → Prop
  | mk {s u t : Stream} {a : α} {as : List α} :
      CursorNontermG G s a u → CursorListTailG G sep u as t → (as = [] ∨ as.length < max) →
      CursorListG G sep max s (a :: as) t

theorem tryNonterminal_at_iff {p : Parser α} {G : Stream → α → Stream → Prop}
    (hp : ∀ {s t a}, p.run s = (.ok a, t) ↔ G s a t) {s t : Stream} {a : α} :
    (tryNonterminal p).run s = (.ok a, t) ↔ CursorNontermG G s a t := by
  unfold tryNonterminal CursorNontermG
  rw [run_bind_eq_ok]
  constructor
  · rintro ⟨b, u, h₁, h₂⟩
    obtain ⟨_, v, hw, h₃⟩ := run_bind_eq_ok.mp h₂
    simp only [run_pure, Prod.mk.injEq, Except.ok.injEq] at h₃
    obtain ⟨rfl, rfl⟩ := h₃
    exact ⟨u, hp.mp h₁, skipTrailingWhitespace_sound.atCursor hw⟩
  · rintro ⟨u, h₁, hw⟩
    exact ⟨a, u, hp.mpr h₁,
      run_bind_eq_ok.mpr ⟨(), t, hw.complete skipTrailingWhitespace_complete, rfl⟩⟩

private theorem listLoop_run_cursor (sep : Char) (max : Nat) (description : String)
    (p : Parser α) (elems : List α) (s : Stream) :
    (listLoop sep max description p elems).run s =
      match (trySyntax sep).run s with
      | (.error .reject, u) => (.ok elems, u)
      | (.error (.fatal sp k), u) => (.error (.fatal sp k), u)
      | (.ok (), u) =>
        if elems.length ≥ max then
          (.error (.fatal ⟨u.getPos, u.getPos⟩ .tooManyItemsInList), u)
        else
          match (expectNonterminal description p).run u with
          | (.ok b, v) => (listLoop sep max description p (elems ++ [b])).run v
          | (.error e, v) => (.error e, v) := by
  unfold listLoop whileMaybe
  rw [loop_run, whileMaybeBody_run]
  rcases (trySyntax sep).run s with ⟨r, u⟩
  cases r with
  | error e => cases e <;> rfl
  | ok x =>
    cases x
    simp only [maybe_ok]
    rw [parseListBody_run]
    by_cases hl : elems.length ≥ max
    · simp only [hl, ite_true]
    · simp only [hl, ite_false]
      rcases (expectNonterminal description p).run u with ⟨r, v⟩
      cases r <;> rfl

private theorem listLoop_at_iff {p : Parser α} {G : Stream → α → Stream → Prop}
    (hp : ∀ {s t a}, p.run s = (.ok a, t) ↔ G s a t) {sep : Char} {max : Nat}
    {description : String} {elems a : List α} {s t : Stream} :
    (listLoop sep max description p elems).run s = (.ok a, t) ↔
      ∃ as, CursorListTailG G sep s as t ∧ a = elems ++ as ∧
        (as = [] ∨ elems.length + as.length ≤ max) := by
  constructor
  · intro h
    induction hs : s.rest.length using Nat.strongRecOn generalizing s elems with
    | _ n ih =>
      rw [listLoop_run_cursor] at h
      rcases hsep : (trySyntax sep).run s with ⟨r, u⟩
      rw [hsep] at h
      cases r with
      | error e =>
        cases e with
        | fatal sp k => cases h
        | reject =>
          obtain ⟨rfl, hn⟩ := trySyntax_reject_iff.mp hsep
          simp only [Prod.mk.injEq, Except.ok.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨[], .nil hn, by simp, .inl rfl⟩
      | ok x =>
        cases x
        by_cases hl : elems.length ≥ max
        · simp [hl] at h
        · simp only [hl, ite_false] at h
          rcases he : (expectNonterminal description p).run u with ⟨r, v⟩
          rw [he] at h
          cases r with
          | error e => cases h
          | ok b =>
            have hlt : v.rest.length < s.rest.length :=
              Nat.lt_of_le_of_lt (length_le_of_run he) (trySyntax_consumes sep _ _ _ hsep)
            obtain ⟨as, ht, ha, hb⟩ := ih _ (hs ▸ hlt) (s := v) (elems := elems ++ [b]) h rfl
            refine ⟨b :: as, .cons ((trySyntax_sound sep).atCursor hsep)
              ((tryNonterminal_at_iff hp).mp (expectNonterminal_ok_iff.mp he)) ht,
              by simpa [List.append_assoc] using ha, .inr ?_⟩
            rcases hb with rfl | hb
            · simp only [List.length_cons, List.length_nil]
              omega
            · simp only [List.length_append, List.length_cons, List.length_nil] at hb ⊢
              omega
  · rintro ⟨as, hg, rfl, hb⟩
    induction hg generalizing elems with
    | nil hstop =>
      have hsep := (trySyntax_reject_iff (ch := sep)).mpr ⟨rfl, hstop⟩
      rw [listLoop_run_cursor, hsep]
      simp
    | @cons s u v t b as hsep hg ht ih =>
      have hl : ¬ elems.length ≥ max := by
        rcases hb with h | h
        · cases h
        · simp only [List.length_cons] at h
          omega
      have hb' : as = [] ∨ (elems ++ [b]).length + as.length ≤ max := by
        right
        rcases hb with h | h
        · cases h
        · simp only [List.length_append, List.length_cons, List.length_nil] at h ⊢
          omega
      have hsep' := hsep.complete (trySyntax_complete sep)
      have he : (expectNonterminal description p).run u = (.ok b, v) :=
        expectNonterminal_ok_iff.mpr ((tryNonterminal_at_iff hp).mpr hg)
      rw [listLoop_run_cursor, hsep']
      simp only [hl, ite_false, he]
      simpa [List.append_assoc] using ih hb'

/-- Success of `parseList` is exactly derivability over the input and returned cursors. -/
theorem parseList_at_iff {p : Parser α} {G : Stream → α → Stream → Prop}
    (hp : ∀ {s t a}, p.run s = (.ok a, t) ↔ G s a t) (sep : Char) (max : Nat)
    (description : String) {s t : Stream} {a : List α} :
    (parseList sep max description p).run s = (.ok a, t) ↔ CursorListG G sep max s a t := by
  unfold parseList
  rw [run_bind_eq_ok]
  constructor
  · rintro ⟨b, u, h₁, h₂⟩
    change (listLoop sep max description p [b]).run u = (.ok a, t) at h₂
    obtain ⟨as, ht, rfl, hb⟩ := (listLoop_at_iff hp).mp h₂
    refine .mk ((tryNonterminal_at_iff hp).mp h₁) ht ?_
    rcases hb with h | h
    · exact .inl h
    · right
      change as.length < max
      change 1 + as.length ≤ max at h
      omega
  · intro h
    cases h with
    | mk h₁ ht hb =>
      refine ⟨_, _, (tryNonterminal_at_iff hp).mpr h₁, ?_⟩
      apply (listLoop_at_iff hp).mpr
      refine ⟨_, ht, rfl, ?_⟩
      rcases hb with h | h
      · exact .inl h
      · right
        simp only [List.length_cons, List.length_nil]
        omega

end SudoersSpec.Grammar
