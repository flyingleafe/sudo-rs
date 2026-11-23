import SudoersSpec.Grammar.Token

/-!
# `Qualified<T>`, `parse_list`, `SpecList<T>`: generic grammar and PT2 to PT4

Each relation is parameterised by the grammar `G` of the element production, and each theorem
takes PT2/PT3/PT4 of the element production as hypotheses:

* `QualG G` (`impl Parse for Qualified<T>`): `('!' W)^n` followed by an element and its
  whitespace; the element must not start with `!` (the loop `while is_syntax('!')` ends there);
  the value is `allow a` for even `n`, `forbid a` for odd `n` (`Qualified.ofBangs`).
* `ListG G sep max` (`parse_list`): an element and its whitespace, then `(sep W element W)*`;
  the list ends in front of a character other than `sep`; at most `max` elements, except that a
  single element is always accepted (the check runs before each further element).
* `SpecListG G m` (`SpecList<T> = Vec<Qualified<Meta<T>>>`): `ListG (QualG G) m.sep m.limit`.
-/

namespace SudoersSpec.Grammar

open SudoersSpec.Syntax
open SudoersSpec.Syntax.Parser

variable {α : Type}

/-! ## `Qualified<T>` -/

/-- `('!' W)^n` with right context `rest`. -/
inductive Bangs : Nat → List Char → List Char → Prop
  | nil {rest : List Char} : Bangs 0 [] rest
  | cons {w b : List Char} {n : Nat} {rest : List Char} : Ws w (b ++ rest) → Bangs n b rest →
      Bangs (n + 1) ('!' :: w ++ b) rest

/-- The value of an item preceded by `n` exclamation marks. -/
def Qualified.ofBangs (n : Nat) (a : α) : Qualified α :=
  if n % 2 = 0 then .allow a else .forbid a

/-- `impl Parse for Qualified<T>` over the element grammar `G`. -/
inductive QualG (G : Gram α) : Gram (Qualified α)
  | mk {n : Nat} {b c : List Char} {a : α} {rest : List Char} : Bangs n b (c ++ rest) →
      NextNot (· = '!') (c ++ rest) → NontermG G c a rest →
      QualG G (b ++ c) (Qualified.ofBangs n a) rest

theorem Bangs.trunc {n : Nat} {b x y : List Char} (h : Bangs n b (x ++ y)) : Bangs n b x := by
  generalize e : x ++ y = r at h
  induction h with
  | nil => exact .nil
  | cons hw _ ih =>
    subst e
    exact .cons (Ws.trunc (by rw [← List.append_assoc] at hw; exact hw)) (ih rfl)

theorem QualG.trunc {G : Gram α} (hG : Trunc G) : Trunc (QualG G) := by
  intro c a x y h
  cases h with
  | mk hb hn hd =>
    refine .mk (Bangs.trunc (by rw [← List.append_assoc] at hb; exact hb)) ?_
      (NontermG.trunc hG _ _ _ _ hd)
    exact NextNot.trunc (by rw [← List.append_assoc] at hn; exact hn)

theorem QualG.mono {G G' : Gram α} (h : ∀ c a r, G c a r → G' c a r) {c : List Char}
    {q : Qualified α} {r : List Char} (hq : QualG G c q r) : QualG G' c q r := by
  cases hq with
  | mk hb hn hd => exact .mk hb hn (NontermG.mono h hd)

/-- The loop `while is_syntax('!')? { neg = !neg; }` from `neg`. -/
def bangLoop (neg : Bool) : Parser Bool :=
  whileMaybe (trySyntax '!') (trySyntax_consumes '!') (fun neg () => pure (.next !neg)) id neg

/-- `neg` flipped `n` times. -/
def flipN : Nat → Bool → Bool
  | 0, b => b
  | n + 1, b => flipN n (!b)

theorem flipN_true (n : Nat) : flipN n true = (n % 2 == 0) ∧ flipN n false = !(n % 2 == 0) := by
  induction n with
  | zero => simp [flipN]
  | succ n ih =>
    simp only [flipN, Bool.not_true, Bool.not_false]
    refine ⟨?_, ?_⟩
    · rw [ih.2]; cases h : n % 2 == 0 <;> simp_all <;> omega
    · rw [ih.1]; cases h : n % 2 == 0 <;> simp_all <;> omega

theorem isSyntax_ne_reject (ch : Char) (s : Stream) : ((isSyntax ch).run s).1 ≠ .error .reject := by
  rw [isSyntax_run]
  cases ((trySyntax ch).run s).1 with
  | ok a => simp
  | error e => cases e <;> simp

theorem bangLoop_sound (neg : Bool) (s : Stream) {v : Bool} {s' : Stream}
    (h : (bangLoop neg).run s = (.ok v, s')) :
    ∃ b n, s.rest = b ++ s'.rest ∧ Bangs n b s'.rest ∧ NextNot (· = '!') s'.rest ∧
      v = flipN n neg := by
  have key := loop_rel (whileMaybeBody_progressive (trySyntax_consumes '!')
      (fun neg () => pure (.next !neg)) id)
    (fun neg s r s'' => ∀ v, r = .ok v → ∃ b n, s.rest = b ++ s''.rest ∧ Bangs n b s''.rest ∧
      NextNot (· = '!') s''.rest ∧ v = flipN n neg) ?_ ?_ ?_ neg s
  · unfold bangLoop whileMaybe at h
    rw [h] at key
    exact key v rfl
  · intro st s b s' hb v hv
    cases hv
    rw [whileMaybeBody_run] at hb
    revert hb
    cases hq : (trySyntax '!').run s with
    | mk r s₁ =>
      cases r with
      | ok x => simp
      | error e =>
        cases e with
        | fatal sp k => simp
        | reject =>
          simp only [maybe_reject, id, Prod.mk.injEq, Except.ok.injEq, Step.done.injEq]
          rintro ⟨rfl, rfl⟩
          obtain ⟨rfl, hn⟩ := trySyntax_reject_iff.mp hq
          exact ⟨[], 0, rfl, .nil, hn, rfl⟩
  · intro st s e s' _ v hv; cases hv
  · intro st s st' s' r s'' hb ih v hv
    obtain ⟨b, n, hb', hbs, hn, rfl⟩ := ih v hv
    rw [whileMaybeBody_run] at hb
    revert hb
    cases hq : (trySyntax '!').run s with
    | mk r₁ s₁ =>
      cases r₁ with
      | ok x =>
        simp only [maybe_ok, run_pure, Prod.mk.injEq, Except.ok.injEq, Step.next.injEq]
        rintro ⟨rfl, rfl⟩
        obtain ⟨c, hc, w, rfl, hw⟩ := trySyntax_sound '!' _ _ _ hq
        refine ⟨'!' :: w ++ b, n + 1, ?_, .cons (by rw [← hb']; exact hw) hbs, hn, rfl⟩
        rw [hc, hb']; simp
      | error e => cases e <;> simp

theorem bangLoop_complete {n : Nat} {b r : List Char} (hb : Bangs n b r) (hn : NextNot (· = '!') r) :
    ∀ (neg : Bool) (s : Stream), s.rest = b ++ r →
      ∃ s', (bangLoop neg).run s = (.ok (flipN n neg), s') ∧ s'.rest = r := by
  induction hb with
  | nil =>
    intro neg s hs
    have hq : (trySyntax '!').run s = (.error .reject, s) :=
      trySyntax_reject_iff.mpr ⟨rfl, by rw [hs]; exact hn⟩
    unfold bangLoop whileMaybe
    rw [loop_run, whileMaybeBody_run, hq]
    exact ⟨s, rfl, hs⟩
  | @cons w b n rest hw _ ih =>
    intro neg s hs
    obtain ⟨s₁, h₁, hs₁⟩ := trySyntax_complete '!' ('!' :: w) () (b ++ rest) s ⟨w, rfl, hw⟩
      (by rw [hs]; simp)
    obtain ⟨s', h', hs'⟩ := ih hn (!neg) s₁ hs₁
    refine ⟨s', ?_, hs'⟩
    have e : (bangLoop neg).run s = (bangLoop (!neg)).run s₁ := by
      unfold bangLoop whileMaybe
      rw [loop_run, whileMaybeBody_run, h₁]
      rfl
    rw [e, h']; rfl

theorem bangLoop_ne_reject (neg : Bool) (s : Stream) :
    ((bangLoop neg).run s).1 ≠ .error .reject := by
  refine loop_invariant (whileMaybeBody_progressive (trySyntax_consumes '!')
      (fun neg () => pure (.next !neg)) id) (fun _ => True) (fun r _ => r ≠ .error .reject)
    (fun _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => by simp) ?_ neg s trivial
  intro st s e s' _ hb
  rw [whileMaybeBody_run] at hb
  revert hb
  cases (trySyntax '!').run s with
  | mk r₁ s₁ =>
    cases r₁ with
    | ok x => simp
    | error e' =>
      cases e' with
      | reject => simp
      | fatal sp k =>
        simp only [maybe_fatal, Prod.mk.injEq, Except.error.injEq]; rintro ⟨rfl, -⟩; simp

theorem qualified_run (description : String) (p : Parser α) (s : Stream) :
    (qualified description p).run s =
      match (isSyntax '!').run s with
      | (.ok true, s₁) =>
        match (bangLoop true).run s₁ with
        | (.ok neg, s₂) =>
          match (expectNonterminal description p).run s₂ with
          | (.ok a, s₃) => (.ok (if neg then .forbid a else .allow a), s₃)
          | (.error e, s₃) => (.error e, s₃)
        | (.error e, s₂) => (.error e, s₂)
      | (.ok false, s₁) =>
        match (tryNonterminal p).run s₁ with
        | (.ok a, s₂) => (.ok (.allow a), s₂)
        | (.error e, s₂) => (.error e, s₂)
      | (.error e, s₁) => (.error e, s₁) := by
  simp only [qualified, run_bind]
  cases (isSyntax '!').run s with
  | mk r₁ s₁ =>
    cases r₁ with
    | error e => rfl
    | ok b =>
      cases b with
      | false =>
        simp only [Bool.false_eq_true, ite_false, run_bind]
        cases (tryNonterminal p).run s₁ with
        | mk r₂ s₂ => cases r₂ <;> rfl
      | true =>
        simp only [ite_true, run_bind]
        rw [show (whileMaybe (trySyntax '!') (trySyntax_consumes '!')
          (fun neg () => pure (.next !neg)) id true) = bangLoop true from rfl]
        cases (bangLoop true).run s₁ with
        | mk r₂ s₂ =>
          cases r₂ with
          | error e => rfl
          | ok neg =>
            simp only [run_bind]
            cases (expectNonterminal description p).run s₂ with
            | mk r₃ s₃ =>
              cases r₃ with
              | error e => rfl
              | ok a => cases neg <;> rfl

/-- PT3 for `Qualified<T>`. -/
theorem qualified_sound {p : Parser α} {G : Gram α} (hp : Sound p G) (description : String) :
    Sound (qualified description p) (QualG G) := by
  intro s q s' h
  rw [qualified_run] at h
  revert h
  cases h₁ : (isSyntax '!').run s with
  | mk r₁ s₁ =>
    cases r₁ with
    | error e => intro h; cases h
    | ok b =>
      cases b with
      | false =>
        obtain ⟨hs1, hn⟩ := isSyntax_false_iff.mp h₁
        subst s₁
        simp only
        cases h₂ : (tryNonterminal p).run s with
        | mk r₂ s₂ =>
          cases r₂ with
          | error e => intro h; cases h
          | ok a =>
            intro h
            simp only [Prod.mk.injEq, Except.ok.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨c, hc, hd⟩ := tryNonterminal_sound hp _ _ _ h₂
            refine ⟨[] ++ c, hc, ?_⟩
            have := QualG.mk (G := G) (n := 0) Bangs.nil (by rw [← hc]; exact hn) hd
            simpa [Qualified.ofBangs] using this
      | true =>
        have h₁' := isSyntax_true_iff.mp h₁
        obtain ⟨c₀, hc₀, w, rfl, hw⟩ := trySyntax_sound '!' _ _ _ h₁'
        simp only
        cases h₂ : (bangLoop true).run s₁ with
        | mk r₂ s₂ =>
          cases r₂ with
          | error e => intro h; cases h
          | ok neg =>
            simp only
            cases h₃ : (expectNonterminal description p).run s₂ with
            | mk r₃ s₃ =>
              cases r₃ with
              | error e => intro h; cases h
              | ok a =>
                intro h
                simp only [Prod.mk.injEq, Except.ok.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                obtain ⟨b, n, hb, hbs, hn, rfl⟩ := bangLoop_sound true s₁ h₂
                obtain ⟨c, hc, hd⟩ := expectNonterminal_sound hp description _ _ _ h₃
                refine ⟨('!' :: w ++ b) ++ c, ?_, ?_⟩
                · rw [hc₀, hb, hc]; simp
                · have hq := QualG.mk (G := G) (n := n + 1)
                    (Bangs.cons (by rw [← hc, ← hb]; exact hw) (by rw [← hc]; exact hbs))
                    (by rw [← hc]; exact hn) hd
                  have hv : Qualified.ofBangs (n + 1) a =
                      (if flipN n true = true then .forbid a else .allow a) := by
                    rw [(flipN_true n).1, Qualified.ofBangs]
                    cases h : n % 2 == 0 <;> simp_all <;> omega
                  rw [hv] at hq; exact hq

/-- PT4 for `Qualified<T>`. -/
theorem qualified_complete {p : Parser α} {G : Gram α} (hp : Complete p G) (description : String) :
    Complete (qualified description p) (QualG G) := by
  intro c q rest s hq hs
  cases hq with
  | @mk n b c a _ hb hn hd =>
    cases hb with
    | nil =>
      have h₁ : (isSyntax '!').run s = (.ok false, s) :=
        isSyntax_false_iff.mpr ⟨rfl, by rw [hs]; exact hn⟩
      obtain ⟨s₂, h₂, hs₂⟩ := tryNonterminal_complete hp c a rest s hd (by rw [hs]; rfl)
      rw [qualified_run, h₁]
      simp only [h₂]
      exact ⟨s₂, by simp [Qualified.ofBangs], hs₂⟩
    | @cons w b' m _ hw hb' =>
      obtain ⟨s₁, h₁, hs₁⟩ := trySyntax_complete '!' ('!' :: w) () (b' ++ (c ++ rest)) s
        ⟨w, rfl, hw⟩ (by rw [hs]; simp)
      obtain ⟨s₂, h₂, hs₂⟩ := bangLoop_complete hb' hn true s₁ hs₁
      obtain ⟨s₃, h₃, hs₃⟩ := expectNonterminal_complete hp description c a rest s₂ hd hs₂
      rw [qualified_run, isSyntax_true_iff.mpr h₁]
      simp only [h₂, h₃]
      refine ⟨s₃, ?_, hs₃⟩
      have hv : Qualified.ofBangs (m + 1) a =
          (if flipN m true = true then .forbid a else .allow a) := by
        rw [(flipN_true m).1, Qualified.ofBangs]
        cases h : m % 2 == 0 <;> simp_all <;> omega
      rw [hv]

/-- PT2 for `Qualified<T>`, exactly: it rejects iff the element production rejects on the
same input with the same result (no `!` was read). -/
theorem qualified_reject {description : String} {p : Parser α} {s s' : Stream}
    (h : (qualified description p).run s = (.error .reject, s')) :
    p.run s = (.error .reject, s') := by
  rw [qualified_run] at h
  revert h
  have hne := isSyntax_ne_reject '!' s
  cases h₁ : (isSyntax '!').run s with
  | mk r₁ s₁ =>
    rw [h₁] at hne
    cases r₁ with
    | error e =>
      intro h; simp only [Prod.mk.injEq] at h
      exact absurd h.1 (by simpa using hne)
    | ok b =>
      cases b with
      | false =>
        obtain ⟨hs1, -⟩ := isSyntax_false_iff.mp h₁
        subst s₁
        simp only
        cases h₂ : (tryNonterminal p).run s with
        | mk r₂ s₂ =>
          cases r₂ with
          | ok a => intro h; simp at h
          | error e =>
            intro h
            simp only [Prod.mk.injEq, Except.error.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact tryNonterminal_reject.mp h₂
      | true =>
        simp only
        have hne2 := bangLoop_ne_reject true s₁
        cases h₂ : (bangLoop true).run s₁ with
        | mk r₂ s₂ =>
          rw [h₂] at hne2
          cases r₂ with
          | error e =>
            intro h; simp only [Prod.mk.injEq] at h
            exact absurd h.1 (by simpa using hne2)
          | ok neg =>
            simp only
            have hne3 := expectNonterminal_ne_reject description p s₂
            cases h₃ : (expectNonterminal description p).run s₂ with
            | mk r₃ s₃ =>
              rw [h₃] at hne3
              cases r₃ with
              | ok a => intro h; simp at h
              | error e =>
                intro h; simp only [Prod.mk.injEq] at h
                exact absurd h.1 (by simpa using hne3)

theorem qualified_rejectPure {p : Parser α} (hp : RejectPure p) (description : String) :
    RejectPure (qualified description p) :=
  fun s s' h => hp s s' (qualified_reject h)

/-! ## `parse_list` -/

/-- The part of a list after the first element: `(sep W element W)*`, ended in front of a
character other than `sep`. -/
inductive ListTail (G : Gram α) (sep : Char) : List Char → List α → List Char → Prop
  | nil {rest : List Char} : NextNot (· = sep) rest → ListTail G sep [] [] rest
  | cons {w c : List Char} {a : α} {c' : List Char} {as : List α} {rest : List Char} :
      Ws w (c ++ c' ++ rest) → NontermG G c a (c' ++ rest) → ListTail G sep c' as rest →
      ListTail G sep (sep :: w ++ c ++ c') (a :: as) rest

/-- `parse_list(sep, max)` over the element grammar `G`. -/
inductive ListG (G : Gram α) (sep : Char) (max : Nat) : Gram (List α)
  | mk {c : List Char} {a : α} {c' : List Char} {as : List α} {rest : List Char} :
      NontermG G c a (c' ++ rest) → ListTail G sep c' as rest → (as = [] ∨ as.length < max) →
      ListG G sep max (c ++ c') (a :: as) rest

theorem ListTail.trunc {G : Gram α} (hG : Trunc G) {sep : Char} {c : List Char} {as : List α}
    {x y : List Char} (h : ListTail G sep c as (x ++ y)) : ListTail G sep c as x := by
  generalize e : x ++ y = r at h
  induction h with
  | nil hn => subst e; exact .nil hn.trunc
  | cons hw hd _ ih =>
    subst e
    refine .cons (Ws.trunc (by rw [← List.append_assoc] at hw; exact hw)) ?_ (ih rfl)
    exact NontermG.trunc hG _ _ _ _ (by rw [← List.append_assoc] at hd; exact hd)

theorem ListG.trunc {G : Gram α} (hG : Trunc G) (sep : Char) (max : Nat) :
    Trunc (ListG G sep max) := by
  intro c as x y h
  cases h with
  | mk hd ht hl =>
    exact .mk (NontermG.trunc hG _ _ _ _ (by rw [← List.append_assoc] at hd; exact hd))
      (ListTail.trunc hG ht) hl

theorem ListTail.mono {G G' : Gram α} (h : ∀ c a r, G c a r → G' c a r) {sep : Char}
    {c : List Char} {as : List α} {r : List Char} (ht : ListTail G sep c as r) :
    ListTail G' sep c as r := by
  induction ht with
  | nil hn => exact .nil hn
  | cons hw hd _ ih => exact .cons hw (NontermG.mono h hd) ih

theorem ListG.mono {G G' : Gram α} (h : ∀ c a r, G c a r → G' c a r) {sep : Char} {max : Nat}
    {c : List Char} {as : List α} {r : List Char} (hl : ListG G sep max c as r) :
    ListG G' sep max c as r := by
  cases hl with
  | mk hd ht hc => exact .mk (NontermG.mono h hd) (ListTail.mono h ht) hc

/-- The loop of `parse_list` from the elements `elems` read so far. -/
def listLoop (sepBy : Char) (max : Nat) (description : String) (p : Parser α) (elems : List α) :
    Parser (List α) :=
  whileMaybe (trySyntax sepBy) (trySyntax_consumes sepBy) (parseListBody max description p) id
    elems

theorem parseListBody_run (max : Nat) (description : String) (p : Parser α) (elems : List α)
    (s : Stream) :
    (parseListBody max description p elems ()).run s =
      if elems.length ≥ max then
        (.error (.fatal ⟨s.getPos, s.getPos⟩ .tooManyItemsInList), s)
      else
        match (expectNonterminal description p).run s with
        | (.ok x, s₁) => (.ok (.next (elems ++ [x])), s₁)
        | (.error e, s₁) => (.error e, s₁) := by
  simp only [parseListBody]
  split
  · rfl
  · simp only [run_bind]
    cases (expectNonterminal description p).run s with
    | mk r s₁ => cases r <;> rfl

theorem listLoop_sound {sep : Char} {max : Nat} {description : String} {p : Parser α}
    {G : Gram α} (hp : Sound p G) (elems : List α) (s : Stream) {v : List α} {s' : Stream}
    (h : (listLoop sep max description p elems).run s = (.ok v, s')) :
    ∃ c as, s.rest = c ++ s'.rest ∧ ListTail G sep c as s'.rest ∧ v = elems ++ as ∧
      (as = [] ∨ elems.length + as.length ≤ max) := by
  have key := loop_rel (whileMaybeBody_progressive (trySyntax_consumes sep)
      (parseListBody max description p) id)
    (fun elems s r s'' => ∀ v, r = .ok v → ∃ c as, s.rest = c ++ s''.rest ∧
      ListTail G sep c as s''.rest ∧ v = elems ++ as ∧
      (as = [] ∨ elems.length + as.length ≤ max)) ?_ ?_ ?_ elems s
  · unfold listLoop whileMaybe at h
    rw [h] at key
    exact key v rfl
  · intro st s b s' hb v hv
    cases hv
    rw [whileMaybeBody_run] at hb
    revert hb
    cases hq : (trySyntax sep).run s with
    | mk r s₁ =>
      cases r with
      | ok x =>
        simp only [maybe_ok]; rw [parseListBody_run]
        split
        · simp
        · cases (expectNonterminal description p).run s₁ with
          | mk r₂ s₂ => cases r₂ <;> simp
      | error e =>
        cases e with
        | fatal sp k => simp
        | reject =>
          simp only [maybe_reject, id, Prod.mk.injEq, Except.ok.injEq, Step.done.injEq]
          rintro ⟨rfl, rfl⟩
          obtain ⟨rfl, hn⟩ := trySyntax_reject_iff.mp hq
          exact ⟨[], [], rfl, .nil hn, by simp, .inl rfl⟩
  · intro st s e s' _ v hv; cases hv
  · intro st s st' s' r s'' hb ih v hv
    obtain ⟨c', as, hc', ht, rfl, hl⟩ := ih v hv
    rw [whileMaybeBody_run] at hb
    revert hb
    cases hq : (trySyntax sep).run s with
    | mk r₁ s₁ =>
      cases r₁ with
      | ok x =>
        simp only [maybe_ok]; rw [parseListBody_run]
        split
        · simp
        · rename_i hlen
          cases h₂ : (expectNonterminal description p).run s₁ with
          | mk r₂ s₂ =>
            cases r₂ with
            | error e => simp
            | ok a =>
              simp only [Prod.mk.injEq, Except.ok.injEq, Step.next.injEq]
              rintro ⟨rfl, rfl⟩
              obtain ⟨c₀, hc₀, w, rfl, hw⟩ := trySyntax_sound sep _ _ _ hq
              obtain ⟨c, hc, hd⟩ := expectNonterminal_sound hp description _ _ _ h₂
              refine ⟨sep :: w ++ c ++ c', a :: as, ?_, ?_, by simp, ?_⟩
              · rw [hc₀, hc, hc']; simp
              · refine .cons ?_ (by rw [← hc']; exact hd) ht
                rw [List.append_assoc, ← hc', ← hc]; exact hw
              · right
                rcases hl with rfl | hl
                · simp; omega
                · simp at hl ⊢; omega
      | error e => cases e <;> simp

theorem listLoop_complete {sep : Char} {max : Nat} {description : String} {p : Parser α}
    {G : Gram α} (hp : Complete p G) {c : List Char} {as : List α} {rest : List Char}
    (ht : ListTail G sep c as rest) :
    ∀ (elems : List α) (s : Stream), (as = [] ∨ elems.length + as.length ≤ max) →
      s.rest = c ++ rest →
      ∃ s', (listLoop sep max description p elems).run s = (.ok (elems ++ as), s') ∧
        s'.rest = rest := by
  induction ht with
  | nil hn =>
    intro elems s _ hs
    have hq : (trySyntax sep).run s = (.error .reject, s) :=
      trySyntax_reject_iff.mpr ⟨rfl, by rw [hs]; exact hn⟩
    unfold listLoop whileMaybe
    rw [loop_run, whileMaybeBody_run, hq]
    exact ⟨s, by simp, hs⟩
  | @cons w c a c' as rest hw hd _ ih =>
    intro elems s hl hs
    obtain ⟨s₁, h₁, hs₁⟩ := trySyntax_complete sep (sep :: w) () (c ++ c' ++ rest) s
      ⟨w, rfl, hw⟩ (by rw [hs]; simp)
    obtain ⟨s₂, h₂, hs₂⟩ := expectNonterminal_complete hp description c a (c' ++ rest) s₁ hd
      (by rw [hs₁, List.append_assoc])
    have hlen : ¬ elems.length ≥ max := by
      rcases hl with h | h
      · cases h
      · simp at h; omega
    have hl' : as = [] ∨ (elems ++ [a]).length + as.length ≤ max := by
      rcases hl with h | h
      · cases h
      · cases as with
        | nil => exact .inl rfl
        | cons _ _ => right; simp only [List.length_append, List.length_cons,
            List.length_nil] at h ⊢; omega
    obtain ⟨s', h', hs'⟩ := ih (elems ++ [a]) s₂ hl' hs₂
    refine ⟨s', ?_, hs'⟩
    have e : (listLoop sep max description p elems).run s =
        (listLoop sep max description p (elems ++ [a])).run s₂ := by
      unfold listLoop whileMaybe
      rw [loop_run, whileMaybeBody_run, h₁]
      simp only [maybe_ok]
      rw [parseListBody_run]
      simp only [hlen, ite_false, h₂]
    rw [e, h']
    simp

theorem listLoop_ne_reject (sep : Char) (max : Nat) (description : String) (p : Parser α)
    (elems : List α) (s : Stream) :
    ((listLoop sep max description p elems).run s).1 ≠ .error .reject := by
  refine loop_invariant (whileMaybeBody_progressive (trySyntax_consumes sep)
      (parseListBody max description p) id) (fun _ => True) (fun r _ => r ≠ .error .reject)
    (fun _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => by simp) ?_ elems s trivial
  intro st s e s' _ hb
  rw [whileMaybeBody_run] at hb
  revert hb
  cases (trySyntax sep).run s with
  | mk r₁ s₁ =>
    cases r₁ with
    | ok x =>
      simp only [maybe_ok]; rw [parseListBody_run]
      split
      · simp only [Prod.mk.injEq, Except.error.injEq]; rintro ⟨rfl, -⟩; simp
      · have hne := expectNonterminal_ne_reject description p s₁
        revert hne
        cases (expectNonterminal description p).run s₁ with
        | mk r₂ s₂ =>
          cases r₂ with
          | ok a => simp
          | error e' =>
            simp only [ne_eq, Prod.mk.injEq, Except.error.injEq]
            rintro hne ⟨rfl, -⟩; simpa using hne
    | error e' =>
      cases e' with
      | reject => simp
      | fatal sp k =>
        simp only [maybe_fatal, Prod.mk.injEq, Except.error.injEq]; rintro ⟨rfl, -⟩; simp

theorem parseList_run (sepBy : Char) (max : Nat) (description : String) (p : Parser α)
    (s : Stream) :
    (parseList sepBy max description p).run s =
      match (tryNonterminal p).run s with
      | (.ok a, s₁) => (listLoop sepBy max description p [a]).run s₁
      | (.error e, s₁) => (.error e, s₁) := by
  simp only [parseList, run_bind]
  rfl

/-- PT3 for `parse_list`. -/
theorem parseList_sound {p : Parser α} {G : Gram α} (hp : Sound p G) (sep : Char) (max : Nat)
    (description : String) : Sound (parseList sep max description p) (ListG G sep max) := by
  intro s v s' h
  rw [parseList_run] at h
  revert h
  cases h₁ : (tryNonterminal p).run s with
  | mk r₁ s₁ =>
    cases r₁ with
    | error e => intro h; cases h
    | ok a =>
      intro h
      obtain ⟨c, hc, hd⟩ := tryNonterminal_sound hp _ _ _ h₁
      obtain ⟨c', as, hc', ht, rfl, hl⟩ := listLoop_sound hp [a] s₁ h
      refine ⟨c ++ c', by rw [hc, hc', List.append_assoc], ?_⟩
      show ListG G sep max (c ++ c') (a :: as) s'.rest
      refine .mk (by rw [← hc']; exact hd) ht ?_
      rcases hl with h | h
      · exact .inl h
      · right; simp only [List.length_singleton] at h; omega

/-- PT4 for `parse_list`. -/
theorem parseList_complete {p : Parser α} {G : Gram α} (hp : Complete p G) (sep : Char)
    (max : Nat) (description : String) : Complete (parseList sep max description p) (ListG G sep max) := by
  intro c v rest s hl hs
  cases hl with
  | @mk c a c' as _ hd ht hcount =>
    obtain ⟨s₁, h₁, hs₁⟩ := tryNonterminal_complete hp c a (c' ++ rest) s hd
      (by rw [hs, List.append_assoc])
    have hc2 : as = [] ∨ [a].length + as.length ≤ max := by
      rcases hcount with h | h
      · exact .inl h
      · right; simp only [List.length_singleton]; omega
    obtain ⟨s', h', hs'⟩ := listLoop_complete (description := description) (max := max) hp ht [a]
      s₁ hc2 hs₁
    rw [parseList_run, h₁]
    refine ⟨s', ?_, hs'⟩
    simp only
    rw [h']; rfl

/-- PT2 for `parse_list`, exactly: it rejects iff the element production rejects on the same
input with the same result. -/
theorem parseList_reject {sep : Char} {max : Nat} {description : String} {p : Parser α}
    {s s' : Stream} (h : (parseList sep max description p).run s = (.error .reject, s')) :
    p.run s = (.error .reject, s') := by
  rw [parseList_run] at h
  revert h
  cases h₁ : (tryNonterminal p).run s with
  | mk r₁ s₁ =>
    cases r₁ with
    | error e =>
      intro h; simp only [Prod.mk.injEq, Except.error.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact tryNonterminal_reject.mp h₁
    | ok a =>
      intro h
      have := listLoop_ne_reject sep max description p [a] s₁
      simp only at h
      rw [h] at this; exact absurd rfl this

theorem parseList_rejectPure {p : Parser α} (hp : RejectPure p) (sep : Char) (max : Nat)
    (description : String) : RejectPure (parseList sep max description p) :=
  fun s s' h => hp s s' (parseList_reject h)

/-! ## `SpecList<T>` -/

/-- `SpecList<T>` over the grammar `G` of `Meta<T>`, with the `Many` of `T`. -/
def SpecListG (G : Gram (Meta α)) (m : Many) : Gram (SpecList α) :=
  ListG (QualG G) m.sep m.limit

theorem specList_eq (m : Many) (description : String) (p : Parser (Meta α)) :
    specList m description p = parseList m.sep m.limit description (qualified description p) :=
  rfl

theorem specList_sound {p : Parser (Meta α)} {G : Gram (Meta α)} (hp : Sound p G) (m : Many)
    (description : String) : Sound (specList m description p) (SpecListG G m) :=
  parseList_sound (qualified_sound hp description) _ _ _

theorem specList_complete {p : Parser (Meta α)} {G : Gram (Meta α)} (hp : Complete p G) (m : Many)
    (description : String) : Complete (specList m description p) (SpecListG G m) :=
  parseList_complete (qualified_complete hp description) _ _ _

theorem specList_reject {m : Many} {description : String} {p : Parser (Meta α)} {s s' : Stream}
    (h : (specList m description p).run s = (.error .reject, s')) :
    p.run s = (.error .reject, s') :=
  qualified_reject (parseList_reject h)

theorem SpecListG.trunc {G : Gram (Meta α)} (hG : Trunc G) (m : Many) : Trunc (SpecListG G m) :=
  ListG.trunc (QualG.trunc hG) _ _

end SudoersSpec.Grammar
