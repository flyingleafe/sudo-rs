import SudoersSpec.Syntax.Ast

/-!
# Grammar: the shape of the declarative grammar and of the theorems PT2 to PT4

A nonterminal of the grammar (PLAN.md section 5.2) is a relation

```
G : List Char → α → List Char → Prop     -- G c a rest
```

"the characters `c` derive the value `a` when they are followed by `rest`". The third argument
is the right context; the grammar only ever asks *negative* questions about it ("the next
character is not a host-name character", "not `,`", "not a blank"), and those questions are the
follow conditions: maximal munch of tokens and of whitespace, the end of a list, the end of a
run of `!`. At the end of the input every such question is answered "yes" (`NextNot.nil`).
Inside a production the right context of a part is what the later parts consumed followed by
the right context of the whole, so the follow conditions between parts are part of the
derivation, and the follow condition of the whole is `G c a rest` for the actual `rest`.

The theorems of PLAN.md section 4 then read, for a production `p : Parser α`:

* PT2 `RejectPure p`: a `Reject` leaves the stream unchanged.
* PT3 `Sound p G`: on success, the consumed characters derive the value, with the actual
  remaining input as right context (positions: `Sound.pos`).
* PT4 `Complete p G`: a derivation with right context `rest` makes `p` succeed on `c ++ rest`
  with the value and leave exactly `rest` (positions: `Complete.run_eq`).

Together they give `run_ok_iff` (the parser succeeds leaving `rest` exactly when the grammar
derives) and unambiguity (`Complete.unambiguous`, `Complete.derives_unique`).
-/

namespace SudoersSpec.Grammar

open SudoersSpec.Syntax
open SudoersSpec.Syntax.Parser
open _root_.SudoersSpec.Syntax.Stream (Reaches)

/-- A nonterminal: `G c a rest`, the characters `c` derive `a` when followed by `rest`. -/
abbrev Gram (α : Type) := List Char → α → List Char → Prop

/-- The follow conditions: the right context `r` does not start with a character satisfying
`P`. -/
def NextNot (P : Char → Prop) (r : List Char) : Prop :=
  ∀ d, r.head? = some d → ¬ P d

@[simp] theorem NextNot.nil (P : Char → Prop) : NextNot P [] := by
  intro d h; cases h

theorem NextNot.cons_iff {P : Char → Prop} {d : Char} {r : List Char} :
    NextNot P (d :: r) ↔ ¬ P d := by
  constructor
  · intro h; exact h d rfl
  · intro h d' e; cases e; exact h

theorem NextNot.append_left {P : Char → Prop} {x y : List Char} (h : NextNot P (x ++ y))
    (hx : x ≠ []) : ∀ d, x.head? = some d → ¬ P d := by
  intro d e
  cases x with
  | nil => exact absurd rfl hx
  | cons a x => exact h d (by simpa using e)

/-- Truncation of the right context: `NextNot` questions about `x ++ y` are questions about
`x` when `x` is non-empty and are vacuous when it is empty. -/
theorem NextNot.trunc {P : Char → Prop} {x y : List Char} (h : NextNot P (x ++ y)) : NextNot P x := by
  intro d e
  cases x with
  | nil => cases e
  | cons a x => exact h d (by simpa using e)

theorem NextNot.mono {P Q : Char → Prop} {r : List Char} (h : NextNot P r) (hq : ∀ d, Q d → P d) :
    NextNot Q r :=
  fun d e hd => h d e (hq d hd)

/-- PT2: a `Reject` of `p` leaves the stream unchanged (the contract written on `trait Parse`). -/
def RejectPure (p : Parser α) : Prop :=
  ∀ s s', p.run s = (.error .reject, s') → s' = s

/-- PT3: soundness of `p` with respect to `G`. -/
def Sound (p : Parser α) (G : Gram α) : Prop :=
  ∀ s a s', p.run s = (.ok a, s') → ∃ c, s.rest = c ++ s'.rest ∧ G c a s'.rest

/-- PT4: completeness of `p` with respect to `G`. -/
def Complete (p : Parser α) (G : Gram α) : Prop :=
  ∀ c a rest s, G c a rest → s.rest = c ++ rest → ∃ s', p.run s = (.ok a, s') ∧ s'.rest = rest

/-- The right context only matters through finite prefixes: shortening it keeps a derivation.
With `x = []` this says that the end of the input is always an admissible follow. -/
def Trunc (G : Gram α) : Prop :=
  ∀ c a x y, G c a (x ++ y) → G c a x

/-- `Derives G c a` (PLAN.md `Derives c a`): `c` derives `a` with some right context. -/
def Derives (G : Gram α) (c : List Char) (a : α) : Prop :=
  ∃ rest, G c a rest

/-! ## Transport along equivalent grammars -/

theorem Sound.mono {p : Parser α} {G G' : Gram α} (h : Sound p G)
    (hg : ∀ c a r, G c a r → G' c a r) : Sound p G' := by
  intro s a s' hr
  obtain ⟨c, hc, hd⟩ := h s a s' hr
  exact ⟨c, hc, hg _ _ _ hd⟩

theorem Complete.mono {p : Parser α} {G G' : Gram α} (h : Complete p G)
    (hg : ∀ c a r, G' c a r → G c a r) : Complete p G' :=
  fun c a rest s hd hs => h c a rest s (hg _ _ _ hd) hs

/-! ## Positions -/

theorem take_sub_length_append (c r : List Char) :
    (c ++ r).take ((c ++ r).length - r.length) = c := by
  simp

/-- PT3 with positions: the position after the run is the position after reading the
consumed characters. -/
theorem Sound.pos {p : Parser α} {G : Gram α} (h : Sound p G) {s s' : Stream} {a : α}
    (hr : p.run s = (.ok a, s')) :
    ∃ c, s.rest = c ++ s'.rest ∧ G c a s'.rest ∧ s'.getPos = posAfter c s.getPos := by
  obtain ⟨c, hc, hd⟩ := h s a s' hr
  refine ⟨c, hc, hd, ?_⟩
  have := (reaches_of_run hr).getPos_eq
  rw [this.2, hc, take_sub_length_append]

/-- The stream after a successful run that left `rest` from `c ++ rest`. -/
theorem run_eq_of_rest {p : Parser α} {c rest : List Char} {line col : Nat} {r : Parsed α}
    {s' : Stream} (h : p.run ⟨c ++ rest, line, col⟩ = (r, s')) (hs : s'.rest = rest) :
    s' = ⟨rest, (posAfter c (line, col)).1, (posAfter c (line, col)).2⟩ := by
  have := (reaches_of_run h).getPos_eq
  simp only [hs, Stream.getPos_mk] at this
  have hp := this.2
  rw [take_sub_length_append] at hp
  rcases s' with ⟨r', l', k'⟩
  simp only at hs
  subst hs
  simp only [Stream.getPos] at hp
  rw [← hp]

/-- PT4 with positions: the stream after the run is `rest` at the position after `c`. -/
theorem Complete.run_eq {p : Parser α} {G : Gram α} (h : Complete p G) {c : List Char} {a : α}
    {rest : List Char} (hd : G c a rest) (line col : Nat) :
    p.run ⟨c ++ rest, line, col⟩ =
      (.ok a, ⟨rest, (posAfter c (line, col)).1, (posAfter c (line, col)).2⟩) := by
  obtain ⟨s', hr, hs⟩ := h c a rest ⟨c ++ rest, line, col⟩ hd rfl
  rw [hr, run_eq_of_rest hr hs]

/-! ## Consequences of PT3 and PT4 together -/

/-- The parser succeeds on `c ++ rest` leaving exactly `rest` if and only if the grammar
derives `a` from `c` with right context `rest`. -/
theorem run_ok_iff {p : Parser α} {G : Gram α} (hs : Sound p G) (hc : Complete p G)
    {c rest : List Char} {a : α} {s : Stream} (h : s.rest = c ++ rest) :
    (∃ s', p.run s = (.ok a, s') ∧ s'.rest = rest) ↔ G c a rest := by
  constructor
  · rintro ⟨s', hr, hrest⟩
    obtain ⟨c', hc', hd⟩ := hs s a s' hr
    rw [hrest] at hc' hd
    rw [h] at hc'
    rw [List.append_cancel_right hc'.symm] at hd
    exact hd
  · intro hd; exact hc c a rest s hd h

/-- Unambiguity (PT4 corollary): two derivations of the same input split it in the same place
and give the same value. -/
theorem Complete.unambiguous {p : Parser α} {G : Gram α} (hc : Complete p G)
    {c c' r r' : List Char} {a a' : α} (h1 : G c a r) (h2 : G c' a' r') (he : c ++ r = c' ++ r') :
    c = c' ∧ a = a' := by
  obtain ⟨s1, hr1, hs1⟩ := hc c a r ⟨c ++ r, 1, 1⟩ h1 rfl
  obtain ⟨s2, hr2, hs2⟩ := hc c' a' r' ⟨c ++ r, 1, 1⟩ h2 he
  rw [hr1] at hr2
  simp only [Prod.mk.injEq, Except.ok.injEq] at hr2
  obtain ⟨rfl, rfl⟩ := hr2
  refine ⟨?_, rfl⟩
  rw [hs1] at hs2
  subst hs2
  exact List.append_cancel_right he

/-- Unambiguity of `Derives`: a text derives at most one value. -/
theorem Complete.derives_unique {p : Parser α} {G : Gram α} (hc : Complete p G) (ht : Trunc G)
    {c : List Char} {a a' : α} (h1 : Derives G c a) (h2 : Derives G c a') : a = a' := by
  obtain ⟨r1, h1⟩ := h1
  obtain ⟨r2, h2⟩ := h2
  have h1' := ht c a [] r1 h1
  have h2' := ht c a' [] r2 h2
  exact (hc.unambiguous h1' h2' rfl).2

/-- With truncation, `Derives` is derivation at the end of the input. -/
theorem derives_iff_nil {G : Gram α} (ht : Trunc G) {c : List Char} {a : α} :
    Derives G c a ↔ G c a [] :=
  ⟨fun ⟨r, h⟩ => ht c a [] r h, fun h => ⟨[], h⟩⟩

/-! ## Loops: an induction principle relating input and output streams -/

/-- Induction over the iterations of `Parser.loop`, for a property `P st s r s'` of the loop
state and input stream and the final result and stream. -/
theorem loop_rel {body : σ → Parser (Step σ β)} (hb : Progressive body)
    (P : σ → Stream → Parsed β → Stream → Prop)
    (hdone : ∀ st s b s', (body st).run s = (.ok (.done b), s') → P st s (.ok b) s')
    (herr : ∀ st s e s', (body st).run s = (.error e, s') → P st s (.error e) s')
    (hnext : ∀ st s st' s' r s'', (body st).run s = (.ok (.next st'), s') → P st' s' r s'' →
      P st s r s'') :
    ∀ st s, P st s ((loop body hb st).run s).1 ((loop body hb st).run s).2 := by
  intro st s
  induction h : s.rest.length using Nat.strongRecOn generalizing st s with
  | _ n ih =>
    rw [loop_run]
    have hd := hdone st s
    have he := herr st s
    have hn := hnext st s
    have hprog := hb st s
    revert hd he hn hprog
    cases (body st).run s with
    | mk r s' =>
      cases r with
      | error e => intro _ he _ _; exact he e s' rfl
      | ok r =>
        cases r with
        | done b => intro hd _ _ _; exact hd b s' rfl
        | next st' =>
          intro _ _ hn hprog
          have hlt := hprog st' s' rfl
          exact hn st' s' _ _ rfl (ih _ (h ▸ hlt) st' s' rfl)

/-- The run of `whileMaybeBody`. -/
theorem whileMaybeBody_run (q : Parser γ) (k : σ → γ → Parser (Step σ β)) (finish : σ → β)
    (st : σ) (s : Stream) :
    (whileMaybeBody q k finish st).run s =
      match Syntax.maybe (q.run s).1 with
      | .ok none => (.ok (.done (finish st)), (q.run s).2)
      | .ok (some a) => (k st a).run (q.run s).2
      | .error e => (.error e, (q.run s).2) := by
  simp only [whileMaybeBody, run_bind, run_maybe]
  cases q.run s with
  | mk r s1 =>
    cases r with
    | ok a => rfl
    | error e => cases e <;> rfl

end SudoersSpec.Grammar
