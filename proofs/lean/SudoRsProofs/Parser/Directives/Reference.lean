import SudoRsProofs.Parser.PermissionLines.Common
import SudoRsProofs.Parser.Analysis.Abs

/-! Reference-side invariants used by the stable directive dispatch. -/

open Aeneas Aeneas.Std Result SudoersSpec

namespace SudoRsProofs.Parser

/-- Moving forward on one physical line cannot decrease the column. The saved cursor in
`get_directive` and the cursor after its first user list satisfy this relation. -/
theorem reaches_col_le_of_line_eq {s t : Syntax.Stream} (h : s.Reaches t)
    (hl : t.line = s.line) : s.col ≤ t.col := by
  obtain ⟨n, rfl⟩ := h
  induction n generalizing s with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    have monotone : ∀ (s : Syntax.Stream) (k : Nat), s.line ≤ (s.advance k).line := by
      intro x k
      induction k generalizing x with
      | zero => exact Nat.le_refl _
      | succ k ihk =>
        rw [Syntax.Stream.advance_succ]
        apply Nat.le_trans _ (ihk x.pop)
        rcases x with ⟨_ | ⟨c, cs⟩, l, k'⟩
        · rfl
        · by_cases hc : c = '\n'
          · subst c; rw [Syntax.Stream.pop_newline]; exact Nat.le_succ _
          · rw [Syntax.Stream.pop_other hc]
    rw [Syntax.Stream.advance_succ] at hl ⊢
    have hm := monotone s.pop n
    rcases s with ⟨_ | ⟨c, cs⟩, l, k⟩
    · exact ih hl
    · by_cases hc : c = '\n'
      · subst c
        simp only [Syntax.Stream.pop_newline] at hl hm
        omega
      · simp only [Syntax.Stream.pop_other hc] at hl ⊢
        exact Nat.le_trans (Nat.le_succ _) (ih hl)

/-- The abstract postcondition of a successful nonterminal use is inherited from the production
itself; trailing whitespace may only fail or leave its value alone. -/
theorem tryNonterminal_value {α : Type} {p : Syntax.Parser α} {P : α → Prop}
    (hp : ∀ s a t, p.run s = (.ok a, t) → P a) {s a t}
    (h : (Syntax.tryNonterminal p).run s = (.ok a, t)) : P a := by
  obtain ⟨b, s1, hb, h⟩ := Syntax.Parser.run_bind_eq_ok.mp h
  obtain ⟨_, _, _, h⟩ := Syntax.Parser.run_bind_eq_ok.mp h
  simp only [Syntax.Parser.run_pure, Prod.mk.injEq, Except.ok.injEq] at h
  exact h.1 ▸ hp _ _ _ hb

theorem expectNonterminal_value {α : Type} {p : Syntax.Parser α} {P : α → Prop}
    (hp : ∀ s a t, p.run s = (.ok a, t) → P a) {d s a t}
    (h : (Syntax.expectNonterminal d p).run s = (.ok a, t)) : P a := by
  simp only [Syntax.expectNonterminal, Syntax.Parser.run_bind, Syntax.Parser.run_getPos,
    Syntax.Parser.run_observe] at h
  split at h
  · simp at h
  · simp only [Syntax.Parser.run_lift, Prod.mk.injEq] at h
    exact tryNonterminal_value hp (Prod.ext h.1 rfl : (Syntax.tryNonterminal p).run s = (.ok a, _))

/-- Successful lists inherit element postconditions, and have at most `max 1 limit` elements.
The first element is parsed before the Rust limit check. -/
theorem parseList_success {α : Type} {p : Syntax.Parser α} {P : α → Prop}
    (hp : ∀ s a t, p.run s = (.ok a, t) → P a) {sep limit d s xs t}
    (h : (Syntax.parseList sep limit d p).run s = (.ok xs, t)) :
    xs.length ≤ max 1 limit ∧ ∀ a ∈ xs, P a := by
  open Syntax.Parser in
    obtain ⟨first, s1, hfirst, htail⟩ := run_bind_eq_ok.mp h
    let inv (l : List α) := l.length ≤ max 1 limit ∧ ∀ a ∈ l, P a
    have base : inv [first] := ⟨Nat.le_max_left .., by simpa using tryNonterminal_value hp hfirst⟩
    have hi := loop_invariant (whileMaybeBody_progressive (Syntax.trySyntax_consumes sep)
        (Syntax.parseListBody limit d p) id) inv
      (fun r _ => ∀ l, r = .ok l → inv l)
      (by
        intro st x st' y hst hstep
        obtain ⟨k, x1, _, hnext⟩ := run_bind_eq_ok.mp hstep
        cases k with
        | none => cases hnext
        | some u =>
          simp only [Syntax.parseListBody] at hnext
          split at hnext
          · simp at hnext
          · rename_i hlen
            obtain ⟨a, x2, ha, hnext⟩ := run_bind_eq_ok.mp hnext
            simp only [run_pure, Prod.mk.injEq, Except.ok.injEq, Step.next.injEq] at hnext
            obtain ⟨rfl, _⟩ := hnext
            refine ⟨?_, ?_⟩
            · simp only [List.length_append, List.length_singleton]
              exact Nat.le_trans (by omega : st.length + 1 ≤ limit) (Nat.le_max_right ..)
            · intro b hb
              simp only [List.mem_append, List.mem_singleton] at hb
              rcases hb with hb | rfl
              · exact hst.2 _ hb
              · exact expectNonterminal_value hp ha)
      (by
        intro st x b y hst hdone l he
        cases he
        obtain ⟨k, x1, _, hdone⟩ := run_bind_eq_ok.mp hdone
        cases k with
        | none =>
          simp only [run_pure, Prod.mk.injEq, Except.ok.injEq, Step.done.injEq, id_eq] at hdone
          obtain ⟨rfl, _⟩ := hdone
          exact hst
        | some u =>
          simp only [Syntax.parseListBody] at hdone
          split at hdone
          · simp at hdone
          · obtain ⟨_, _, _, hdone⟩ := run_bind_eq_ok.mp hdone
            simp at hdone)
      (by intro _ _ _ _ _ _ _ h; cases h) [first] s1 base
    change ∀ l, ((whileMaybe (Syntax.trySyntax sep) (Syntax.trySyntax_consumes sep)
      (Syntax.parseListBody limit d p) id [first]).run s1).1 = .ok l → inv l at hi
    exact hi xs (congrArg Prod.fst htail)

end SudoRsProofs.Parser
