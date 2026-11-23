import SudoersSpec.Grammar.Basic

/-!
# Lexical layer: trailing whitespace, syntax characters, nonterminals

The grammar of `TrailingWhitespace` (`Ws`), of `try_syntax` (`SynG`) and of `try_nonterminal`
/ `expect_nonterminal` (`NontermG`), with PT2 to PT4 for each. These are generic: every
production of the sudoers grammar is built from them.

Lexical conventions, as the code has them (`basic_parser.rs` at `70fdb56b`):

* A blank is `' '` or `'\t'` (`"\t ".contains(c)`); no other white space counts.
* Whitespace after a token or syntax character is `W ::= blank* ('\' newline W)?`, read with
  maximal munch: it ends before a character that is neither a blank nor `\`. A `\` not followed
  by a newline is a fatal error (`stray escape sequence`), so a derivation never stops in front
  of `\`. Comments are not part of it.
* Every terminal (token or syntax character) swallows the whitespace after it.
-/

namespace SudoersSpec.Grammar

open SudoersSpec.Syntax
open SudoersSpec.Syntax.Parser
open _root_.SudoersSpec.Syntax.Stream (Reaches)

/-- A blank: `' '` or `'\t'` (`"\t ".contains(c)` in `LeadingWhitespace::parse`). -/
def blank (c : Char) : Bool := c == '\t' || c == ' '

/-- `W`, the whitespace a terminal swallows (`TrailingWhitespace::parse`): blanks and line
continuations, maximal. `Ws w rest`: `w` is such whitespace and `rest` does not continue it
(its first character is not a blank and not `\`). -/
inductive Ws : List Char → List Char → Prop
  | stop {bs rest : List Char} : (∀ x ∈ bs, blank x = true) →
      NextNot (fun d => blank d = true ∨ d = '\\') rest → Ws bs rest
  | cont {bs w rest : List Char} : (∀ x ∈ bs, blank x = true) → Ws w rest →
      Ws (bs ++ '\\' :: '\n' :: w) rest

/-- `Ws` as a nonterminal with value `()`. -/
def WsG : Gram Unit := fun c _ rest => Ws c rest

/-- After whitespace, the right context does not start with a blank or `\`. -/
theorem Ws.stopAt {w rest : List Char} (h : Ws w rest) :
    NextNot (fun d => blank d = true ∨ d = '\\') rest := by
  induction h with
  | stop _ hn => exact hn
  | cont _ _ ih => exact ih

/-- The empty whitespace: possible exactly when nothing could continue it. -/
theorem Ws.nil_iff {rest : List Char} :
    Ws [] rest ↔ NextNot (fun d => blank d = true ∨ d = '\\') rest := by
  constructor
  · exact Ws.stopAt
  · intro h; exact .stop (by simp) h

theorem Ws.trunc {w x y : List Char} (h : Ws w (x ++ y)) : Ws w x := by
  generalize e : x ++ y = r at h
  induction h with
  | stop hb hn => subst e; exact .stop hb hn.trunc
  | cont hb _ ih => exact .cont hb (ih e)

theorem WsG.trunc : Trunc WsG := fun _ _ _ _ h => Ws.trunc h

/-! ## Stream facts -/

theorem blank_eq : (fun c : Char => c == '\t' || c == ' ') = blank := rfl

theorem dropWhile_of_prefix {f : Char → Bool} {bs r : List Char} (hb : ∀ x ∈ bs, f x = true)
    (hr : NextNot (fun d => f d = true) r) : (bs ++ r).dropWhile f = r := by
  induction bs with
  | nil =>
    cases r with
    | nil => rfl
    | cons d r =>
      have : f d = false := by simpa using NextNot.cons_iff.mp hr
      simp [this]
  | cons x bs ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hb
    simp [hb.1, ih hb.2]

/-- Skipping blanks over a prefix of blanks that is followed by a non-blank. -/
theorem skipWhile_blank_rest {s : Stream} {bs r : List Char} (hb : ∀ x ∈ bs, blank x = true)
    (hr : NextNot (fun d => blank d = true) r) (hs : s.rest = bs ++ r) :
    (s.skipWhile blank).rest = r := by
  rw [Stream.skipWhile_rest, hs, dropWhile_of_prefix hb hr]

theorem all_takeWhile {f : Char → Bool} {l : List Char} : ∀ x ∈ l.takeWhile f, f x = true := by
  intro x hx
  have := List.all_eq_true.mp (List.all_takeWhile (p := f) (l := l)) x hx
  simpa using this

theorem head_dropWhile {f : Char → Bool} {l : List Char} :
    NextNot (fun d => f d = true) (l.dropWhile f) := by
  intro d e
  have := List.head?_dropWhile_not f l
  rw [e] at this
  simp [this]

/-- The stream after skipping blanks, in terms of the input. -/
theorem skipWhile_blank_split (s : Stream) :
    s.rest = s.rest.takeWhile blank ++ (s.skipWhile blank).rest ∧
      (∀ x ∈ s.rest.takeWhile blank, blank x = true) ∧
      NextNot (fun d => blank d = true) (s.skipWhile blank).rest := by
  rw [Stream.skipWhile_rest]
  exact ⟨List.takeWhile_append_dropWhile.symm, all_takeWhile, head_dropWhile⟩

theorem Stream.peek_eq_head (s : Stream) : s.peek = s.rest.head? := rfl

theorem Stream.rest_of_peek {s : Stream} {c : Char} (h : s.peek = some c) :
    s.rest = c :: s.pop.rest := by
  rcases s with ⟨_ | ⟨d, ds⟩, l, k⟩
  · cases h
  · simp only [Stream.peek_mk, List.head?_cons, Option.some.injEq] at h
    subst h; simp

/-! ## `TrailingWhitespace` -/

theorem leadingWhitespace_snd (s : Stream) : (leadingWhitespace.run s).2 = s.skipWhile blank := by
  rw [leadingWhitespace_run]; split <;> rfl

/-- One iteration of the loop of `TrailingWhitespace::parse`, in closed form. -/
theorem trailingWhitespaceBody_run (s : Stream) :
    (trailingWhitespaceBody ()).run s =
      if (s.skipWhile blank).peek = some '\\' then
        if (s.skipWhile blank).pop.peek = some '\n' then
          (.ok (.next ()), (s.skipWhile blank).pop.pop)
        else
          (.error (.fatal ⟨(s.skipWhile blank).pop.getPos, (s.skipWhile blank).pop.getPos⟩
            .strayEscapeSequence), (s.skipWhile blank).pop)
      else (.ok (.done ()), s.skipWhile blank) := by
  simp only [trailingWhitespaceBody, run_bind, run_observe, leadingWhitespace_snd, run_eatChar,
    Stream.eatChar_eq]
  by_cases h1 : (s.skipWhile blank).peek = some '\\'
  · simp only [h1, ite_true, run_bind, run_eatChar, Stream.eatChar_eq]
    by_cases h2 : (s.skipWhile blank).pop.peek = some '\n'
    · simp only [h2, ite_true]; rfl
    · simp only [h2, ite_false]; rfl
  · simp only [h1, ite_false]; rfl

/-- PT3 for `TrailingWhitespace`. -/
theorem trailingWhitespace_sound : Sound trailingWhitespace WsG := by
  intro s a s' h
  have key := loop_rel trailingWhitespaceBody_progressive
    (fun _ s r s'' => ∀ u, r = .ok u → ∃ c, s.rest = c ++ s''.rest ∧ Ws c s''.rest)
    ?_ ?_ ?_ () s
  · rw [show trailingWhitespace.run s = (loop trailingWhitespaceBody
      trailingWhitespaceBody_progressive ()).run s from rfl] at h
    rw [h] at key
    exact key a rfl
  · intro st s b s' hb u _
    rw [trailingWhitespaceBody_run] at hb
    obtain ⟨hs, hbl, hnb⟩ := skipWhile_blank_split s
    split at hb
    · split at hb <;> simp at hb
    · rename_i hp
      simp only [Prod.mk.injEq] at hb
      obtain ⟨-, rfl⟩ := hb
      refine ⟨_, hs, .stop hbl ?_⟩
      intro d e hd
      rcases hd with hd | rfl
      · exact hnb d e hd
      · exact hp (by rw [Stream.peek_eq_head, e])
  · intro st s e s' _ u hu; cases hu
  · intro st s st' s' r s'' hb ih u hu
    obtain ⟨c, hc, hw⟩ := ih u hu
    rw [trailingWhitespaceBody_run] at hb
    obtain ⟨hs, hbl, _⟩ := skipWhile_blank_split s
    split at hb
    · rename_i h1
      split at hb
      · rename_i h2
        simp only [Prod.mk.injEq] at hb
        obtain ⟨-, rfl⟩ := hb
        refine ⟨_ ++ '\\' :: '\n' :: c, ?_, .cont hbl hw⟩
        have e1 := Stream.rest_of_peek h1
        have e2 := Stream.rest_of_peek h2
        calc s.rest = _ := hs
          _ = _ := by rw [e1, e2, hc]; simp
      · simp at hb
    · simp at hb

/-- PT4 for `TrailingWhitespace`. -/
theorem trailingWhitespace_complete : Complete trailingWhitespace WsG := by
  intro c a rest s hw hs
  show ∃ s', (loop trailingWhitespaceBody trailingWhitespaceBody_progressive ()).run s =
    (.ok a, s') ∧ s'.rest = rest
  induction hw generalizing s with
  | stop hb hn =>
    rw [loop_run, trailingWhitespaceBody_run]
    have h1 := skipWhile_blank_rest hb (hn.mono fun d hd => .inl hd) hs
    have hp : ¬ (s.skipWhile blank).peek = some '\\' := by
      rw [Stream.peek_eq_head, h1]; intro e; exact hn _ e (.inr rfl)
    simp only [hp, ite_false]
    exact ⟨_, rfl, h1⟩
  | @cont bs w rest hb hw ih =>
    rw [loop_run, trailingWhitespaceBody_run]
    have h1 := skipWhile_blank_rest (r := '\\' :: '\n' :: (w ++ rest)) hb
      (by intro d e; simp only [List.head?_cons, Option.some.injEq] at e; subst e; decide)
      (by rw [hs]; simp)
    have hp : (s.skipWhile blank).peek = some '\\' := by rw [Stream.peek_eq_head, h1]; rfl
    have hp2 : (s.skipWhile blank).pop.peek = some '\n' := by
      rw [Stream.peek_eq_head, Stream.pop_rest, h1]; rfl
    simp only [hp, hp2, ite_true]
    exact ih _ (by rw [Stream.pop_rest, Stream.pop_rest, h1]; rfl)

theorem skipTrailingWhitespace_run (s : Stream) :
    skipTrailingWhitespace.run s = trailingWhitespace.run s := by
  simp only [skipTrailingWhitespace, run_bind]
  cases trailingWhitespace.run s with
  | mk r s' => cases r <;> rfl

theorem skipTrailingWhitespace_sound : Sound skipTrailingWhitespace WsG := by
  intro s a s' h; rw [skipTrailingWhitespace_run] at h; exact trailingWhitespace_sound s a s' h

theorem skipTrailingWhitespace_complete : Complete skipTrailingWhitespace WsG := by
  intro c a rest s hw hs; rw [skipTrailingWhitespace_run]; exact trailingWhitespace_complete c a rest s hw hs

/-- PT2 for `TrailingWhitespace`: it never rejects. -/
theorem trailingWhitespace_rejectPure : RejectPure trailingWhitespace := by
  intro s s' h
  exact absurd (congrArg Prod.fst h) (trailingWhitespace_ne_reject s)

/-! ## `try_syntax` -/

/-- A syntax character `ch` and the whitespace after it (`try_syntax(ch)`). -/
def SynG (ch : Char) : Gram Unit := fun c _ rest => ∃ w, c = ch :: w ∧ Ws w rest

theorem SynG.trunc (ch : Char) : Trunc (SynG ch) := by
  rintro c a x y ⟨w, rfl, hw⟩; exact ⟨w, rfl, hw.trunc⟩

theorem trySyntax_run (ch : Char) (s : Stream) :
    (trySyntax ch).run s =
      if s.peek = some ch then skipTrailingWhitespace.run s.pop else (.error .reject, s) := by
  simp only [trySyntax, run_bind, run_eatChar, Stream.eatChar_eq]
  by_cases h : s.peek = some ch
  · simp only [h, ite_true]; rfl
  · simp only [h, ite_false]; rfl

/-- PT2 for `try_syntax`, exactly: it rejects iff the character is not next, and then it has
consumed nothing. -/
theorem trySyntax_reject_iff {ch : Char} {s s' : Stream} :
    (trySyntax ch).run s = (.error .reject, s') ↔ s' = s ∧ NextNot (· = ch) s.rest := by
  rw [trySyntax_run]
  by_cases h : s.peek = some ch
  · simp only [h, ite_true]
    constructor
    · intro e
      exact absurd (congrArg Prod.fst e) (skipTrailingWhitespace_ne_reject _)
    · rintro ⟨-, hn⟩
      exact absurd rfl (hn ch (by rw [← Stream.peek_eq_head, h]))
  · simp only [h, ite_false, Prod.mk.injEq, true_and]
    constructor
    · intro e; subst e
      refine ⟨rfl, ?_⟩
      intro d e hd; subst hd; exact h (by rw [Stream.peek_eq_head, e])
    · rintro ⟨rfl, -⟩; rfl

theorem trySyntax_rejectPure (ch : Char) : RejectPure (trySyntax ch) :=
  fun _ _ h => (trySyntax_reject_iff.mp h).1

/-- PT3 for `try_syntax`. -/
theorem trySyntax_sound (ch : Char) : Sound (trySyntax ch) (SynG ch) := by
  intro s a s' h
  rw [trySyntax_run] at h
  split at h
  · rename_i hp
    obtain ⟨w, hw, hws⟩ := skipTrailingWhitespace_sound _ _ _ h
    exact ⟨ch :: w, by rw [Stream.rest_of_peek hp, hw]; rfl, w, rfl, hws⟩
  · cases h

/-- PT4 for `try_syntax`. -/
theorem trySyntax_complete (ch : Char) : Complete (trySyntax ch) (SynG ch) := by
  rintro c a rest s ⟨w, rfl, hw⟩ hs
  rw [trySyntax_run]
  have hp : s.peek = some ch := by rw [Stream.peek_eq_head, hs]; rfl
  simp only [hp, ite_true]
  exact skipTrailingWhitespace_complete w a rest s.pop hw (by rw [Stream.pop_rest, hs]; rfl)

/-- `is_syntax` in terms of `try_syntax`. -/
theorem isSyntax_run (ch : Char) (s : Stream) :
    (isSyntax ch).run s =
      match Syntax.maybe ((trySyntax ch).run s).1 with
      | .ok r => (.ok r.isSome, ((trySyntax ch).run s).2)
      | .error e => (.error e, ((trySyntax ch).run s).2) := by
  simp only [isSyntax, run_bind, run_maybe]
  cases (trySyntax ch).run s with
  | mk r s1 =>
    cases r with
    | ok a => rfl
    | error e => cases e <;> rfl

/-- `is_syntax` is `false` exactly when the character is not next; nothing is consumed then. -/
theorem isSyntax_false_iff {ch : Char} {s s' : Stream} :
    (isSyntax ch).run s = (.ok false, s') ↔ s' = s ∧ NextNot (· = ch) s.rest := by
  rw [isSyntax_run, ← trySyntax_reject_iff]
  cases h : (trySyntax ch).run s with
  | mk r s1 =>
    cases r with
    | ok a => simp
    | error e => cases e <;> simp

/-- `is_syntax` is `true` exactly when `try_syntax` succeeds. -/
theorem isSyntax_true_iff {ch : Char} {s s' : Stream} :
    (isSyntax ch).run s = (.ok true, s') ↔ (trySyntax ch).run s = (.ok (), s') := by
  rw [isSyntax_run]
  cases h : (trySyntax ch).run s with
  | mk r s1 =>
    cases r with
    | ok a => simp
    | error e => cases e <;> simp

/-- `is_syntax` never rejects. -/
theorem isSyntax_rejectPure (ch : Char) : RejectPure (isSyntax ch) := by
  intro s s' h
  rw [isSyntax_run] at h
  revert h
  cases (trySyntax ch).run s with
  | mk r s1 =>
    cases r with
    | ok a => simp
    | error e => cases e <;> simp

/-! ## `expect_syntax` -/

/-- On success `expect_syntax` is `try_syntax`. -/
theorem expectSyntax_ok_iff {ch : Char} {s s' : Stream} :
    (expectSyntax ch).run s = (.ok (), s') ↔ (trySyntax ch).run s = (.ok (), s') := by
  simp only [expectSyntax, run_bind, run_observe]
  cases (trySyntax ch).run s with
  | mk r s1 =>
    cases r with
    | ok a => simp
    | error e => simp [run_bind]

theorem expectSyntax_sound (ch : Char) : Sound (expectSyntax ch) (SynG ch) :=
  fun s a s' h => trySyntax_sound ch s a s' (expectSyntax_ok_iff.mp h)

theorem expectSyntax_complete (ch : Char) : Complete (expectSyntax ch) (SynG ch) := by
  intro c a rest s hd hs
  obtain ⟨s', h, hs'⟩ := trySyntax_complete ch c a rest s hd hs
  exact ⟨s', expectSyntax_ok_iff.mpr h, hs'⟩

/-- `expect_syntax` never rejects. -/
theorem expectSyntax_rejectPure (ch : Char) : RejectPure (expectSyntax ch) := by
  intro s s' h
  simp only [expectSyntax, run_bind, run_observe] at h
  revert h
  cases (trySyntax ch).run s with
  | mk r s1 =>
    cases r with
    | ok a => simp
    | error e => simp [run_bind]

/-! ## `try_nonterminal` and `expect_nonterminal` -/

/-- A nonterminal and the whitespace after it (`try_nonterminal`): `c₁` derives `a` by `G`,
then whitespace `w`. -/
def NontermG (G : Gram α) : Gram α :=
  fun c a rest => ∃ c₁ w, c = c₁ ++ w ∧ G c₁ a (w ++ rest) ∧ Ws w rest

theorem NontermG.trunc {G : Gram α} (hG : Trunc G) : Trunc (NontermG G) := by
  rintro c a x y ⟨c₁, w, rfl, hd, hw⟩
  refine ⟨c₁, w, rfl, ?_, hw.trunc⟩
  exact hG c₁ a (w ++ x) y (by simpa using hd)

theorem NontermG.mono {G G' : Gram α} (h : ∀ c a r, G c a r → G' c a r) {c : List Char} {a : α}
    {r : List Char} : NontermG G c a r → NontermG G' c a r := by
  rintro ⟨c₁, w, e, hd, hw⟩; exact ⟨c₁, w, e, h _ _ _ hd, hw⟩

theorem tryNonterminal_run (p : Parser α) (s : Stream) :
    (tryNonterminal p).run s =
      match p.run s with
      | (.ok a, s₁) =>
        match skipTrailingWhitespace.run s₁ with
        | (.ok _, s₂) => (.ok a, s₂)
        | (.error e, s₂) => (.error e, s₂)
      | (.error e, s₁) => (.error e, s₁) := by
  simp only [tryNonterminal, run_bind]
  cases p.run s with
  | mk r s₁ =>
    cases r with
    | error e => rfl
    | ok a =>
      simp only
      cases skipTrailingWhitespace.run s₁ with
      | mk r₂ s₂ => cases r₂ <;> rfl

/-- PT3 for `try_nonterminal`. -/
theorem tryNonterminal_sound {p : Parser α} {G : Gram α} (hp : Sound p G) :
    Sound (tryNonterminal p) (NontermG G) := by
  intro s a s' h
  rw [tryNonterminal_run] at h
  revert h
  cases h₁ : p.run s with
  | mk r s₁ =>
    cases r with
    | error e => intro h; cases h
    | ok b =>
      simp only
      cases h₂ : skipTrailingWhitespace.run s₁ with
      | mk r₂ s₂ =>
        cases r₂ with
        | error e => intro h; cases h
        | ok u =>
          intro h
          simp only [Prod.mk.injEq, Except.ok.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨c₁, hc₁, hd⟩ := hp _ _ _ h₁
          obtain ⟨w, hw, hws⟩ := skipTrailingWhitespace_sound _ _ _ h₂
          refine ⟨c₁ ++ w, ?_, c₁, w, rfl, ?_, hws⟩
          · rw [hc₁, hw, List.append_assoc]
          · rw [← hw]; exact hd

/-- PT4 for `try_nonterminal`. -/
theorem tryNonterminal_complete {p : Parser α} {G : Gram α} (hp : Complete p G) :
    Complete (tryNonterminal p) (NontermG G) := by
  rintro c a rest s ⟨c₁, w, rfl, hd, hw⟩ hs
  obtain ⟨s₁, h₁, hs₁⟩ := hp c₁ a (w ++ rest) s hd (by rw [hs, List.append_assoc])
  obtain ⟨s₂, h₂, hs₂⟩ := skipTrailingWhitespace_complete w () rest s₁ hw hs₁
  rw [tryNonterminal_run, h₁]
  simp only [h₂]
  exact ⟨s₂, rfl, hs₂⟩

/-- PT2 for `try_nonterminal`, exactly: it rejects iff `p` rejects, with the same stream. -/
theorem tryNonterminal_reject {p : Parser α} {s s' : Stream} :
    (tryNonterminal p).run s = (.error .reject, s') ↔ p.run s = (.error .reject, s') := by
  rw [tryNonterminal_run]
  cases h₁ : p.run s with
  | mk r s₁ =>
    cases r with
    | error e => simp
    | ok b =>
      simp only [reduceCtorEq, Prod.mk.injEq, false_and, iff_false]
      have := skipTrailingWhitespace_ne_reject s₁
      revert this
      cases skipTrailingWhitespace.run s₁ with
      | mk r₂ s₂ =>
        cases r₂ with
        | ok _ => simp
        | error e => simp; intro h1 h2; exact absurd h2 h1

theorem tryNonterminal_rejectPure {p : Parser α} (hp : RejectPure p) :
    RejectPure (tryNonterminal p) :=
  fun s s' h => hp s s' (tryNonterminal_reject.mp h)

/-- On success `expect_nonterminal` is `try_nonterminal`. -/
theorem expectNonterminal_ok_iff {description : String} {p : Parser α} {s s' : Stream} {a : α} :
    (expectNonterminal description p).run s = (.ok a, s') ↔
      (tryNonterminal p).run s = (.ok a, s') := by
  simp only [expectNonterminal, run_bind, run_getPos, run_observe]
  cases h : (tryNonterminal p).run s with
  | mk r s₁ =>
    cases r with
    | ok b => simp
    | error e => cases e <;> simp

theorem expectNonterminal_sound {p : Parser α} {G : Gram α} (hp : Sound p G) (description : String) :
    Sound (expectNonterminal description p) (NontermG G) :=
  fun s a s' h => tryNonterminal_sound hp s a s' (expectNonterminal_ok_iff.mp h)

theorem expectNonterminal_complete {p : Parser α} {G : Gram α} (hp : Complete p G)
    (description : String) : Complete (expectNonterminal description p) (NontermG G) := by
  intro c a rest s hd hs
  obtain ⟨s', h, hs'⟩ := tryNonterminal_complete hp c a rest s hd hs
  exact ⟨s', expectNonterminal_ok_iff.mpr h, hs'⟩

/-- PT2 for `expect_nonterminal`: it never rejects. -/
theorem expectNonterminal_rejectPure (description : String) (p : Parser α) :
    RejectPure (expectNonterminal description p) :=
  fun s _ h => absurd (congrArg Prod.fst h) (expectNonterminal_ne_reject description p s)

end SudoersSpec.Grammar
