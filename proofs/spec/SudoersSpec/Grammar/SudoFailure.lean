import SudoersSpec.Grammar.PermissionAtoms

/-! Consumed-prefix grammars for lexical failures, including those ignored by a fallback. -/

namespace SudoersSpec.Grammar

open SudoersSpec.Syntax
open SudoersSpec.Syntax.Parser

variable {α β : Type}

/-- Even on failure, the consumed characters must derive the failure for the actual remaining
input. The diagnostic itself is not part of the grammar. -/
def FailureSound (p : Parser α) (F : Gram Unit) : Prop :=
  ∀ s e t, p.run s = (.error e, t) → ∃ c, s.rest = c ++ t.rest ∧ F c () t.rest

/-- A derived failure reproduces its consumed prefix regardless of the starting position. -/
def FailureComplete (p : Parser α) (F : Gram Unit) : Prop :=
  ∀ c r s, F c () r → s.rest = c ++ r → ∃ e t, p.run s = (.error e, t) ∧ t.rest = r

theorem FailureSound.mono {p : Parser α} {F F' : Gram Unit} (h : FailureSound p F)
    (hf : ∀ c u r, F c u r → F' c u r) : FailureSound p F' := by
  intro s e t hr
  obtain ⟨c, hc, hd⟩ := h s e t hr
  exact ⟨c, hc, hf _ _ _ hd⟩

/-- A sequence fails either in its first parser or after deriving an intermediate value. -/
theorem bind_failure_sound {p : Parser α} {f : α → Parser β} {G : Gram α}
    {F : Gram Unit} {H : α → Gram Unit} (hs : Sound p G) (hp : FailureSound p F)
    (hf : ∀ a, FailureSound (f a) (H a)) :
    FailureSound (p >>= f) (fun c u r => F c u r ∨ SeqG G H c u r) := by
  intro s e t h
  rcases run_bind_eq_error.mp h with h | ⟨a, s₁, h₁, h₂⟩
  · obtain ⟨c, hc, hd⟩ := hp _ _ _ h
    exact ⟨c, hc, .inl hd⟩
  · obtain ⟨c₁, hc₁, hd₁⟩ := hs _ _ _ h₁
    obtain ⟨c₂, hc₂, hd₂⟩ := hf a _ _ _ h₂
    refine ⟨c₁ ++ c₂, by rw [hc₁, hc₂, List.append_assoc], .inr ?_⟩
    exact ⟨c₁, c₂, a, rfl, hc₂ ▸ hd₁, hd₂⟩

/-! ## Tokens -/

/-- After a backslash opening an escape, the next character is neither an allowed escape nor a
newline, and the backslash cannot stand on its own. Only the backslash is consumed. -/
def EscIllegal (T : TokenSpec α) (pred : Char → Bool) (rest : List Char) : Prop :=
  T.allowEscape = true ∧ pred '\\' = false ∧
    NextNot (fun d => T.escaped d = true ∨ d = '\n') rest

private theorem acceptEscaped_fatal_sound (T : TokenSpec α) (pred : Char → Bool)
    {s t : Stream} {sp : Span} {k : ErrKind}
    (h : (acceptEscaped T pred).run s = (.error (.fatal sp k), t)) :
    s.rest = '\\' :: t.rest ∧ EscIllegal T pred t.rest := by
  by_cases hE : T.allowEscape = true ∧ s.peek = some '\\'
  · rw [acceptEscaped_run_esc T pred s hE.1 hE.2] at h
    have hrest := Stream.rest_of_peek hE.2
    revert h
    cases hp : s.pop.peek with
    | none =>
      by_cases hb : pred '\\' = true
      · simp [hb]
      · simp only [hb]
        rintro ⟨-, rfl⟩
        refine ⟨hrest, hE.1, by simpa using hb, ?_⟩
        intro d hd
        rw [← Stream.peek_eq_head, hp] at hd
        cases hd
    | some d =>
      by_cases he : T.escaped d = true
      · simp [he]
      · by_cases hb : pred '\\' = true
        · simp [he, hb]
        · by_cases hn : d = '\n'
          · subst d
            by_cases hs : pred ' ' = true <;> simp [he, hb, hs]
          · simp only [he, hb, hn, ite_false]
            rintro ⟨-, rfl⟩
            refine ⟨hrest, hE.1, by simpa using hb, ?_⟩
            intro d' hd'
            rw [← Stream.peek_eq_head, hp] at hd'
            cases hd'
            exact fun hd => hd.elim he hn
  · rw [acceptEscaped_run_plain T pred s hE] at h
    revert h
    cases s.peek with
    | none => simp
    | some d => simp only; split <;> simp

private theorem acceptEscaped_fatal_complete (T : TokenSpec α) (pred : Char → Bool)
    {rest : List Char} {s : Stream} (h : EscIllegal T pred rest) (hs : s.rest = '\\' :: rest) :
    ∃ sp k t, (acceptEscaped T pred).run s = (.error (.fatal sp k), t) ∧ t.rest = rest := by
  obtain ⟨hA, hb, hn⟩ := h
  have hp : s.peek = some '\\' := by rw [Stream.peek_eq_head, hs]; rfl
  have hr : s.pop.rest = rest := by rw [Stream.pop_rest, hs]; rfl
  rw [acceptEscaped_run_esc T pred s hA hp]
  cases hp₂ : s.pop.peek with
  | none =>
    simp only [hb, Bool.false_eq_true, ite_false]
    exact ⟨_, _, s.pop, rfl, hr⟩
  | some d =>
    have hd := hn d (by rw [← hr, ← Stream.peek_eq_head, hp₂])
    have hne : T.escaped d ≠ true := fun he => hd (.inl he)
    have he : T.escaped d = false := by simpa using hne
    have hd' : d ≠ '\n' := fun h' => hd (.inr h')
    simp only [he, hb, hd', Bool.false_eq_true, ite_false]
    exact ⟨_, _, s.pop, rfl, hr⟩

/-- A failure during the tail of the token, from the decoded characters `str` accumulated so
far. For the length error the triggering unit has been consumed but not appended. -/
inductive TokLoopFailure (T : TokenSpec α) : List Char → List Char → List Char → Prop
  | illegal {str rest} : EscIllegal T T.accept rest → TokLoopFailure T str ['\\'] rest
  | length {str u x rest} : EscUnit T T.accept u x rest → T.maxLen ≤ utf8Len str →
      TokLoopFailure T str u rest
  | cons {str u x c rest} : EscUnit T T.accept u x (c ++ rest) → utf8Len str < T.maxLen →
      TokLoopFailure T (str ++ [x]) c rest → TokLoopFailure T str (u ++ c) rest

private theorem tokenLoop_failure_sound (T : TokenSpec α) (str : List Char) (s : Stream)
    {e : Status} {t : Stream} (h : (tokenLoop T str).run s = (.error e, t)) :
    ∃ c, s.rest = c ++ t.rest ∧ TokLoopFailure T str c t.rest := by
  have key := loop_rel (whileMaybeBody_progressive (acceptEscaped_consumes T T.accept)
      (tokenBody T) id)
    (fun str s r t => ∀ e, r = .error e → ∃ c, s.rest = c ++ t.rest ∧
      TokLoopFailure T str c t.rest) ?_ ?_ ?_ str s
  · unfold tokenLoop whileMaybe at h
    rw [h] at key
    exact key e rfl
  · intro st s b t _ e he; cases he
  · intro st s e t hb e' he
    cases he
    rw [whileMaybeBody_run] at hb
    revert hb
    cases hq : (acceptEscaped T T.accept).run s with
    | mk r s₁ =>
      cases r with
      | ok x =>
        simp only [maybe_ok, tokenBody_run]
        split
        · rename_i hlen
          simp only [Prod.mk.injEq, Except.error.injEq]
          rintro ⟨-, rfl⟩
          obtain ⟨u, hu, hunit⟩ := acceptEscaped_sound T T.accept hq
          exact ⟨u, hu, .length hunit hlen⟩
        · simp
      | error e₁ =>
        cases e₁ with
        | reject => simp
        | fatal sp k =>
          simp only [maybe_fatal, Prod.mk.injEq, Except.error.injEq]
          rintro ⟨-, rfl⟩
          obtain ⟨hc, hd⟩ := acceptEscaped_fatal_sound T T.accept hq
          exact ⟨['\\'], hc, .illegal hd⟩
  · intro st s st' s' r t hb ih e he
    obtain ⟨c, hc, hd⟩ := ih e he
    rw [whileMaybeBody_run] at hb
    revert hb
    cases hq : (acceptEscaped T T.accept).run s with
    | mk r₁ s₁ =>
      cases r₁ with
      | ok x =>
        simp only [maybe_ok, tokenBody_run]
        split
        · simp
        · rename_i hlen
          simp only [Prod.mk.injEq, Except.ok.injEq, Step.next.injEq]
          rintro ⟨rfl, rfl⟩
          obtain ⟨u, hu, hunit⟩ := acceptEscaped_sound T T.accept hq
          refine ⟨u ++ c, by rw [hu, hc, List.append_assoc], .cons ?_ (by omega) hd⟩
          rw [← hc]; exact hunit
      | error e₁ => cases e₁ <;> simp

private theorem tokenLoop_fatal_complete (T : TokenSpec α) {str c rest : List Char}
    (h : TokLoopFailure T str c rest) {s : Stream} (hs : s.rest = c ++ rest) :
    ∃ sp k t, (tokenLoop T str).run s = (.error (.fatal sp k), t) ∧ t.rest = rest := by
  induction h generalizing s with
  | illegal hi =>
    obtain ⟨sp, k, t, ht, hr⟩ := acceptEscaped_fatal_complete T T.accept hi hs
    unfold tokenLoop whileMaybe
    rw [loop_run, whileMaybeBody_run, ht]
    exact ⟨sp, k, t, rfl, hr⟩
  | length hu hlen =>
    obtain ⟨t, ht, hr⟩ := acceptEscaped_complete T T.accept hu hs
    unfold tokenLoop whileMaybe
    rw [loop_run, whileMaybeBody_run, ht]
    simp only [maybe_ok, tokenBody_run, hlen, ite_true]
    exact ⟨_, _, t, rfl, hr⟩
  | cons hu hlen _ ih =>
    obtain ⟨s₁, h₁, hs₁⟩ := acceptEscaped_complete T T.accept hu (by rw [hs, List.append_assoc])
    have hlt := Nat.not_le_of_gt hlen
    unfold tokenLoop whileMaybe
    rw [loop_run, whileMaybeBody_run, h₁]
    simp only [maybe_ok, tokenBody_run, hlt, ite_false]
    exact ih hs₁

/-- A token fails fatally on an illegal opening escape, during the loop, or when constructing
its value from a successfully scanned token. -/
inductive TokenFatalG (T : TokenSpec α) : Gram Unit
  | illegal {rest} : EscIllegal T T.accept1st rest → TokenFatalG T ['\\'] () rest
  | loop {u x c rest} : EscUnit T T.accept1st u x (c ++ rest) → TokLoopFailure T [x] c rest →
      TokenFatalG T (u ++ c) () rest
  | construct {u x c xs rest k} : EscUnit T T.accept1st u x (c ++ rest) → TokTail T c xs rest →
      LenOK T.maxLen [x] xs → T.construct (x :: xs) = .error k → TokenFatalG T (u ++ c) () rest

/-- The consumed-prefix grammar for any token failure. -/
def TokenFailureG (T : TokenSpec α) : Gram Unit :=
  fun c u r => TokenRejectG T c u r ∨ TokenFatalG T c u r

theorem token_fatal_sound (T : TokenSpec α) {s t : Stream} {sp : Span} {k : ErrKind}
    (h : (token T).run s = (.error (.fatal sp k), t)) :
    ∃ c, s.rest = c ++ t.rest ∧ TokenFatalG T c () t.rest := by
  rw [token_run] at h
  revert h
  cases h₁ : (acceptEscaped T T.accept1st).run s with
  | mk r₁ s₁ =>
    cases r₁ with
    | error e =>
      simp only [Prod.mk.injEq, Except.error.injEq]
      rintro ⟨rfl, rfl⟩
      obtain ⟨hc, hd⟩ := acceptEscaped_fatal_sound T T.accept1st h₁
      exact ⟨['\\'], hc, .illegal hd⟩
    | ok x =>
      simp only
      obtain ⟨u, hu, hunit⟩ := acceptEscaped_sound T T.accept1st h₁
      cases h₂ : (tokenLoop T [x]).run s₁ with
      | mk r₂ s₂ =>
        cases r₂ with
        | error e =>
          simp only [Prod.mk.injEq, Except.error.injEq]
          rintro ⟨rfl, rfl⟩
          obtain ⟨c, hc, hd⟩ := tokenLoop_failure_sound T [x] s₁ h₂
          exact ⟨u ++ c, by rw [hu, hc, List.append_assoc], .loop (hc ▸ hunit) hd⟩
        | ok str =>
          simp only
          cases h₃ : T.construct str with
          | ok a => simp
          | error k' =>
            simp only [Prod.mk.injEq, Except.error.injEq]
            rintro ⟨-, rfl⟩
            obtain ⟨c, xs, hc, ht, hl, rfl⟩ := tokenLoop_sound T [x] s₁ h₂
            exact ⟨u ++ c, by rw [hu, hc, List.append_assoc],
              .construct (hc ▸ hunit) ht hl (by simpa using h₃)⟩

theorem token_failure_sound (T : TokenSpec α) : FailureSound (token T) (TokenFailureG T) := by
  intro s e t h
  cases e with
  | reject =>
    obtain ⟨c, hc, hd⟩ := token_rejectSound T _ _ h
    exact ⟨c, hc, .inl hd⟩
  | fatal sp k =>
    obtain ⟨c, hc, hd⟩ := token_fatal_sound T h
    exact ⟨c, hc, .inr hd⟩

/-- Reverse the fatal-token grammar without fixing the diagnostic span or error kind. -/
theorem token_fatal_complete (T : TokenSpec α) :
    ∀ c r s, TokenFatalG T c () r → s.rest = c ++ r →
      ∃ span kind t, (token T).run s = (.error (.fatal span kind), t) ∧ t.rest = r := by
  intro c r s h hs
  cases h with
  | illegal hi =>
    obtain ⟨sp, k, t, ht, hr⟩ := acceptEscaped_fatal_complete T T.accept1st hi hs
    exact ⟨sp, k, t, by rw [token_run, ht], hr⟩
  | loop hu hl =>
    obtain ⟨s₁, h₁, hs₁⟩ := acceptEscaped_complete T T.accept1st hu (by rw [hs, List.append_assoc])
    obtain ⟨sp, k, t, ht, hr⟩ := tokenLoop_fatal_complete T hl hs₁
    exact ⟨sp, k, t, by simp only [token_run, h₁, ht], hr⟩
  | @construct u x c xs rest k hu ht hl hk =>
    obtain ⟨s₁, h₁, hs₁⟩ := acceptEscaped_complete T T.accept1st hu (by rw [hs, List.append_assoc])
    obtain ⟨t, h₂, hr⟩ := tokenLoop_complete T ht [x] s₁ hl hs₁
    change (tokenLoop T [x]).run s₁ = (.ok (x :: xs), t) at h₂
    exact ⟨⟨s.getPos, t.getPos⟩, k, t, by simp only [token_run, h₁, h₂, hk], hr⟩

theorem token_failure_complete (T : TokenSpec α) : FailureComplete (token T) (TokenFailureG T) := by
  intro c r s h hs
  rcases h with h | h
  · obtain ⟨t, ht, hr⟩ := token_rejectComplete T c r s h hs
    exact ⟨.reject, t, ht, hr⟩
  · obtain ⟨sp, k, t, ht, hr⟩ := token_fatal_complete T c r s h hs
    exact ⟨.fatal sp k, t, ht, hr⟩

/-! ## Whitespace -/

/-- Blanks and complete continuations, ending with a backslash not followed by a newline.
The stray backslash is consumed; the next character, if any, is not. -/
inductive WsFailureG : Gram Unit
  | stray {bs rest} : (∀ x ∈ bs, blank x = true) → NextNot (· = '\n') rest →
      WsFailureG (bs ++ ['\\']) () rest
  | cont {bs w rest} : (∀ x ∈ bs, blank x = true) → WsFailureG w () rest →
      WsFailureG (bs ++ '\\' :: '\n' :: w) () rest

theorem ws_failure_sound : FailureSound skipTrailingWhitespace WsFailureG := by
  intro s e t h
  rw [skipTrailingWhitespace_run] at h
  have key := loop_rel trailingWhitespaceBody_progressive
    (fun _ s r t => ∀ e, r = .error e → ∃ c, s.rest = c ++ t.rest ∧ WsFailureG c () t.rest)
    ?_ ?_ ?_ () s
  · change (loop trailingWhitespaceBody trailingWhitespaceBody_progressive ()).run s = _ at h
    rw [h] at key
    exact key e rfl
  · intro st s b t _ e he; cases he
  · intro st s e t hb e' _
    rw [trailingWhitespaceBody_run] at hb
    obtain ⟨hs, hbl, _⟩ := skipWhile_blank_split s
    split at hb
    · rename_i h₁
      split at hb
      · simp at hb
      · rename_i h₂
        simp only [Prod.mk.injEq] at hb
        obtain ⟨-, rfl⟩ := hb
        refine ⟨_ ++ ['\\'], ?_, .stray hbl ?_⟩
        · calc s.rest = _ := hs
            _ = _ := by rw [Stream.rest_of_peek h₁, List.append_assoc]; rfl
        · intro d hd hdn
          subst d
          exact h₂ (by rwa [Stream.peek_eq_head])
    · simp at hb
  · intro st s st' s' r t hb ih e he
    obtain ⟨c, hc, hd⟩ := ih e he
    rw [trailingWhitespaceBody_run] at hb
    obtain ⟨hs, hbl, _⟩ := skipWhile_blank_split s
    split at hb
    · rename_i h₁
      split at hb
      · rename_i h₂
        simp only [Prod.mk.injEq] at hb
        obtain ⟨-, rfl⟩ := hb
        refine ⟨_ ++ '\\' :: '\n' :: c, ?_, .cont hbl hd⟩
        calc s.rest = _ := hs
          _ = _ := by rw [Stream.rest_of_peek h₁, Stream.rest_of_peek h₂, hc]; simp
      · simp at hb
    · simp at hb

theorem ws_failure_complete : FailureComplete skipTrailingWhitespace WsFailureG := by
  intro c r s h hs
  rw [skipTrailingWhitespace_run]
  change ∃ e t, (loop trailingWhitespaceBody trailingWhitespaceBody_progressive ()).run s =
    (.error e, t) ∧ t.rest = r
  have afterBlanks {s : Stream} {bs rest : List Char} (hb : ∀ x ∈ bs, blank x = true)
      (hs : s.rest = bs ++ '\\' :: rest) : (s.skipWhile blank).rest = '\\' :: rest :=
    skipWhile_blank_rest hb
      (by intro d hd; simp only [List.head?_cons, Option.some.injEq] at hd; subst d; decide) hs
  generalize () = u at h
  induction h generalizing s with
  | @stray bs rest hb hn =>
    have hr := afterBlanks (rest := rest) hb
      (hs.trans (List.append_assoc bs ['\\'] rest))
    have hp : (s.skipWhile blank).peek = some '\\' := by rw [Stream.peek_eq_head, hr]; rfl
    have hpop : (s.skipWhile blank).pop.rest = rest := by rw [Stream.pop_rest, hr]; rfl
    have hp₂ : (s.skipWhile blank).pop.peek ≠ some '\n' := by
      rw [Stream.peek_eq_head, hpop]
      exact fun he => hn '\n' he rfl
    rw [loop_run, trailingWhitespaceBody_run]
    simp only [hp, hp₂, ite_true, ite_false]
    exact ⟨_, _, rfl, hpop⟩
  | @cont bs w rest hb _ ih =>
    have hr := afterBlanks hb (show s.rest = bs ++ '\\' :: '\n' :: (w ++ rest) by rw [hs]; simp)
    have hp : (s.skipWhile blank).peek = some '\\' := by rw [Stream.peek_eq_head, hr]; rfl
    have hp₂ : (s.skipWhile blank).pop.peek = some '\n' := by
      rw [Stream.peek_eq_head, Stream.pop_rest, hr]; rfl
    rw [loop_run, trailingWhitespaceBody_run]
    simp only [hp, hp₂, ite_true]
    exact ih _ (by rw [Stream.pop_rest, Stream.pop_rest, hr]; rfl)

end SudoersSpec.Grammar
