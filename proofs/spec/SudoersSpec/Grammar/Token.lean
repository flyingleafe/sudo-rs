import SudoersSpec.Grammar.Lexical

/-!
# Tokens: the grammar of `impl<T: Token> Parse for T`, for any `TokenSpec`

A token of class `T` is a first character unit read with `T.accept1st`, then character units
read with `T.accept`, maximal, then `T.construct` on the characters read. A character unit
(`accept_escaped`) is one of:

| unit | consumed | value | condition |
|---|---|---|---|
| plain | `c` | `c` | `pred c`, and `c ≠ \` if escapes are allowed |
| escaped | `\ d` | `d` | escapes allowed, `T.escaped d` |
| backslash | `\` | `\` | escapes allowed, `pred '\'`, the next character is not `T.escaped` |
| continuation | `\ newline` | `' '` | escapes allowed, newline not `T.escaped`, `pred '\'` false, `pred ' '` |

The token ends (maximal munch) where `accept_escaped` rejects. It rejects without consuming in
front of a character that `pred` refuses and that is not a `\` opening an escape
(`EscStop`); it also rejects *after* consuming `\ newline` when escapes are allowed, newline is
not `T.escaped`, and `pred` accepts neither `\` nor `' '` (`EscRejects`). In the second case
the two characters are gone: inside a token they end it silently (`TokTail.term`), at the
start of a token the token rejects having consumed input (PT2 fails: `token_reject`,
`token_rejectPure_counterexample`).

Length: the check `str.len() >= MAX_LEN` runs on the UTF-8 length of the characters read so
far, before each character after the first is appended (`LenOK`): a token of `n` characters is
accepted iff its first `n - 1` characters take fewer than `MAX_LEN` bytes.
-/

namespace SudoersSpec.Grammar

open SudoersSpec.Syntax
open SudoersSpec.Syntax.Parser
open _root_.SudoersSpec.Syntax.Stream (Reaches)

variable {α : Type}

/-! ## Character units -/

/-- One character unit read by `accept_escaped T pred`: consumed `u`, value `x`, right context
`rest`. -/
inductive EscUnit (T : TokenSpec α) (pred : Char → Bool) : List Char → Char → List Char → Prop
  | plain {c : Char} {rest : List Char} : pred c = true → (T.allowEscape = true → c ≠ '\\') →
      EscUnit T pred [c] c rest
  | escaped {d : Char} {rest : List Char} : T.allowEscape = true → T.escaped d = true →
      EscUnit T pred ['\\', d] d rest
  | backslash {rest : List Char} : T.allowEscape = true → pred '\\' = true →
      NextNot (fun d => T.escaped d = true) rest → EscUnit T pred ['\\'] '\\' rest
  | continuation {rest : List Char} : T.allowEscape = true → T.escaped '\n' = false →
      pred '\\' = false → pred ' ' = true → EscUnit T pred ['\\', '\n'] ' ' rest

/-- `accept_escaped T pred` rejects without consuming: the next character is refused by `pred`
and does not open an escape. -/
def EscStop (T : TokenSpec α) (pred : Char → Bool) (r : List Char) : Prop :=
  NextNot (fun d => pred d = true ∨ (T.allowEscape = true ∧ d = '\\')) r

/-- The conditions under which `\ newline` makes `accept_escaped T pred` reject after consuming
both characters. -/
def EscRejects (T : TokenSpec α) (pred : Char → Bool) : Prop :=
  T.allowEscape = true ∧ T.escaped '\n' = false ∧ pred '\\' = false ∧ pred ' ' = false

theorem EscUnit.trunc {T : TokenSpec α} {pred : Char → Bool} {u : List Char} {x : Char}
    {a b : List Char} (h : EscUnit T pred u x (a ++ b)) : EscUnit T pred u x a := by
  cases h with
  | plain h1 h2 => exact .plain h1 h2
  | escaped h1 h2 => exact .escaped h1 h2
  | backslash h1 h2 h3 => exact .backslash h1 h2 h3.trunc
  | continuation h1 h2 h3 h4 => exact .continuation h1 h2 h3 h4

theorem EscUnit.ne_nil {T : TokenSpec α} {pred : Char → Bool} {u : List Char} {x : Char}
    {r : List Char} (h : EscUnit T pred u x r) : u ≠ [] := by
  cases h <;> simp

/-! ## `accept_escaped`: closed forms -/

theorem acceptEscaped_run_plain (T : TokenSpec α) (pred : Char → Bool) (s : Stream)
    (h : ¬ (T.allowEscape = true ∧ s.peek = some '\\')) :
    (acceptEscaped T pred).run s =
      match s.peek with
      | some c => if pred c then (.ok c, s.pop) else (.error .reject, s)
      | none => (.error .reject, s) := by
  have hb : ((if T.allowEscape then eatChar '\\' else pure false : Parser Bool).run s) =
      (.ok false, s) := by
    cases hA : T.allowEscape
    · rfl
    · simp only [hA, true_and] at h
      simp only [ite_true, run_eatChar, Stream.eatChar_eq, h, ite_false]
  simp only [acceptEscaped, run_bind, hb, Bool.false_eq_true, ite_false, run_nextIf]
  rcases s with ⟨_ | ⟨c, cs⟩, l, k⟩
  · rfl
  · simp only [Stream.nextIf_cons, Stream.peek_mk, List.head?_cons]
    by_cases hc : pred c = true
    · simp only [hc, ite_true]; rfl
    · simp only [hc, Bool.false_eq_true, ite_false]; rfl

theorem acceptEscaped_run_esc (T : TokenSpec α) (pred : Char → Bool) (s : Stream)
    (hA : T.allowEscape = true) (h : s.peek = some '\\') :
    (acceptEscaped T pred).run s =
      match s.pop.peek with
      | some d =>
        if T.escaped d then (.ok d, s.pop.pop)
        else if pred '\\' then (.ok '\\', s.pop)
        else if d = '\n' then
          (if pred ' ' then (.ok ' ', s.pop.pop) else (.error .reject, s.pop.pop))
        else (.error (.fatal ⟨s.pop.getPos, s.pop.getPos⟩ .illegalEscapeSequence), s.pop)
      | none =>
        if pred '\\' then (.ok '\\', s.pop)
        else (.error (.fatal ⟨s.pop.getPos, s.pop.getPos⟩ .illegalEscapeSequence), s.pop) := by
  have hb : ((if T.allowEscape then eatChar '\\' else pure false : Parser Bool).run s) =
      (.ok true, s.pop) := by
    simp only [hA, ite_true, run_eatChar, Stream.eatChar_eq, h]
  simp only [acceptEscaped, run_bind, hb, ite_true, run_nextIf]
  generalize s.pop = t
  rcases t with ⟨_ | ⟨d, ds⟩, l, k⟩
  · simp only [Stream.nextIf_nil, Stream.peek_mk, List.head?_nil]
    by_cases hp : pred '\\' = true
    · simp only [hp, ite_true]; rfl
    · simp only [hp, Bool.false_eq_true, ite_false, run_bind, run_eatChar, Stream.eatChar_eq,
        Stream.peek_mk, List.head?_nil, reduceCtorEq]; rfl
  · simp only [Stream.nextIf_cons, Stream.peek_mk, List.head?_cons]
    by_cases he : T.escaped d = true
    · simp only [he, ite_true]; rfl
    · simp only [he, Bool.false_eq_true, ite_false]
      by_cases hp : pred '\\' = true
      · simp only [hp, ite_true]; rfl
      · simp only [hp, Bool.false_eq_true, ite_false, run_bind, run_eatChar, Stream.eatChar_eq,
          Stream.peek_mk, List.head?_cons, Option.some.injEq]
        by_cases hd : d = '\n'
        · subst hd
          simp only [ite_true]
          by_cases hs : pred ' ' = true
          · simp only [hs, ite_true]; rfl
          · simp only [hs, Bool.false_eq_true, ite_false]; rfl
        · simp only [hd, ite_false]; rfl

/-! ## `accept_escaped`: PT2 to PT4 -/

/-- PT3 for one character unit. -/
theorem acceptEscaped_sound (T : TokenSpec α) (pred : Char → Bool) {s s' : Stream} {x : Char}
    (h : (acceptEscaped T pred).run s = (.ok x, s')) :
    ∃ u, s.rest = u ++ s'.rest ∧ EscUnit T pred u x s'.rest := by
  by_cases hE : T.allowEscape = true ∧ s.peek = some '\\'
  · rw [acceptEscaped_run_esc T pred s hE.1 hE.2] at h
    have e1 := Stream.rest_of_peek hE.2
    revert h
    cases hp : s.pop.peek with
    | none =>
      have : s.pop.rest = [] := by
        rw [Stream.peek_eq_head] at hp; exact List.head?_eq_none_iff.mp hp
      simp only
      split
      · rename_i hpb
        intro h; simp only [Prod.mk.injEq, Except.ok.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨['\\'], e1, .backslash hE.1 hpb (by rw [this]; exact NextNot.nil _)⟩
      · intro h; simp at h
    | some d =>
      have e2 := Stream.rest_of_peek hp
      simp only
      split
      · rename_i hed
        intro h; simp only [Prod.mk.injEq, Except.ok.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨['\\', d], by rw [e1, e2]; rfl, .escaped hE.1 hed⟩
      · rename_i hed
        split
        · rename_i hpb
          intro h; simp only [Prod.mk.injEq, Except.ok.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨['\\'], e1, .backslash hE.1 hpb ?_⟩
          rw [e2]; intro d' e hd'; simp only [List.head?_cons, Option.some.injEq] at e
          subst e; exact hed hd'
        · rename_i hpb
          split
          · rename_i hdn
            subst hdn
            split
            · rename_i hps
              intro h; simp only [Prod.mk.injEq, Except.ok.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact ⟨['\\', '\n'], by rw [e1, e2]; rfl,
                .continuation hE.1 (by simpa using hed) (by simpa using hpb) hps⟩
            · intro h; simp at h
          · intro h; simp at h
  · rw [acceptEscaped_run_plain T pred s hE] at h
    revert h
    cases hp : s.peek with
    | none => intro h; simp at h
    | some c =>
      simp only
      split
      · rename_i hc
        intro h; simp only [Prod.mk.injEq, Except.ok.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨[c], Stream.rest_of_peek hp, .plain hc ?_⟩
        intro hA e; subst e; exact hE ⟨hA, hp⟩
      · intro h; simp at h

/-- PT4 for one character unit. -/
theorem acceptEscaped_complete (T : TokenSpec α) (pred : Char → Bool) {u : List Char} {x : Char}
    {rest : List Char} {s : Stream} (hu : EscUnit T pred u x rest) (hs : s.rest = u ++ rest) :
    ∃ s', (acceptEscaped T pred).run s = (.ok x, s') ∧ s'.rest = rest := by
  cases hu with
  | plain hc hA =>
    have hp : s.peek = some x := by rw [Stream.peek_eq_head, hs]; rfl
    have hE : ¬ (T.allowEscape = true ∧ s.peek = some '\\') := by
      rintro ⟨h1, h2⟩; rw [hp] at h2; exact hA h1 (Option.some.inj h2)
    rw [acceptEscaped_run_plain T pred s hE, hp]
    simp only [hc, ite_true]
    exact ⟨_, rfl, by rw [Stream.pop_rest, hs]; rfl⟩
  | escaped hA hed =>
    have hp : s.peek = some '\\' := by rw [Stream.peek_eq_head, hs]; rfl
    have hp2 : s.pop.peek = some x := by rw [Stream.peek_eq_head, Stream.pop_rest, hs]; rfl
    rw [acceptEscaped_run_esc T pred s hA hp, hp2]
    simp only [hed, ite_true]
    exact ⟨_, rfl, by rw [Stream.pop_rest, Stream.pop_rest, hs]; rfl⟩
  | backslash hA hpb hn =>
    have hp : s.peek = some '\\' := by rw [Stream.peek_eq_head, hs]; rfl
    rw [acceptEscaped_run_esc T pred s hA hp]
    have hr : s.pop.rest = rest := by rw [Stream.pop_rest, hs]; rfl
    cases hp2 : s.pop.peek with
    | none => simp only [hpb, ite_true]; exact ⟨_, rfl, hr⟩
    | some d =>
      have hed : T.escaped d = false := by
        have := hn d (by rw [← hr, ← Stream.peek_eq_head, hp2]); simpa using this
      simp only [hed, hpb, Bool.false_eq_true, ite_false, ite_true]
      exact ⟨_, rfl, hr⟩
  | continuation hA hen hpb hps =>
    have hp : s.peek = some '\\' := by rw [Stream.peek_eq_head, hs]; rfl
    have hp2 : s.pop.peek = some '\n' := by rw [Stream.peek_eq_head, Stream.pop_rest, hs]; rfl
    rw [acceptEscaped_run_esc T pred s hA hp, hp2]
    simp only [hen, hpb, hps, Bool.false_eq_true, ite_false, ite_true]
    exact ⟨_, rfl, by rw [Stream.pop_rest, Stream.pop_rest, hs]; rfl⟩

/-- PT2 for one character unit, exactly: a `Reject` either consumed nothing (and then the
input satisfies `EscStop`) or consumed `\ newline` under `EscRejects`. -/
theorem acceptEscaped_reject (T : TokenSpec α) (pred : Char → Bool) {s s' : Stream}
    (h : (acceptEscaped T pred).run s = (.error .reject, s')) :
    (s' = s ∧ EscStop T pred s.rest) ∨
      (EscRejects T pred ∧ s.rest = '\\' :: '\n' :: s'.rest) := by
  by_cases hE : T.allowEscape = true ∧ s.peek = some '\\'
  · right
    rw [acceptEscaped_run_esc T pred s hE.1 hE.2] at h
    have e1 := Stream.rest_of_peek hE.2
    revert h
    cases hp : s.pop.peek with
    | none => simp only; split <;> intro h <;> simp at h
    | some d =>
      have e2 := Stream.rest_of_peek hp
      simp only
      split
      · intro h; simp at h
      · rename_i hed
        split
        · intro h; simp at h
        · rename_i hpb
          split
          · rename_i hdn
            subst hdn
            split
            · intro h; simp at h
            · rename_i hps
              intro h; simp only [Prod.mk.injEq] at h
              obtain ⟨-, rfl⟩ := h
              exact ⟨⟨hE.1, by simpa using hed, by simpa using hpb, by simpa using hps⟩,
                by rw [e1, e2]⟩
          · intro h; simp at h
  · left
    rw [acceptEscaped_run_plain T pred s hE] at h
    revert h
    cases hp : s.peek with
    | none =>
      intro h; simp only [Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      refine ⟨rfl, ?_⟩
      rw [Stream.peek_eq_head] at hp; rw [List.head?_eq_none_iff.mp hp]; exact NextNot.nil _
    | some c =>
      simp only
      split
      · intro h; simp at h
      · rename_i hc
        intro h; simp only [Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        refine ⟨rfl, ?_⟩
        intro d e hd
        rw [← Stream.peek_eq_head, hp] at e
        cases e
        rcases hd with hd | hd
        · exact hc hd
        · exact hE ⟨hd.1, hd.2 ▸ hp⟩

/-- Converse of `acceptEscaped_reject`, first case. -/
theorem acceptEscaped_stop (T : TokenSpec α) (pred : Char → Bool) {s : Stream}
    (h : EscStop T pred s.rest) : (acceptEscaped T pred).run s = (.error .reject, s) := by
  have hE : ¬ (T.allowEscape = true ∧ s.peek = some '\\') := by
    rintro ⟨h1, h2⟩; exact h '\\' (by rw [← Stream.peek_eq_head, h2]) (.inr ⟨h1, rfl⟩)
  rw [acceptEscaped_run_plain T pred s hE]
  cases hp : s.peek with
  | none => rfl
  | some c =>
    have : pred c = false := by
      have := h c (by rw [← Stream.peek_eq_head, hp]); simp at this; exact this.1
    simp [this]

/-- Converse of `acceptEscaped_reject`, second case. -/
theorem acceptEscaped_rejects (T : TokenSpec α) (pred : Char → Bool) {s : Stream} {r : List Char}
    (h : EscRejects T pred) (hs : s.rest = '\\' :: '\n' :: r) :
    ∃ s', (acceptEscaped T pred).run s = (.error .reject, s') ∧ s'.rest = r := by
  obtain ⟨hA, hen, hpb, hps⟩ := h
  have hp : s.peek = some '\\' := by rw [Stream.peek_eq_head, hs]; rfl
  have hp2 : s.pop.peek = some '\n' := by rw [Stream.peek_eq_head, Stream.pop_rest, hs]; rfl
  rw [acceptEscaped_run_esc T pred s hA hp, hp2]
  simp only [hen, hpb, hps, Bool.false_eq_true, ite_false, ite_true]
  exact ⟨_, rfl, by rw [Stream.pop_rest, Stream.pop_rest, hs]; rfl⟩

/-- `accept_escaped` fails with `Reject` or with a fatal error, never otherwise. -/
theorem acceptEscaped_maybe_none {T : TokenSpec α} {pred : Char → Bool} {s : Stream} :
    Syntax.maybe ((acceptEscaped T pred).run s).1 = .ok none →
      ((acceptEscaped T pred).run s).1 = .error .reject := by
  cases ((acceptEscaped T pred).run s).1 with
  | ok a => simp
  | error e => cases e <;> simp

/-! ## The token loop -/

/-- The loop of `impl<T: Token> Parse for T` from the characters `str` read so far. -/
def tokenLoop (T : TokenSpec α) (str : List Char) : Parser (List Char) :=
  whileMaybe (acceptEscaped T T.accept) (acceptEscaped_consumes T T.accept) (tokenBody T) id str

/-- The length check of the token loop: before each further character is appended, the UTF-8
length of the characters so far (`str`) is below `maxLen`. -/
def LenOK (maxLen : Nat) : List Char → List Char → Prop
  | _, [] => True
  | str, x :: xs => utf8Len str < maxLen ∧ LenOK maxLen (str ++ [x]) xs

/-- The units of a token after the first, up to the end of the token: consumed `c`, values
`xs`, right context `rest`. -/
inductive TokTail (T : TokenSpec α) : List Char → List Char → List Char → Prop
  | stop {rest : List Char} : EscStop T T.accept rest → TokTail T [] [] rest
  | term {rest : List Char} : EscRejects T T.accept → TokTail T ['\\', '\n'] [] rest
  | cons {u x u' xs rest} : EscUnit T T.accept u x (u' ++ rest) → TokTail T u' xs rest →
      TokTail T (u ++ u') (x :: xs) rest

theorem TokTail.trunc {T : TokenSpec α} {c xs a b : List Char} (h : TokTail T c xs (a ++ b)) :
    TokTail T c xs a := by
  generalize e : a ++ b = r at h
  induction h with
  | stop hs => subst e; exact .stop hs.trunc
  | term hr => exact .term hr
  | cons hu _ ih =>
    subst e
    exact .cons (EscUnit.trunc (by rw [← List.append_assoc] at hu; exact hu)) (ih rfl)

theorem tokenBody_run (T : TokenSpec α) (str : List Char) (c : Char) (s : Stream) :
    (tokenBody T str c).run s =
      if utf8Len str ≥ T.maxLen then
        (.error (.fatal ⟨s.getPos, s.getPos⟩ .tokenExceedsMaximumLength), s)
      else (.ok (.next (str ++ [c])), s) := by
  simp only [tokenBody]; split <;> rfl

theorem tokenLoop_sound (T : TokenSpec α) (str : List Char) (s : Stream) {v : List Char}
    {s' : Stream} (h : (tokenLoop T str).run s = (.ok v, s')) :
    ∃ c xs, s.rest = c ++ s'.rest ∧ TokTail T c xs s'.rest ∧ LenOK T.maxLen str xs ∧
      v = str ++ xs := by
  have key := loop_rel (whileMaybeBody_progressive (acceptEscaped_consumes T T.accept)
      (tokenBody T) id)
    (fun str s r s'' => ∀ v, r = .ok v → ∃ c xs, s.rest = c ++ s''.rest ∧
      TokTail T c xs s''.rest ∧ LenOK T.maxLen str xs ∧ v = str ++ xs) ?_ ?_ ?_ str s
  · unfold tokenLoop whileMaybe at h
    rw [h] at key
    exact key v rfl
  · intro st s b s' hb v hv
    cases hv
    rw [whileMaybeBody_run] at hb
    revert hb
    cases hq : (acceptEscaped T T.accept).run s with
    | mk r s₁ =>
      cases r with
      | ok x => simp only [maybe_ok]; rw [tokenBody_run]; split <;> simp
      | error e =>
        cases e with
        | fatal sp k => simp
        | reject =>
          simp only [maybe_reject, id, Prod.mk.injEq, Except.ok.injEq, Step.done.injEq]
          rintro ⟨rfl, rfl⟩
          rcases acceptEscaped_reject T T.accept hq with ⟨rfl, hst⟩ | ⟨hr, hrest⟩
          · exact ⟨[], [], rfl, .stop hst, trivial, by simp⟩
          · exact ⟨['\\', '\n'], [], hrest, .term hr, trivial, by simp⟩
  · intro st s e s' _ v hv; cases hv
  · intro st s st' s' r s'' hb ih v hv
    obtain ⟨c, xs, hc, ht, hl, rfl⟩ := ih v hv
    rw [whileMaybeBody_run] at hb
    revert hb
    cases hq : (acceptEscaped T T.accept).run s with
    | mk r₁ s₁ =>
      cases r₁ with
      | ok x =>
        simp only [maybe_ok]; rw [tokenBody_run]
        split
        · simp
        · rename_i hlen
          simp only [Prod.mk.injEq, Except.ok.injEq, Step.next.injEq]
          rintro ⟨rfl, rfl⟩
          obtain ⟨u, hu, hunit⟩ := acceptEscaped_sound T T.accept hq
          refine ⟨u ++ c, x :: xs, ?_, .cons (by rw [← hc]; exact hunit) ht,
            ⟨by omega, hl⟩, by simp⟩
          rw [hu, hc, List.append_assoc]
      | error e => cases e <;> simp

theorem tokenLoop_complete (T : TokenSpec α) {c xs rest : List Char} (ht : TokTail T c xs rest) :
    ∀ (str : List Char) (s : Stream), LenOK T.maxLen str xs → s.rest = c ++ rest →
      ∃ s', (tokenLoop T str).run s = (.ok (str ++ xs), s') ∧ s'.rest = rest := by
  induction ht with
  | stop hst =>
    intro str s _ hs
    unfold tokenLoop whileMaybe
    rw [loop_run, whileMaybeBody_run, acceptEscaped_stop T T.accept (by rw [hs]; exact hst)]
    exact ⟨s, by simp, hs⟩
  | term hr =>
    intro str s _ hs
    obtain ⟨s', h, hs'⟩ := acceptEscaped_rejects T T.accept hr hs
    unfold tokenLoop whileMaybe
    rw [loop_run, whileMaybeBody_run, h]
    exact ⟨s', by simp, hs'⟩
  | @cons u x u' xs rest hu _ ih =>
    intro str s hl hs
    obtain ⟨s₁, h₁, hs₁⟩ := acceptEscaped_complete T T.accept hu (by rw [hs, List.append_assoc])
    obtain ⟨s', h', hs'⟩ := ih (str ++ [x]) s₁ hl.2 hs₁
    have hlen : ¬ utf8Len str ≥ T.maxLen := by have := hl.1; omega
    refine ⟨s', ?_, hs'⟩
    have e : (tokenLoop T str).run s = (tokenLoop T (str ++ [x])).run s₁ := by
      unfold tokenLoop whileMaybe
      rw [loop_run, whileMaybeBody_run, h₁]
      simp only [maybe_ok]
      rw [tokenBody_run]
      simp only [hlen, ite_false]
    rw [e, h']
    simp

theorem tokenLoop_ne_reject (T : TokenSpec α) (str : List Char) (s : Stream) :
    ((tokenLoop T str).run s).1 ≠ .error .reject := by
  refine loop_invariant (whileMaybeBody_progressive (acceptEscaped_consumes T T.accept)
      (tokenBody T) id) (fun _ => True) (fun r _ => r ≠ .error .reject)
    (fun _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => by simp) ?_ str s trivial
  intro st s e s' _ hb
  rw [whileMaybeBody_run] at hb
  revert hb
  cases (acceptEscaped T T.accept).run s with
  | mk r₁ s₁ =>
    cases r₁ with
    | ok x =>
      simp only [maybe_ok]; rw [tokenBody_run]
      split
      · simp only [Prod.mk.injEq, Except.error.injEq]; rintro ⟨rfl, -⟩; simp
      · simp
    | error e' =>
      cases e' with
      | reject => simp
      | fatal sp k => simp only [maybe_fatal, Prod.mk.injEq, Except.error.injEq]; rintro ⟨rfl, -⟩; simp

/-! ## Tokens -/

/-- A token of class `T` (`impl<T: Token> Parse for T`): the first unit (by `accept_1st`), the
further units up to the end of the token, the length condition, and `T.construct` on the
characters read. -/
inductive TokenG (T : TokenSpec α) : Gram α
  | mk {u x c' xs a rest} : EscUnit T T.accept1st u x (c' ++ rest) → TokTail T c' xs rest →
      LenOK T.maxLen [x] xs → T.construct (x :: xs) = .ok a → TokenG T (u ++ c') a rest

theorem TokenG.trunc (T : TokenSpec α) : Trunc (TokenG T) := by
  intro c a x y h
  cases h with
  | mk hu ht hl hc =>
    exact .mk (EscUnit.trunc (by rw [← List.append_assoc] at hu; exact hu)) ht.trunc hl hc

theorem token_run (T : TokenSpec α) (s : Stream) :
    (token T).run s =
      match (acceptEscaped T T.accept1st).run s with
      | (.ok x, s₁) =>
        match (tokenLoop T [x]).run s₁ with
        | (.ok str, s₂) =>
          match T.construct str with
          | .ok a => (.ok a, s₂)
          | .error msg => (.error (.fatal ⟨s.getPos, s₂.getPos⟩ msg), s₂)
        | (.error e, s₂) => (.error e, s₂)
      | (.error e, s₁) => (.error e, s₁) := by
  simp only [token, run_bind, run_getPos]
  cases (acceptEscaped T T.accept1st).run s with
  | mk r₁ s₁ =>
    cases r₁ with
    | error e => rfl
    | ok x =>
      simp only
      rw [show (whileMaybe (acceptEscaped T T.accept) (acceptEscaped_consumes T T.accept)
        (tokenBody T) id [x]) = tokenLoop T [x] from rfl]
      cases (tokenLoop T [x]).run s₁ with
      | mk r₂ s₂ =>
        cases r₂ with
        | error e => rfl
        | ok str => simp only; cases T.construct str <;> rfl

/-- PT3 for tokens. -/
theorem token_sound (T : TokenSpec α) : Sound (token T) (TokenG T) := by
  intro s a s' h
  rw [token_run] at h
  revert h
  cases h₁ : (acceptEscaped T T.accept1st).run s with
  | mk r₁ s₁ =>
    cases r₁ with
    | error e => intro h; cases h
    | ok x =>
      simp only
      cases h₂ : (tokenLoop T [x]).run s₁ with
      | mk r₂ s₂ =>
        cases r₂ with
        | error e => intro h; cases h
        | ok str =>
          simp only
          cases h₃ : T.construct str with
          | error msg => intro h; cases h
          | ok b =>
            intro h
            simp only [Prod.mk.injEq, Except.ok.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨u, hu, hunit⟩ := acceptEscaped_sound T T.accept1st h₁
            obtain ⟨c', xs, hc', ht, hl, rfl⟩ := tokenLoop_sound T [x] s₁ h₂
            refine ⟨u ++ c', by rw [hu, hc', List.append_assoc], ?_⟩
            exact .mk (by rw [← hc']; exact hunit) ht hl (by simpa using h₃)

/-- PT4 for tokens. -/
theorem token_complete (T : TokenSpec α) : Complete (token T) (TokenG T) := by
  intro c a rest s hd hs
  cases hd with
  | @mk u x c' xs _ _ hu ht hl hc =>
    obtain ⟨s₁, h₁, hs₁⟩ := acceptEscaped_complete T T.accept1st hu (by rw [hs, List.append_assoc])
    obtain ⟨s₂, h₂, hs₂⟩ := tokenLoop_complete T ht [x] s₁ hl hs₁
    rw [token_run, h₁]
    simp only [h₂]
    rw [show [x] ++ xs = x :: xs from rfl, hc]
    exact ⟨s₂, rfl, hs₂⟩

/-- PT2 for tokens, exactly: a token rejects iff its first unit rejects, and then either
nothing was consumed or `\ newline` was consumed under `EscRejects T T.accept1st`. -/
theorem token_reject (T : TokenSpec α) {s s' : Stream}
    (h : (token T).run s = (.error .reject, s')) :
    (s' = s ∧ EscStop T T.accept1st s.rest) ∨
      (EscRejects T T.accept1st ∧ s.rest = '\\' :: '\n' :: s'.rest) := by
  rw [token_run] at h
  revert h
  cases h₁ : (acceptEscaped T T.accept1st).run s with
  | mk r₁ s₁ =>
    cases r₁ with
    | error e =>
      intro h; simp only [Prod.mk.injEq, Except.error.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact acceptEscaped_reject T T.accept1st h₁
    | ok x =>
      simp only
      have hne := tokenLoop_ne_reject T [x] s₁
      revert hne
      cases (tokenLoop T [x]).run s₁ with
      | mk r₂ s₂ =>
        cases r₂ with
        | error e =>
          simp only [ne_eq, Prod.mk.injEq, Except.error.injEq]
          intro hne h; exact absurd (by rw [h.1]) hne
        | ok str => simp only; intro _; cases T.construct str <;> simp

/-- The exact condition of PT2 for tokens: unless escapes are allowed, newline is not escaped
and `accept_1st` accepts neither `\` nor `' '`, a `Reject` of the token consumed nothing. -/
theorem token_rejectPure (T : TokenSpec α) (hT : ¬ EscRejects T T.accept1st) :
    RejectPure (token T) := by
  intro s s' h
  rcases token_reject T h with ⟨rfl, -⟩ | ⟨hr, -⟩
  · rfl
  · exact absurd hr hT

/-- Outside that condition PT2 fails: on `\ newline` the token rejects having consumed both
characters. -/
theorem token_reject_of_escRejects (T : TokenSpec α) (hT : EscRejects T T.accept1st)
    {s : Stream} {r : List Char} (hs : s.rest = '\\' :: '\n' :: r) :
    ∃ s', (token T).run s = (.error .reject, s') ∧ s'.rest = r := by
  obtain ⟨s', h, hs'⟩ := acceptEscaped_rejects T T.accept1st hT hs
  rw [token_run, h]
  exact ⟨s', rfl, hs'⟩

theorem token_rejectPure_iff (T : TokenSpec α) :
    RejectPure (token T) ↔ ¬ EscRejects T T.accept1st := by
  constructor
  · intro hp hT
    obtain ⟨s', h, hs'⟩ := token_reject_of_escRejects T hT (s := ⟨['\\', '\n'], 1, 1⟩) rfl
    have := hp _ _ h
    subst this
    simp at hs'
  · exact token_rejectPure T

/-! ## Tokens without escapes (`ALLOW_ESCAPE = false`) -/

theorem utf8Len_append (a b : List Char) : utf8Len (a ++ b) = utf8Len a + utf8Len b := by
  simp [utf8Len, List.map_append, List.sum_append]

/-- `LenOK` in closed form: either no character follows the first ones in `str`, or the
characters before the last one take fewer than `m` bytes. -/
theorem lenOK_iff (m : Nat) :
    ∀ (str xs : List Char), LenOK m str xs ↔ (xs = [] ∨ utf8Len (str ++ xs.dropLast) < m)
  | str, [] => by simp [LenOK]
  | str, [x] => by simp [LenOK]
  | str, x :: y :: ys => by
    have ih := lenOK_iff m (str ++ [x]) (y :: ys)
    simp only [LenOK] at ih ⊢
    rw [ih]
    simp only [reduceCtorEq, false_or, List.dropLast_cons_cons, List.append_assoc,
      List.singleton_append, utf8Len_append]
    constructor
    · intro h; exact h.2
    · intro h; exact ⟨by have := utf8Len_append str (x :: (y :: ys).dropLast); omega, h⟩

theorem escUnit_noEsc {T : TokenSpec α} (hA : T.allowEscape = false) {pred : Char → Bool}
    {u : List Char} {x : Char} {r : List Char} :
    EscUnit T pred u x r ↔ u = [x] ∧ pred x = true := by
  constructor
  · intro h
    cases h with
    | plain hc _ => exact ⟨rfl, hc⟩
    | escaped h1 _ => rw [hA] at h1; cases h1
    | backslash h1 _ _ => rw [hA] at h1; cases h1
    | continuation h1 _ _ _ => rw [hA] at h1; cases h1
  · rintro ⟨rfl, h⟩
    exact .plain h (by intro h'; rw [hA] at h'; cases h')

theorem escStop_noEsc {T : TokenSpec α} (hA : T.allowEscape = false) {pred : Char → Bool}
    {r : List Char} : EscStop T pred r ↔ NextNot (fun d => pred d = true) r := by
  unfold EscStop NextNot
  simp [hA]

theorem tokTail_noEsc {T : TokenSpec α} (hA : T.allowEscape = false) {xs rest : List Char} :
    ∀ {c : List Char}, TokTail T c xs rest ↔
      c = xs ∧ (∀ x ∈ c, T.accept x = true) ∧ NextNot (fun d => T.accept d = true) rest := by
  intro c
  constructor
  · intro h
    induction h with
    | stop hs => exact ⟨rfl, by simp, (escStop_noEsc hA).mp hs⟩
    | term hr => have := hr.1; rw [hA] at this; cases this
    | cons hu _ ih =>
      obtain ⟨rfl, hc⟩ := (escUnit_noEsc hA).mp hu
      obtain ⟨rfl, hall, hn⟩ := ih
      refine ⟨rfl, ?_, hn⟩
      intro y hy
      simp only [List.singleton_append, List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact hc
      · exact hall y hy
  · rintro ⟨rfl, hall, hn⟩
    induction c with
    | nil => exact .stop ((escStop_noEsc hA).mpr hn)
    | cons x c ih =>
      have := TokTail.cons (T := T) (u := [x]) (x := x)
        ((escUnit_noEsc hA).mpr ⟨rfl, hall x (by simp)⟩)
        (ih (fun y hy => hall y (List.mem_cons_of_mem _ hy)))
      exact this

/-- The token grammar for a class without escapes: a first character of `accept_1st`, further
characters of `accept`, ended in front of a character outside `accept`, the length condition,
and `construct` on the characters. -/
theorem tokenG_noEsc {T : TokenSpec α} (hA : T.allowEscape = false) {c : List Char} {a : α}
    {rest : List Char} :
    TokenG T c a rest ↔
      ∃ x xs, c = x :: xs ∧ T.accept1st x = true ∧ (∀ y ∈ xs, T.accept y = true) ∧
        NextNot (fun d => T.accept d = true) rest ∧ (xs = [] ∨ utf8Len c.dropLast < T.maxLen) ∧
        T.construct c = .ok a := by
  constructor
  · intro h
    cases h with
    | @mk u x c' xs _ _ hu ht hl hc =>
      obtain ⟨rfl, h1⟩ := (escUnit_noEsc hA).mp hu
      obtain ⟨rfl, hall, hn⟩ := (tokTail_noEsc hA).mp ht
      refine ⟨x, c', rfl, h1, hall, hn, ?_, hc⟩
      rcases (lenOK_iff _ _ _).mp hl with h | h
      · exact .inl h
      · cases c' with
        | nil => exact .inl rfl
        | cons y ys => right; simpa using h
  · rintro ⟨x, xs, rfl, h1, hall, hn, hl, hc⟩
    refine TokenG.mk (u := [x]) (c' := xs) ((escUnit_noEsc hA).mpr ⟨rfl, h1⟩)
      ((tokTail_noEsc hA).mpr ⟨rfl, hall, hn⟩) ?_ hc
    apply (lenOK_iff _ _ _).mpr
    rcases hl with h | h
    · exact .inl h
    · cases xs with
      | nil => exact .inl rfl
      | cons y ys => right; simpa using h

end SudoersSpec.Grammar
