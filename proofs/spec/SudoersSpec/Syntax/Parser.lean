import SudoersSpec.Syntax.CharOracle

/-!
# The parser type, its primitives and the loop combinator

Rust: `trait Parse { fn parse(stream: &mut CharStream) -> Parsed<Self>; }`. A production is a
function `Stream → Parsed α × Stream`: the stream survives errors, because recovery continues from
where the failure left it.

`Parser α` bundles such a function with the proof that its output stream is reached from its
input stream (`Stream.Reaches`: the input advanced by some characters, so the output `rest` is a
suffix and the position is the position after the consumed characters). `Parser` is a monad,
so a production written in `do` notation from the primitives below comes with this proof for
free; `do` notation also mirrors Rust's `?`.

Loops (`while` in Rust) go through `Parser.loop`, which needs a proof that every iteration
that continues consumed input (`Progressive`). It is defined by structural recursion on a fuel
of `rest.length + 1` iterations, which is always enough: `loop_run` is the unfolding equation
without fuel. Because the recursion is structural, everything here reduces in the kernel
(`decide`, `rfl` on concrete inputs).

How to add a production: see `Syntax/README.md`.
-/

namespace SudoersSpec.Syntax

open _root_.SudoersSpec.Syntax.Stream (Reaches)

/-- A production of the reference parser: `impl Parse for T` in Rust. `run` maps a stream to
the result and the stream after it; `reaches` says that the output stream is the input
advanced by some characters. -/
structure Parser (α : Type) where
  run : Stream → Parsed α × Stream
  reaches : ∀ s, Reaches s (run s).2

namespace Parser

/-! ## Monad -/

/-- `make(value)` / `Ok(value)`: succeed without consuming. -/
protected def pure (a : α) : Parser α where
  run s := (.ok a, s)
  reaches s := .refl s

/-- Sequencing with Rust's `?`: run `p`; on `Ok(a)` continue with `f a`, on `Err(e)` stop with
`Err(e)` and the stream `p` left. -/
protected def bind (p : Parser α) (f : α → Parser β) : Parser β where
  run s :=
    match p.run s with
    | (.ok a, s₁) => (f a).run s₁
    | (.error e, s₁) => (.error e, s₁)
  reaches s := by
    have h := p.reaches s
    revert h
    cases p.run s with
    | mk r s₁ =>
      cases r with
      | error e => exact id
      | ok a => exact fun h => h.trans ((f a).reaches s₁)

instance : Monad Parser where
  pure := Parser.pure
  bind := Parser.bind

@[simp] theorem run_pure (a : α) (s : Stream) : (pure a : Parser α).run s = (.ok a, s) := rfl

theorem run_bind (p : Parser α) (f : α → Parser β) (s : Stream) :
    (p >>= f).run s =
      match p.run s with
      | (.ok a, s₁) => (f a).run s₁
      | (.error e, s₁) => (.error e, s₁) := rfl

@[simp] theorem run_bind_of_ok {p : Parser α} {s s₁ : Stream} {a : α} (h : p.run s = (.ok a, s₁))
    (f : α → Parser β) : (p >>= f).run s = (f a).run s₁ := by
  rw [run_bind, h]

@[simp] theorem run_bind_of_error {p : Parser α} {s s₁ : Stream} {e : Status}
    (h : p.run s = (.error e, s₁)) (f : α → Parser β) : (p >>= f).run s = (.error e, s₁) := by
  rw [run_bind, h]

/-- Inversion of `bind` on success. -/
theorem run_bind_eq_ok {p : Parser α} {f : α → Parser β} {s s' : Stream} {b : β} :
    (p >>= f).run s = (.ok b, s') ↔ ∃ a s₁, p.run s = (.ok a, s₁) ∧ (f a).run s₁ = (.ok b, s') := by
  rw [run_bind]
  constructor
  · intro h
    revert h
    cases hp : p.run s with
    | mk r s₁ =>
      cases r with
      | error e => intro h; cases h
      | ok a => intro h; exact ⟨a, s₁, rfl, h⟩
  · rintro ⟨a, s₁, hp, hf⟩
    rw [hp]; exact hf

/-- Inversion of `bind` on failure. -/
theorem run_bind_eq_error {p : Parser α} {f : α → Parser β} {s s' : Stream} {e : Status} :
    (p >>= f).run s = (.error e, s') ↔
      p.run s = (.error e, s') ∨ ∃ a s₁, p.run s = (.ok a, s₁) ∧ (f a).run s₁ = (.error e, s') := by
  rw [run_bind]
  constructor
  · intro h
    revert h
    cases hp : p.run s with
    | mk r s₁ =>
      cases r with
      | error e' => intro h; left; simpa using h
      | ok a => intro h; right; exact ⟨a, s₁, rfl, h⟩
  · rintro (hp | ⟨a, s₁, hp, hf⟩)
    · rw [hp]
    · rw [hp]; exact hf

theorem length_le (p : Parser α) (s : Stream) : (p.run s).2.rest.length ≤ s.rest.length :=
  (p.reaches s).length_le

/-- The output `rest` of every parser is a suffix of its input `rest`. -/
theorem suffix (p : Parser α) (s : Stream) : (p.run s).2.rest <:+ s.rest :=
  (p.reaches s).suffix

theorem reaches_of_run {p : Parser α} {s s' : Stream} {r : Parsed α} (h : p.run s = (r, s')) :
    Reaches s s' := by
  have := p.reaches s; rw [h] at this; exact this

theorem length_le_of_run {p : Parser α} {s s' : Stream} {r : Parsed α} (h : p.run s = (r, s')) :
    s'.rest.length ≤ s.rest.length :=
  (reaches_of_run h).length_le

/-! ## Primitives -/

/-- `return Err(e)`: fail without consuming. -/
def fail (e : Status) : Parser α where
  run s := (.error e, s)
  reaches s := .refl s

/-- `basic_parser::reject`: `Err(Status::Reject)`. -/
def reject : Parser α := fail .reject

/-- `r?` on a `Parsed` value already computed, or returning it as the result. -/
def lift (r : Parsed α) : Parser α where
  run s := (r, s)
  reaches s := .refl s

/-- Run `p` and keep its result as a value, without propagating an error: Rust code that
stores a `Parsed<T>` (`let item = expect_nonterminal(stream);`) or tests it with `is_ok()`. -/
def observe (p : Parser α) : Parser (Parsed α) where
  run s := match p.run s with | (r, s') => (.ok r, s')
  reaches s := by
    have h := p.reaches s
    revert h
    cases p.run s with | mk r s' => exact id

/-- `maybe(p)`: `basic_parser::maybe` applied to the result of `p`. -/
def maybe (p : Parser α) : Parser (Option α) where
  run s := match p.run s with | (r, s') => (Syntax.maybe r, s')
  reaches s := by
    have h := p.reaches s
    revert h
    cases p.run s with | mk r s' => exact id

/-- `CharStream::get_pos`. -/
def getPos : Parser (Nat × Nat) where
  run s := (.ok s.getPos, s)
  reaches s := .refl s

/-- `CharStream::peek`. -/
def peek : Parser (Option Char) where
  run s := (.ok s.peek, s)
  reaches s := .refl s

/-- `stream.clone()`: the current stream as a value. -/
def getStream : Parser Stream where
  run s := (.ok s, s)
  reaches s := .refl s

/-- `CharStream::next_if`. -/
def nextIf (f : Char → Bool) : Parser (Option Char) where
  run s := match s.nextIf f with | (c, s') => (.ok c, s')
  reaches s := by
    have h := Reaches.nextIf f s
    revert h
    cases s.nextIf f with | mk c s' => exact id

/-- `CharStream::eat_char`. -/
def eatChar (c : Char) : Parser Bool where
  run s := match s.eatChar c with | (b, s') => (.ok b, s')
  reaches s := by
    have h := Reaches.eatChar c s
    revert h
    cases s.eatChar c with | mk b s' => exact id

/-- `while stream.next_if(f).is_some() {}`. -/
def skipWhile (f : Char → Bool) : Parser Unit where
  run s := (.ok (), s.skipWhile f)
  reaches s := Reaches.skipWhile f s

/-- `CharStream::skip_to_newline`. -/
def skipToNewline : Parser Unit where
  run s := (.ok (), s.skipToNewline)
  reaches s := Reaches.skipWhile _ s

/-- `CharStream::advance`. -/
def advance (n : Nat) : Parser Unit where
  run s := (.ok (), s.advance n)
  reaches s := Reaches.advance s n

/-- `unrecoverable!(stream, ...)`: a fatal error with the empty span at the current position. -/
def fatalHere (kind : ErrKind) : Parser α := do
  let pos ← getPos
  fail (.fatal ⟨pos, pos⟩ kind)

/-- `unrecoverable!(pos = start, stream, ...)`: a fatal error spanning from `start` to the
current position. -/
def fatalFrom (start : Nat × Nat) (kind : ErrKind) : Parser α := do
  let pos ← getPos
  fail (.fatal ⟨start, pos⟩ kind)

@[simp] theorem run_fail (e : Status) (s : Stream) : (fail e : Parser α).run s = (.error e, s) :=
  rfl
@[simp] theorem run_reject (s : Stream) : (reject : Parser α).run s = (.error .reject, s) := rfl
@[simp] theorem run_lift (r : Parsed α) (s : Stream) : (lift r).run s = (r, s) := rfl
@[simp] theorem run_observe (p : Parser α) (s : Stream) :
    (observe p).run s = (.ok (p.run s).1, (p.run s).2) := by
  simp only [observe]
@[simp] theorem run_maybe (p : Parser α) (s : Stream) :
    (maybe p).run s = (Syntax.maybe (p.run s).1, (p.run s).2) := by
  simp only [maybe]
@[simp] theorem run_getPos (s : Stream) : getPos.run s = (.ok s.getPos, s) := rfl
@[simp] theorem run_peek (s : Stream) : peek.run s = (.ok s.peek, s) := rfl
@[simp] theorem run_getStream (s : Stream) : getStream.run s = (.ok s, s) := rfl
@[simp] theorem run_nextIf (f : Char → Bool) (s : Stream) :
    (nextIf f).run s = (.ok (s.nextIf f).1, (s.nextIf f).2) := by
  simp only [nextIf]
@[simp] theorem run_eatChar (c : Char) (s : Stream) :
    (eatChar c).run s = (.ok (s.eatChar c).1, (s.eatChar c).2) := by
  simp only [eatChar]
@[simp] theorem run_skipWhile (f : Char → Bool) (s : Stream) :
    (skipWhile f).run s = (.ok (), s.skipWhile f) := rfl
@[simp] theorem run_skipToNewline (s : Stream) :
    skipToNewline.run s = (.ok (), s.skipToNewline) := rfl
@[simp] theorem run_advance (n : Nat) (s : Stream) : (advance n).run s = (.ok (), s.advance n) :=
  rfl
@[simp] theorem run_fatalHere (kind : ErrKind) (s : Stream) :
    (fatalHere kind : Parser α).run s = (.error (.fatal ⟨s.getPos, s.getPos⟩ kind), s) := rfl
@[simp] theorem run_fatalFrom (start : Nat × Nat) (kind : ErrKind) (s : Stream) :
    (fatalFrom start kind : Parser α).run s = (.error (.fatal ⟨start, s.getPos⟩ kind), s) := rfl

/-! ## Consuming parsers -/

/-- On success, `p` consumed at least one character. -/
def Consumes (p : Parser α) : Prop :=
  ∀ s a s', p.run s = (.ok a, s') → s'.rest.length < s.rest.length

theorem Consumes.bind_left {p : Parser α} (hp : p.Consumes) (f : α → Parser β) :
    (p >>= f).Consumes := by
  intro s b s' h
  obtain ⟨a, s₁, h1, h2⟩ := run_bind_eq_ok.mp h
  exact Nat.lt_of_le_of_lt (length_le_of_run h2) (hp _ _ _ h1)

theorem Consumes.bind_right (p : Parser α) {f : α → Parser β} (hf : ∀ a, (f a).Consumes) :
    (p >>= f).Consumes := by
  intro s b s' h
  obtain ⟨a, s₁, h1, h2⟩ := run_bind_eq_ok.mp h
  exact Nat.lt_of_lt_of_le (hf a _ _ _ h2) (length_le_of_run h1)

/-- `maybe p` returns `some` only after `p` succeeded, so only after consuming. -/
theorem Consumes.maybe_some {p : Parser α} (hp : p.Consumes) {s s' : Stream} {a : α}
    (h : (maybe p).run s = (.ok (some a), s')) : s'.rest.length < s.rest.length := by
  rw [run_maybe] at h
  revert h
  cases hp' : p.run s with
  | mk r s₁ =>
    cases r with
    | ok x => intro h; cases h; exact hp _ _ _ hp'
    | error e => cases e <;> intro h <;> cases h

/-! ## Loops -/

/-- The result of one iteration of a loop: stop with a result, or continue with a new loop
state (the mutable variables of the Rust loop). -/
inductive Step (σ β : Type) where
  | done (b : β)
  | next (st : σ)
  deriving DecidableEq, Repr

/-- Every iteration that continues has consumed input. -/
def Progressive (body : σ → Parser (Step σ β)) : Prop :=
  ∀ st s st' s', (body st).run s = (.ok (.next st'), s') → s'.rest.length < s.rest.length

/-- The loop, iterating `body` at most `fuel` times. Only `loop` uses it, with enough fuel. -/
def loopFuel (body : σ → Parser (Step σ β)) : Nat → σ → Stream → Parsed β × Stream
  | 0, _, s => (.error .reject, s)
  | n + 1, st, s =>
    match (body st).run s with
    | (.ok (.done b), s') => (.ok b, s')
    | (.ok (.next st'), s') => loopFuel body n st' s'
    | (.error e, s') => (.error e, s')

theorem loopFuel_reaches (body : σ → Parser (Step σ β)) :
    ∀ (n : Nat) (st : σ) (s : Stream), Reaches s (loopFuel body n st s).2
  | 0, _, s => .refl s
  | n + 1, st, s => by
    have h := (body st).reaches s
    simp only [loopFuel]
    revert h
    cases (body st).run s with
    | mk r s' =>
      cases r with
      | error e => exact id
      | ok r =>
        cases r with
        | done b => exact id
        | next st' => exact fun h => h.trans (loopFuel_reaches body n st' s')

/-- Any fuel above the length of the input gives the same result. -/
theorem loopFuel_eq {body : σ → Parser (Step σ β)} (hb : Progressive body) :
    ∀ (n m : Nat) (st : σ) (s : Stream), s.rest.length < n → s.rest.length < m →
      loopFuel body n st s = loopFuel body m st s
  | 0, _, _, _, hn, _ => absurd hn (Nat.not_lt_zero _)
  | _ + 1, 0, _, _, _, hm => absurd hm (Nat.not_lt_zero _)
  | n + 1, m + 1, st, s, hn, hm => by
    have hprog := hb st s
    simp only [loopFuel]
    revert hprog
    cases (body st).run s with
    | mk r s' =>
      cases r with
      | error e => intro _; rfl
      | ok r =>
        cases r with
        | done b => intro _; rfl
        | next st' =>
          intro hprog
          have := hprog st' s' rfl
          exact loopFuel_eq hb n m st' s' (by omega) (by omega)

/-- A Rust `loop`/`while` over the stream: iterate `body` from the loop state `st` until it
returns `done` or fails. The definition recurses structurally on a fuel of `rest.length + 1`
iterations; `_hb` (every continuing iteration consumes) makes that fuel sufficient, so that
`loop_run`, the fuel-free unfolding equation, holds. -/
def loop (body : σ → Parser (Step σ β)) (_hb : Progressive body) (st : σ) : Parser β where
  run s := loopFuel body (s.rest.length + 1) st s
  reaches s := loopFuel_reaches body _ st s

/-- The unfolding equation of `loop`: one iteration, then the loop again. -/
theorem loop_run (body : σ → Parser (Step σ β)) (hb : Progressive body) (st : σ) (s : Stream) :
    (loop body hb st).run s =
      match (body st).run s with
      | (.ok (.done b), s') => (.ok b, s')
      | (.ok (.next st'), s') => (loop body hb st').run s'
      | (.error e, s') => (.error e, s') := by
  show loopFuel body (s.rest.length + 1) st s = _
  simp only [loopFuel]
  have hprog := hb st s
  revert hprog
  cases (body st).run s with
  | mk r s' =>
    cases r with
    | error e => intro _; rfl
    | ok r =>
      cases r with
      | done b => intro _; rfl
      | next st' =>
        intro hprog
        have := hprog st' s' rfl
        exact loopFuel_eq hb _ _ st' s' (by omega) (by omega)

/-- Induction principle for `loop`: a property `R` of the final result follows from a loop
invariant `Inv`. -/
theorem loop_invariant {body : σ → Parser (Step σ β)} (hb : Progressive body)
    (Inv : σ → Prop) (R : Parsed β → Stream → Prop)
    (hnext : ∀ st s st' s', Inv st → (body st).run s = (.ok (.next st'), s') → Inv st')
    (hdone : ∀ st s b s', Inv st → (body st).run s = (.ok (.done b), s') → R (.ok b) s')
    (herr : ∀ st s e s', Inv st → (body st).run s = (.error e, s') → R (.error e) s') :
    ∀ (st : σ) (s : Stream), Inv st → R ((loop body hb st).run s).1 ((loop body hb st).run s).2 := by
  intro st s
  induction h : s.rest.length using Nat.strongRecOn generalizing st s with
  | _ n ih =>
    intro hinv
    rw [loop_run]
    have hn := hnext st s
    have hd := hdone st s
    have he := herr st s
    have hprog := hb st s
    revert hn hd he hprog
    cases (body st).run s with
    | mk r s' =>
      cases r with
      | error e => intro _ _ he _; exact he e s' hinv rfl
      | ok r =>
        cases r with
        | done b => intro _ hd _ _; exact hd b s' hinv rfl
        | next st' =>
          intro hn _ _ hprog
          have hlt := hprog st' s' rfl
          exact ih _ (h ▸ hlt) st' s' rfl (hn st' s' hinv rfl)

/-! ## `while let Some(a) = maybe(q)? { ... }` -/

/-- One iteration of `whileMaybe`. -/
def whileMaybeBody (q : Parser γ) (k : σ → γ → Parser (Step σ β)) (finish : σ → β) (st : σ) :
    Parser (Step σ β) := do
  match ← maybe q with
  | none => pure (.done (finish st))
  | some a => k st a

theorem whileMaybeBody_progressive {q : Parser γ} (hq : q.Consumes)
    (k : σ → γ → Parser (Step σ β)) (finish : σ → β) :
    Progressive (whileMaybeBody q k finish) := by
  intro st s st' s' h
  obtain ⟨a?, s₁, h1, h2⟩ := run_bind_eq_ok.mp h
  cases a? with
  | none => cases h2
  | some a => exact Nat.lt_of_le_of_lt (length_le_of_run h2) (hq.maybe_some h1)

/-- The Rust loop `while let Some(a) = maybe(q)? { body }` (and `while is_syntax(c)? {..}`)
with loop state `st`: `k st a` is the body, which may continue (`next`), return early
(`done`), or fail; `finish st` is the result when `q` rejects. -/
def whileMaybe (q : Parser γ) (hq : q.Consumes) (k : σ → γ → Parser (Step σ β))
    (finish : σ → β) (st : σ) : Parser β :=
  loop (whileMaybeBody q k finish) (whileMaybeBody_progressive hq k finish) st

end Parser

end SudoersSpec.Syntax
