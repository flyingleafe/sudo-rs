import SudoersSpec.Ast

/-!
# `char_stream.rs`: the character stream

`CharStream` is a `Peekable<Chars>` with a line and a column. Here the iterator is the list of
the characters not yet read (`rest`); line and column are `Nat` (Rust `usize`: overflow is a
precondition of the refinement proof, not modelled here).

Every way the parser moves the stream goes through `next_if`, so the position of a stream
is always the position reached by reading the consumed characters (`Stream.Reaches`,
`Reaches.getPos_eq`).
-/

namespace SudoersSpec.Syntax

/-- `char_stream.rs` `CharStream`: the characters not read yet, the current line and column
(both start at 1). `#[derive(Clone)]` in Rust; a Lean value is copied freely. -/
structure Stream where
  rest : List Char
  line : Nat
  col : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The position after reading `c` at `pos`: the bookkeeping of `CharStream::next_if`. A
newline moves to column 1 of the next line, every other character to the next column. -/
def stepPos (c : Char) (pos : Nat × Nat) : Nat × Nat :=
  if c = '\n' then (pos.1 + 1, 1) else (pos.1, pos.2 + 1)

/-- The position after reading the characters `cs` from `pos`. -/
def posAfter : List Char → Nat × Nat → Nat × Nat
  | [], pos => pos
  | c :: cs, pos => posAfter cs (stepPos c pos)

namespace Stream

/-- `CharStream::new_with_pos`. -/
def newWithPos (src : List Char) (pos : Nat × Nat) : Stream :=
  ⟨src, pos.1, pos.2⟩

/-- `CharStream::new`: a stream at line 1, column 1. -/
def new (src : List Char) : Stream :=
  newWithPos src (1, 1)

/-- `CharStream::new` on the characters of a string (`src.chars()`). -/
def ofString (src : String) : Stream :=
  new src.toList

/-- `CharStream::get_pos`: `(line, col)`. -/
def getPos (s : Stream) : Nat × Nat :=
  (s.line, s.col)

/-- `CharStream::peek`. -/
def peek (s : Stream) : Option Char :=
  s.rest.head?

/-- The stream after `next_if` accepted the head character: the character is dropped and
the position moves by `stepPos`. On an empty stream nothing changes. Lean-only helper. -/
def pop : Stream → Stream
  | ⟨c :: cs, line, col⟩ => ⟨cs, (stepPos c (line, col)).1, (stepPos c (line, col)).2⟩
  | s@⟨[], _, _⟩ => s

/-- `CharStream::next_if`: consume the next character if `f` accepts it. -/
def nextIf (f : Char → Bool) (s : Stream) : Option Char × Stream :=
  match s.rest with
  | c :: _ => if f c then (some c, s.pop) else (none, s)
  | [] => (none, s)

/-- `CharStream::eat_char`: `next_if(|c| c == expect_char).is_some()`. -/
def eatChar (expectChar : Char) (s : Stream) : Bool × Stream :=
  let (r, s') := s.nextIf (fun c => c == expectChar)
  (r.isSome, s')

/-- `CharStream::advance`: `for _ in 0..n { self.next_if(|_| true); }`. -/
def advance (s : Stream) : Nat → Stream
  | 0 => s
  | n + 1 => (s.nextIf (fun _ => true)).2.advance n

/-- The loop `while stream.next_if(f).is_some() {}`, with the list `fuel` (always the `rest`
of the stream it is called on, see `skipWhile`) as structural measure. -/
def skipWhileFuel (f : Char → Bool) : List Char → Stream → Stream
  | [], s => s
  | _ :: fuel, s =>
    match s.nextIf f with
    | (some _, s') => skipWhileFuel f fuel s'
    | (none, s') => s'

/-- `while stream.next_if(f).is_some() {}`: the loop of `skip_to_newline` and of
`LeadingWhitespace::parse`. The loop form is `skipWhile_eq`. -/
def skipWhile (f : Char → Bool) (s : Stream) : Stream :=
  skipWhileFuel f s.rest s

/-- `CharStream::skip_to_newline`: `while self.next_if(|c| c != '\n').is_some() {}`. The
newline itself is not consumed. -/
def skipToNewline (s : Stream) : Stream :=
  skipWhile (fun c => c != '\n') s

/-- `s'` is `s` advanced over some characters: `s' = s.advance n` for some `n`. Every parser
of this development maps its input stream to a stream it reaches (`Parser.reaches`). -/
def Reaches (s s' : Stream) : Prop :=
  ∃ n, s.advance n = s'

/-! ## Lemmas: single steps -/

@[simp] theorem getPos_mk (rest line col) : getPos ⟨rest, line, col⟩ = (line, col) := rfl

@[simp] theorem peek_mk (rest line col) : peek ⟨rest, line, col⟩ = rest.head? := rfl

@[simp] theorem pop_cons (c : Char) (cs line col) :
    pop ⟨c :: cs, line, col⟩ = ⟨cs, (stepPos c (line, col)).1, (stepPos c (line, col)).2⟩ :=
  rfl

@[simp] theorem pop_nil (line col) : pop ⟨[], line, col⟩ = ⟨[], line, col⟩ := rfl

@[simp] theorem pop_rest (s : Stream) : s.pop.rest = s.rest.tail := by
  rcases s with ⟨_ | ⟨c, cs⟩, l, k⟩ <;> rfl

theorem pop_getPos_cons {s : Stream} {c cs} (h : s.rest = c :: cs) :
    s.pop.getPos = stepPos c s.getPos := by
  rcases s with ⟨_ | ⟨c', cs'⟩, l, k⟩
  · cases h
  · cases h; rfl

/-- Position bookkeeping of `next_if` on a newline. -/
theorem pop_newline (cs line col) :
    pop ⟨'\n' :: cs, line, col⟩ = ⟨cs, line + 1, 1⟩ := by
  simp [pop, stepPos]

/-- Position bookkeeping of `next_if` on any other character. -/
theorem pop_other {c : Char} (h : c ≠ '\n') (cs line col) :
    pop ⟨c :: cs, line, col⟩ = ⟨cs, line, col + 1⟩ := by
  simp [pop, stepPos, h]

@[simp] theorem nextIf_nil (f : Char → Bool) (line col) :
    nextIf f ⟨[], line, col⟩ = (none, ⟨[], line, col⟩) := rfl

/-- `next_if` on a non-empty stream. -/
theorem nextIf_cons (f : Char → Bool) (c : Char) (cs line col) :
    nextIf f ⟨c :: cs, line, col⟩ =
      if f c then (some c, pop ⟨c :: cs, line, col⟩) else (none, ⟨c :: cs, line, col⟩) := rfl

theorem nextIf_of_rest_cons {f : Char → Bool} {s : Stream} {c cs} (h : s.rest = c :: cs) :
    s.nextIf f = if f c then (some c, s.pop) else (none, s) := by
  simp [nextIf, h]

/-- `next_if` returns `some c` exactly when `c` is the next character and `f` accepts it;
the stream is then `pop`ped. -/
theorem nextIf_eq_some {f : Char → Bool} {s s' : Stream} {c : Char} :
    s.nextIf f = (some c, s') ↔ s.peek = some c ∧ f c = true ∧ s' = s.pop := by
  rcases s with ⟨_ | ⟨d, ds⟩, l, k⟩
  · simp [nextIf]
  · simp only [nextIf, peek, List.head?_cons, Option.some.injEq]
    by_cases hd : f d = true
    · simp only [hd, ite_true, Prod.mk.injEq, Option.some.injEq]
      constructor
      · rintro ⟨rfl, rfl⟩; exact ⟨rfl, hd, rfl⟩
      · rintro ⟨rfl, -, rfl⟩; exact ⟨rfl, rfl⟩
    · simp only [hd, Prod.mk.injEq, reduceCtorEq, false_and, Bool.false_eq_true, ite_false,
        false_iff, not_and]
      rintro rfl h; exact absurd h hd

/-- `next_if` returns `none` exactly when the next character is missing or rejected; the
stream is then unchanged. -/
theorem nextIf_eq_none {f : Char → Bool} {s s' : Stream} :
    s.nextIf f = (none, s') ↔ (∀ c, s.peek = some c → f c = false) ∧ s' = s := by
  rcases s with ⟨_ | ⟨d, ds⟩, l, k⟩
  · simp only [nextIf, Prod.mk.injEq, true_and, peek, List.head?_nil, reduceCtorEq,
      false_implies, implies_true]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  · simp only [nextIf, peek, List.head?_cons, Option.some.injEq, forall_eq']
    by_cases hd : f d = true
    · simp [hd]
    · simp only [Bool.not_eq_true] at hd
      simp only [hd, Bool.false_eq_true, ite_false, Prod.mk.injEq, true_and]
      constructor
      · intro h; subst h; simp
      · intro h; simp_all

theorem nextIf_snd_eq (f : Char → Bool) (s : Stream) :
    (s.nextIf f).2 = s ∨ (s.nextIf f).2 = s.pop := by
  unfold nextIf
  split
  · split <;> simp
  · simp

theorem eatChar_eq (c : Char) (s : Stream) :
    s.eatChar c = if s.peek = some c then (true, s.pop) else (false, s) := by
  rcases s with ⟨_ | ⟨d, ds⟩, l, k⟩
  · simp [eatChar, nextIf]
  · by_cases h : d = c
    · subst h; simp [eatChar, nextIf]
    · simp [eatChar, nextIf, h]

/-- Position bookkeeping of `eat_char`: on success the stream is `pop`ped (`pop_newline`,
`pop_other`). -/
theorem eatChar_true {c : Char} {s s' : Stream} :
    s.eatChar c = (true, s') ↔ s.peek = some c ∧ s' = s.pop := by
  rw [eatChar_eq]
  by_cases h : s.peek = some c
  · simp only [h, ite_true, Prod.mk.injEq, true_and]; exact ⟨fun h => h.symm, fun h => h.symm⟩
  · simp [h]

theorem eatChar_false {c : Char} {s s' : Stream} :
    s.eatChar c = (false, s') ↔ s.peek ≠ some c ∧ s' = s := by
  rw [eatChar_eq]
  by_cases h : s.peek = some c
  · simp [h]
  · simp only [h, ite_false, Prod.mk.injEq, true_and, ne_eq, not_false_eq_true]
    exact ⟨fun h => h.symm, fun h => h.symm⟩

@[simp] theorem nextIf_true_snd (s : Stream) : (s.nextIf (fun _ => true)).2 = s.pop := by
  rcases s with ⟨_ | ⟨d, ds⟩, l, k⟩ <;> rfl

/-! ## Lemmas: `advance` and `Reaches` -/

@[simp] theorem advance_zero (s : Stream) : s.advance 0 = s := rfl

theorem advance_succ (s : Stream) (n : Nat) : s.advance (n + 1) = s.pop.advance n := by
  simp [advance]

theorem advance_succ' (s : Stream) (n : Nat) : s.advance (n + 1) = (s.advance n).pop := by
  induction n generalizing s with
  | zero => simp [advance_succ]
  | succ n ih => rw [advance_succ, ih, advance_succ]

theorem advance_add (s : Stream) (n m : Nat) : (s.advance n).advance m = s.advance (n + m) := by
  induction n generalizing s with
  | zero => simp
  | succ n ih => rw [advance_succ, ih, Nat.add_right_comm, advance_succ]

@[simp] theorem advance_rest (s : Stream) (n : Nat) : (s.advance n).rest = s.rest.drop n := by
  induction n generalizing s with
  | zero => simp
  | succ n ih => rw [advance_succ, ih, pop_rest, List.drop_tail]

theorem pop_eq_advance (s : Stream) : s.pop = s.advance 1 := by
  rw [advance_succ, advance_zero]

/-- Position bookkeeping of `advance`: the position after reading the first `n` characters. -/
theorem advance_getPos (s : Stream) (n : Nat) :
    (s.advance n).getPos = posAfter (s.rest.take n) s.getPos := by
  induction n generalizing s with
  | zero => simp [posAfter]
  | succ n ih =>
    rw [advance_succ, ih]
    rcases s with ⟨_ | ⟨c, cs⟩, l, k⟩
    · simp [posAfter]
    · simp [posAfter, getPos]

@[simp] theorem advance_nil (line col n) : (Stream.mk [] line col).advance n = ⟨[], line, col⟩ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [advance_succ]; exact ih

/-- Advancing past the end changes nothing more. -/
theorem advance_of_length_le {s : Stream} {n : Nat} (h : s.rest.length ≤ n) :
    s.advance n = s.advance s.rest.length := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [← advance_add]
  rcases hs : s.advance s.rest.length with ⟨r, l, c⟩
  have : r = [] := by
    have := congrArg Stream.rest hs; simp at this; exact this
  subst this; simp

@[simp] theorem Reaches.refl (s : Stream) : Reaches s s := ⟨0, rfl⟩

theorem Reaches.trans {s₁ s₂ s₃ : Stream} : Reaches s₁ s₂ → Reaches s₂ s₃ → Reaches s₁ s₃ := by
  rintro ⟨n, rfl⟩ ⟨m, rfl⟩; exact ⟨n + m, (advance_add _ _ _).symm⟩

theorem Reaches.pop (s : Stream) : Reaches s s.pop := ⟨1, (pop_eq_advance s).symm⟩

theorem Reaches.advance (s : Stream) (n : Nat) : Reaches s (s.advance n) := ⟨n, rfl⟩

theorem Reaches.nextIf (f : Char → Bool) (s : Stream) : Reaches s (s.nextIf f).2 := by
  rcases nextIf_snd_eq f s with h | h <;> rw [h]
  · exact .refl s
  · exact .pop s

theorem Reaches.eatChar (c : Char) (s : Stream) : Reaches s (s.eatChar c).2 :=
  Reaches.nextIf _ s

/-- The output `rest` of a reached stream is a suffix of the input `rest`. -/
theorem Reaches.suffix {s s' : Stream} : Reaches s s' → s'.rest <:+ s.rest := by
  rintro ⟨n, rfl⟩; simpa using List.drop_suffix n s.rest

theorem Reaches.length_le {s s' : Stream} (h : Reaches s s') : s'.rest.length ≤ s.rest.length :=
  h.suffix.length_le

/-- A reached stream is determined by its length: `s'` is `s` advanced by the number of
characters consumed. -/
theorem Reaches.eq_advance {s s' : Stream} (h : Reaches s s') :
    s' = s.advance (s.rest.length - s'.rest.length) := by
  obtain ⟨n, rfl⟩ := h
  simp only [advance_rest, List.length_drop]
  by_cases hn : n ≤ s.rest.length
  · congr 1; omega
  · rw [advance_of_length_le (by omega : s.rest.length ≤ n)]
    congr 1; omega

/-- A reached stream has the position reached by reading the consumed prefix. -/
theorem Reaches.getPos_eq {s s' : Stream} (h : Reaches s s') :
    s.rest = s.rest.take (s.rest.length - s'.rest.length) ++ s'.rest ∧
      s'.getPos = posAfter (s.rest.take (s.rest.length - s'.rest.length)) s.getPos := by
  have e := h.eq_advance
  generalize s.rest.length - s'.rest.length = k at e ⊢
  have hr : s'.rest = s.rest.drop k := by rw [e, advance_rest]
  refine ⟨?_, ?_⟩
  · rw [hr]; exact (List.take_append_drop _ _).symm
  · rw [e]; exact advance_getPos _ _

/-- A reached stream with the same length is the stream itself. -/
theorem Reaches.eq_of_length_eq {s s' : Stream} (h : Reaches s s')
    (hl : s'.rest.length = s.rest.length) : s' = s := by
  rw [h.eq_advance, hl, Nat.sub_self, advance_zero]

/-! ## Lemmas: `skip_to_newline` -/

theorem skipWhileFuel_eq (f : Char → Bool) (s : Stream) :
    skipWhileFuel f s.rest s = s.advance (s.rest.takeWhile f).length := by
  rcases s with ⟨rest, l, k⟩
  induction rest generalizing l k with
  | nil => simp [skipWhileFuel]
  | cons c cs ih =>
    simp only [skipWhileFuel, nextIf_cons]
    by_cases hc : f c = true
    · simp only [hc, ite_true, List.takeWhile_cons_of_pos, List.length_cons, advance_succ, pop_cons]
      exact ih _ _
    · simp [hc]

/-- Closed form of the loop `while stream.next_if(f).is_some() {}`. -/
theorem skipWhile_eq_advance (f : Char → Bool) (s : Stream) :
    s.skipWhile f = s.advance (s.rest.takeWhile f).length :=
  skipWhileFuel_eq f s

/-- The loop equation of `skipWhile`: one call of `next_if`, then the loop again. -/
theorem skipWhile_eq (f : Char → Bool) (s : Stream) :
    s.skipWhile f =
      match s.nextIf f with
      | (some _, s') => s'.skipWhile f
      | (none, s') => s' := by
  rcases s with ⟨_ | ⟨c, cs⟩, l, k⟩
  · rfl
  · by_cases hc : f c = true
    · simp [skipWhile, skipWhileFuel, nextIf_cons, hc]
    · simp [skipWhile, skipWhileFuel, nextIf_cons, hc]

theorem skipWhile_rest (f : Char → Bool) (s : Stream) :
    (s.skipWhile f).rest = s.rest.dropWhile f := by
  rw [skipWhile_eq_advance, advance_rest]
  induction s.rest with
  | nil => rfl
  | cons c cs ih =>
    by_cases hc : f c = true
    · simp [List.takeWhile_cons_of_pos hc, List.dropWhile_cons_of_pos hc, ih]
    · simp [List.takeWhile_cons_of_neg hc, List.dropWhile_cons_of_neg hc]

theorem Reaches.skipWhile (f : Char → Bool) (s : Stream) : Reaches s (s.skipWhile f) := by
  rw [skipWhile_eq_advance]; exact .advance _ _

/-- `skip_to_newline` stops at the first newline or at the end of the input. -/
theorem skipToNewline_rest (s : Stream) :
    s.skipToNewline.rest = s.rest.dropWhile (fun c => c != '\n') :=
  skipWhile_rest _ _

theorem posAfter_of_no_newline {cs : List Char} (h : ∀ c ∈ cs, c ≠ '\n') (line col : Nat) :
    posAfter cs (line, col) = (line, col + cs.length) := by
  induction cs generalizing col with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.mem_cons, ne_eq, forall_eq_or_imp] at h
    simp only [posAfter, stepPos, h.1, ite_false, List.length_cons]
    rw [ih h.2]; congr 1; omega

theorem take_length_takeWhile (p : α → Bool) (l : List α) :
    l.take (l.takeWhile p).length = l.takeWhile p := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases ha : p a = true
    · simp [List.takeWhile_cons_of_pos ha, ih]
    · simp [List.takeWhile_cons_of_neg ha]

/-- Position bookkeeping of `skip_to_newline`: the line does not change and the column moves
by the number of characters skipped. -/
theorem skipToNewline_getPos (s : Stream) :
    s.skipToNewline.getPos =
      (s.line, s.col + (s.rest.takeWhile (fun c => c != '\n')).length) := by
  rw [skipToNewline, skipWhile_eq_advance, advance_getPos, take_length_takeWhile]
  apply posAfter_of_no_newline
  intro c hc
  have := List.all_eq_true.mp (List.all_takeWhile (p := fun c => c != '\n') (l := s.rest)) c hc
  simpa using this

end Stream

end SudoersSpec.Syntax
