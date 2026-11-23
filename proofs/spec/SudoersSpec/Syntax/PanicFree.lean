import SudoersSpec.Syntax.Sudo

/-!
# PT1 for the reference parser: towards `parseSudoersWith` never returning the panic record

`parseSudoersWith` turns the model's record of a Rust panic into `.error`:

```
if items.any (fun i => match i with | .error (.fatal _ .unwrapNone) => true | _ => false)
then .error ErrKind.unwrapNone.render else .ok items
```

so "the result is total" is "no item carries that marker". The marker is produced at exactly one
place: `Command.construct`, when the token text consists of whitespace only (`splitWhitespace` is
empty) — `cmd_iter.next().unwrap()` — reached only through `token (commandToken O)` and
`token (metaToken O.char (commandToken O))`.

This file provides the ingredients of the argument; what is missing is the `token` step that
combines them (the head of the `whileMaybe` accumulation) and the composition of `MarkerFree`
through the productions of `ast.rs`/`Sudo`. The all-production claim is composed elsewhere (from
the extracted `ok` proof and the fact that the error kind relation has no `.unwrapNone`
constructor), which is stronger than a claim about the outer marker alone.

1. `MarkerFree` is about the *outer result* of a parser: it says the result is never the marker.
   `MarkerFree.bind`, `.maybe`, `.lift` and `.loop` carry this absence from the parts to the
   composite's outer result (`?` propagates an error, `maybe` recovers only `Reject`, a loop
   returns an iteration's result). `MarkerFree.observe` holds for **every** `p`, because
   `observe` wraps the inner result in `.ok`: it is a fact about the shape of the outer result,
   **not** a non-suppression statement — an observer that discards the result it observed can
   hide a marker, and this family of lemmas says nothing about provenance. (In this parser
   `observe` is used where the inner `Parsed` is kept — `parseLinesItem` pushes it into the item
   list — and where it is discarded — the `RunAs` user list, the `#` branch of `Sudo::parse`,
   the optional comment of `parseLines`; those discarding sites contain no command token, but
   that composition is not given here.)
2. `CharLaws`: the character-oracle laws the last step needs.
3. `splitWhen`/`splitWhitespace`: a token text whose first character is not whitespace is never
   split into no words.
4. `SimpleCommand_construct_ne_unwrap`, `Command_construct_ne_unwrap_of_head`: the constructors
   return ordinary results (no marker), the second when the text has a non-whitespace head — so
   `cmd_iter.next().unwrap()` finds a word.
5. `metaCommand_first_not_ws`, `commandToken_first_not_ws`: the first character produced by
   `accept_escaped` on a cursor with no leading `\` is not whitespace (the escape branch, the
   only other source, needs a leading `\`).

The statement is `result totality in the model`: the model represents the one Rust panic of the
parser as an error value, so proving `.error` is never returned would be the model-level
panic-freedom claim; it is not a statement about other Rust panics (the model has none: the
settings checkers are panic-free, integers are `Nat`).

Core parser statements are unchanged; this file only adds lemmas about them.
-/

namespace SudoersSpec.Syntax

open Parser

/-! ## The marker -/

/-- The model's record of the panic of `Command::construct`; exactly the item that
`parseSudoersWith` turns into `.error`. -/
def markerItem : Parsed α → Bool
  | .error (.fatal _ .unwrapNone) => true
  | _ => false

@[simp] theorem markerItem_ok (x : α) : markerItem (.ok x : Parsed α) = false := rfl

@[simp] theorem markerItem_reject : markerItem (.error .reject : Parsed α) = false := rfl

theorem markerItem_fatal_ne {sp : Span} {k : ErrKind} (hk : k ≠ .unwrapNone) :
    markerItem (.error (.fatal sp k) : Parsed α) = false := by
  cases k <;> first | exact absurd rfl hk | rfl

theorem markerItem_fatal_eq {sp : Span} {k : ErrKind} (hk : k = .unwrapNone) :
    markerItem (.error (.fatal sp k) : Parsed α) = true := by
  subst hk; rfl

/-- No run of `p` produces the marker. -/
def MarkerFree (p : Parser α) : Prop := ∀ s, markerItem (p.run s).1 = false

theorem MarkerFree.at {p : Parser α} (hp : MarkerFree p) {s r s'} (h : p.run s = (r, s')) :
    markerItem r = false := by
  have h' := hp s
  rw [h] at h'
  exact h'

theorem MarkerFree.elim {p : Parser α} (hp : MarkerFree p) {s r s'} (h : p.run s = (r, s'))
    (hm : markerItem r = true) : False := by
  rw [hp.at h] at hm
  simp at hm

/-! ## Generic combinators: absence at the outer result -/

theorem MarkerFree.pure (a : α) : MarkerFree (pure a : Parser α) := by
  intro s
  simp only [Parser.run_pure, markerItem_ok]

theorem MarkerFree.fail {e : Status} (he : markerItem (.error e : Parsed α) = false) :
    MarkerFree (fail e : Parser α) := by
  intro s
  simp only [Parser.run_fail]
  exact he

theorem MarkerFree.reject : MarkerFree (reject : Parser α) := by
  intro s
  simp only [Parser.run_reject, markerItem_reject]

theorem MarkerFree.lift {r : Parsed α} (hr : markerItem r = false) :
    MarkerFree (lift r : Parser α) := by
  intro s
  simp only [Parser.run_lift]
  exact hr

/-- `observe` keeps the result as a value, so its own result is always `Ok` — for **any** `p`,
including one that can produce a marker. This is a fact about the outer result's shape, not a
non-suppression property: a caller that discards the observed value loses that information. -/
theorem MarkerFree.observe (p : Parser α) : MarkerFree (observe p) := by
  intro s
  simp only [Parser.run_observe, markerItem_ok]

/-- `?` propagates a marker. -/
theorem MarkerFree.bind {p : Parser α} {f : α → Parser β} (hp : MarkerFree p)
    (hf : ∀ a, MarkerFree (f a)) : MarkerFree (p >>= f) := by
  intro s
  rw [Parser.run_bind]
  cases hr : p.run s with
  | mk r₁ s₁ =>
    cases r₁ with
    | ok a => exact hf a s₁
    | error e =>
      have h0 := hp.at hr
      cases e with
      | reject => rfl
      | fatal sp k => exact markerItem_fatal_ne (by intro hk; rw [hk] at h0; simp [markerItem] at h0)

/-- `maybe` recovers only `Reject`: a marker passes through. -/
theorem MarkerFree.maybe {p : Parser α} (hp : MarkerFree p) : MarkerFree (Parser.maybe p) := by
  intro s
  rw [Parser.run_maybe]
  cases hr : p.run s with
  | mk r₁ s₁ =>
    cases r₁ with
    | ok x => rfl
    | error e =>
      cases e with
      | reject => rfl
      | fatal sp k =>
        have h0 := hp.at hr
        exact markerItem_fatal_ne (by intro hk; rw [hk] at h0; simp [markerItem] at h0)

theorem MarkerFree.fatalHere {k : ErrKind} (hk : k ≠ .unwrapNone) :
    MarkerFree (fatalHere k : Parser α) := by
  intro s
  simp only [Parser.run_fatalHere]
  exact markerItem_fatal_ne hk

theorem MarkerFree.fatalFrom {k : ErrKind} (hk : k ≠ .unwrapNone) (p : Nat × Nat) :
    MarkerFree (fatalFrom p k : Parser α) := by
  intro s
  simp only [Parser.run_fatalFrom]
  exact markerItem_fatal_ne hk

/-! ## Primitives that always succeed -/

theorem MarkerFree.getPos : MarkerFree (getPos : Parser (Nat × Nat)) := by
  intro s; simp only [Parser.run_getPos, markerItem_ok]

theorem MarkerFree.peek : MarkerFree (peek : Parser (Option Char)) := by
  intro s; simp only [Parser.run_peek, markerItem_ok]

theorem MarkerFree.getStream : MarkerFree (getStream : Parser Stream) := by
  intro s; simp only [Parser.run_getStream, markerItem_ok]

theorem MarkerFree.nextIf (f : Char → Bool) : MarkerFree (nextIf f) := by
  intro s; simp only [Parser.run_nextIf, markerItem_ok]

theorem MarkerFree.eatChar (c : Char) : MarkerFree (eatChar c) := by
  intro s; simp only [Parser.run_eatChar, markerItem_ok]

theorem MarkerFree.skipWhile (f : Char → Bool) : MarkerFree (skipWhile f) := by
  intro s; simp only [Parser.run_skipWhile, markerItem_ok]

theorem MarkerFree.skipToNewline : MarkerFree (skipToNewline : Parser Unit) := by
  intro s; simp only [Parser.run_skipToNewline, markerItem_ok]

theorem MarkerFree.advance (n : Nat) : MarkerFree (advance n : Parser Unit) := by
  intro s; simp only [Parser.run_advance, markerItem_ok]

/-- The quoted-user nested parse returns its result as a value. -/
theorem MarkerFree.nested (p : Parser α) (s₀ : Stream) : MarkerFree (nested p s₀) := by
  intro s; simp only [Parser.run_nested, markerItem_ok]

theorem MarkerFree.anchored {f : (s₀ : Stream) → AParser s₀ α}
    (hf : ∀ s₀ s, markerItem ((f s₀).run s).1 = false) : MarkerFree (Parser.anchored f) := by
  intro s; simp only [Parser.run_anchored]; exact hf s s

/-- A marker produced in any iteration of a `loop` is the loop's result (`Reject` at fuel 0 is
unreachable, `loopFuel_eq`). -/
theorem MarkerFree.loop {body : σ → Parser (Step σ β)} {hb : Progressive body}
    (hbody : ∀ st, MarkerFree (body st)) (st : σ) : MarkerFree (loop body hb st) := by
  intro s
  exact loop_invariant hb (fun _ => True) (fun r _ => markerItem r = false)
    (fun _ _ _ _ _ _ => trivial)
    (fun st s b s' _ hb' => by simp only [markerItem_ok])
    (fun st s e s' _ hb' =>
      have h0 := MarkerFree.at (hbody st) hb'
      by
        cases e with
        | reject => rfl
        | fatal sp k =>
          exact markerItem_fatal_ne (by intro hk; rw [hk] at h0; simp [markerItem] at h0))
    st s trivial

/-! ## Character-oracle laws -/

/-- The laws about the character classes the last step needs: `/`, `s` and `l` are not
whitespace, and no character with `char::is_uppercase` is. They hold for Rust's `char`
predicates (`/`, `s`, `l` are not `White_Space`; the `Uppercase` property and `White_Space` are
disjoint). `CharOracle.latin1` satisfies them by `decide`. -/
structure CharLaws (O : CharOracle) : Prop where
  slash : O.isWhitespace '/' = false
  ess : O.isWhitespace 's' = false
  ell : O.isWhitespace 'l' = false
  upper : ∀ c, O.isUppercase c = true → O.isWhitespace c = false

/-- `SimpleCommand::accept_1st` accepts only `/`, `s`, `l`, none of which is whitespace. -/
theorem not_ws_of_simpleCommand_accept1st (h : CharLaws O) {c : Char}
    (hc : SimpleCommand.accept1st c = true) : O.isWhitespace c = false := by
  by_cases h1 : (c == '/') = true
  · rw [beq_iff_eq] at h1; rw [h1]; exact h.slash
  by_cases h2 : (c == 's') = true
  · rw [beq_iff_eq] at h2; rw [h2]; exact h.ess
  by_cases h3 : (c == 'l') = true
  · rw [beq_iff_eq] at h3; rw [h3]; exact h.ell
  · exfalso
    simp only [SimpleCommand.accept1st] at hc
    simp [h1, h2, h3] at hc

/-- The first character of a `Meta<Command>` token (`accept_1st` or `isUppercase`) is not
whitespace. -/
theorem not_ws_of_meta_accept1st (h : CharLaws O) {c : Char}
    (hc : (SimpleCommand.accept1st c || O.isUppercase c) = true) : O.isWhitespace c = false := by
  by_cases hu : O.isUppercase c = true
  · exact h.upper c hu
  · simp only [Bool.not_eq_true] at hu
    simp only [hu, Bool.or_false] at hc
    exact not_ws_of_simpleCommand_accept1st h hc

/-! ## `split_whitespace`: a token text with a non-whitespace head has a word -/

theorem splitWhen_ne_nil (p : Char → Bool) (l : List Char) : splitWhen p l ≠ [] := by
  cases l with
  | nil => simp [splitWhen]
  | cons c cs =>
    rw [splitWhen]
    split
    · simp
    · cases splitWhen p cs with
      | nil => simp
      | cons w ws => simp

/-- `str::split_whitespace` is non-empty when the head character is not whitespace: hence
`Command::construct` finds a word and does not panic. -/
theorem splitWhitespace_ne_nil {O : CharOracle} {c : Char} {cs : List Char}
    (h : O.isWhitespace c = false) : splitWhitespace O (c :: cs) ≠ [] := by
  unfold splitWhitespace
  rw [splitWhen]
  simp only [h, Bool.false_eq_true, ite_false]
  cases hsp : splitWhen O.isWhitespace cs with
  | nil => simp
  | cons w ws => simp

/-! ## The panic site is out of reach for a non-whitespace command text -/

/-- `eatChar` on a cursor whose next character is not `c`. -/
theorem eatChar_run_false {c : Char} {s : Stream} (hs : s.peek ≠ some c) :
    (eatChar c).run s = (.ok false, s) := by
  have h : s.eatChar c = (false, s) := by
    rw [Stream.eatChar_eq, if_neg hs]
  rw [Parser.run_eatChar, h]

/-- The else branch of `accept_escaped` (`nextIf pred`, then `Reject`). -/
theorem nextIf_branch_pred {pred : Char → Bool} {s s' : Stream} {c : Char}
    (h : ((nextIf pred) >>= fun o => match o with
        | some c => pure c
        | none => (reject : Parser Char)).run s = (.ok c, s')) : pred c = true := by
  rw [Parser.run_bind] at h
  cases hr : s.rest with
  | nil =>
    simp only [Parser.run_nextIf, Stream.nextIf, hr] at h
    simp [Parser.run_reject] at h
  | cons d ds =>
    simp only [Parser.run_nextIf, Stream.nextIf, hr] at h
    by_cases hd : pred d = true
    · simp only [hd, ite_true, Parser.run_pure, Prod.mk.injEq, Except.ok.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact hd
    · simp only [hd, Bool.false_eq_true, ite_false] at h
      simp [Parser.run_reject] at h

/-- A token cursor with no leading `\` cannot take the escape branch of `accept_escaped`, so the
character it produces satisfies `pred`. -/
theorem acceptEscaped_pred_of_no_escape {T : TokenSpec α} {pred : Char → Bool} {s s' : Stream}
    {c : Char} (hs : s.peek ≠ some '\\')
    (h : (acceptEscaped T pred).run s = (.ok c, s')) : pred c = true := by
  rw [acceptEscaped, Parser.run_bind] at h
  have hg : ((if T.allowEscape then eatChar '\\' else (pure false : Parser Bool))).run s
      = (.ok false, s) := by
    by_cases hA : T.allowEscape = true
    · rw [if_pos hA]; exact eatChar_run_false hs
    · rw [if_neg hA]; rfl
  rw [hg] at h
  simp only [] at h
  simp only [Bool.false_eq_true, ite_false] at h
  exact nextIf_branch_pred h

/-- First character of a `Meta<Command>` token from a cursor with no leading escape: not
whitespace. -/
theorem metaCommand_first_not_ws {O : Oracles} (hL : CharLaws O.char) {s s' : Stream} {c : Char}
    (hs : s.peek ≠ some '\\')
    (h : (acceptEscaped (metaToken O.char (commandToken O))
          (metaToken O.char (commandToken O)).accept1st).run s = (.ok c, s')) :
    O.char.isWhitespace c = false :=
  not_ws_of_meta_accept1st hL (acceptEscaped_pred_of_no_escape hs h)

/-- First character of a `Command` token from a cursor with no leading escape: not whitespace. -/
theorem commandToken_first_not_ws {O : Oracles} (hL : CharLaws O.char) {s s' : Stream} {c : Char}
    (hs : s.peek ≠ some '\\')
    (h : (acceptEscaped (commandToken O) SimpleCommand.accept1st).run s = (.ok c, s')) :
    O.char.isWhitespace c = false :=
  not_ws_of_simpleCommand_accept1st hL (acceptEscaped_pred_of_no_escape hs h)

/-! ## The constructors return ordinary results -/

/-- `glob::Pattern::new` errors are never the panic marker. -/
theorem SimpleCommand_compile_ne_unwrap (O : Oracles) (cmd : List Char) :
    SimpleCommand.compile O cmd ≠ .error .unwrapNone := by
  intro h
  rw [SimpleCommand.compile] at h
  cases hg : O.glob.compile (String.ofList cmd) with
  | none => rw [hg] at h; simp at h
  | some e => rw [hg] at h; simp at h

/-- The canonicalize-and-compile tail of `SimpleCommand::construct`. -/
theorem SimpleCommand_tail_ne_unwrap (O : Oracles) (cmd : List Char) (isDir : Bool) :
    (match (match O.fs.canonicalize (String.ofList (if isDir then cmd.dropLast else cmd)) with
      | .ok real => Except.ok real.toList
      | .okNonUtf8 => Except.error ErrKind.nonUtf8Filesystem
      | .err => Except.ok (if isDir then cmd.dropLast else cmd)) with
     | .error e => Except.error e
     | .ok c => SimpleCommand.compile O (if isDir then c ++ "/*".toList else c)) ≠
    .error .unwrapNone := by
  cases hg : O.fs.canonicalize (String.ofList (if isDir then cmd.dropLast else cmd)) with
  | ok real => simp only []; exact SimpleCommand_compile_ne_unwrap O _
  | okNonUtf8 => simp only []; simp
  | err => simp only []; exact SimpleCommand_compile_ne_unwrap O _

/-- `SimpleCommand::construct` returns an ordinary result, never the panic marker. -/
theorem SimpleCommand_construct_ne_unwrap {O : Oracles} (cmd : List Char) :
    SimpleCommand.construct O cmd ≠ .error .unwrapNone := by
  intro h
  rw [SimpleCommand.construct] at h
  simp only [] at h
  split at h
  · exact SimpleCommand_compile_ne_unwrap O cmd h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · exact SimpleCommand_tail_ne_unwrap O cmd _ h

/-- `Command::argPattern` errors are never the panic marker. -/
theorem Command_argPattern_ne_unwrap (args : List (List Char)) :
    Command.argPattern args ≠ .error .unwrapNone := by
  intro h
  rw [Command.argPattern] at h
  simp only [] at h
  repeat' split at h
  all_goals simp at h

/-- The word-and-arguments tail of `Command::construct`. -/
theorem Command_head_ne_unwrap {O : Oracles} {cmd : List Char} {args : List (List Char)} :
    (match SimpleCommand.construct O cmd with
     | .error e => Except.error e
     | .ok command =>
       match Command.argPattern args with
       | .error e => Except.error e
       | .ok argpat =>
         if command == "list" && argpat != Args.prefix [] then
           Except.error ErrKind.listTakesNoArguments
         else Except.ok ({ pattern := command, args := argpat } : Command)) ≠ .error .unwrapNone := by
  cases hs : SimpleCommand.construct O cmd with
  | error e =>
    simp only []
    intro hh
    exact SimpleCommand_construct_ne_unwrap cmd (by rw [hs]; simpa using hh)
  | ok command =>
    simp only []
    cases ha : Command.argPattern args with
    | error e =>
      simp only []
      intro hh
      exact Command_argPattern_ne_unwrap args (by rw [ha]; simpa using hh)
    | ok argpat => simp only []; split <;> simp

/-- `Command::construct` finds a word when the text has a non-whitespace first character, so
`cmd_iter.next().unwrap()` cannot panic. -/
theorem Command_construct_ne_unwrap_of_head {O : Oracles} {c : Char} {cs : List Char}
    (hws : O.char.isWhitespace c = false) :
    Command.construct O (c :: cs) ≠ .error .unwrapNone := by
  intro h
  have hne : splitWhitespace O.char (c :: cs) ≠ [] := splitWhitespace_ne_nil hws
  rw [Command.construct] at h
  cases hsp : splitWhitespace O.char (c :: cs) with
  | nil => exact hne hsp
  | cons cmd args =>
    rw [hsp] at h
    exact Command_head_ne_unwrap h

end SudoersSpec.Syntax
