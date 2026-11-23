import SudoersSpec.Syntax.Parser

/-!
# `basic_parser.rs`

The combinators of the legacy parser, one Lean definition per Rust item, in Rust order. Trait
parameters become value parameters: a production `p : Parser α` for `T: Parse`, a string
`description` for `T::DESCRIPTION` (`UserFriendly`, see `AstNames.lean`), a `TokenSpec` for
`T: Token`, a `Many` for `T: Many`.

Every definition is a `Parser`, so its output stream is reached from its input
(`Parser.reaches`, `Parser.suffix`). The facts the loops need are proved here:
`trySyntax_consumes`, `acceptEscaped_consumes`, `token_consumes`, `tryNonterminal_consumes`,
`parseList_consumes`, and the progress of the bodies of `TrailingWhitespace::parse` and
`parse_lines`.
-/

namespace SudoersSpec.Syntax

open Parser
open _root_.SudoersSpec.Syntax.Stream (Reaches)

/-! ## Stream facts used by the progress proofs -/

theorem Stream.pop_length_lt {s : Stream} {c : Char} (h : s.peek = some c) :
    s.pop.rest.length < s.rest.length := by
  rcases s with ⟨_ | ⟨d, ds⟩, l, k⟩
  · cases h
  · simp

theorem run_eatChar_true_lt {c : Char} {s s' : Stream} (h : (eatChar c).run s = (.ok true, s')) :
    s'.rest.length < s.rest.length := by
  simp only [run_eatChar, Prod.mk.injEq, Except.ok.injEq] at h
  obtain ⟨h1, rfl⟩ := h
  have := (Stream.eatChar_true (s := s) (s' := (s.eatChar c).2)).mp (by rw [← h1])
  rw [this.2]; exact Stream.pop_length_lt this.1

theorem run_nextIf_some_lt {f : Char → Bool} {c : Char} {s s' : Stream}
    (h : (nextIf f).run s = (.ok (some c), s')) : s'.rest.length < s.rest.length := by
  simp only [run_nextIf, Prod.mk.injEq, Except.ok.injEq] at h
  obtain ⟨h1, rfl⟩ := h
  have := (Stream.nextIf_eq_some (s := s) (s' := (s.nextIf f).2)).mp (by rw [← h1])
  rw [this.2.2]; exact Stream.pop_length_lt this.1

theorem Stream.skipToNewline_lt {s : Stream} {c : Char} (h : s.peek = some c) (hc : c ≠ '\n') :
    s.skipToNewline.rest.length < s.rest.length := by
  rw [Stream.skipToNewline_rest]
  rcases s with ⟨_ | ⟨d, ds⟩, l, k⟩
  · cases h
  · simp only [Stream.peek_mk, List.head?_cons, Option.some.injEq] at h
    subst h
    have : (d != '\n') = true := by simpa using hc
    show (List.dropWhile _ (d :: ds)).length < (d :: ds).length
    rw [List.dropWhile_cons_of_pos (p := fun c => c != '\n') (a := d) this]
    exact Nat.lt_of_le_of_lt (List.dropWhile_suffix _).length_le (by simp)

/-! ## Whitespace and comments -/

/-- `impl Parse for LeadingWhitespace`: skip `'\t'` and `' '`
(`"\t ".contains(c)`); fail with `"superfluous whitespace"` if nothing follows (this is how the
end of the input is detected). The Rust unit struct `LeadingWhitespace` is `Unit`. -/
def leadingWhitespace : Parser Unit := do
  skipWhile (fun c => c == '\t' || c == ' ')
  if (← peek).isSome then
    pure ()
  else
    fatalHere .superfluousWhitespace

/-- Closed form of `LeadingWhitespace::parse`. -/
theorem leadingWhitespace_run (s : Stream) :
    leadingWhitespace.run s =
      if (s.skipWhile (fun c => c == '\t' || c == ' ')).peek.isSome then
        (.ok (), s.skipWhile (fun c => c == '\t' || c == ' '))
      else
        (.error (.fatal ⟨(s.skipWhile (fun c => c == '\t' || c == ' ')).getPos,
          (s.skipWhile (fun c => c == '\t' || c == ' ')).getPos⟩ .superfluousWhitespace),
          s.skipWhile (fun c => c == '\t' || c == ' ')) := by
  simp only [leadingWhitespace, run_bind, run_skipWhile, run_peek]
  split <;> rfl

/-- One iteration of the loop of `impl Parse for TrailingWhitespace`:
```
let _ = LeadingWhitespace::parse(stream);
if stream.eat_char('\\') {
    if !stream.eat_char('\n') { unrecoverable!(stream, "stray escape sequence") }
} else { break; }
```
-/
def trailingWhitespaceBody (_ : Unit) : Parser (Step Unit Unit) := do
  let _ ← observe leadingWhitespace
  if ← eatChar '\\' then
    if ← eatChar '\n' then
      pure (.next ())
    else
      fatalHere .strayEscapeSequence
  else
    pure (.done ())

theorem trailingWhitespaceBody_progressive : Progressive trailingWhitespaceBody := by
  intro st s st' s' h
  obtain ⟨_, s₁, h₁, h⟩ := run_bind_eq_ok.mp h
  obtain ⟨b, s₂, h₂, h⟩ := run_bind_eq_ok.mp h
  cases b with
  | false => simp at h
  | true =>
    simp only [ite_true] at h
    have l₁ := length_le_of_run h₁
    have l₂ := run_eatChar_true_lt h₂
    have l₃ := length_le_of_run h
    omega

/-- `impl Parse for TrailingWhitespace`: whitespace, and line continuations (`\` newline).
Comments are not part of it, contrary to the Rust doc comment. -/
def trailingWhitespace : Parser Unit :=
  loop trailingWhitespaceBody trailingWhitespaceBody_progressive ()

theorem trailingWhitespaceBody_ne_reject (st : Unit) (s : Stream) :
    ((trailingWhitespaceBody st).run s).1 ≠ .error .reject := by
  intro h
  simp only [trailingWhitespaceBody, run_bind, run_observe, run_eatChar] at h
  repeat' (first | split at h | simp only [run_bind, run_eatChar, run_pure, run_fatalHere] at h)
  all_goals simp at h

/-- `TrailingWhitespace::parse` never rejects (its only error is `stray escape sequence`). -/
theorem trailingWhitespace_ne_reject (s : Stream) :
    (trailingWhitespace.run s).1 ≠ .error .reject :=
  loop_invariant trailingWhitespaceBody_progressive (fun _ => True)
    (fun r _ => r ≠ .error .reject)
    (fun _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ => by simp)
    (fun st s e s' _ h => by
      have := trailingWhitespaceBody_ne_reject st s
      rw [h] at this; simpa using this)
    () s trivial

/-- `impl Parse for Comment`: `#` up to (not including) the end of the line. -/
def comment : Parser Unit := do
  if !(← eatChar '#') then
    reject
  else
    skipToNewline

/-- Closed form of `Comment::parse`. -/
theorem comment_run (s : Stream) :
    comment.run s =
      if s.peek = some '#' then (.ok (), s.pop.skipToNewline) else (.error .reject, s) := by
  simp only [comment, run_bind, run_eatChar, Stream.eatChar_eq]
  split <;> rfl

/-- `skip_trailing_whitespace`. -/
def skipTrailingWhitespace : Parser Unit := do
  let _ ← trailingWhitespace
  pure ()

theorem skipTrailingWhitespace_ne_reject (s : Stream) :
    (skipTrailingWhitespace.run s).1 ≠ .error .reject := by
  have := trailingWhitespace_ne_reject s
  simp only [skipTrailingWhitespace, run_bind]
  revert this
  cases trailingWhitespace.run s with
  | mk r s' => cases r <;> simp

/-! ## Syntax characters -/

/-- `try_syntax`: accept one character and the trailing whitespace; reject (consuming
nothing) if the character is not next. -/
def trySyntax (syntax_ : Char) : Parser Unit := do
  if !(← eatChar syntax_) then
    reject
  else
    skipTrailingWhitespace

/-- `expect_syntax`: `try_syntax`, or the fatal error `"expecting '{syntax}' but found '{str}'"`
at the current position. Any error of `try_syntax` is replaced, including a fatal one from the
trailing whitespace after the character was consumed: `=\x` gives `expecting '=' but found 'x'`
after the backslash, not `stray escape sequence`. -/
def expectSyntax (syntax_ : Char) : Parser Unit := do
  match ← observe (trySyntax syntax_) with
  | .error _ =>
    let found ← peek
    fatalHere (.expectingSyntax syntax_ found)
  | .ok () => pure ()

/-- `is_syntax`: `maybe(try_syntax(syntax, stream))?.is_some()`. -/
def isSyntax (syntax_ : Char) : Parser Bool := do
  let result ← Parser.maybe (trySyntax syntax_)
  pure result.isSome

theorem trySyntax_consumes (syntax_ : Char) : (trySyntax syntax_).Consumes := by
  intro s a s' h
  obtain ⟨b, s₁, h₁, h⟩ := run_bind_eq_ok.mp h
  cases b with
  | false => simp at h
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ite_false] at h
    exact Nat.lt_of_le_of_lt (length_le_of_run h) (run_eatChar_true_lt h₁)

/-- `try_syntax` rejects only without consuming. -/
theorem trySyntax_reject {syntax_ : Char} {s s' : Stream}
    (h : (trySyntax syntax_).run s = (.error .reject, s')) : s' = s := by
  rcases run_bind_eq_error.mp h with h | ⟨b, s₁, h₁, h⟩
  · cases h
  · simp only [run_eatChar, Prod.mk.injEq, Except.ok.injEq] at h₁
    obtain ⟨hb, rfl⟩ := h₁
    cases b with
    | true =>
      exfalso
      simp only [Bool.not_true, Bool.false_eq_true, ite_false] at h
      have := skipTrailingWhitespace_ne_reject (s.eatChar syntax_).2
      rw [h] at this; exact this rfl
    | false =>
      simp only [Bool.not_false, ite_true, run_reject, Prod.mk.injEq] at h
      exact (Stream.eatChar_false.mp (by rw [← hb])).2 ▸ h.2.symm

/-! ## Nonterminals -/

/-- `try_nonterminal`: the production, then trailing whitespace. -/
def tryNonterminal (p : Parser α) : Parser α := do
  let result ← p
  skipTrailingWhitespace
  pure result

/-- `expect_nonterminal`: `try_nonterminal`, with a `Reject` turned into the fatal error
`"expected {description}"` spanning from the start position to where the production stopped
(a production that rejects after consuming, F-P3, gives a non-empty span). -/
def expectNonterminal (description : String) (p : Parser α) : Parser α := do
  let beginPos ← getPos
  match ← observe (tryNonterminal p) with
  | .error .reject => fatalFrom beginPos (.expected description)
  | result => lift result

/-- `impl<T: Parse> Parse for Option<T>`: `maybe(T::parse(stream))`. -/
def parseOption (p : Parser α) : Parser (Option α) :=
  Parser.maybe p

theorem tryNonterminal_consumes {p : Parser α} (hp : p.Consumes) :
    (tryNonterminal p).Consumes :=
  Consumes.bind_left hp _

/-- `expect_nonterminal` never rejects. -/
theorem expectNonterminal_ne_reject (description : String) (p : Parser α) (s : Stream) :
    ((expectNonterminal description p).run s).1 ≠ .error .reject := by
  simp only [expectNonterminal, run_bind, run_getPos, run_observe]
  split
  · simp
  · rename_i r h
    simpa using h

theorem expectNonterminal_consumes {p : Parser α} (hp : p.Consumes) (description : String) :
    (expectNonterminal description p).Consumes := by
  intro s a s' h
  simp only [expectNonterminal, run_bind, run_getPos, run_observe] at h
  split at h
  · simp at h
  · simp only [run_lift, Prod.mk.injEq] at h
    obtain ⟨h1, rfl⟩ := h
    apply tryNonterminal_consumes hp s a
    rw [← h1]

/-! ## Tokens -/

/-- `trait Token`. The token text is a `List Char` (the `char`s of the Rust `String`);
`construct` returns the error message as an `ErrKind`. Defaults as in Rust: `MAX_LEN = 255`,
`accept_1st = accept`, `ALLOW_ESCAPE = false`, `escaped = |_| false`. -/
structure TokenSpec (α : Type) where
  /-- `Token::MAX_LEN`, a bound on the UTF-8 length in bytes (`String::len`). -/
  maxLen : Nat := 255
  /-- `Token::construct`. -/
  construct : List Char → Except ErrKind α
  /-- `Token::accept`. -/
  accept : Char → Bool
  /-- `Token::accept_1st`. -/
  accept1st : Char → Bool := accept
  /-- `Token::ALLOW_ESCAPE`. -/
  allowEscape : Bool := false
  /-- `Token::escaped`. -/
  escaped : Char → Bool := fun _ => false

/-- `String::len`: the UTF-8 length in bytes. -/
def utf8Len (cs : List Char) : Nat :=
  (cs.map Char.utf8Size).sum

/-- `accept_escaped` inside `impl<T: Token> Parse for T`. With escapes allowed, `\` followed by
an `escaped` character gives that character; else, if `pred` accepts `\`, the backslash itself
(the next character stays); else `\` newline is a line continuation, read as `' '` if `pred`
accepts a space and otherwise a `Reject` *after consuming both characters*; anything else is
`"illegal escape sequence"`. Without an escape: one character accepted by `pred`, or `Reject`. -/
def acceptEscaped (T : TokenSpec α) (pred : Char → Bool) : Parser Char := do
  if ← (if T.allowEscape then eatChar '\\' else pure false) then
    match ← nextIf T.escaped with
    | some c => pure c
    | none =>
      if pred '\\' then
        pure '\\'
      else if ← eatChar '\n' then
        if pred ' ' then pure ' ' else reject
      else
        fatalHere .illegalEscapeSequence
  else
    match ← nextIf pred with
    | some c => pure c
    | none => reject

theorem acceptEscaped_consumes (T : TokenSpec α) (pred : Char → Bool) :
    (acceptEscaped T pred).Consumes := by
  intro s c s' h
  obtain ⟨b, s₁, h₁, h⟩ := run_bind_eq_ok.mp h
  cases b with
  | true =>
    have l₁ : s₁.rest.length < s.rest.length := by
      cases hT : T.allowEscape
      · simp [hT] at h₁
      · simp only [hT, ite_true] at h₁; exact run_eatChar_true_lt h₁
    exact Nat.lt_of_le_of_lt (length_le_of_run h) l₁
  | false =>
    simp only [Bool.false_eq_true, ite_false] at h
    obtain ⟨c?, s₂, h₂, h⟩ := run_bind_eq_ok.mp h
    have l₀ := length_le_of_run h₁
    cases c? with
    | none => simp at h
    | some c' =>
      simp only [run_pure, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact Nat.lt_of_lt_of_le (run_nextIf_some_lt h₂) l₀

/-- One iteration of the token loop:
`if str.len() >= T::MAX_LEN { unrecoverable!(stream, "token exceeds maximum length") }
str.push(c)`. The check happens after `c` was read and before it is appended, so a token can
end up to 3 bytes longer than `MAX_LEN` when its last character is multi-byte. -/
def tokenBody (T : TokenSpec α) (str : List Char) (c : Char) :
    Parser (Step (List Char) (List Char)) :=
  if utf8Len str ≥ T.maxLen then
    fatalHere .tokenExceedsMaximumLength
  else
    pure (.next (str ++ [c]))

/-- `impl<T: Token> Parse for T`: the first character by `accept_1st`, then
`while let Some(c) = maybe(accept_escaped::<T>(T::accept, stream))? { ... }`, then
`T::construct`; its error is fatal and spans from the start of the token to the current
position. -/
def token (T : TokenSpec α) : Parser α := do
  let startPos ← getPos
  let first ← acceptEscaped T T.accept1st
  let str ← whileMaybe (acceptEscaped T T.accept) (acceptEscaped_consumes T T.accept)
    (tokenBody T) id [first]
  match T.construct str with
  | .ok result => pure result
  | .error msg => fatalFrom startPos msg

theorem token_consumes (T : TokenSpec α) : (token T).Consumes :=
  Consumes.bind_right _ fun _ => Consumes.bind_left (acceptEscaped_consumes T _) _

/-! ## Lists -/

/-- One iteration of the loop of `parse_list`, after the separator was accepted:
`if elems.len() >= max { unrecoverable!(stream, "too many items in list") }
elems.push(expect_nonterminal(stream)?);`. -/
def parseListBody (max : Nat) (description : String) (p : Parser α) (elems : List α) (_ : Unit) :
    Parser (Step (List α) (List α)) :=
  if elems.length ≥ max then
    fatalHere .tooManyItemsInList
  else do
    let x ← expectNonterminal description p
    pure (.next (elems ++ [x]))

/-- `parse_list`: one element by `try_nonterminal`, then
`while maybe(try_syntax(sep_by, stream))?.is_some() { ... }`. At most `max` elements. -/
def parseList (sepBy : Char) (max : Nat) (description : String) (p : Parser α) :
    Parser (List α) := do
  let first ← tryNonterminal p
  whileMaybe (trySyntax sepBy) (trySyntax_consumes sepBy) (parseListBody max description p) id
    [first]

theorem parseList_consumes {p : Parser α} (hp : p.Consumes) (sepBy : Char) (max : Nat)
    (description : String) : (parseList sepBy max description p).Consumes :=
  Consumes.bind_left (tryNonterminal_consumes hp) _

/-- `parse_list` returns at least one element (so `users[0]` in `Sudo::parse` exists). -/
theorem parseList_ne_nil {sepBy : Char} {max : Nat} {description : String} {p : Parser α}
    {s s' : Stream} {l : List α} (h : (parseList sepBy max description p).run s = (.ok l, s')) :
    l ≠ [] := by
  obtain ⟨first, s₁, -, h⟩ := run_bind_eq_ok.mp h
  have key := loop_invariant (whileMaybeBody_progressive (trySyntax_consumes sepBy)
      (parseListBody max description p) id)
    (fun elems => elems ≠ []) (fun r _ => ∀ l, r = .ok l → l ≠ [])
    (by
      intro st s st' s' hst hrun
      obtain ⟨a?, s₁, -, hrun⟩ := run_bind_eq_ok.mp hrun
      cases a? with
      | none => simp at hrun
      | some u =>
        simp only [parseListBody] at hrun
        split at hrun
        · simp at hrun
        · obtain ⟨x, s₂, -, hrun⟩ := run_bind_eq_ok.mp hrun
          simp only [run_pure, Prod.mk.injEq, Except.ok.injEq, Step.next.injEq] at hrun
          rw [← hrun.1]; simp)
    (by
      intro st s b s' hst hrun
      obtain ⟨a?, s₁, -, hrun⟩ := run_bind_eq_ok.mp hrun
      cases a? with
      | none =>
        simp only [run_pure, Prod.mk.injEq, Except.ok.injEq, Step.done.injEq] at hrun
        intro l hl; cases hl; rw [← hrun.1]; exact hst
      | some u =>
        simp only [parseListBody] at hrun
        split at hrun
        · simp at hrun
        · obtain ⟨x, s₂, -, hrun⟩ := run_bind_eq_ok.mp hrun
          simp at hrun)
    (by intro _ _ _ _ _ _ l hl; cases hl)
    [first] s₁ (by simp)
  exact key l (by
    show ((whileMaybe (trySyntax sepBy) (trySyntax_consumes sepBy) (parseListBody max description p)
      id [first]).run s₁).1 = .ok l
    rw [h])

/-- `trait Many`: the separator and the maximum number of elements of a `Vec<T>`. -/
structure Many where
  /-- `Many::SEP`. -/
  sep : Char := ','
  /-- `Many::LIMIT`. -/
  limit : Nat := 127
  deriving DecidableEq, Repr

/-- `impl<T: Parse + Many + UserFriendly> Parse for Vec<T>`. -/
def parseVec (m : Many) (description : String) (p : Parser α) : Parser (List α) :=
  parseList m.sep m.limit description p

theorem parseVec_consumes {p : Parser α} (hp : p.Consumes) (m : Many) (description : String) :
    (parseVec m description p).Consumes :=
  parseList_consumes hp _ _ _

/-! ## Lines -/

/-- One iteration of the loop of `parse_lines`, after `LeadingWhitespace::parse` succeeded:
```
let item = expect_nonterminal(stream);
let parsed_item_ok = item.is_ok();
result.push(item);
let _ = maybe(Comment::parse(stream));
if !stream.eat_char('\n') {
    if parsed_item_ok {
        let msg = if stream.peek().is_none() { "missing line terminator at end of file" }
                  else { "garbage at end of line" };
        result.push(error(stream));      // unrecoverable!(stream, "{msg}")
    }
    stream.skip_to_newline();
}
```
After an error the line is skipped up to the next newline character, the end of the physical
line (F-P2). -/
def parseLinesItem (description : String) (p : Parser α) (result : List (Parsed α)) :
    Parser (List (Parsed α)) := do
  let item ← observe (expectNonterminal description p)
  let parsedItemOk := item.isOk
  let result := result ++ [item]
  let _ ← observe (Parser.maybe comment)
  if ← eatChar '\n' then
    pure result
  else
    let result ← if parsedItemOk then do
        let msg := if (← peek).isNone then ErrKind.missingLineTerminator else .garbageAtEndOfLine
        let error ← observe (fatalHere msg)
        pure (result ++ [error])
      else
        pure result
    skipToNewline
    pure result

/-- One iteration of the loop `while LeadingWhitespace::parse(stream).is_ok() { ... }` of
`parse_lines`. -/
def parseLinesBody (description : String) (p : Parser α) (result : List (Parsed α)) :
    Parser (Step (List (Parsed α)) (List (Parsed α))) := do
  match ← observe leadingWhitespace with
  | .error _ => pure (.done result)
  | .ok () => do
    let result ← parseLinesItem description p result
    pure (.next result)

theorem leadingWhitespace_ok {s s' : Stream} (h : leadingWhitespace.run s = (.ok (), s')) :
    s'.rest ≠ [] := by
  simp only [leadingWhitespace, run_bind, run_skipWhile, run_peek] at h
  split at h
  · rename_i hp
    simp only [run_pure, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    intro hnil
    simp [Stream.peek, hnil] at hp
  · simp at h

theorem parseLinesItem_lt {description : String} {p : Parser α} {result result' : List (Parsed α)}
    {s s' : Stream} (hne : s.rest ≠ [])
    (h : (parseLinesItem description p result).run s = (.ok result', s')) :
    s'.rest.length < s.rest.length := by
  obtain ⟨item, s₁, h₁, h⟩ := run_bind_eq_ok.mp h
  obtain ⟨_, s₂, h₂, h⟩ := run_bind_eq_ok.mp h
  obtain ⟨b, s₃, h₃, h⟩ := run_bind_eq_ok.mp h
  have l₁ := length_le_of_run h₁
  have l₂ := length_le_of_run h₂
  cases b with
  | true =>
    have l₃ := run_eatChar_true_lt h₃
    simp only [ite_true, run_pure, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    omega
  | false =>
    simp only [Bool.false_eq_true, ite_false] at h
    simp only [run_eatChar, Prod.mk.injEq, Except.ok.injEq] at h₃
    obtain ⟨hb, rfl⟩ := h₃
    have hs₃ := (Stream.eatChar_false (s := s₂) (s' := (s₂.eatChar '\n').2)).mp (by rw [← hb])
    -- both branches end with `skip_to_newline` on the stream left by `eat_char`
    have e : s' = (s₂.eatChar '\n').2.skipToNewline := by
      cases hok : item.isOk
      · simp only [hok, Bool.false_eq_true, ite_false, run_bind, run_pure, run_skipToNewline,
          Prod.mk.injEq] at h
        exact h.2.symm
      · simp only [hok, ite_true, run_bind, run_peek, run_observe, run_fatalHere, run_pure,
          run_skipToNewline, Prod.mk.injEq] at h
        exact h.2.symm
    rw [e, hs₃.2]
    cases hc : s₂.rest with
    | nil =>
      have : s₂.skipToNewline.rest = [] := by rw [Stream.skipToNewline_rest, hc]; rfl
      rw [this]
      have : 0 < s.rest.length := List.length_pos_iff.mpr hne
      simp only [List.length_nil]; omega
    | cons c cs =>
      have hpk : s₂.peek = some c := by simp [Stream.peek, hc]
      have hc' : c ≠ '\n' := fun e => hs₃.1 (e ▸ hpk)
      have := Stream.skipToNewline_lt hpk hc'
      omega

theorem parseLinesBody_progressive (description : String) (p : Parser α) :
    Progressive (parseLinesBody description p) := by
  intro st s st' s' h
  obtain ⟨r, s₁, h₁, h⟩ := run_bind_eq_ok.mp h
  simp only [run_observe, Prod.mk.injEq, Except.ok.injEq] at h₁
  obtain ⟨hr, rfl⟩ := h₁
  cases r with
  | error e => simp at h
  | ok u =>
    have hlw : leadingWhitespace.run s = (.ok (), (leadingWhitespace.run s).2) := by
      rw [← hr]
    have hne := leadingWhitespace_ok hlw
    have l₁ := leadingWhitespace.length_le s
    obtain ⟨result', s₂, h₂, h⟩ := run_bind_eq_ok.mp h
    simp only [run_pure, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    have := parseLinesItem_lt hne h₂
    omega

/-- `parse_lines`: `parse_lines::<T>(stream)` with the production `p` of `T` and
`T::DESCRIPTION`. One result per line that starts with something other than blanks, followed
by a fatal error for garbage after a successful item; never fails (`parseLines_ok`) and never
yields `Reject` (`parseLines_ne_reject`). -/
def parseLines (description : String) (p : Parser α) : Parser (List (Parsed α)) :=
  loop (parseLinesBody description p) (parseLinesBody_progressive description p) []

/-- One line of `parse_lines` keeps the invariant "no `Reject` in the result". -/
theorem parseLinesItem_ok (description : String) (p : Parser α) (result : List (Parsed α))
    (s : Stream) (hinv : ∀ item ∈ result, item ≠ .error .reject) :
    ∃ result', ((parseLinesItem description p result).run s).1 = .ok result' ∧
      ∀ item ∈ result', item ≠ .error .reject := by
  have hne := expectNonterminal_ne_reject description p s
  simp only [parseLinesItem, run_bind, run_observe, run_eatChar]
  split
  · refine ⟨_, rfl, ?_⟩
    simp only [List.mem_append, List.mem_singleton]
    rintro i (hi | rfl)
    · exact hinv i hi
    · exact hne
  · split
    · refine ⟨_, rfl, ?_⟩
      simp only [List.mem_append, List.mem_singleton]
      rintro i ((hi | rfl) | rfl)
      · exact hinv i hi
      · exact hne
      · split <;> simp
    · refine ⟨_, rfl, ?_⟩
      simp only [List.mem_append, List.mem_singleton]
      rintro i (hi | rfl)
      · exact hinv i hi
      · exact hne

/-- `parse_lines` returns a list, and no element of it is `Err(Reject)`; in Rust this makes
`panic!("internal parser error")` in `Sudoers::process` unreachable (PT1). -/
theorem parseLines_ok (description : String) (p : Parser α) (s : Stream) :
    ∃ items, ((parseLines description p).run s).1 = .ok items ∧
      ∀ item ∈ items, item ≠ .error .reject := by
  refine loop_invariant (parseLinesBody_progressive description p)
    (fun result => ∀ item ∈ result, item ≠ .error .reject)
    (fun r _ => ∃ items, r = .ok items ∧ ∀ item ∈ items, item ≠ .error .reject)
    ?_ ?_ ?_ [] s (by simp)
  · intro st s st' s' hinv h
    obtain ⟨r, s₁, h₁, h⟩ := run_bind_eq_ok.mp h
    cases r with
    | error e => simp at h
    | ok u =>
      obtain ⟨result', s₂, h₂, h⟩ := run_bind_eq_ok.mp h
      simp only [run_pure, Prod.mk.injEq, Except.ok.injEq, Step.next.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨r', hr', hinv'⟩ := parseLinesItem_ok description p st s₁ hinv
      rw [h₂] at hr'; cases hr'; exact hinv'
  · intro st s b s' hinv h
    obtain ⟨r, s₁, h₁, h⟩ := run_bind_eq_ok.mp h
    cases r with
    | error e =>
      simp only [run_pure, Prod.mk.injEq, Except.ok.injEq, Step.done.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨_, rfl, hinv⟩
    | ok u =>
      obtain ⟨result', s₂, h₂, h⟩ := run_bind_eq_ok.mp h
      simp at h
  · intro st s e s' hinv h
    exfalso
    rcases run_bind_eq_error.mp h with h | ⟨r, s₁, h₁, h⟩
    · simp at h
    · cases r with
      | error e' => simp at h
      | ok u =>
        rcases run_bind_eq_error.mp h with h | ⟨result', s₂, h₂, h⟩
        · obtain ⟨r', hr', -⟩ := parseLinesItem_ok description p st s₁ hinv
          rw [h] at hr'; cases hr'
        · simp at h

/-! ## Test helpers (`#[cfg(test)]` in Rust) -/

/-- `expect_complete` (`#[cfg(test)]`): a nonterminal that must extend to the end of the input. -/
def expectComplete (description : String) (p : Parser α) : Parser α := do
  let result ← expectNonterminal description p
  match ← peek with
  | some c => fatalHere (.garbageAtEndOfLineChar c)
  | none => pure result

/-- `parse_string` (`#[cfg(test)]`). In test builds every `UserFriendly::DESCRIPTION` is
`"elem"`. -/
def parseString (p : Parser α) (text : String) : Parsed α :=
  ((expectComplete "elem" p).run (Stream.ofString text)).1

end SudoersSpec.Syntax
