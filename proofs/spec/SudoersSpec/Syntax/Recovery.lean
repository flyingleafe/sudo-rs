import SudoersSpec.Syntax.BasicParser

/-!
# Line recovery and source accounting (PT7)

A trace describes precisely which items and diagnostics the reference line driver emits. It
uses the item parser as a parameter; the trace does not run `parseLines` or its loop body.
Distinguish the location of a diagnostic from the text skipped while recovering from it.
-/

namespace SudoersSpec.Syntax.Recovery

open Parser

/-- Only horizontal ASCII blanks are skipped at the start of a physical line. -/
def afterBlanks (s : Stream) : Stream := s.skipWhile (fun c => c == '\t' || c == ' ')

/-- An optional end-of-line comment stops *before* the physical newline. -/
def afterComment (s : Stream) : Stream :=
  if s.peek = some '#' then s.pop.skipToNewline else s

/-- A successful item not followed by a newline gets a second record. Its diagnostic is a
point at the end of the parsed prefix, not a range covering the discarded text. -/
def terminatorError (s : Stream) : Status :=
  .fatal ⟨s.getPos, s.getPos⟩ (if s.peek.isNone then .missingLineTerminator else .garbageAtEndOfLine)

/-- Finish one item after attempting an optional comment. Only an immediately available
newline is consumed; recovery from other text leaves the next physical newline unread. -/
def finish (r : Parsed α) (stop : Stream) : List (Parsed α) × Stream :=
  let t := afterComment stop
  if t.peek = some '\n' then ([r], t.pop)
  else (match r with | .ok a => [.ok a, .error (terminatorError t)] | .error e => [.error e],
        t.skipToNewline)

/-- A derivation records every iteration, including the stop after trailing blanks. -/
inductive Trace (d : String) (p : Parser α) : Stream → List (Parsed α) → Stream → Prop where
  | eof {s} (empty : (afterBlanks s).rest = []) : Trace d p s [] (afterBlanks s)
  | line {s r stop tail out} (more : (afterBlanks s).rest ≠ [])
      (item : (expectNonterminal d p).run (afterBlanks s) = (r, stop))
      (next : Trace d p (finish r stop).2 tail out) :
      Trace d p s ((finish r stop).1 ++ tail) out

private theorem comment_cursor (s : Stream) : (comment.run s).2 = afterComment s := by
  rw [comment_run, afterComment]; split <;> rfl

/-- In particular an accepted prefix is retained before its terminator diagnostic; an item
already in error does not get a second diagnostic from this iteration. -/
theorem parseLinesItem_finish {r : Parsed α} {s stop : Stream} {d : String} {p : Parser α}
    (h : (expectNonterminal d p).run s = (r, stop)) (acc : List (Parsed α)) :
    (parseLinesItem d p acc).run s = (.ok (acc ++ (finish r stop).1), (finish r stop).2) := by
  cases r <;> by_cases nl : (afterComment stop).peek = some '\n' <;>
    simp [parseLinesItem, run_bind, run_observe, run_maybe, h, comment_cursor, run_eatChar,
      Stream.eatChar_eq, finish, nl, terminatorError, Except.isOk, Except.toBool, List.append_assoc]

private theorem leading_run (s : Stream) :
    leadingWhitespace.run s = if (afterBlanks s).peek.isSome then (.ok (), afterBlanks s)
      else (.error (.fatal ⟨(afterBlanks s).getPos, (afterBlanks s).getPos⟩ .superfluousWhitespace),
        afterBlanks s) := leadingWhitespace_run s

private theorem body_eof {s : Stream} (h : (afterBlanks s).rest = [])
    (d : String) (p : Parser α) (acc : List (Parsed α)) :
    (parseLinesBody d p acc).run s = (.ok (.done acc), afterBlanks s) := by
  have he : (afterBlanks s).peek = none := by simp [Stream.peek, h]
  simp [parseLinesBody, run_bind, run_observe, leading_run, he]

private theorem body_more {s stop : Stream} {d : String} {p : Parser α} {r : Parsed α}
    (h : (afterBlanks s).rest ≠ [])
    (hi : (expectNonterminal d p).run (afterBlanks s) = (r, stop)) (acc : List (Parsed α)) :
    (parseLinesBody d p acc).run s = (.ok (.next (acc ++ (finish r stop).1)), (finish r stop).2) := by
  have he : (afterBlanks s).peek.isSome = true := by
    cases hs : (afterBlanks s).rest with
    | nil => exact (h hs).elim
    | cons => simp [Stream.peek, hs]
  simp [parseLinesBody, run_bind, run_observe, leading_run, he, parseLinesItem_finish hi]

private abbrev fromAcc (d : String) (p : Parser α) (acc : List (Parsed α)) :=
  loop (parseLinesBody d p) (parseLinesBody_progressive d p) acc

private theorem run_trace {d : String} {p : Parser α} {s out : Stream} {rs : List (Parsed α)}
    (ht : Trace d p s rs out) (acc : List (Parsed α)) :
    (fromAcc d p acc).run s = (.ok (acc ++ rs), out) := by
  induction ht generalizing acc with
  | eof empty => rw [fromAcc, loop_run, body_eof empty]; simp
  | line more item _ ih =>
    rw [fromAcc, loop_run, body_more more item]
    simpa only [List.append_assoc] using ih (acc ++ _)

private theorem trace_exists (d : String) (p : Parser α) (s : Stream) :
    ∃ rs out, Trace d p s rs out := by
  by_cases h : (afterBlanks s).rest = []
  · exact ⟨_, _, .eof h⟩
  · rcases hi : (expectNonterminal d p).run (afterBlanks s) with ⟨r, stop⟩
    have hl := parseLinesBody_progressive d p [] s _ _ (body_more h hi [])
    obtain ⟨tail, out, ht⟩ := trace_exists d p (finish r stop).2
    exact ⟨_, out, .line h hi ht⟩
termination_by s.rest.length

/-- The trace is both necessary and sufficient, including the final cursor and the exact list
of diagnostics. No assumption about tokens, syntax classes or the environment is needed. -/
theorem parseLines_iff_trace (d : String) (p : Parser α) (s out : Stream) (rs : List (Parsed α)) :
    (parseLines d p).run s = (.ok rs, out) ↔ Trace d p s rs out := by
  constructor
  · intro h
    obtain ⟨rs', out', ht⟩ := trace_exists d p s
    have he : (parseLines d p).run s = (.ok rs', out') := by
      simpa only [parseLines, fromAcc, List.nil_append] using run_trace ht []
    rw [he] at h; cases h; exact ht
  · intro ht; simpa only [parseLines, fromAcc, List.nil_append] using run_trace ht []

/-- The driver accounts for the entire input, including any final blanks, even after a
failed item. Both the remaining characters and the line/column are determined. -/
theorem parseLines_end (d : String) (p : Parser α) (s : Stream) :
    ((parseLines d p).run s).2 = s.advance s.rest.length := by
  obtain ⟨rs, out, ht⟩ := trace_exists d p s
  have empty : out.rest = [] := by induction ht with
    | eof he => exact he
    | line _ _ _ ih => exact ih
  have h := (parseLines_iff_trace d p s out rs).mpr ht
  have endPos := (Parser.reaches_of_run h).eq_advance
  simpa [h, empty] using endPos

/-- The source consumed by the final step of a line. A newline at the cursor is consumed;
otherwise the characters up to, but excluding, the next newline are discarded. -/
def terminatorText (t : Stream) : List Char :=
  if t.peek = some '\n' then ['\n'] else t.rest.takeWhile (fun c => c != '\n')

private theorem finish_partition (r : Parsed α) (stop : Stream) :
    (afterComment stop).rest = terminatorText (afterComment stop) ++ (finish r stop).2.rest := by
  by_cases hn : (afterComment stop).peek = some '\n'
  · obtain ⟨tail, ht⟩ := List.head?_eq_some_iff.mp hn
    simp [finish, terminatorText, hn, Stream.pop_rest, ht]
  · simp only [finish, terminatorText, hn, ite_false, Stream.skipToNewline_rest]
    exact List.takeWhile_append_dropWhile.symm

/-- The characters between two successive cursors of the same parse. -/
def between (first last : Stream) : List Char :=
  first.rest.take (first.rest.length - last.rest.length)

/-- Source accounting for every `Trace.line`: no overlap or gap between leading blanks,
the attempted item, the optional comment, the newline or skipped text, and the next iteration.
A fatal item's consumed prefix need not itself be grammatical. -/
theorem source_partition {s stop : Stream} {d : String} {p : Parser α} {r : Parsed α}
    (hi : (expectNonterminal d p).run (afterBlanks s) = (r, stop)) :
    s.rest = s.rest.takeWhile (fun c => c == '\t' || c == ' ') ++
      (between (afterBlanks s) stop ++ (between stop (afterComment stop) ++
      (terminatorText (afterComment stop) ++ (finish r stop).2.rest))) := by
  have hb : s.rest = s.rest.takeWhile (fun c => c == '\t' || c == ' ') ++ (afterBlanks s).rest := by
    rw [afterBlanks, Stream.skipWhile_rest, List.takeWhile_append_dropWhile]
  have hp : (afterBlanks s).rest = between (afterBlanks s) stop ++ stop.rest :=
    (Parser.reaches_of_run hi).getPos_eq.1
  have hr : stop.Reaches (afterComment stop) := comment_cursor stop ▸ comment.reaches stop
  have hc : stop.rest = between stop (afterComment stop) ++ (afterComment stop).rest := hr.getPos_eq.1
  rw [finish_partition r stop] at hc
  rw [hc] at hp
  rw [hp] at hb
  exact hb

/-- The diagnostic locates the start of a nonempty recovery interval; it does not *span*
that interval. Interpreting PT7 as literal coverage by the reported spans is incorrect. -/
theorem garbage_point {s stop : Stream} {d : String} {p : Parser α} {a : α} {c : Char}
    (item : (expectNonterminal d p).run s = (.ok a, stop))
    (ch : (afterComment stop).peek = some c) (hn : c ≠ '\n') (acc : List (Parsed α)) :
    (parseLinesItem d p acc).run s =
      (.ok (acc ++ [.ok a, .error (.fatal ⟨(afterComment stop).getPos, (afterComment stop).getPos⟩
        .garbageAtEndOfLine)]), (afterComment stop).skipToNewline) ∧
      (afterComment stop).skipToNewline.rest.length < (afterComment stop).rest.length := by
  constructor
  · rw [parseLinesItem_finish item]; simp [finish, terminatorError, ch, hn]
  · exact Stream.skipToNewline_lt ch hn

-- An inert, one-letter production: the unparsed character is outside the diagnostic's span.
example : (parseLinesItem "letter" (trySyntax 'a') []).run (Stream.ofString "ab\n") =
    (.ok [.ok (), .error (.fatal ⟨(1, 2), (1, 2)⟩ .garbageAtEndOfLine)],
      Stream.newWithPos ['\n'] (1, 3)) := by decide

/-- A clean file in terms of a separately specified item grammar. Its judgement includes
the remaining input and position so lexical follow conditions are expressible. -/
inductive CleanFile (derives : Stream → α → Stream → Prop) : Stream → List α → Stream → Prop where
  | eof {s} (empty : (afterBlanks s).rest = []) : CleanFile derives s [] (afterBlanks s)
  | line {s a stop tail out} (more : (afterBlanks s).rest ≠ [])
      (item : derives (afterBlanks s) a stop) (newline : (afterComment stop).peek = some '\n')
      (next : CleanFile derives (afterComment stop).pop tail out) : CleanFile derives s (a :: tail) out

private theorem clean_of_trace {d : String} {p : Parser α} {derives : Stream → α → Stream → Prop}
    (sound : ∀ s a stop, (expectNonterminal d p).run s = (.ok a, stop) → derives s a stop)
    {s rs out} (ht : Trace d p s rs out) {items : List α} (he : rs = items.map Except.ok) :
    CleanFile derives s items out := by
  induction ht generalizing items with
  | eof empty =>
    cases items with
    | nil => exact .eof empty
    | cons => cases he
  | @line s r stop tail out more item _ ih =>
    by_cases nl : (afterComment stop).peek = some '\n'
    · cases items with
      | nil => simp [finish, nl] at he
      | cons b bs =>
        obtain ⟨rfl, rest⟩ : r = .ok b ∧ tail = bs.map Except.ok := by simpa [finish, nl] using he
        exact .line more (sound _ _ _ item) nl (by simpa [finish, nl] using ih rest)
    · cases r with
      | error => cases items <;> simp [finish, nl] at he
      | ok => cases items with
        | nil => simp [finish, nl] at he
        | cons b bs => cases bs <;> simp [finish, nl] at he

/-- PT6 composition: the clean-file driver is sound given *single-item* grammar soundness.
This theorem does not assume a grammar for line recovery or that the whole file parses. -/
theorem cleanFile_sound {d : String} {p : Parser α} {derives : Stream → α → Stream → Prop}
    (sound : ∀ s a stop, (expectNonterminal d p).run s = (.ok a, stop) → derives s a stop)
    {s out} {items : List α} (h : (parseLines d p).run s = (.ok (items.map Except.ok), out)) :
    CleanFile derives s items out :=
  clean_of_trace sound ((parseLines_iff_trace ..).mp h) rfl

/-- The converse uses only single-item completeness: no complete-file assumption is needed. -/
theorem cleanFile_complete {d : String} {p : Parser α} {derives : Stream → α → Stream → Prop}
    (complete : ∀ s a stop, derives s a stop → (expectNonterminal d p).run s = (.ok a, stop))
    {s out} {items : List α} (h : CleanFile derives s items out) :
    (parseLines d p).run s = (.ok (items.map Except.ok), out) := by
  apply (parseLines_iff_trace ..).mpr
  induction h with
  | eof empty => exact .eof empty
  | @line s a stop tail out more item newline _ ih =>
    have next : Trace d p (finish (.ok a) stop).2 (tail.map Except.ok) out := by
      simpa only [finish, newline, ite_true] using ih
    simpa [finish, newline] using Trace.line more (complete _ _ _ item) next

end SudoersSpec.Syntax.Recovery
