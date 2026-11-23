import SudoRsProofs.AbsTags
import SudoersSpec

/-!
# Parser refinement: abstraction, invariants, refinement predicates

The extracted parser (`proofs/parser/RESTYLE.md` section 5.1) against the reference parser
`SudoersSpec.Syntax` (`proofs/spec/SudoersSpec/Syntax/README.md`).

* **Stream.** A Rust `CharStream { src, pos, line, col }` is the reference `Stream` of the
  characters not read yet, `src.drop pos`, at the same line and column (`absStream`).
* **Representability.** `StreamOK`: `pos` within the slice, and line and column so small that no
  `+ 1` of `bump` overflows before the input ends. Every refinement lemma preserves it; the
  final theorems need it only for the initial stream, where it follows from the input length
  (`StreamOK.initial`).
* **Errors.** `ErrorKind` and `Status` are related to `ErrKind` and `Syntax.Status` by the
  relations `KindRel` and `StatusRel`. The payload of `Expected` (a `&str`, its UTF-8 bytes) is
  related to the reference `String` through `sudo_rs.stringBytes`. The transitional
  `ErrorKind::Message(String)` has no reference counterpart: no constructor of `KindRel`
  mentions it (`KindRel.not_message`), so a function that refines a reference production never
  produces it (`Refines.not_message`).
* **Results.** `ResultRel f` relates `Result<T, Status>` to `Parsed α`, with an abstraction
  function `f : T → α` of the AST type (the functions of `Abs*.lean`).
* **Refinement.** `Refines f x out`: the extracted computation `x` returns `ok (r, s')` (no
  panic, no overflow, no divergence), `r` is related to the reference result, `s'` is
  representable and abstracts to the reference output stream.
* **Instances.** `ParseRefines P f p`: an extracted `Parse T` instance refines a reference
  `Parser α` on every representable stream. `TokenRefines Tk f T' Pre`: an extracted `Token T`
  instance refines a reference `TokenSpec α` with constructor domain `Pre`. `ManyRefines`, `DescRel`: `Many` and
  `UserFriendly`. Generic lemmas take these as hypotheses, so a new production only supplies
  its instance proofs.
* **Characters.** `UnicodeOracle O`: the three `opaque` Unicode predicates of
  `SudoRs/FunsExternal.lean` agree with the reference `CharOracle` `O`.
-/

open Aeneas Aeneas.Std Result
open SudoersSpec.Syntax (Stream ErrKind Parser Parsed TokenSpec CharOracle)

namespace SudoRsProofs.Parser

/-! ## Names of the extracted types -/

/-- The extracted `CharStream`. -/
abbrev CS := sudo_rs.sudoers.char_stream.CharStream
/-- The extracted `Status`. -/
abbrev RStatus := sudo_rs.sudoers.basic_parser.Status
/-- The extracted `ErrorKind`. -/
abbrev RKind := sudo_rs.sudoers.basic_parser.ErrorKind
/-- The extracted `Parsed<T> = Result<T, Status>`. -/
abbrev RParsed (T : Type) := core.result.Result T RStatus

/-! ## Stream -/

/-- The reference stream of an extracted cursor: the characters from `pos` on, same line and
column. -/
def absStream (s : CS) : Stream :=
  ⟨s.src.val.drop s.pos.val, s.line.val, s.col.val⟩

@[simp] theorem absStream_rest (s : CS) : (absStream s).rest = s.src.val.drop s.pos.val := rfl
@[simp] theorem absStream_line (s : CS) : (absStream s).line = s.line.val := rfl
@[simp] theorem absStream_col (s : CS) : (absStream s).col = s.col.val := rfl
@[simp] theorem absStream_getPos (s : CS) :
    (absStream s).getPos = (s.line.val, s.col.val) := rfl

/-- Representability of a cursor: `pos` within the slice, and line and column so small that
every remaining character can still be read by `bump` without an overflow of `line + 1` or
`col + 1`. -/
structure StreamOK (s : CS) : Prop where
  pos_le : s.pos.val ≤ s.src.val.length
  line_le : s.line.val + (s.src.val.length - s.pos.val) ≤ Usize.max
  col_le : s.col.val + (s.src.val.length - s.pos.val) ≤ Usize.max

/-- The stream at the start of an input: representable iff the input is shorter than
`usize::MAX` characters. -/
theorem StreamOK.initial (src : Slice Char) (h : src.val.length < Usize.max) :
    StreamOK ⟨src, 0#usize, 1#usize, 1#usize⟩ := by
  constructor <;> simp <;> omega

/-! ## Errors -/

/-- `ErrorKind` against `ErrKind`. `Expected(&str)` carries the UTF-8 bytes of the reference
description. `Message(String)` (transitional) has no constructor: it is related to nothing. -/
inductive KindRel : RKind → ErrKind → Prop
  | superfluousWhitespace : KindRel .SuperfluousWhitespace .superfluousWhitespace
  | strayEscape : KindRel .StrayEscape .strayEscapeSequence
  | expecting (c : Char) (o : Option Char) : KindRel (.Expecting c o) (.expectingSyntax c o)
  | expected (s : Str) (d : String) (h : s.val = sudo_rs.stringBytes d) :
      KindRel (.Expected s) (.expected d)
  | illegalEscape : KindRel .IllegalEscape .illegalEscapeSequence
  | tokenTooLong : KindRel .TokenTooLong .tokenExceedsMaximumLength
  | tooManyItems : KindRel .TooManyItems .tooManyItemsInList
  | missingLineTerminator : KindRel .MissingLineTerminator .missingLineTerminator
  | garbageAtEndOfLine : KindRel .GarbageAtEndOfLine .garbageAtEndOfLine
  | hostIpv4 : KindRel .HostIpv4 .hostIPv4Address

/-- The transitional `ErrorKind::Message` refines no reference message. -/
theorem KindRel.not_message {m : String} {k : ErrKind} : ¬ KindRel (.Message m) k := by
  intro h; cases h

/-- `KindRel` is functional: the reference message is determined. -/
theorem KindRel.unique {k : RKind} {a b : ErrKind} (ha : KindRel k a) (hb : KindRel k b) :
    a = b := by
  cases ha <;> cases hb <;> try rfl
  rename_i h1 _ h2
  rw [stringBytes_inj.mp (h1.symm.trans h2)]

/-- `Status` against `Syntax.Status`; spans through `absSpan`. -/
inductive StatusRel : RStatus → SudoersSpec.Syntax.Status → Prop
  | fatal (sp : sudo_rs.sudoers.basic_parser.Span) (k : RKind) (k' : ErrKind) :
      KindRel k k' → StatusRel (.Fatal sp k) (.fatal (absSpan sp) k')
  | reject : StatusRel .Reject .reject

/-- `Result<T, Status>` against `Parsed α`, the values through `f`. -/
def ResultRel {T α : Type} (f : T → α) : RParsed T → Parsed α → Prop
  | .Ok x, .ok a => f x = a
  | .Err e, .error e' => StatusRel e e'
  | _, _ => False

@[simp] theorem ResultRel.ok_ok {T α : Type} (f : T → α) (x : T) (a : α) :
    ResultRel f (.Ok x) (.ok a) ↔ f x = a := Iff.rfl
@[simp] theorem ResultRel.err_err {T α : Type} (f : T → α) (e : RStatus)
    (e' : SudoersSpec.Syntax.Status) :
    ResultRel f (.Err e) (.error e') ↔ StatusRel e e' := Iff.rfl
@[simp] theorem ResultRel.ok_err {T α : Type} (f : T → α) (x : T)
    (e' : SudoersSpec.Syntax.Status) : ¬ ResultRel f (.Ok x) (.error e') := id
@[simp] theorem ResultRel.err_ok {T α : Type} (f : T → α) (e : RStatus) (a : α) :
    ¬ ResultRel f (.Err e) (.ok a) := id

/-- `Result<T, ErrorKind>` (the result of `Token::construct`) against `Except ErrKind α`. -/
def ConstructRel {T α : Type} (f : T → α) :
    core.result.Result T RKind → Except ErrKind α → Prop
  | .Ok x, .ok a => f x = a
  | .Err k, .error k' => KindRel k k'
  | _, _ => False

/-! ## Refinement -/

/-- **The extracted computation `x` refines the reference outcome `out`**: it returns
`ok (r, s')` (no panic, overflow or divergence), `r` is related to the reference result, and
`s'` is representable and is the reference output stream. -/
def Refines {T α : Type} (f : T → α) (x : Result (RParsed T × CS)) (out : Parsed α × Stream) :
    Prop :=
  ∃ r s', x = ok (r, s') ∧ ResultRel f r out.1 ∧ StreamOK s' ∧ absStream s' = out.2

/-- **An extracted `Parse T` instance refines a reference production `p`** (values through
`f`) on every representable stream. -/
structure ParseRefines {T α : Type} (P : sudo_rs.sudoers.basic_parser.Parse T) (f : T → α)
    (p : Parser α) : Prop where
  parse : ∀ s, StreamOK s → Refines f (P.parse s) (p.run (absStream s))

/-- A result related to a reference result is never the transitional `Message`. -/
theorem ResultRel.not_message {T α : Type} {f : T → α} {r : RParsed T} {r' : Parsed α}
    (h : ResultRel f r r') (sp : sudo_rs.sudoers.basic_parser.Span) (m : String) :
    r ≠ .Err (.Fatal sp (.Message m)) := by
  rintro rfl
  rcases r' with (⟨sp', k'⟩ | _) | a <;> simp only [ResultRel] at h <;> cases h
  exact KindRel.not_message (by assumption)

/-- **A refining computation never produces `ErrorKind::Message`.** -/
theorem Refines.not_message {T α : Type} {f : T → α} {x : Result (RParsed T × CS)}
    {out : Parsed α × Stream} (h : Refines f x out) :
    ∃ r s', x = ok (r, s') ∧ ∀ sp m, r ≠ .Err (.Fatal sp (.Message m)) := by
  obtain ⟨r, s', e, hr, -⟩ := h
  exact ⟨r, s', e, hr.not_message⟩

/-- `UserFriendly::DESCRIPTION` is the reference description `d` (its UTF-8 bytes). -/
def DescRel {T : Type} (UF : sudo_rs.sudoers.ast_names.UserFriendly T) (d : String) : Prop :=
  ∃ s : Str, UF.DESCRIPTION = ok s ∧ s.val = sudo_rs.stringBytes d

/-- An extracted `Many` instance has the separator and limit of the reference `Many`. -/
structure ManyRefines {T : Type} (M : sudo_rs.sudoers.basic_parser.Many T)
    (m : SudoersSpec.Syntax.Many) : Prop where
  sep : M.SEP = ok m.sep
  limit : ∃ n : Usize, M.LIMIT = ok n ∧ n.val = m.limit

/-- A character that `acceptEscaped T' pred` can return: one accepted by `pred` (this includes
the backslash and the blank of a line continuation, both returned only if `pred` accepts them),
or an `escaped` character after a backslash. -/
def Produces {α : Type} (T' : TokenSpec α) (pred : Char → Bool) (c : Char) : Prop :=
  pred c = true ∨ (T'.allowEscape = true ∧ T'.escaped c = true)

/-- A text the token loop of `token T'` can hand to `construct`: non-empty, the first character
produced by `acceptEscaped` with `accept1st`, the others with `accept`
(`token_loop_text`). -/
def TokenText {α : Type} (T' : TokenSpec α) : List Char → Prop
  | [] => False
  | c :: cs => Produces T' T'.accept1st c ∧ ∀ d ∈ cs, Produces T' T'.accept d

/-- **An extracted `Token T` instance refines a reference `TokenSpec α`** (values through
`f`), with `construct` refined on the texts satisfying `Pre`. `max_len_le` keeps the token text
(at most `MAX_LEN + 3` bytes, see `SudoersSpec.Syntax.tokenBody`) within `usize`, so
`String::len` does not fail. `Pre` lets an instance whose `construct` panics on some texts (as
`Command::construct` does on a text without a non-blank character) refine on the texts the
token loop can build: `token_refines` needs `∀ cs, TokenText T' cs → Pre cs`. Instances whose
`construct` is total take `Pre := fun _ => True`. -/
structure TokenRefines {T α : Type} (Tk : sudo_rs.sudoers.basic_parser.Token T) (f : T → α)
    (T' : TokenSpec α) (Pre : List Char → Prop) : Prop where
  max_len : ∃ n : Usize, Tk.MAX_LEN = ok n ∧ n.val = T'.maxLen
  max_len_le : T'.maxLen + 4 ≤ Usize.max
  allow_escape : Tk.ALLOW_ESCAPE = ok T'.allowEscape
  accept : ∀ c, Tk.accept c = ok (T'.accept c)
  accept_1st : ∀ c, Tk.accept_1st c = ok (T'.accept1st c)
  escaped : ∀ c, Tk.escaped c = ok (T'.escaped c)
  construct : ∀ s : String, s.utf8ByteSize ≤ Usize.max → Pre s.toList →
    ∃ r, Tk.construct s = ok r ∧ ConstructRel f r (T'.construct s.toList)

/-! ## Characters -/

/-- **The Unicode predicates of the extracted code agree with the character oracle `O`.** The
three predicates are `opaque` in `SudoRs/FunsExternal.lean` (Unicode tables of the Rust standard
library); `is_alphanumeric` and `is_control` of `CharOracle` are not called by the extracted
code. -/
structure UnicodeOracle (O : CharOracle) : Prop where
  /-- `char::is_uppercase`. -/
  is_uppercase : ∀ c, core.char.methods.Char.is_uppercase c = ok (O.isUppercase c)
  /-- `char::is_numeric`. -/
  is_numeric : ∀ c, core.char.methods.Char.is_numeric c = ok (O.isNumeric c)
  /-- `char::is_whitespace`. -/
  is_whitespace : ∀ c, core.char.methods.Char.is_whitespace c = ok (O.isWhitespace c)

/-! ## The `?` operator of the extracted code -/

@[simp] theorem branch_Ok {T E : Type} (v : T) :
    core.result.Result.Insts.CoreOpsTry.branch (T := T) (E := E) (.Ok v) = ok (.Continue v) :=
  rfl

@[simp] theorem branch_Err {T E : Type} (e : E) :
    core.result.Result.Insts.CoreOpsTry.branch (T := T) (E := E) (.Err e) =
      ok (.Break (.Err e)) := rfl

@[simp] theorem from_residual_Err {T E : Type} (e : E) :
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual T
      (core.convert.FromSame E) (.Err e) = ok (.Err e) := by
  simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from]

end SudoRsProofs.Parser
