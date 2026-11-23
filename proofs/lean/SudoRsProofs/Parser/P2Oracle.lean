import SudoRsProofs.Parser.Ast
import SudoRsProofs.AbsMatch
import SudoersSpec.Syntax.Oracles

/-! Primitive agreement at the permission parser's external-call boundary. These hypotheses
say what the wrappers return, not what any token or parser returns. -/

open Aeneas Aeneas.Std Result
open SudoersSpec.Syntax (Canonical CharOracle ErrKind FmtOracle Oracles)

namespace SudoRsProofs.Parser

/-- Character operations and the selector facts about the Rust Unicode tables that are
needed at constructor call sites. -/
structure P2CharOracle (O : CharOracle) : Prop extends UnicodeOracle O where
  is_alphanumeric : ∀ c, core.char.methods.Char.is_alphanumeric c = ok (O.isAlphanumeric c)
  is_control : ∀ c, core.char.methods.Char.is_control c = ok (O.isControl c)
  nul_not_alphanumeric : O.isAlphanumeric '\x00' = false
  nul_not_uppercase : O.isUppercase '\x00' = false
  /-- Direct first characters of `Command` and uppercase extensions of `Meta` are not
  Unicode whitespace. -/
  command_start_nonWhitespace : ∀ c,
    (SudoersSpec.Syntax.SimpleCommand.accept1st c || O.isUppercase c) = true →
    O.isWhitespace c = false

/-- The three outcomes of the filesystem wrapper. -/
def canonicalOf : Canonical → sudo_rs.sudoers.tokens.Canonical
  | .err => .Unresolved
  | .ok s => .Resolved s
  | .okNonUtf8 => .NotUtf8

/-- Agreement for the existing primitive models. `A` is the very same abstraction used in
match/authorization refinement. `O.fmt` supplies Rust's formatting at diagnostic-render time;
its functions are not called by the extracted parser. -/
structure P2Oracle (A : GlobAbs) (O : Oracles) : Prop where
  chars : P2CharOracle O.char
  canonical : ∀ s, sudoers.tokens.canonical s = ok (canonicalOf (O.fs.canonicalize s))
  /-- A successful `canonicalize` yields an absolute path on the Unix target. -/
  canonical_absolute : ∀ s real,
    O.fs.canonicalize s = .ok real → real.toList.head? = some '/'
  /-- The checked wrapper preserves the pattern source on success and the rendered
  `glob::PatternError` (without the parser diagnostic prefix) on failure. -/
  compile_pattern : ∀ s : String, match O.glob.compile s with
    | none => ∃ pat, sudoers.tokens.compile_pattern s = ok (.Ok pat) ∧ A.pat pat = s
    | some e => sudoers.tokens.compile_pattern s = ok (.Err (.WildcardPattern e.render))
  /-- Unix conversion preserves the UTF-8 bytes of a representable parser argument and
  reads back as the same text. No bounded `OsString` is required for a larger Lean string.
  This fixes `A.os` only on UTF-8 bytes in range. It is compatible with `GlobOracle.os_inj`:
  non-UTF-8 byte strings can be given distinct equality keys outside the representable
  text range (for example, a fixed oversized ASCII prefix followed by one scalar per byte).
  Those keys are not UTF-8 decodings of the native values. -/
  os_string : ∀ s : String, s.utf8ByteSize ≤ Usize.max →
    ∃ os, sudoers.tokens.os_string s = ok os ∧
      os.inner.val = sudo_rs.stringBytes s ∧ A.os os = s

/-- The first three character agreements, for code that does not need the P2 selectors. -/
theorem P2CharOracle.unicode {O : CharOracle} (h : P2CharOracle O) : UnicodeOracle O :=
  h.toUnicodeOracle

/-- `NulInString` and `NulInPath` store an unformatted payload. Their diagnostic rendering
uses Rust's `Debug` for the matching type, supplied by the reference `FmtOracle`. This is
separate from `KindRel`, which does not discard the formatting difference. -/
def validationDiagnostic (fmt : FmtOracle) : RKind → Option ErrKind
  | .NulInString s => some (.sudoStringValidation ("Unexpected null character in input: " ++ fmt.debugStr s))
  | .NulInPath s => some (.sudoPathValidation ("Unexpected null character in input: " ++ fmt.debugPath s))
  | _ => none

theorem P2Oracle.compile {A : GlobAbs} {O : Oracles} (hO : P2Oracle A O) (s : String) :
    ∃ r, sudoers.tokens.compile_pattern s = ok r ∧
      ConstructRel A.pat r (SudoersSpec.Syntax.SimpleCommand.compile O s.toList) := by
  have hc := hO.compile_pattern s
  unfold SudoersSpec.Syntax.SimpleCommand.compile
  rw [String.ofList_toList]
  cases he : O.glob.compile s with
  | none =>
    rw [he] at hc
    obtain ⟨pat, e, hp⟩ := hc
    exact ⟨.Ok pat, e, hp⟩
  | some e =>
    rw [he] at hc
    exact ⟨.Err (.WildcardPattern e.render), hc, .wildcardPattern _⟩

end SudoRsProofs.Parser
