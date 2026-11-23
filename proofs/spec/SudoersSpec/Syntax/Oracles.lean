import SudoersSpec.Syntax.CharOracle

/-!
# The oracles of the reference parser (PLAN.md section 5.3)

Parsing calls code whose result depends on the environment or on tables outside the parser:

| Oracle | Rust | Used by |
|---|---|---|
| `CharOracle` | the Unicode `char` predicates | tokens, `trim_end`, `split_whitespace` |
| `FsOracle.canonicalize` | `common::resolve::canonicalize` | `SimpleCommand::construct` |
| `GlobOracle.compile` | `glob::Pattern::new` | `SimpleCommand::construct` |
| `FmtOracle` | `{:?}` of a `String` / `PathBuf` | the messages of `SudoString::new`, `SudoPath::try_from` |

Decisions for the message texts produced outside the parser:

* `SudoString::new`, `SudoPath::try_from` (`src/common/{string,path}.rs`): when they fail
  (a NUL character) the message is `"Unexpected null character in input: {x:?}"`. The condition
  and the prefix are modelled; the `Debug` rendering needs Unicode tables (`escape_debug`), so
  `FmtOracle` supplies it.
* `glob::PatternError`'s `Display` is the simple `"Pattern syntax error near position {pos}:
  {msg}"` and is modelled (`GlobError.render`); the oracle supplies whether the pattern compiles
  and, if not, `pos` and `msg`.
* `"non-UTF8 characters in filesystem"` is a literal of `SimpleCommand::construct`; the oracle
  says whether the canonical path is UTF-8.
-/

namespace SudoersSpec.Syntax

/-- The result of `common::resolve::canonicalize(path)` as `SimpleCommand::construct` uses it. -/
inductive Canonical where
  /-- `Err(_)`: the path does not resolve; the command is kept as written. -/
  | err
  /-- `Ok(p)` with `p.to_str() == Some(s)`. -/
  | ok (s : String)
  /-- `Ok(p)` with `p.to_str() == None`. -/
  | okNonUtf8
  deriving DecidableEq, Repr

/-- The file system as seen at parse time (F-P5: the AST depends on it). -/
structure FsOracle where
  /-- `common::resolve::canonicalize`. -/
  canonicalize : String → Canonical

/-- `glob::PatternError { pos, msg }`. -/
structure GlobError where
  pos : Nat
  msg : String
  deriving DecidableEq, Repr

/-- `impl Display for glob::PatternError` (glob 0.3.4). -/
def GlobError.render (e : GlobError) : String :=
  "Pattern syntax error near position " ++ toString e.pos ++ ": " ++ e.msg

/-- `glob::Pattern::new`. The compiled pattern keeps its source text (`Pattern::as_str`), which
is what the AST stores, so only success or the error is needed. -/
structure GlobOracle where
  /-- `none`: `Pattern::new(p)` is `Ok`; `some e`: it is `Err(e)`. -/
  compile : String → Option GlobError

/-- `Debug` formatting (`{:?}`), quotes included. -/
structure FmtOracle where
  /-- `<str as Debug>::fmt`. -/
  debugStr : String → String
  /-- `<PathBuf as Debug>::fmt`. -/
  debugPath : String → String

/-- The oracle bundle `O` of the reference parser. -/
structure Oracles where
  char : CharOracle
  fs : FsOracle
  glob : GlobOracle
  fmt : FmtOracle

end SudoersSpec.Syntax
