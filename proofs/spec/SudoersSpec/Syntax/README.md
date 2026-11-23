# `SudoersSpec.Syntax`: the reference parser

A transcription of the legacy sudoers parser (`src/sudoers/{char_stream,basic_parser,tokens,ast}.rs`
at `70fdb56b`) into total, executable Lean 4 (core only), for PLAN.md stage P0 (section 5.1). This
directory holds the core: the character stream, every combinator of `basic_parser.rs`, the token
machinery, the tokens `Hostname` and `AliasName`, `Meta<T>`, `Qualified<T>` and
`SpecList<Hostname>`. The rest of the grammar (`ast.rs`, the other tokens, `Sudo`) is added on
top of it in the same style.

Everything is a definition; nothing uses `partial`, `unsafe` or `implemented_by`. Definitions
reduce in the kernel, so concrete runs can be checked with `by decide`.

## Files

| File | Rust | Content |
|---|---|---|
| `CharStream.lean` | `char_stream.rs` | `Stream`, `nextIf`, `eatChar`, `skipToNewline`, `peek`, `getPos`, `advance`, `new`, `newWithPos`; `Reaches`; position lemmas |
| `Status.lean` | `basic_parser.rs` `Status`, `Parsed`, `maybe`; all message texts | `ErrKind` (one constructor per message template), `ErrKind.render`, `Status`, `Parsed`, `maybe` |
| `CharOracle.lean` | `char` predicates | ASCII classes as definitions; `CharOracle` (5 Unicode predicates); `CharOracle.latin1` for tests |
| `Parser.lean` | `trait Parse`, `?`, `unrecoverable!`, loops | `Parser` (function + `reaches` proof), monad, primitives, `loop`, `whileMaybe`, `Consumes` |
| `BasicParser.lean` | `basic_parser.rs` | whitespace, comments, `try_syntax` …, `trait Token` and its `Parse` impl, `parse_list`, `Many`, `parse_lines`, test helpers |
| `Tokens.lean` | `tokens.rs` (part) | `aliasNameToken`, `hostnameToken`, `metaToken`; `rsplitn`, `trimEnd` |
| `AstNames.lean` | `ast_names.rs` | `Descriptions` (`UserFriendly::DESCRIPTION`), `.release`, `.test` |
| `Ast.lean` | `ast.rs` (part) | `qualified`, `spec`, `specList`, `metaHostname`, `specListHostname` |
| `Tests.lean` | unit tests | 49 kernel-checked `example`s, 113 `#guard` tests against legacy Rust output |

## Rust item → Lean name

All names are in namespace `SudoersSpec.Syntax`; `Parser.x` is in `SudoersSpec.Syntax.Parser`.

| Rust | Lean |
|---|---|
| `CharStream` | `Stream` (`rest : List Char`, `line col : Nat`) |
| `CharStream::new`, `new_with_pos` | `Stream.new`, `Stream.newWithPos` (`Stream.ofString` for a `&str`) |
| `CharStream::next_if`, `eat_char`, `peek`, `get_pos` | `Stream.nextIf`, `Stream.eatChar`, `Stream.peek`, `Stream.getPos`; as parsers `Parser.nextIf`, `Parser.eatChar`, `Parser.peek`, `Parser.getPos` |
| `CharStream::skip_to_newline` | `Stream.skipToNewline` (= `Stream.skipWhile (· != '\n')`), `Parser.skipToNewline` |
| `CharStream::advance` | `Stream.advance`, `Parser.advance` |
| `stream.clone()` | `Parser.getStream` |
| `Span` | `SudoersSpec.Span` (`start`, `stop`) |
| `Status::{Fatal, Reject}` | `Status.fatal span kind`, `Status.reject`; message `kind.render` |
| `Parsed<T>` | `Parsed α := Except Status α` |
| `make`, `reject` | `pure`, `Parser.reject` |
| `unrecoverable!(stream, ..)` / `(pos = p, stream, ..)` | `Parser.fatalHere kind` / `Parser.fatalFrom p kind` |
| `maybe` | `Syntax.maybe` (on values), `Parser.maybe p` (on a parser) |
| `trait Parse`, `T::parse` | `Parser α` value |
| `LeadingWhitespace`, `TrailingWhitespace`, `Comment` | `leadingWhitespace`, `trailingWhitespace` (loop body `trailingWhitespaceBody`), `comment` (all `Parser Unit`) |
| `skip_trailing_whitespace` | `skipTrailingWhitespace` |
| `try_syntax`, `expect_syntax`, `is_syntax` | `trySyntax`, `expectSyntax`, `isSyntax` |
| `try_nonterminal`, `expect_nonterminal` | `tryNonterminal p`, `expectNonterminal description p` |
| `UserFriendly::DESCRIPTION` | a `String` argument; table `Descriptions.release` / `Descriptions.test` |
| `trait Token` | `TokenSpec α` (`maxLen`, `construct : List Char → Except ErrKind α`, `accept`, `accept1st`, `allowEscape`, `escaped`) |
| `impl<T: Token> Parse for T`, `accept_escaped` | `token T`, `acceptEscaped T pred`, loop body `tokenBody` |
| `String::len` | `utf8Len` |
| `impl<T: Parse> Parse for Option<T>` | `parseOption p` |
| `parse_list` | `parseList sepBy max description p`, loop body `parseListBody` |
| `trait Many` (`SEP`, `LIMIT`) | `Many` (`sep := ','`, `limit := 127`) |
| `impl Parse for Vec<T>` | `parseVec m description p` |
| `parse_lines` | `parseLines description p : Parser (List (Parsed α))`, loop body `parseLinesBody` / `parseLinesItem` |
| `expect_complete`, `parse_string` (`#[cfg(test)]`) | `expectComplete`, `parseString` |
| `AliasName` | `aliasNameToken`, `AliasName.accept1st`, `AliasName.accept` |
| `Hostname` | `hostnameToken O`, `Hostname.accept`, `Hostname.construct O`, `Hostname.looksLikeIPv4 O`, `hostnameMany` |
| `Meta<T>` as a token | `metaToken O T`, `Meta.construct O T`, `metaMany` |
| `impl Parse for Qualified<T>` | `qualified description p`, `qualifiedMany` |
| `Spec<T>`, `SpecList<T>` | `spec description p`, `specList m description p` |
| `SpecList<Hostname>` | `specListHostname O D` (`Meta<Hostname>`: `metaHostname O`) |
| `str::rsplitn`, `trim_end`, `starts_with(pred)` | `rsplitn`, `trimEnd O`, `startsWithPred` |
| `char::is_ascii_*` | `isAsciiDigit`, `isAsciiUppercase`, `isAsciiAlphanumeric`, `isAsciiHexdigit` |
| `char::{is_alphanumeric, is_uppercase, is_numeric, is_control, is_whitespace}` | fields of `CharOracle` |

`ErrKind` covers the 30 `unrecoverable!` sites of `basic_parser.rs` and `ast.rs` (one of them,
`expect_complete`, is `#[cfg(test)]`) and every `Err` text a `Token::construct` can return. The
texts of `SudoString::new`, `SudoPath::try_from` and `glob::PatternError` are carried as opaque
strings (`sudoStringValidation`, `sudoPathValidation`, `wildcardPatternError`).

## Recursion scheme

A production is `Parser α`:

```lean
structure Parser (α : Type) where
  run : Stream → Parsed α × Stream
  reaches : ∀ s, Stream.Reaches s (run s).2
```

`Stream.Reaches s s'` is `∃ n, s.advance n = s'`: the output is the input advanced over some
characters. It gives the suffix property (`Parser.suffix`) and the position of the output
(`Stream.Reaches.getPos_eq`). `Parser` is a monad (`do` with `←` is Rust's `?`) and every
primitive carries its `reaches` proof, so a production written in `do` notation needs no proof.

The grammar has no recursive nonterminal; recursion only comes from Rust loops. A loop is
`Parser.loop body hb st`: `body : σ → Parser (Step σ β)` is one iteration (state `σ` = the
loop's mutable variables; `Step.done b` leaves the loop with `b`, `Step.next st'` continues), and
`hb : Progressive body` says that an iteration returning `next` has consumed input. `loop` runs
`loopFuel` with fuel `rest.length + 1`, by structural recursion on the fuel, so it reduces in the
kernel; the fuel never runs out (`loopFuel_eq`), and users see only

- `Parser.loop_run`: one iteration, then `loop` again (the fuel-free unfolding equation);
- `Parser.loop_invariant`: induction over the iterations with an invariant.

The common shape `while let Some(a) = maybe(q)? { body }` (and `while is_syntax(c)? {..}`) is
`Parser.whileMaybe q hq k finish st`, which needs only `hq : q.Consumes` ("on success `q`
consumed at least one character"); its progress proof is `whileMaybeBody_progressive`.
`Consumes` composes: `Consumes.bind_left`, `Consumes.bind_right`, `tryNonterminal_consumes`,
`qualified_consumes`, `parseList_consumes`, `token_consumes`.

The two `while next_if(..)` loops of `char_stream.rs` and `LeadingWhitespace` are
`Stream.skipWhile`, structural on the list `rest` (`skipWhile_eq` is the loop equation,
`skipWhile_eq_advance` the closed form).

Definitions that are not loops are plain non-recursive definitions; unfold them with
`simp only [name, Parser.run_bind, …]` or use the inversion lemmas `Parser.run_bind_eq_ok` and
`Parser.run_bind_eq_error`. Note that `do` notation pushes the continuation of a
`let x ← if c then A else B` into both branches.

## How to add a production

1. Write it in `do` notation over the primitives and existing productions, one Lean definition
   per Rust item, with a doc comment naming the item. Trait parameters become value parameters:
   `p : Parser α` for `T: Parse`, a `description` (from `Descriptions`) for `T: UserFriendly`, a
   `TokenSpec` for `T: Token`, a `Many` for `T: Many`, `O : CharOracle` when a Unicode predicate
   is involved. A new token is a `TokenSpec` value; its parser is `token spec`.
2. Mind short-circuiting: `(← e)` inside `a && (← e)` runs `e` unconditionally; write
   `if a then e else pure false` (see `acceptEscaped`).
3. Each Rust loop becomes `whileMaybe` (if it has that shape) or `loop` with a body and a
   `Progressive` proof. The proof chains `run_bind_eq_ok` and uses the strict-progress facts
   (`run_eatChar_true_lt`, `run_nextIf_some_lt`, `Consumes.maybe_some`, `trySyntax_consumes`, …);
   see `trailingWhitespaceBody_progressive` and `parseLinesBody_progressive`.
4. If a production restores an earlier stream (`*stream = begin_state` in `get_directive`),
   `getStream` gives the saved state but no primitive sets it: build that production with
   `Parser.mk run proof` and prove `reaches` by hand (the restored state is reached from the
   production's input, so the property still holds).
5. A new message is a new `ErrKind` constructor with its `render` case; the existing ones
   already cover the whole legacy parser.
6. Add kernel-checked examples (`by decide`) and `#guard` tests to `Tests.lean`; expected values
   for `#guard`s should come from the legacy Rust code.

## Lemma inventory

Stream (`Stream.*`):

- single steps: `pop_newline`, `pop_other`, `nextIf_cons`, `nextIf_eq_some`, `nextIf_eq_none`,
  `eatChar_eq`, `eatChar_true`, `eatChar_false`, `pop_length_lt`;
- `advance`: `advance_rest` (`= rest.drop n`), `advance_getPos` (`= posAfter (rest.take n) pos`),
  `advance_add`, `advance_succ`, `advance_of_length_le`;
- `skipToNewline`: `skipWhile_eq` (loop equation), `skipWhile_eq_advance`, `skipToNewline_rest`
  (`= rest.dropWhile (· != '\n')`), `skipToNewline_getPos` (same line, column plus the number of
  skipped characters), `skipToNewline_lt`;
- `Reaches`: `refl`, `trans`, `pop`, `advance`, `nextIf`, `eatChar`, `skipWhile`, `suffix`,
  `length_le`, `eq_advance` (a reached stream is `s.advance (len s - len s')`), `getPos_eq`
  (`s.rest = consumed ++ s'.rest` and `s'.getPos = posAfter consumed s.getPos`),
  `eq_of_length_eq`.

Parser (`Parser.*`): `run_pure`, `run_bind`, `run_bind_of_ok`, `run_bind_of_error`,
`run_bind_eq_ok`, `run_bind_eq_error`, `run_*` for every primitive, `suffix`, `length_le`,
`reaches_of_run`, `length_le_of_run`, `Consumes.*`, `loopFuel_eq`, `loop_run`,
`loop_invariant`, `whileMaybeBody_progressive`.

Combinators: `leadingWhitespace_run` and `comment_run` (closed forms), `leadingWhitespace_ok`,
`trailingWhitespaceBody_progressive`, `trailingWhitespace_ne_reject`,
`skipTrailingWhitespace_ne_reject`, `trySyntax_consumes`, `trySyntax_reject` (rejects only
without consuming), `isSyntax_true_lt`, `tryNonterminal_consumes`, `expectNonterminal_ne_reject`,
`expectNonterminal_consumes`, `acceptEscaped_consumes`, `token_consumes`, `parseList_consumes`,
`parseVec_consumes`, `parseLinesItem_lt`, `parseLinesBody_progressive`, `parseLinesItem_ok`,
`parseLines_ok` (`parse_lines` returns `Ok`, and no element is `Reject`), `qualified_consumes`,
`metaHostname_consumes`, `specListHostname_consumes`.

## Evidence

- Kernel-checked: the lemmas above; 49 `example … := by decide` in `Tests.lean` (the unit tests
  of `char_stream.rs` and `basic_parser.rs`, and the cases listed there).
- Tests: 113 `#guard`s whose expected strings are the output of the legacy Rust code on the same
  inputs: `char_stream.rs` and `basic_parser.rs` and the items `Hostname`, `AliasName`, `Meta<T>`,
  `Qualified<T>` copied verbatim from `70fdb56b` into a scratch harness (release descriptions,
  test tokens as in `Tests.lean`), compiled with the pinned `rustc`. Lean and Rust agreed on all
  113 lines (result, span, message, final position, remaining input). The harness is not
  committed.
- `CharOracle.latin1` was compared with the pinned `rustc` on all 256 code points `U+0000..U+00FF`
  for the five predicates: identical.

## Rust behaviour transcribed as is

- `TrailingWhitespace::parse` does not skip comments, although its doc comment says so.
- `expect_syntax` replaces every error of `try_syntax`, also a fatal `stray escape sequence`
  raised after the character was consumed: `=\x` gives `expecting '=' but found 'x'` after the
  backslash.
- `accept_escaped`: `\` newline in a token whose class has no space returns `Reject` after
  consuming both characters. At the start of a token the token rejects having consumed input;
  inside a token the token ends and the two characters are gone.
- The token length check runs before the character is appended, on the UTF-8 length: a token can
  be up to 3 bytes longer than `MAX_LEN`.
- `Hostname::construct` refuses every name of at most four dot-separated parts that are all
  non-empty, at most 3 bytes and `char::is_numeric` (`123`, `1.2.3`, not only `1.2.3.4`).
- `Meta<T>` widens the classes of `T` by `char::is_uppercase`, so `Meta<Hostname>` accepts
  non-ASCII uppercase letters that `Hostname` does not. The `ALL`/alias decision uses the text
  without trailing whitespace, `T::construct` the raw text.
- `parse_lines`: after an error the rest of the line up to the newline character is skipped,
  but the newline itself is not consumed in that iteration; the next iteration starts at it. For
  a production that rejects an empty line (any production but `Sudo`) this gives a second
  diagnostic (`expected …`) for the same line. Blanks after the last newline end the loop
  without a diagnostic.
- In `#[cfg(test)]` builds every `DESCRIPTION` is `"elem"` (`Descriptions.test`).

## Open questions

- The opaque messages (`sudoStringValidation`, `sudoPathValidation`, `wildcardPatternError`)
  need a model of `{:?}` on strings and paths and of `glob::PatternError`'s `Display` when the
  tokens that produce them are added (or an oracle returning the text).
- `CharOracle` has no hypotheses. Proofs about tokens with Unicode classes may need some (for
  example, agreement with the ASCII classes on ASCII characters); they would be a separate
  `Prop` structure, as `Oracle.SudoRsHosts` is for the decision.
- `Status.lean` derives `DecidableEq` for `Except` (needed by `decide`); if core adds that
  instance the derivation must go.
- The differential test must choose `Descriptions.test` or `.release` according to how the Rust
  dump is built.
- The value of `loopFuel` at fuel 0 (`Reject`) is unreachable from `loop` (`loopFuel_eq`).
