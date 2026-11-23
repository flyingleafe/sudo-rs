# `SudoersSpec.Syntax`: the reference parser

A transcription of the legacy sudoers parser (`src/sudoers/{char_stream,basic_parser,tokens,ast}.rs`
at `70fdb56b`) into total, executable Lean 4 (core only), for PLAN.md stage P0 (section 5.1): the
character stream, every combinator of `basic_parser.rs`, every token of `tokens.rs`, every
production of `ast.rs` including the `Defaults` settings parser, and the entry point
`parseSudoers`, the reference parser of a whole file. Settings and their modifiers are the shared
model `SudoersSpec.Settings` (`proofs/spec/SudoersSpec/Settings/`).

Everything is a definition; nothing uses `partial`, `unsafe` or `implemented_by`. Definitions
reduce in the kernel, so concrete runs can be checked with `by decide`.

## Entry point

```lean
def parseSudoersWith (D : Descriptions) (O : Oracles) (src : List Char) :
    Except String (List (Parsed Sudo))
def parseSudoers (O : Oracles) (src : List Char) : Except String (List (Parsed Sudo))
  -- = parseSudoersWith .release O src
```

`parse_lines::<Sudo>(&mut CharStream::new(text))` on the characters of `text`: the items in
order, or `.error msg` when Rust panics (the only panic is `unwrap` in `Command::construct`, see
below). `D` is the `UserFriendly::DESCRIPTION` table: `.release` for a release build, `.test` for
a `cfg(test)` build such as the parser dump of `proofs/parser/DUMP.md`. `O` bundles the oracles:

| Field | Stands for | Used by |
|---|---|---|
| `O.char : CharOracle` | `char::{is_alphanumeric, is_uppercase, is_numeric, is_control, is_whitespace}` | tokens, `trim_end`, `split_whitespace` |
| `O.fs : FsOracle` | `common::resolve::canonicalize` | `SimpleCommand::construct` (F-P5) |
| `O.glob : GlobOracle` | `glob::Pattern::new` (success, or `pos` and `msg` of the error) | `SimpleCommand::construct` |
| `O.fmt : FmtOracle` | `{:?}` of a `String` / `PathBuf` | the messages of `SudoString::new`, `SudoPath::try_from` |

Message texts produced outside the parser: the `Display` of `glob::PatternError` is modelled
(`GlobError.render`); the conditions and prefixes of the `SudoString::new` and
`SudoPath::try_from` errors are modelled, the `Debug` rendering comes from `O.fmt` (it needs
Unicode tables). Both errors need a NUL character in a token, which no token that reaches them
accepts with the Rust character classes (NUL is a control character).

## Files

| File | Rust | Content |
|---|---|---|
| `CharStream.lean` | `char_stream.rs` | `Stream`, `nextIf`, `eatChar`, `skipToNewline`, `peek`, `getPos`, `advance`, `new`, `newWithPos`; `Reaches`; position lemmas |
| `Status.lean` | `Status`, `Parsed`, `maybe`; all message texts | `ErrKind` (one constructor per message template), `ErrKind.render`, `Status`, `Parsed`, `maybe` |
| `CharOracle.lean` | `char` predicates | ASCII classes as definitions; `CharOracle`; `CharOracle.latin1` for tests |
| `Oracles.lean` | environment | `Oracles`, `FsOracle`, `Canonical`, `GlobOracle`, `GlobError`, `FmtOracle` |
| `Parser.lean` | `trait Parse`, `?`, `unrecoverable!`, loops | `Parser`, monad, primitives, `loop`, `whileMaybe`, `whileSome`, `nested`, `AParser`, `Parser.anchored` |
| `BasicParser.lean` | `basic_parser.rs` | whitespace, comments, `try_syntax` …, `trait Token` and its `Parse` impl, `parse_list`, `Many`, `parse_lines`, test helpers |
| `Tokens.lean` | `tokens.rs` | every token: `Username`, `DigitsU32`, `Numeric`, `Hostname`, `Meta<T>`, `AliasName`, `Command`, `SimpleCommand`, `DefaultName`, `EnvVar`, `QuotedStringParameter`, `QuotedIncludePath`, `IncludePath`, `StringParameter`, `ChDir`, `Unquoted<T>`; `SudoString::new`, `SudoPath::try_from`; `str` helpers |
| `AstNames.lean` | `ast_names.rs` | `Descriptions`, `.release`, `.test` |
| `Ast.lean` | `ast.rs` | `Qualified`, `Identifier`, `parse_meta`, `UserSpecifier`, `RunAs`, `MetaOrTag`, `CommandSpec`, the permission tuples, `Def<T>` |
| `SettingsParser.lean` | `impl Parse for defaults::SettingsModifier` | `parseVars`, `listItems`, `textItem`, `settingsModifier` |
| `Sudo.lean` | `ast.rs` | `ConfigScope`, `Directive`, `Sudo`; `parse_include`, `get_directive`, `impl Parse for Sudo`; `parseSudoers` |
| `Tests.lean`, `TestsGrammar.lean`, `TestsSudo.lean` | unit tests, legacy output | kernel-checked examples and `#guard` tests (section Evidence) |

## Rust item → Lean name

All names are in namespace `SudoersSpec.Syntax`; `Parser.x` is in `SudoersSpec.Syntax.Parser`.
Every definition's doc comment names its Rust item.

| Rust | Lean |
|---|---|
| `CharStream` | `Stream` (`rest : List Char`, `line col : Nat`) |
| `CharStream::new`, `new_with_pos` | `Stream.new`, `Stream.newWithPos` (`Stream.ofString` for a `&str`) |
| `CharStream::next_if`, `eat_char`, `peek`, `get_pos` | `Stream.nextIf`, `Stream.eatChar`, `Stream.peek`, `Stream.getPos`; as parsers `Parser.nextIf`, `Parser.eatChar`, `Parser.peek`, `Parser.getPos` |
| `CharStream::skip_to_newline` | `Stream.skipToNewline` (= `Stream.skipWhile (· != '\n')`), `Parser.skipToNewline` |
| `CharStream::advance` | `Stream.advance`, `Parser.advance` |
| `stream.clone()` / `*stream = begin_state` | `Parser.getStream`, `Parser.anchored` / `AParser.restore` |
| `CharStream::new_with_pos` on a second text | `Parser.nested p s` |
| `Span` | `SudoersSpec.Span` (`start`, `stop`) |
| `Status::{Fatal, Reject}` | `Status.fatal span kind`, `Status.reject`; message `kind.render` |
| `Parsed<T>` | `Parsed α := Except Status α` |
| `make`, `reject` | `pure`, `Parser.reject` |
| `unrecoverable!(stream, ..)` / `(pos = p, stream, ..)` | `Parser.fatalHere kind` / `Parser.fatalFrom p kind` |
| `maybe` | `Syntax.maybe` (on values), `Parser.maybe p`, `AParser.maybe p` |
| `trait Parse`, `T::parse` | `Parser α` value |
| `LeadingWhitespace`, `TrailingWhitespace`, `Comment` | `leadingWhitespace`, `trailingWhitespace` (loop body `trailingWhitespaceBody`), `comment` |
| `skip_trailing_whitespace` | `skipTrailingWhitespace` |
| `try_syntax`, `expect_syntax`, `is_syntax` | `trySyntax`, `expectSyntax`, `isSyntax` |
| `try_nonterminal`, `expect_nonterminal` | `tryNonterminal p`, `expectNonterminal description p` |
| `UserFriendly::DESCRIPTION` | a `String` argument; table `Descriptions` (`D.hostname`, …) |
| `trait Token` | `TokenSpec α` (`maxLen`, `construct : List Char → Except ErrKind α`, `accept`, `accept1st`, `allowEscape`, `escaped`) |
| `impl<T: Token> Parse for T`, `accept_escaped` | `token T`, `acceptEscaped T pred`, loop body `tokenBody` |
| `String::len` | `utf8Len` |
| `impl<T: Parse> Parse for Option<T>` | `parseOption p` |
| `parse_list` | `parseList sepBy max description p`, loop body `parseListBody` |
| `trait Many` (`SEP`, `LIMIT`) | `Many` (`sep := ','`, `limit := 127`); `hostnameMany`, `identifierMany`, `userSpecifierMany`, `runasCommandMany`, `hostsRunasCommandsMany` (`:`), `defMany` (`:`), `settingsModifierMany` |
| `impl Parse for Vec<T>` | `parseVec m description p` |
| `parse_lines` | `parseLines description p`, loop body `parseLinesBody` / `parseLinesItem` |
| `expect_complete`, `parse_string` (`#[cfg(test)]`) | `expectComplete`, `parseString` |
| `Username` | `usernameToken O`, `Username.{accept, accept1st, escaped, construct}` |
| `SudoString::new`, `SudoPath::try_from` | `sudoStringNew O`, `sudoPathTryFrom O` |
| `DigitsU32`, `Numeric` | `digitsU32Token`, `numericToken` |
| `Hostname` | `hostnameToken O`, `Hostname.{accept, construct, looksLikeIPv4}` |
| `Meta<T>` as a token | `metaToken O T`, `Meta.construct O T`, `metaMany` |
| `AliasName` | `aliasNameToken`, `AliasName.{accept1st, accept}` |
| `SimpleCommand` (`glob::Pattern`, kept as its text) | `simpleCommandToken O`, `SimpleCommand.{construct, compile, accept, accept1st, escaped}`, `SimpleCommand` (= `String`) |
| `Command` | `commandToken O`, `Command.construct O`, `Command.argPattern` |
| `DefaultName`, `EnvVar` | `defaultNameToken`, `envVarToken O` |
| `QuotedStringParameter`, `QuotedIncludePath`, `IncludePath`, `StringParameter` | `quotedStringParameterToken O`, `quotedIncludePathToken O`, `includePathToken O`, `stringParameterToken O` |
| `ChDir` | `chDirToken O`, `ChDir.construct O` |
| `Unquoted<T>` | `unquotedToken O T`, `Unquoted.construct T` |
| `str::rsplitn`, `split`, `split_whitespace`, `split_once`, `trim_end`, `starts_with(pred)` | `rsplitn`, `splitWhen`, `splitWhitespace O`, `splitOnce`, `trimEnd O`, `startsWithPred` |
| `uN::from_str_radix`, `str::parse::<uN>`, `char::to_digit` | `fromStrRadix radix bits`, `charToDigit` |
| `char::is_ascii_*` | `isAsciiDigit`, `isAsciiUppercase`, `isAsciiAlphanumeric`, `isAsciiHexdigit` |
| `impl Parse for Qualified<T>` | `qualified description p`, `qualifiedMany` |
| `Spec<T>`, `SpecList<T>` | `spec description p`, `specList m description p`; `specListHostname`, `specListUserSpecifier`, `specListIdentifier`, `specListSimpleCommand`, `specCommand` |
| `impl Parse for Identifier`, `Meta<Identifier>` | `identifier O D`, `metaIdentifier O D` |
| `parse_meta` | `parseMeta O p embed` |
| `impl Parse for UserSpecifier` (`parse_user`), `Meta<UserSpecifier>` | `userSpecifier O D` (`parseUser O D`), `metaUserSpecifier O D` |
| `impl Parse for RunAs` | `runAs O D` |
| `MetaOrTag` | `metaOrTag O D` |
| `impl Parse for CommandSpec` | `commandSpec O D`, loop body `commandSpecBody` |
| `impl Parse for (Option<RunAs>, CommandSpec)`, `(SpecList<Hostname>, Vec<..>)` | `runasCommand O D`, `hostsRunasCommands O D`; the list of the latter `permissions O D` |
| `is_reserved_alias`, `impl Parse for Def<T>`, `Defs<T>` | `isReservedAlias`, `defParser m description p`, `defs D m description p` |
| `impl Parse for defaults::SettingsModifier` (`parse_vars`, `list_items`, `text_item`) | `settingsModifier O D` (`parseVars`, `parseVarsBody`, `listItems`, `textItem`) |
| `ConfigScope`, `Directive`, `Directive::could_be_username`, `Sudo` | `ConfigScope`, `Directive`, `Directive.couldBeUsername`, `Sudo` |
| `parse_include` (`get_path`) | `parseInclude O D` (`getPath`) |
| `get_directive` | `getDirective O D key s0` (scope: `defaultsScope`) |
| `impl Parse for Sudo` | `sudo O D` (`sudoHash`, `sudoMain`) |
| `parse_lines::<Sudo>` | `parseSudoersWith D O`, `parseSudoers O` |

`ErrKind` covers the 30 `unrecoverable!` sites of `basic_parser.rs` and `ast.rs` (one of them,
`expect_complete`, is `#[cfg(test)]`), every `Err` text a `Token::construct` can return, and
`unwrapNone`, the panic of `Command::construct` (not a diagnostic: `parseSudoersWith` turns it
into `.error`).

Not transcribed: the `@socket` directive and `PeerSpec` (feature `unstable-remote-sudoers`, off
by default).

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

Two common shapes have their progress proof built in:
`while let Some(a) = maybe(q)? { body }` and `while is_syntax(c)? {..}` are
`Parser.whileMaybe q hq k finish st` with `hq : q.Consumes` ("on success `q` consumed at least
one character"); `while let Some(a) = try_nonterminal::<Option<T>>(stream)? { body }` is
`Parser.whileSome q hq k finish st` with `hq : q.ConsumesSome`
(`tryNonterminal_parseOption_consumesSome` gives it from `T`'s `Consumes`). `Consumes` composes:
`Consumes.bind_left`, `Consumes.bind_right`, and the lemmas `*_consumes` of the productions.

Two productions leave the plain scheme:

- `get_directive` sets the stream back to a clone taken at the start of the line
  (`*stream = begin_state`, `Defaults@`). It is an `AParser s0`: a parser whose results are
  reached from the anchor `s0` rather than from its input; `Parser.anchored f` runs `f s0` with
  `s0` the input and is a `Parser` again (`sudoMain` is anchored). Every `Parser` lifts into
  `AParser s0` (`MonadLift`), so the code is written in `do` notation as well.
- The quoted user of `UserSpecifier::parse` runs `parse_user` on a second stream over the
  unquoted text: `Parser.nested p s` returns `p`'s result on `s` and does not move the outer
  stream.

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
   `p : Parser α` for `T: Parse`, a description from `D : Descriptions` for `T: UserFriendly`, a
   `TokenSpec` for `T: Token`, a `Many` for `T: Many`, `O : Oracles` (or `O.char`) for the
   environment. A new token is a `TokenSpec` value; its parser is `token spec`.
2. Mind short-circuiting: `(← e)` inside `a && (← e)` runs `e` unconditionally; write
   `if a then e else pure false` (see `acceptEscaped`). Prefer explicit `let b ← e` lines
   before an `if`.
3. Each Rust loop becomes `whileMaybe` or `whileSome` (if it has that shape) or `loop` with a
   body and a `Progressive` proof. The proof chains `run_bind_eq_ok` and uses the strict-progress
   facts (`run_eatChar_true_lt`, `run_nextIf_some_lt`, `Consumes.maybe_some`,
   `trySyntax_consumes`, …); see `trailingWhitespaceBody_progressive` and
   `parseLinesBody_progressive`.
4. A production that restores a cloned stream is an `AParser s0` under `Parser.anchored`; one
   that parses a second text uses `Parser.nested`.
5. A new message is a new `ErrKind` constructor with its `render` case; the existing ones cover
   the whole legacy parser.
6. Add kernel-checked examples (`by decide`) and `#guard` tests; expected values for `#guard`s
   come from the legacy Rust code.

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

Parser (`Parser.*`, `AParser.*`): `run_pure`, `run_bind`, `run_bind_of_ok`, `run_bind_of_error`,
`run_bind_eq_ok`, `run_bind_eq_error`, `run_*` for every primitive (`run_nested`,
`run_anchored`, `AParser.run_lift`, `AParser.run_restore`, `AParser.run_maybe`), `suffix`,
`length_le`, `reaches_of_run`, `length_le_of_run`, `Consumes.*`, `Consumes.maybe_consumesSome`,
`loopFuel_eq`, `loop_run`, `loop_invariant`, `whileMaybeBody_progressive`,
`whileSomeBody_progressive`.

Combinators: `leadingWhitespace_run` and `comment_run` (closed forms), `leadingWhitespace_ok`,
`trailingWhitespaceBody_progressive`, `trailingWhitespace_ne_reject`,
`skipTrailingWhitespace_ne_reject`, `trySyntax_consumes`, `trySyntax_reject` (rejects only
without consuming), `isSyntax_true_lt`, `tryNonterminal_consumes`,
`tryNonterminal_parseOption_consumesSome`, `expectNonterminal_ne_reject`,
`expectNonterminal_consumes`, `acceptEscaped_consumes`, `token_consumes`, `parseList_consumes`,
`parseList_ne_nil` (at least one element), `parseVec_consumes`, `parseLinesItem_lt`,
`parseLinesBody_progressive`, `parseLinesItem_ok`, `parseLines_ok` (`parse_lines` returns `Ok`,
and no element is `Reject`).

Productions: `qualified_consumes`, `metaHostname_consumes`, `specListHostname_consumes`,
`identifier_consumes`, `parseMeta_consumes`, `parseUser_consumes`, `userSpecifier_consumes`,
`metaOrTag_consumes`; `parseSudoersWith_ne_reject`, `parseSudoers_ne_reject` (no item of a
whole file is `Reject`).

## Evidence

- Kernel-checked: the lemmas above; `example … := by decide` in `Tests.lean` (49: the unit tests
  of `char_stream.rs` and `basic_parser.rs`, the core cases), `TestsGrammar.lean` (30: tokens,
  productions, the oracles, the opaque messages, the panic marker) and `TestsSudo.lean` (21:
  `Sudo`, `Defaults` scopes and settings, F-P1, F-P3, F-P4, the panic of the whole parse).
- Tests (`#guard`): `Tests.lean` 113, `TestsGrammar.lean` 313, `TestsSudo.lean` 177. Their
  expected strings are the output of the legacy Rust code at `70fdb56b` on the same inputs (the
  core: the Rust files copied verbatim into a scratch harness; the rest: a scratch test module
  of the crate, a `cfg(test)` build, so descriptions are `"elem"`). Lean and Rust agreed on every
  case; every production and every `ErrKind` but `garbageAtEndOfLineChar` (core tests),
  `nonUtf8Filesystem`, `sudoStringValidation`, `sudoPathValidation` and `unwrapNone` (kernel
  examples with oracles that reach them) is among them, and so are the rows of PLAN.md 3.3.
  The scratch harnesses are not committed.
- `CharOracle.latin1` was compared with the pinned `rustc` on all 256 code points `U+0000..U+00FF`
  for the five predicates: identical.
- Whole files: the differential comparison of `proofs/parser/DUMP.md` (`proofs/parser/P0.md`).

## Rust behaviour transcribed as is

Lexical layer:

- `TrailingWhitespace::parse` does not skip comments, although its doc comment says so. It reads
  any `\` as the start of a line continuation, so a backslash right after whitespace that is not
  followed by a newline is `stray escape sequence`, and `expect_syntax` reports that as
  `expecting 'c' but found 'x'` after the backslash.
- `accept_escaped`: `\` newline in a token whose class has no space returns `Reject` after
  consuming both characters. At the start of a token the token rejects having consumed input;
  inside a token the token ends and the two characters are gone.
- The token length check runs before the character is appended, on the UTF-8 length: a token can
  be up to 3 bytes longer than `MAX_LEN`.
- `parse_lines`: after an error the rest of the line up to the newline character is skipped,
  but the newline itself is not consumed in that iteration; the next iteration starts at it (for
  `Sudo` a `LineComment` item; for other productions a second diagnostic). Blanks after the last
  newline end the loop without a diagnostic. A carriage return before the newline is garbage.
- In `#[cfg(test)]` builds every `DESCRIPTION` is `"elem"` (`Descriptions.test`).

Tokens:

- `Hostname::construct` refuses every name of at most four dot-separated parts that are all
  non-empty, at most 3 bytes and `char::is_numeric` (`123`, `1.2.3`, not only `1.2.3.4`).
- `Meta<T>` widens the classes of `T` by `char::is_uppercase`; the `ALL`/alias decision uses the
  text without trailing whitespace, `T::construct` the raw text.
- `Command` tokens contain spaces and most punctuation: `ALL !/usr/bin/su` in a `Cmnd_Alias` is
  one token that is not `ALL`, so `Command::construct` refuses it. Arguments: a final `*` allows
  further arguments, a final `""` none; `^` is refused only as the first argument; `list` takes
  no arguments.
- `Command::construct` unwraps the first whitespace-separated word. The parser never gives it a
  text without one with the Rust character classes: the first character of a command token is
  `/`, `s`, `l` or an escaped character, and every command token follows trailing whitespace,
  which does not let a backslash through. The panic is kept (`ErrKind.unwrapNone`); a kernel
  example reaches it with an oracle in which `/` is whitespace.
- `SimpleCommand::construct` canonicalizes an existing path (F-P5); `"/"` becomes `/*`.
- `DigitsU32` refuses values above `u32::MAX` ("value too large"); after `#` in `Sudo::parse`
  that makes the line a comment (F-P4).

Productions:

- `RunAs`: `unwrap_or_default` discards every error of the user list, fatal ones included, and
  the stream stays where the list stopped (`(+x)` reports `expecting ')' but found 'x'`); a `:`
  followed by a rejected group list gives no groups, the `:` consumed.
- Quoted users: the text between the quotes is re-escaped for `Username` and parsed again from
  the position after the opening quote; whatever `parse_user` does not read is ignored
  (`"a+b"` is the user `a`), `%:` inside quotes is a group whose name starts with `:`, positions
  in errors count the inserted backslashes, and a text that is not a user is a `Reject` after
  consuming (F-P3).
- The span of an ignored tag (`LOG_INPUT` …) runs from the keyword to the end of the whitespace
  after it.
- At most 127 tags, 127 list elements, 127 variables in a quoted `env_keep` list.
- `get_directive`: every name that starts with `Defaults` begins a `Defaults` line
  (`Defaultsfoo`); a scope (`:`, `!`, `>`) only directly after the 8 characters `Defaults` on the
  same line; `Defaults@` goes back to the start of the line and 9 characters forward, so the host
  list is read from that position whatever the first user was made of.
- `parse_include`: an unquoted path must be followed by a newline (end of input or a comment
  is an error).
- Settings: `list_items` expects `=` before checking that the setting is a list; `umask` needs a
  leading `0` and one more digit (`0` is refused, `00` is 0); a timeout without `.` must fit in
  `u64` seconds (18 nines are refused), `.5` and `5.` are refused; values after `=` end at `,`,
  so `secure_path=a,b` continues with a setting `b`.

## Open questions

- `CharOracle` and the other oracles have no hypotheses. Proofs about tokens with Unicode classes
  may need some (for example, agreement with the ASCII classes on ASCII characters, or NUL
  being a control character, which makes the `SudoString`/`SudoPath` errors unreachable); they
  would be a separate `Prop` structure, as `Oracle.SudoRsHosts` is for the decision.
- `Status.lean` derives `DecidableEq` for `Except` (needed by `decide`); if core adds that
  instance the derivation must go.
- The value of `loopFuel` at fuel 0 (`Reject`) is unreachable from `loop` (`loopFuel_eq`).
- The unreachability of `ErrKind.unwrapNone` is argued above, not proved.
