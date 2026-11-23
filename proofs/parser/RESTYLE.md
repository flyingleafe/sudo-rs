# Restricted-style parser: M1 report and style guide for M2

Stage P1 of `PLAN.md`, Rust side (sections 3.2, 6, 7), milestone M1: the lexical layer of the
sudoers parser and the `SpecList<Hostname>` production rewritten so that Charon and Aeneas
translate them, the legacy parser kept as a test oracle, and the evidence that the rewrite
preserves behaviour. Milestone M2 (every other token and production) follows this guide.

Evidence kinds used below: **test** (the equivalence harness and the fuzz smoke run cover only
the inputs they ran) and **extraction** (Charon and Aeneas translate the code and the generated
Lean builds). Nothing in this file is a proof.

## 1. What exists

| Item | Where |
|---|---|
| Live parser, M1 part in the restricted style | `src/sudoers/char_stream.rs` (all), `src/sudoers/basic_parser.rs` (all), `src/sudoers/tokens.rs` (`Hostname`, `AliasName`, `Meta<T>` and their helpers), `src/sudoers/ast.rs` (`Qualified<T>::parse`, `host_list`) |
| Live parser, M2 part, adapted only | the rest of `tokens.rs` and `ast.rs`: closures, `format!` and the `str` API are still there |
| Legacy parser (ground truth, `70fdb56b` with the `Defaults` block of the base) | `src/sudoers/legacy/`, compiled for `cfg(any(test, fuzzing))` only |
| Equivalence harness | `src/sudoers/equiv.rs` (printer, `compare`), `src/sudoers/equiv/corpus.rs` (texts of the unit tests, seeded generator, mutations) |
| Fuzz target | `fuzz/fuzz_targets/parser_equiv.rs`, entry point `fuzz_api::sudoers_parser_equiv` |
| Extraction roots and opaque items | `Cargo.toml` `[package.metadata.charon]` |
| External models | `proofs/lean/SudoRs/FunsExternal.lean` (section "Sudoers parser: characters and strings"), rows in `proofs/lean/ASSUMPTIONS.md` |

## 2. Style guide

The rules below were all exercised by M1; each says what fails otherwise.

### 2.1 Idioms that extract

| Idiom | Example in M1 |
|---|---|
| Cursor over `&[char]` with `pos`, `line`, `col`; methods `peek`, `bump(c)`, `eat_char`, `skip_to_newline`, `get_pos`, `advance` | `char_stream.rs` |
| `match stream.peek() { Some(c) if pred(c) => { stream.bump(c); … } _ => … }` instead of `next_if(closure)` | `LeadingWhitespace::parse`, `accept_escaped` |
| Every loop in the form `let mut more = true; while more { … }`, or `while ok && i < len { … }` over locals; the exit is a flag | all loops |
| `?` and `return` outside loops only; inside a loop the error goes to `failure: Option<Status>` and the loop ends; after the loop `match failure { Some(s) => Err(s), None => … }` | token loop, `parse_list`, `Qualified::parse` |
| An error kind (`ErrorKind`, data) instead of a formatted message; spans with `fatal_here(stream, kind)` / `fatal_from(start, stream, kind)` | `basic_parser.rs` |
| `match` on `Result`/`Option` instead of `is_ok`, `is_err`, `is_some`, `unwrap_or`: those std methods have no Aeneas model (`#[allow(clippy::redundant_pattern_matching)]` where clippy objects) | `line_follows`, `expect_syntax`, `is_syntax` |
| `matches!(x, Ok(_))` (expands to a `match`) | `parse_lines` |
| A `first: bool` argument instead of a `fn(char) -> bool` parameter | `accepts::<T>(first, c)` |
| Traits with associated constants and default methods; blanket `impl<T: Token> Parse for T`; generic impls whose constants come from `T` (`Meta<T>::MAX_LEN = T::MAX_LEN`) | `Token`, `Many`, `Meta<T>` |
| `&'static str` constants (`UserFriendly::DESCRIPTION`) and string literals: they become `Str` | `ErrorKind::Expected(T::DESCRIPTION)` |
| `String::new`, `String::push`, `String::len` (modelled), `Vec::new`, `Vec::push`, `Vec::len`, slice indexing (Aeneas library) | token loop, `string_of` |
| A named monomorphic function for an instance the proof needs | `ast::host_list` = `try_nonterminal::<SpecList<Hostname>>` |
| A loop that the generic code calls through a trait, nested calls of functions that contain loops | `TrailingWhitespace` calls `LeadingWhitespace::parse` in its loop |
| Integer variables with an explicit type (`let mut parts: usize = 1`); an unannotated literal defaults to `i32` and gives `I32` arithmetic in Lean | `resembles_ipv4` |
| Character literals in Latin-1 except the backslash: `'\n'` and `'\t'` are printed raw inside the quotes and Lean accepts them | `eat_char('\n')` |

### 2.2 Idioms that do not extract, and the way round

| Construct | Outcome with the pinned toolchain | Way round |
|---|---|---|
| A loop whose condition calls a function on the stream, with a large body: `while line_follows(stream) { … }` in `parse_lines` | Aeneas "Could not match the contexts"; the function body is dropped | compute the condition into a flag before the loop and at the end of the body (`let mut more = line_follows(stream); while more { …; more = line_follows(stream); }`) |
| `?` or `return` inside a loop | "Early returns inside of loops are not supported yet" | failure flag, see 2.1 |
| `'\\'` | printed as `'\'`; Lean rejects the file | `basic_parser::escape_char()`, opaque for Charon, modelled as `ok '\\'` (section 5) |
| Character literals above `U+00FF` | Aeneas: "non-ASCII chars … are unsupported" (`ExtractTypes.ml`) | compare with a constant through a predicate, or keep the comparison outside the extracted code |
| `'\''` | not tried; by the same printing rule it would become `'''` | avoid, or route through an opaque constant as for `'\\'` |
| `c as u32`, `92u8 as char` | "Unreachable" (spike) | comparisons on `char`; `char::to_digit` |
| Closures over the stream, `fn` pointers, `Box<dyn …>` | "Unexpected bound region", "Arrow types are not supported", "Dynamic trait types are not supported" | named functions, `first: bool`; data types with an `apply` function (the `Defaults` refactor) |
| `str` pattern API (`contains`, `starts_with(fn)`, `rsplitn`, `trim_end`, `split_whitespace`) | `core::str::pattern::Pattern` unimplemented | a character loop over `chars_of(&text)` (opaque, modelled as `String.toList`) |
| `str::chars().collect()` and other iterator adapters | `Chars::next` and `collect` are `opaque` in the Aeneas library | `chars_of` (one trusted model) |
| `format!` | not modelled | `ErrorKind` with payload; `Display for ErrorKind` is the only renderer and is never extracted |
| `Result::is_ok`, `Option::is_some`, `Option::map_or` … | no Aeneas model | `match` |

### 2.3 Behaviour preservation rules for M2

- One Rust function per legacy function where possible; helpers only for loops (one loop per
  function is not required, but a loop must not be nested inside another loop's condition).
- The same order of stream operations as the legacy code: the position at which a fatal error
  is raised is observable (spans).
- No machine arithmetic the legacy code did not have unless the style forces it. M1 added: the
  cursor's `pos += 1` (bounded by the slice length), `i += 1` loop counters over slices,
  `len = i + 1` in `trimmed_len`, and `parts`/`part_len` in `resembles_ipv4` (bounded by 5 and 7
  while the loop runs). The legacy `line += 1`, `col += 1` stay.
- The legacy token loop compares the UTF-8 byte length of the text so far with `MAX_LEN`; the
  live loop keeps a `String` accumulator and `text.len()` for that reason.
- Transitional: `unrecoverable!` now builds `ErrorKind::Message(format!(…))`, and the M2
  `construct` functions return `Err(ErrorKind::Message(…))`. M2 replaces each by a variant of
  `ErrorKind` and extends `Display for ErrorKind` with its exact legacy text.
- `CharStream` is `Clone`, not `Copy` (clippy `clone_on_copy` in `ast.rs`); backtracking in M2 is
  `let saved = stream.clone(); … *stream = saved;`.
- Tests that build streams from text use the test-only `CharStream::new(&str)` (it leaks a copy
  of the characters); live code calls `chars_of` once and `CharStream::from_chars(&chars)`.
- Every M2 change runs the harness of section 4 (`cargo test --lib sudoers::equiv`) and the
  extraction with the new item added to `start_from`.

## 3. Legacy to live mapping

| Legacy (`src/sudoers/legacy/…`) | Live | Change |
|---|---|---|
| `CharStream { iter: Peekable<Chars>, line, col }` | `CharStream { src: &[char], pos, line, col }` | cursor; `new(&str)` is now test-only, live code uses `from_chars`/`new_with_pos` over `chars_of(&text)` |
| `CharStream::next_if(f)` | `peek` + `bump(c)` | no closure |
| `eat_char`, `skip_to_newline`, `peek`, `get_pos`, `advance` | same names | loops with a flag |
| `Status::Fatal(Span, String)` | `Status::Fatal(Span, ErrorKind)` | `kind.to_string()` is the legacy text |
| `unrecoverable!(…)` | `fatal_here` / `fatal_from` with an `ErrorKind`; the macro remains for M2 with `ErrorKind::Message` | |
| `LeadingWhitespace::parse` (`"\t ".contains(c)`) | same | `c == '\t' \|\| c == ' '` |
| `TrailingWhitespace::parse` (`unrecoverable!` in the loop) | same | `stray` flag |
| `Comment::parse`, `skip_trailing_whitespace`, `try_syntax`, `try_nonterminal`, `maybe`, `make`, `reject` | same | none |
| `expect_syntax` (`is_err()`, `c.to_string()` or `"EOF"`) | same | `ErrorKind::Expecting(syntax, found)` |
| `is_syntax` (`maybe(..)?.is_some()`) | same | `match` |
| `expect_nonterminal` (`"expected {DESCRIPTION}"`) | same | `ErrorKind::Expected(T::DESCRIPTION)` |
| `Token::construct(String) -> Result<Self, String>` | `-> Result<Self, ErrorKind>` | |
| nested `accept_escaped::<T>(pred: fn(char) -> bool, …)`, `const ESCAPE` | `accept_escaped::<T>(first: bool, …)`, `accepts::<T>(first, c)`, `escape_char()` | |
| `impl<T: Token> Parse for T` (`?` inside `while let`) | same, `failure` flag | |
| `impl Parse for Option<T>` | same | none |
| `parse_list` (`?` and `unrecoverable!` in the loop) | same, `failure` flag | |
| `impl Parse for Vec<T>`, `Many` | same | none |
| `parse_lines` (`while LeadingWhitespace::parse(stream).is_ok()`, closure for the error) | same, `more` flag and `line_follows` | |
| `Hostname::construct` (`rsplitn(5, '.')`, `take(4).all(…)`, `next().is_none()`) | same; `resembles_ipv4(&chars_of(&text))` | `ErrorKind::HostIpv4` |
| `Hostname::accept` (`".-_".contains(c)`) | `c == '.' \|\| c == '-' \|\| c == '_'` | |
| `AliasName` | same | `construct` type |
| `Meta<T>::construct` (`trim_end`, `== "ALL"`, `starts_with(fn)`, `chars().skip(1).all(fn)`) | `trimmed_len`, `is_all`, `is_alias_name`, `string_of` over `chars_of(&raw)` | |
| `Qualified<T>::parse` (`?` in `while`) | same, `failure` flag | |
| `(SpecList<Hostname>, …)::parse`: `try_nonterminal(stream)?` | `host_list(stream)?` | the same call, named |
| `read_sudoers`: `CharStream::new(&buffer)` | `chars_of(&buffer)`, `CharStream::from_chars` | |
| `Sudoers` diagnostics: `message` | `kind.to_string()` | |

AST types are unchanged (names, fields, representation); `Span` is unchanged. No type of the
decision proofs changed. `ChDir::construct` (opaque, used by `authorization`) changed its error
type to `ErrorKind`; its model and the proof of `construct_ok_eq` (statement unchanged) follow.

## 4. Behaviour preservation evidence (test)

`equiv::compare(text)` runs the legacy and the live `parse_lines::<Sudo>` twice each and prints
every result: all AST fields, every span, the message text of each fatal error (live: the
rendered `ErrorKind`), and for every `Defaults` modifier the fields of `Settings::dump_fields`
it changes, applied once to `Settings::default()` and once to a second base in which every
negatable setting is negated and every list has extra entries. A panic of either side is caught
and compared as a value (in `cfg(test)`).

| Corpus | Texts | Result |
|---|---:|---|
| String literals of the sudoers, defaults and policy sources and their tests (with and without a final newline), the line groups of `sudoer![..]`, `pass!([..])`, `FAIL!([..])`, `SYNTAX!([..])`, `docs/sudoers.example` | 1,403 | no difference |
| Generated from a grammar (rules with user, host, runas, tag and command lists; the five alias kinds; `Defaults` with every scope; includes; comments; continuations; long tokens at the 255- and 1024-byte limits in 1- to 4-byte characters; host lists at the 127-item limit), seed `0x5eed0f5ed0e50001` | 8,000 | no difference |
| Mutations of the generated texts, 1 to 3 per text | 16,000 | no difference |

Mutation operators: delete a character; insert a character of the alphabet; replace a character
by one of the alphabet; duplicate a slice of up to 8 characters; swap two adjacent characters;
truncate; splice (this text's prefix, another generated text's suffix); delete a range of up to
12 characters. The alphabet has the syntax characters, blank, tab, newline, carriage return,
NUL, DEL, and the Unicode characters `Ⅷ` (upper case and numeric), `É`, `ß`, `ǅ` (title case),
`İ`, `٣` (numeric), U+2003, U+00A0, U+0085 (white space), U+1F600 and U+1D400 (4-byte).

The summary the tests print shows what the corpora reached: of the generated texts 5,767 have a
fatal error, the others none; they produced 3,476 rules, 2,746 alias definitions, 3,092
`Defaults` lines, 1,723 includes and 133 distinct fatal messages; the mutated texts produced 926
distinct fatal messages. Neither parser panicked on any text. The three tests take about 13 s
in the debug build (`cargo test --lib sudoers::equiv -- --nocapture` prints the summaries).

Under `cfg(test)` every `UserFriendly::DESCRIPTION` is `"elem"`; the descriptions themselves are
compared only by the fuzz target, which builds without `cfg(test)`.

Fuzz smoke run: `parser_equiv` built with `fuzz/run.sh build parser_equiv`, seeded with the
`sudoers_parse` seeds and the sudoers dictionary, run for 55 s: 48,771 executions, 5,897 edges,
no difference, no crash. The campaign belongs on the cluster:
`FUZZ_SECONDS=1800 fuzz/run.sh campaign parser_equiv`.

The existing unit tests pass unchanged, apart from `assert_remote_failure` (feature
`unstable-remote-sudoers`, compares the rendered kind) and the test-only `impl Token for
String` in `basic_parser.rs`.

## 5. Extraction

Roots added to `start_from`: `basic_parser::parse_lines`, `expect_syntax`, `is_syntax`,
`expect_nonterminal`, `parse_list`, `ast::host_list`. Opaque items added: `char_stream::chars_of`,
`basic_parser::escape_char`.

### 5.1 Extracted M1 functions (Lean names, `Funs.lean`)

The cursor is `structure sudoers.char_stream.CharStream { src : Slice Char, pos line col :
Std.Usize }`; `sudoers.basic_parser.Status = Fatal (Span) (ErrorKind) | Reject`; a production is
`structure sudoers.basic_parser.Parse (Self) { parse : CharStream → Result ((core.result.Result
Self Status) × CharStream) }`. Loops become `…_loop` functions defined by `partial_fixpoint`
that receive the cursor's fields separately.

| Rust | Lean | Type |
|---|---|---|
| `CharStream::peek` | `sudoers.char_stream.CharStream.peek` | `CharStream → Result (Option Char)` |
| `CharStream::bump` | `sudoers.char_stream.CharStream.bump` | `CharStream → Char → Result CharStream` |
| `CharStream::eat_char` | `sudoers.char_stream.CharStream.eat_char` | `CharStream → Char → Result (Bool × CharStream)` |
| `CharStream::skip_to_newline` | `….skip_to_newline` (+ `_loop`) | `CharStream → Result CharStream` |
| `CharStream::get_pos` | `….get_pos` | `CharStream → Result (Usize × Usize)` |
| `LeadingWhitespace::parse` | `sudoers.basic_parser.LeadingWhitespace.Insts.Sudo_rsSudoersBasic_parserParse.parse` (+ `_loop`) | `CharStream → Result ((Result LeadingWhitespace Status) × CharStream)` |
| `TrailingWhitespace::parse` | `sudoers.basic_parser.TrailingWhitespace.Insts.Sudo_rsSudoersBasic_parserParse.parse` (+ `_loop`) | idem |
| `Comment::parse` | `sudoers.basic_parser.Comment.Insts.Sudo_rsSudoersBasic_parserParse.parse` | idem |
| `skip_trailing_whitespace` | `sudoers.basic_parser.skip_trailing_whitespace` | `CharStream → Result ((Result Unit Status) × CharStream)` |
| `try_syntax`, `expect_syntax` | `sudoers.basic_parser.try_syntax`, `….expect_syntax` | `Char → CharStream → Result ((Result Unit Status) × CharStream)` |
| `is_syntax` | `sudoers.basic_parser.is_syntax` | `Char → CharStream → Result ((Result Bool Status) × CharStream)` |
| `try_nonterminal` | `sudoers.basic_parser.try_nonterminal` | `Parse T → CharStream → Result ((Result T Status) × CharStream)` |
| `expect_nonterminal` | `sudoers.basic_parser.expect_nonterminal` | `Parse T → UserFriendly T → CharStream → …` |
| `maybe`, `make`, `reject`, `fatal_here`, `fatal_from` | `sudoers.basic_parser.{maybe,make,reject,fatal_here,fatal_from}` | |
| `accepts`, `accept_escaped` | `sudoers.basic_parser.accepts`, `….accept_escaped` | `Token T → Bool → Char → Result Bool`; `Token T → Bool → CharStream → Result ((Result Char Status) × CharStream)` |
| `impl<T: Token> Parse for T` | `sudoers.basic_parser.Parse.Blanket.parse` (+ `_loop`), instance `sudoers.basic_parser.Parse.Blanket` | `Token T → CharStream → Result ((Result T Status) × CharStream)` |
| `impl Parse for Vec<T>` | `alloc.vec.Vec.Insts.Sudo_rsSudoersBasic_parserParse.parse` | `Parse T → Many T → UserFriendly T → CharStream → Result ((Result (Vec T) Status) × CharStream)` |
| `parse_list` | `sudoers.basic_parser.parse_list` (+ `_loop`) | `Parse T → UserFriendly T → Char → Usize → CharStream → Result ((Result (Vec T) Status) × CharStream)` |
| `parse_lines`, `line_follows` | `sudoers.basic_parser.parse_lines` (+ `_loop`), `….line_follows` | `Parse T → UserFriendly T → CharStream → Result (Vec (Result T Status) × CharStream)` |
| `Hostname` token | `sudoers.tokens.Hostname.Insts.Sudo_rsSudoersBasic_parserToken.{accept,construct}`, `sudoers.tokens.resembles_ipv4` (+ `_loop`) | `construct : String → Result (Result Hostname ErrorKind)` |
| `AliasName` classes | `sudoers.tokens.AliasName.Insts.Sudo_rsSudoersBasic_parserToken.{accept_1st,accept}` | `Char → Result Bool` |
| `impl<T: Token> Token for Meta<T>` | instance `sudoers.tokens.Meta.Insts.Sudo_rsSudoersBasic_parserToken`, `….construct`, `….accept`, `….accept_1st`; helpers `sudoers.tokens.{trimmed_len,is_all,is_alias_name,string_of}` | `construct : Token T → String → Result (Result (Meta T) ErrorKind)` |
| `impl Parse for Qualified<T>` | `sudoers.ast.Qualified.Insts.Sudo_rsSudoersBasic_parserParse.parse` (+ `_loop`) | `Parse T → UserFriendly T → CharStream → Result ((Result (Qualified T) Status) × CharStream)` |
| `host_list` | `sudoers.ast.host_list` | `CharStream → Result ((Result (Vec (Qualified (Meta Hostname))) Status) × CharStream)` |

`AliasName::construct` is not reached: `Meta<T>` uses only the character classes of `AliasName`.
The `AliasName` token as a whole is reached in M2 through `MetaOrTag` and `Def<T>`.

### 5.2 External models

All are definitions except three `opaque` Unicode predicates; each has a row in
`ASSUMPTIONS.md`.

| Rust | Lean model |
|---|---|
| `char::is_ascii_uppercase`, `is_ascii_digit`, `is_ascii_alphanumeric` | `Char.isUpper`, `isDigit`, `isAlphanum` |
| `char::len_utf8` | 1 / 2 / 3 / 4 by the bounds `0x80`, `0x800`, `0x10000` |
| `char::is_uppercase`, `is_numeric`, `is_whitespace` | `opaque` (character oracle) |
| `String::new`, `String::push`, `String::len` | `""`, `String.push`, `utf8ByteSize` (fails outside `usize`) |
| `char_stream::chars_of` (opaque for Charon) | `String.toList` as a `Vec` |
| `basic_parser::escape_char` (opaque for Charon) | `'\\'` |

The `'\\'` defect: of the three ways round, post-processing the generated file would put a text
rewrite of every generated file into the trusted base, and a newer Aeneas does not fix it (see
section 7). An opaque Rust function with a one-line Lean definition adds one item that can be
checked by reading it (`fn escape_char() -> char { '\\' }` against `def … := ok '\\'`), changes no
pipeline script, and the backslash enters the extracted code nowhere else. The cost is one
function call where the legacy code used a constant.

## 6. Measured sizes

| Measure | Value |
|---|---:|
| Rust lines changed in the parser (`git diff --numstat` against the base: added/removed) | `char_stream.rs` 62/20, `basic_parser.rs` 250/76, `tokens.rs` 130/49, `ast.rs` 23/4, `mod.rs` 8/3 |
| Non-test lines of the rewritten files | `char_stream.rs` 82, `basic_parser.rs` 514 (comments included) |
| Generated Lean for the M1 functions (81 definitions, without doc comments) | 1,156 lines |
| `Funs.lean` / `Types.lean` growth | +1,640 / +188 lines (doc comments included) |
| Extraction time (`proofs/extract.sh`) | 16 to 70 s wall clock (the longer runs recompile the crate for Charon); Aeneas reports about 19 s |

Generated lines of the larger M1 definitions: `accept_escaped` 87, `Qualified…parse` 63,
`parse_lines_loop` 51, `parse_list_loop` 46, `LeadingWhitespace…parse_loop` 37,
`Parse.Blanket.parse` 37, `Parse.Blanket.parse_loop` 37, `resembles_ipv4_loop` 36,
`TrailingWhitespace…parse_loop` 29, `parse_list` 28, `Meta…construct` 27, `try_nonterminal` 26;
the remaining 69 definitions have 2 to 24 lines each.

## 7. Aeneas pin: recommendation

Keep `8f4466db` for P1 and M2. Evidence:

- The two toolchain limits M1 met are handled within the pin: early returns in loops by the
  failure-flag idiom (the code stays close to the legacy shape), the backslash literal by one
  opaque constant.
- Upstream `main` at `fb44cb40` (2026-11-23) prints character literals exactly as the pin does
  (`src/extract/ExtractTypes.ml`, `VChar` case: `"'" ^ String.make 1 c ^ "'"`, and characters
  above `U+00FF` are rejected), so a bump does not remove the backslash workaround.
- Upstream `main` no longer raises "Early returns inside of loops are not supported yet" in
  `PrePasses.ml`, so a bump would allow `?` inside loops. Upstream issue #1221 (open, filed
  2026-07-18) reports that the Lean backend emits a bodyless `axiom` instead of failing for a
  `return` nested two loop levels deep; with that open, the restricted style is the safer input
  anyway.
- A bump changes the Lean library and toolchain under the existing decision proofs
  (`permission_flags_eq`, `authorization_eq`, the sanitizer and escaping proofs), which would
  have to be re-validated; nothing in M1 or M2 needs it.

Revisit after M2 if the failure-flag idiom makes the refinement proofs markedly longer than the
legacy shape would; that is a measurement for the proof stage.

## 8. Notes for the next stages

- M2 scope: every other `Token` (`Username`, `DigitsU32`, `Numeric`, `Command`, `SimpleCommand`,
  `DefaultName`, `EnvVar`, the string parameters, include paths, `ChDir`, `Unquoted<T>`) and every
  other production of `ast.rs`. `SimpleCommand::construct` needs the oracle parameters of
  `PLAN.md` section 6 (`canonicalize`, `glob::Pattern::new`); `UserSpecifier::parse` already
  re-parses a quoted token through a nested cursor (`CharStream::new_with_pos(&chars, pos)`).
- The `Defaults` block of the legacy snapshot is the legacy-style parser at this branch's base.
  When the settings-modifier refactor lands, re-take that block from the new base, adapt the
  printer in `equiv.rs` (`settings_modifier`) to the data type, and rerun the harness.
- `CharStream::new(&str)` is test-only; a new test module that builds streams from text keeps
  working unchanged.
- For the proof: `Status` is in the result, not in a separate error channel (`Result
  ((core.result.Result T Status) × CharStream)`); Aeneas `fail` arises only from arithmetic
  overflow, slice indexing, `chars_of`/`String::len` on texts beyond `usize`, and the opaque
  character predicates. The token text is a Lean `String` built by `String.push`, and the length
  check reads `utf8ByteSize`.
