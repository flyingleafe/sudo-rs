# Restricted-style parser: P1/P2 report and style guide

Stages P1 and P2 of `PLAN.md`, Rust side (sections 3.2, 6, 7). M1 was the lexical layer and the
`SpecList<Hostname>` production; M2a added the rest of the tokens of a permission line and its
productions (`Identifier`, users, runas, tags, commands, the rule itself). Everything here is
rewritten so that Charon and Aeneas translate it, the legacy parser is kept as a test oracle,
and the evidence that the rewrite preserves behaviour. M2b (`Def<T>`, `get_directive`,
`parse_include`, `Sudo::parse` beyond the named entries, the `Defaults` settings parser) follows
this guide.

Evidence kinds used below: **test** (the equivalence harness and the fuzz smoke run cover only
the inputs they ran) and **extraction** (Charon and Aeneas translate the code and the generated
Lean builds). Nothing in this file is a proof.

## 1. What exists

| Item | Where |
|---|---|
| Live parser, P1/P2 part in the restricted style | `src/sudoers/char_stream.rs` (all), `src/sudoers/basic_parser.rs` (all), `src/sudoers/tokens.rs` (`Username`, `DigitsU32`, `Hostname`, `AliasName`, `Meta<T>`, `Command`, `SimpleCommand`, `ChDir`, `Unquoted<T>`, `StringParameter`'s classes), `src/sudoers/ast.rs` (`Qualified<T>::parse`, `Identifier`, `parse_meta`, `UserSpecifier`, `Meta<UserSpecifier>`/`Meta<Identifier>`, `RunAs`, `MetaOrTag`, `CommandSpec`, the two rule tuples, `host_list`, `user_list`, `expect_user_list`, `permissions`) |
| Live parser, M2b part, adapted only | `Def<T>`, `get_directive`, `parse_include`, `Sudo::parse`, the `Defaults` settings parser, and the tokens only it uses (`Numeric`, `DefaultName`, `EnvVar`, `QuotedStringParameter`, `IncludePath`, `QuotedIncludePath`): closures, `format!` and the `str` API are still there |
| Legacy parser (ground truth, `70fdb56b`, with the `Defaults` block of the base and its data API) | `src/sudoers/legacy/`, compiled for `cfg(any(test, fuzzing))` only |
| Equivalence harness | `src/sudoers/equiv.rs` (printer, `compare`, directed diagnostic cases, kind-coverage table), `src/sudoers/equiv/corpus.rs` (texts of the unit tests, seeded generator, mutations) |
| Fuzz target | `fuzz/fuzz_targets/parser_equiv.rs`, entry point `fuzz_api::sudoers_parser_equiv` |
| Extraction roots and opaque items | `Cargo.toml` `[package.metadata.charon]` |
| External models | `proofs/lean/SudoRs/FunsExternal.lean` (sections "Sudoers parser: characters and strings", "Permission-line parser externals"), rows in `proofs/lean/ASSUMPTIONS.md` |

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
| A small data type instead of a constructor function or a closure where the branch is chosen by a parsed flag | `ChDirForm` (`classify_chdir`), `TagClass` (`tag_class`) |
| A trait with one method instead of `impl FnOnce(SudoString) -> T` | `FromUsername` (`parse_meta`) |
| Word scanning as ranges into the token text (`Vec<(usize, usize)>`), encoding a word only where it is needed | `split_words`, `word_text`, `os_strings` |
| A `match` on a nested scrutinee split into two `match`es, or moved into its own function, when Aeneas says "Could not match the contexts" | `command_tag_step` (`CommandSpec`), `TagClass` (`MetaOrTag`) |
| A `match` whose arms all *consume* the scrutinee (`Err(_status)` rather than `Err(_)`) when a `do`-block temporary is dropped | `RunAs::parse` |
| One loop per function whose body does one thing; a two-phase scan written as repeated calls of a scanning function | `skip_word_class`, `split_words` |

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
| `matches!(c, 'a' \| 'b' \| ' ')` on a `char` | Aeneas "Unsupported switch scrutinee" | `c == 'a' \|\| c == 'b' \|\| …` (`Username::escaped`, `SimpleCommand::escaped`, `StringParameter::escaped`) |
| `bool`-valued expression assigned to a loop variable (`found = c == '?' \|\| …`) | the assignment is read as `Prop` after the `if`/`else` shaping | `if c == '?' \|\| … { found = true; }` (`has_glob_char`) |
| `Vec::with_capacity`, `str::split_whitespace`, `str::contains`, `str::starts_with(fn)`, `str::ends_with`, `str::trim_end`, `str::pop` | iterator or `Pattern` API | a character scan over `chars_of`, or a range scan (`split_words`, `classify_chdir` for the byte-level checks) |
| `Path`/`PathBuf` conversions (`to_str`, `into_os_string().into_string()`), `std::fs`, `glob::Pattern::new`, `OsString::from` | not modelled (opaque types, file-system state) | one thin wrapper per call, opaque for Charon, with a hand-written model or `opaque` constant (`canonical`, `compile_pattern`, `os_string`, `sudo_path`, `classify_chdir`) |
| A `Token` impl whose `construct` reads the text through `chars_of` while an existing theorem states success for *every* `String` | a `fail` case the theorem cannot absorb (`chars_of` fails above `usize::MAX`) | keep that one constructor opaque with a total model over the Lean `String` (`ChDir`), or state a representability hypothesis in the new proofs |

### 2.3 Behaviour preservation rules for M2

- One Rust function per legacy function where possible; helpers only for loops (one loop per
  function is not required, but a loop must not be nested inside another loop's condition).
- The same order of stream operations as the legacy code: the position at which a fatal error
  is raised is observable (spans).
- No machine arithmetic the legacy code did not have unless the style forces it. P1 added: the
  cursor's `pos += 1` (bounded by the slice length), `i += 1` loop counters over slices,
  `len = i + 1` in `trimmed_len`, and `parts`/`part_len` in `resembles_ipv4` (bounded by 5 and 7
  while the loop runs). P2 added: `kept = n_args - 1` (only when `n_args ≥ 1`), `last_end -
  last_start` (a word range), `value.checked_mul(10)`/`checked_add(digit)` in `parse_u32`
  (the overflow test `str::parse::<u32>` does) and `end - 1` in `os_strings` (`end ≥ 1`). The
  legacy `line += 1`, `col += 1` stay.
- The legacy token loop compares the UTF-8 byte length of the text so far with `MAX_LEN`; the
  live loop keeps a `String` accumulator and `text.len()` for that reason.
- Transitional state after M2a: `unrecoverable!` still builds `ErrorKind::Message(format!(…))`,
  but only M2b sites use it (`get_directive`, the `Defaults` settings parser, `parse_include`).
  Every error site of P1/P2 has its own `ErrorKind` variant with the exact legacy text; no
  `ErrorKind::Message` is produced by a P1/P2 construct or production.
- `CharStream` is `Clone`, not `Copy` (clippy `clone_on_copy` in `ast.rs`); backtracking is
  `let saved = stream.clone(); … *stream = saved;`.
- Tests use `CharStream::with_text` to borrow a cursor for one call. The character buffer is
  freed on return. Live code calls `chars_of` once and borrows the result with `from_chars`.
- Every change runs the harness of section 4 (`cargo test --lib sudoers::equiv`) and the
  extraction with the new item added to `start_from`.

## 3. Legacy to live mapping

| Legacy (`src/sudoers/legacy/…`) | Live | Change |
|---|---|---|
| `CharStream { iter: Peekable<Chars>, line, col }` | `CharStream { src: &[char], pos, line, col }` | `from_chars`/`new_with_pos` borrow a character slice; test code can use `with_text` |
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
| `Username::construct` (`strip_suffix('$').unwrap_or(&text).contains('$')`, `SudoString::new`) | `embedded_dollar(&chars_of(&text))`, `sudo_string` | `ErrorKind::EmbeddedDollar`, `ErrorKind::NulInString` |
| `Username::accept`/`escaped` (`".-_@$".contains(c)`, `matches!`) | `c == '.' \|\| …`, `c == escape_char() \|\| …` | |
| `DigitsU32::construct` (`str::parse::<u32>`) | `parse_u32(&chars_of(&s))` with `to_digit(10)` and checked arithmetic | `ErrorKind::ValueTooLarge` |
| `Command::construct` (`split_whitespace`, `OsString::from`, `first().is_some_and`, `last()`, `pop`, `into_boxed_slice`, `as_str() == "list"`) | `split_words` (ranges), `any_glob`, `os_strings`, `os_string`, `compile_pattern`; `command.as_str() == "list"` becomes `is_list` on the command text | `ErrorKind::{RegexNotSupported, GlobInArguments, ListArguments}` |
| `SimpleCommand::construct` (`==`, `starts_with`, `ends_with`, `pop`, `push_str`, `canonicalize`, `glob::Pattern::new`) | `equals_text`, `starts_with_text`, `string_of`, `String::push`, `canonical`, `compile_pattern` | `ErrorKind::{DigestNotSupported, RegexNotSupported, FullyQualifiedPath, NonUtf8Path, WildcardPattern}` |
| `SimpleCommand::accept`/`escaped`, `Command::accept`/`escaped` | `!c.is_control()` chains, `escape_char()` | |
| `ChDir::construct` (`==`, `contains`, `SudoPath::try_from`) | `classify_chdir` + `sudo_path` (both opaque, total models) | `ErrorKind::{StarInPath, NulInPath}` |
| `Unquoted<T>::construct` (`for ch in text.chars()`) | a `while` over `chars_of(&text)` | `escape_char()` |
| `StringParameter::accept`/`escaped` | same, `escape_char()` | |
| `Identifier::parse` | unchanged (it only uses `eat_char` and two nonterminals) | |
| `parse_meta` (`impl FnOnce(SudoString) -> T` argument) | the `FromUsername` trait | one generic function, two instances |
| `UserSpecifier::parse` (nested `fn parse_user`, `ctor` function, quoted form) | the same nested function; a `nonunix: bool` instead of `ctor`; the quoted form keeps the nested cursor over `chars_of(&text)` | `ErrorKind::NetgroupsNotSupported`; the contract deviation of F-P3 is unchanged |
| `RunAs::parse` (`unwrap_or_default`, `maybe(..and_then(..))?`) | explicit `match`es (see 2.1) | |
| `MetaOrTag::parse` (closure `switch`, one large `match`) | `tag_class` (a data type) + `equals_keyword` + `switch` | `ErrorKind::{TagNotSupported, SelinuxNotSupported, UnsupportedModifier}` |
| `CommandSpec::parse` (`while let Some(..)`, `return` in the loop) | `command_tag_step` + a loop over `failure`/`found` | `ErrorKind::TooManyTags` |
| `(Option<RunAs>, CommandSpec)::parse` (`runas.is_some()`) | `match runas` | |
| `(SpecList<Hostname>, …)::parse` / `Sudo::parse` choices | named entries `permissions`, `user_list`, `expect_user_list` | the same calls, named |

AST types are unchanged (names, fields, representation); `Span` is unchanged. No type of the
decision proofs changed. `ChDir::construct` is now **extracted**: its text checks moved behind
two opaque wrappers (`classify_chdir`, `sudo_path`) that are total on the Lean `String`, so the
statement of `construct_ok_eq` is unchanged; the proof now unfolds the real constructor, and
`Authorization.lean` gained `open sudo_rs` because extracted names live in that namespace.

## 4. Behaviour preservation evidence (test)

`equiv::compare(text)` runs the legacy and the live `parse_lines::<Sudo>` twice each and prints
every result: all AST fields, every span, the message text of each fatal error (live: the
rendered `ErrorKind`), and for every `Defaults` modifier the fields of `Settings::dump_fields`
it changes, applied once to `Settings::default()` and once to a second base in which every
negatable setting is negated and every list has extra entries. A panic of either side is caught
and compared as a value (in `cfg(test)`).

| Corpus | Texts | Result |
|---|---:|---|
| String literals of the sudoers, defaults and policy sources and their tests (with and without a final newline), the line groups of `sudoer![..]`, `pass!([..])`, `FAIL!([..])`, `SYNTAX!([..])`, `docs/sudoers.example` | 1,393 | no difference |
| Generated from a grammar (rules with user, host, runas, tag and command lists; the five alias kinds; `Defaults` with every scope; includes; comments; continuations; long tokens at the 255- and 1024-byte limits in 1- to 4-byte characters; host lists at the 127-item limit; command specs at the 127-tag limit), seed `0x5eed0f5ed0e50001` | 8,000 | no difference |
| Mutations of the generated texts, 1 to 3 per text | 16,000 | no difference |
| Directed cases (`diagnostic_kinds`, `non_utf8_canonical_path`): one text per error kind, boundary cases of `Command`, and a scratch tree with a non-UTF-8 path component | 30 | no difference |

Mutation operators: delete a character; insert a character of the alphabet; replace a character
by one of the alphabet; duplicate a slice of up to 8 characters; swap two adjacent characters;
truncate; splice (this text's prefix, another generated text's suffix); delete a range of up to
12 characters. The alphabet has the syntax characters, blank, tab, newline, carriage return,
NUL, DEL, and the Unicode characters `Ⅷ` (upper case and numeric), `É`, `ß`, `ǅ` (title case),
`İ`, `٣` (numeric), U+2003, U+00A0, U+0085 (white space), U+1F600 and U+1D400 (4-byte).

The summary the tests print shows what the corpora reached: of the generated texts 5,872 have a
fatal error, the others none; they produced 3,414 rules, 2,842 alias definitions, 3,104
`Defaults` lines, 1,683 includes and 129 distinct fatal messages; the mutated texts produced 861
distinct fatal messages. Neither parser panicked on any text. The tests take about 14 s in the
debug build (`cargo test --lib sudoers::equiv -- --nocapture` prints the summaries).

### 4.1 Error-kind coverage

`corpus_kind_coverage` parses the three corpora with the live parser and prints the table below
(hits per corpus); the test fails if a kind that a text can reach is missing. `NonUtf8Path`
needs a file system (the scratch tree), `SuperfluousWhitespace` is the sentinel that ends the
line loop of `parse_lines` (it never reaches a result; `basic_parser`'s
`superfluous_whitespace_at_eof` covers it), and the two NUL kinds are unreachable from text: no
token class that can reach `SudoString::new` or `SudoPath::try_from` accepts a control character,
so `nul_in_constructor_arguments` checks them at the constructor level, including that their text
equals the legacy `Error` text.

| Kind | unit | gen | mut |
|---|---:|---:|---:|
| `StrayEscape` | 3 | 21 | 266 |
| `Expecting` | 145 | 946 | 4,002 |
| `Expected` | 565 | 6,368 | 16,745 |
| `IllegalEscape` | 8 | 187 | 394 |
| `TokenTooLong` | 2 | 264 | 357 |
| `TooManyItems` | 0 | 87 | 94 |
| `MissingLineTerminator` | 190 | 674 | 1,362 |
| `GarbageAtEndOfLine` | 208 | 5,216 | 12,100 |
| `HostIpv4` | 8 | 671 | 1,187 |
| `EmbeddedDollar` | 2 | 103 | 192 |
| `ValueTooLarge` | 2 | 58 | 83 |
| `RegexNotSupported` | 0 | 56 | 61 |
| `GlobInArguments` | 0 | 151 | 234 |
| `ListArguments` | 0 | 81 | 102 |
| `WildcardPattern` | 0 | 68 | 99 |
| `DigestNotSupported` | 0 | 80 | 109 |
| `FullyQualifiedPath` | 0 | 240 | 602 |
| `StarInPath` | 0 | 334 | 457 |
| `NetgroupsNotSupported` | 0 | 90 | 158 |
| `TagNotSupported` | 0 | 323 | 444 |
| `SelinuxNotSupported` | 0 | 173 | 231 |
| `UnsupportedModifier` | 0 | 86 | 191 |
| `TooManyTags` | 0 | 126 | 37 |
| `Message` (M2b sites: `Defaults`, directives) | 46 | 880 | 2,864 |

Under `cfg(test)` every `UserFriendly::DESCRIPTION` is `"elem"`; the descriptions themselves are
compared only by the fuzz target, which builds without `cfg(test)`.

Fuzz smoke run: `parser_equiv` built with `fuzz/run.sh build parser_equiv`, seeded with the
`sudoers_parse` seeds and the sudoers dictionary, run for 55 s: 36,097 executions, 6,198 edges,
no difference, no crash. The campaign belongs on the cluster:
`FUZZ_SECONDS=1800 fuzz/run.sh campaign parser_equiv`.

Historical dump comparison (v1; `proofs/parser/DUMP.md`): the corpus of
`parser corpus 20260101 25` (749 cases: every grammar, mutation and `known` category) dumped by
`SUDO_PARSER_DUMP_CORPUS=… SUDO_PARSER_DUMP_OUT=… cargo test --lib sudoers::test::parser_dump::`
at the merge base (`b6a9bbdb`) and at the restyle revision was **byte-identical** — 3,153 dump
lines, plus the v1 `.bases` and chartable outputs. This compared the live parser before and after the
rewrite independently of `equiv.rs`, with settings observed only by their effect on two bases.

The existing unit tests pass unchanged, apart from `assert_remote_failure` (feature
`unstable-remote-sudoers`, compares the rendered kind) and the test-only `impl Token for
String` in `basic_parser.rs`.

## 5. Extraction

Roots added to `start_from`:
- P1: `basic_parser::parse_lines`, `expect_syntax`, `is_syntax`, `expect_nonterminal`,
  `parse_list`, `ast::host_list`;
- P2: `ast::user_list`, `ast::expect_user_list`, `ast::permissions` (the entries `Sudo::parse`
  calls to build a `PermissionSpec`).

Opaque items added, all thin wrappers with a hand-written model:
- P1: `char_stream::chars_of`, `basic_parser::escape_char`;
- P2: `tokens::sudo_string` (`SudoString::new`), `tokens::canonical` (`resolve::canonicalize` +
  `to_str`), `tokens::compile_pattern` (`glob::Pattern::new`), `tokens::os_string`
  (`OsString::from`), `tokens::classify_chdir` and `tokens::sudo_path` (the text checks of
  `ChDir::construct`, so that the constructor itself is extracted and total).

`ChDir::construct` is now extracted (`sudoers.tokens.ChDir.Insts.Sudo_rsSudoersBasic_parserToken.construct`);
the theorem `construct_ok_eq` is unchanged and is proved by unfolding it. Extracting
`SudoPath::try_from` itself was not viable: it goes through `PathBuf`/`OsStr` conversions that
are opaque in the model, and it would force a representability premise into
`construct_ok_eq`. `Cargo.toml` therefore keeps no `ChDir` opaque item.

### 5.1 Extracted P1/P2 functions (Lean names, `Funs.lean`)

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
The `AliasName` token as a whole is reached through `MetaOrTag` and `Def<T>`.

### 5.1.1 Extracted P2 functions

All productions take and return the cursor: `CharStream → Result ((core.result.Result T Status) ×
CharStream)`, as `Parse` does; the table gives the extra arguments and the result type `T`, and
the helpers their plain types. `T` below is the production's item type.

| Rust | Lean | Extra arguments / type |
|---|---|---|
| `Identifier::parse` | `sudoers.ast.Identifier.Insts.Sudo_rsSudoersBasic_parserParse.parse` | `T = Identifier` |
| `parse_meta` | `sudoers.ast.parse_meta` | `Parse T → FromUsername T → …`; `T = Meta T` |
| `FromUsername` for `Identifier`/`UserSpecifier` | `sudoers.ast.{Identifier,UserSpecifier}.Insts.Sudo_rsSudoersAstFromUsername.from_username` | `SudoString → Result T` |
| `Meta<Identifier>::parse`, `Meta<UserSpecifier>::parse` | `sudoers.tokens.{MetaIdentifier,MetaUserSpecifier}.Insts.Sudo_rsSudoersBasic_parserParse.parse` | `T = Meta Identifier`, `Meta UserSpecifier` |
| `UserSpecifier::parse`, `parse_user` | `sudoers.ast.UserSpecifier.Insts.Sudo_rsSudoersBasic_parserParse.parse`, `sudoers.ast.ParseUserSpecifier.parse.parse_user` | `T = UserSpecifier` |
| `RunAs::parse` | `sudoers.ast.RunAs.Insts.Sudo_rsSudoersBasic_parserParse.parse` | `T = RunAs` |
| `switch` | `sudoers.ast.switch` | `Modifier → CharStream → Result ((Result Modifier Status) × CharStream)` |
| `tag_class`, `equals_keyword` | inlined into `MetaOrTag…parse` | |
| `MetaOrTag::parse` | `sudoers.ast.MetaOrTag.Insts.Sudo_rsSudoersBasic_parserParse.parse` | `T = MetaOrTag` |
| `command_tag_step` | `sudoers.ast.command_tag_step` | `CharStream → Vec Modifier → Result ((Result (Option (Option (Meta (Pattern × Args)))) Status) × CharStream × Vec Modifier)` |
| `CommandSpec::parse` | `sudoers.ast.CommandSpec.Insts.Sudo_rsSudoersBasic_parserParse.parse` (+ `_loop`) | `T = CommandSpec` |
| `(Option<RunAs>, CommandSpec)::parse` | `PairOptionRunAsCommandSpec.Insts.Sudo_rsSudoersBasic_parserParse.parse` | `T = Option RunAs × CommandSpec` |
| `(SpecList<Hostname>, Vec<(Option<RunAs>, CommandSpec)>)::parse` | `PairVecQualifiedMetaHostnameVecPairOptionRunAsCommandSpec.Insts.Sudo_rsSudoersBasic_parserParse.parse` | `T = Vec (Qualified (Meta Hostname)) × Vec (Option RunAs × CommandSpec)` |
| `user_list`, `expect_user_list` | `sudoers.ast.user_list`, `sudoers.ast.expect_user_list` | `CharStream → Result ((Result (Vec (Qualified (Meta UserSpecifier))) Status) × CharStream)` |
| `permissions` | `sudoers.ast.permissions` | `CharStream → Result ((Result (Vec (Vec (Qualified (Meta Hostname)) × Vec (Option RunAs × CommandSpec))) Status) × CharStream)` |
| `Username` token | `sudoers.tokens.Username.Insts.Sudo_rsSudoersBasic_parserToken.{construct,accept,accept_1st,escaped,ALLOW_ESCAPE}`; `sudoers.tokens.{embedded_dollar,contains_char}` (+ `_loop`) | `construct : String → Result (Result Username ErrorKind)` |
| `DigitsU32` token | `sudoers.tokens.DigitsU32.Insts.Sudo_rsSudoersBasic_parserToken.{construct,accept}`; `sudoers.tokens.parse_u32` (+ `_loop`) | `construct : String → Result (Result DigitsU32 ErrorKind)` |
| `Command` token | `PairPatternArgs.Insts.Sudo_rsSudoersBasic_parserToken.{construct,accept,accept_1st,escaped,ALLOW_ESCAPE}`; `sudoers.tokens.{split_words,skip_word_class,any_glob,has_glob_char,os_strings,word_text,starts_with_text,equals_text}` (each with its `_loop`) | `construct : String → Result (Result (Pattern × Args) ErrorKind)` |
| `SimpleCommand` token | `glob.Pattern.Insts.Sudo_rsSudoersBasic_parserToken.{construct,accept,accept_1st,escaped,ALLOW_ESCAPE}` | `construct : String → Result (Result Pattern ErrorKind)` |
| `ChDir` token | `sudoers.tokens.ChDir.Insts.Sudo_rsSudoersBasic_parserToken.{construct,accept,accept_1st,escaped,ALLOW_ESCAPE}`; `classify_chdir`, `sudo_path` are the opaque models | `construct : String → Result (Result ChDir ErrorKind)` |
| `Unquoted<T>` token | `sudoers.tokens.Unquoted.Insts.Sudo_rsSudoersBasic_parserToken.{construct,construct_loop,accept}` | `construct : Token T → String → Result (Result (Unquoted T) ErrorKind)` |
| `StringParameter` classes | `sudoers.tokens.StringParameter.Insts.Sudo_rsSudoersBasic_parserToken.{accept,escaped,construct,ALLOW_ESCAPE,MAX_LEN}` | |

Loops become `…_loop` functions (`partial_fixpoint`) that take the cursor fields and the loop
variables separately and return the tuple of them; `CommandSpec`'s loop carries `tags`,
`failure` and `found`.

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
| `char::is_alphanumeric` | `opaque` (character oracle) |
| `char::is_control` | code point in `[0, 31]` or `[127, 159]` (category `Cc`) |
| `char::to_digit` | ASCII digit (`sudo_rs.asciiDigit`), panics outside radix `2..=36` |
| `Vec::into_boxed_slice` | `ok v.slice` |
| `tokens::sudo_string` (opaque for Charon) | NUL ↦ `Err (NulInString s)`, else `Ok ⟨s⟩` |
| `tokens::canonical` (opaque for Charon) | `opaque` `String → Result Canonical` (oracle) |
| `tokens::compile_pattern` (opaque for Charon) | `opaque` (oracle) returning `glob.Pattern` or the `ErrorKind` payload |
| `tokens::os_string` (opaque for Charon) | `opaque` `String → Result OsString` over the existing byte model |
| `tokens::classify_chdir`, `tokens::sudo_path` (opaque for Charon) | definitions over the Lean `String` (`"*"`/`*`/NUL tests) |

The `'\\'` defect: of the three ways round, post-processing the generated file would put a text
rewrite of every generated file into the trusted base, and a newer Aeneas does not fix it (see
section 7). An opaque Rust function with a one-line Lean definition adds one item that can be
checked by reading it (`fn escape_char() -> char { '\\' }` against `def … := ok '\\'`), changes no
pipeline script, and the backslash enters the extracted code nowhere else. The cost is one
function call where the legacy code used a constant.

## 6. Measured sizes

P1 (M1) against `70fdb56b`, P2 (M2a) against `ad41ddd4` (`git diff --numstat`, added/removed):

| Measure | P1 | P2 |
|---|---:|---:|
| `char_stream.rs` | 62/20 | 0 |
| `basic_parser.rs` | 250/76 | 72/0 (the new `ErrorKind` variants and their `Display` arms) |
| `tokens.rs` | 130/49 | 320/92 |
| `ast.rs` | 23/4 | 154/82 |
| `Cargo.toml` (roots and opaque items) | 9/1 | 17/4 |
| Non-test lines of the rewritten files | `char_stream.rs` 82, `basic_parser.rs` 514 | `tokens.rs` 775, `ast.rs` 1004 |
| Generated Lean for the scope's functions (without doc comments) | 81 definitions, 1,156 lines | 126 new definitions, 2,572 lines |
| `Funs.lean` growth (doc comments included) | +1,640 | +3,205 |
| `Types.lean` growth | +188 | +137 |
| Extraction time (`proofs/extract.sh`) | 16 to 70 s | 26 to 48 s |

Generated lines of the larger P1 definitions: `accept_escaped` 87, `Qualified…parse` 63,
`parse_lines_loop` 51, `parse_list_loop` 46, `LeadingWhitespace…parse_loop` 37,
`Parse.Blanket.parse` 37, `Parse.Blanket.parse_loop` 37, `resembles_ipv4_loop` 36,
`TrailingWhitespace…parse_loop` 29, `parse_list` 28, `Meta…construct` 27, `try_nonterminal` 26.

Generated lines of the larger P2 definitions: `MetaOrTag…parse` 652, `Command…construct
(PairPatternArgs)` 290, `RunAs…parse` 106, `SimpleCommand…construct (glob.Pattern)` 77,
`parse_user` 58, the two rule tuples 54 and 52, `UserSpecifier…parse` 52, `parse_meta` 49,
`command_tag_step` 48, `CommandSpec…parse` 42, `Identifier…parse` 40, `parse_u32_loop` 30,
`CommandSpec…parse_loop` 29, `Unquoted…construct_loop` 26, `Username…escaped` 26, `parse_u32`
20, `split_words` 20, `ChDir…construct` 18, `permissions` 15.

`MetaOrTag…parse` is the outlier: the Rust `match keyword.as_str()` becomes a chain of `Str`
equality tests, and each of its eight `expect_syntax(…)?` steps becomes a `Try::branch` plus a
residual conversion, nested inside that chain. A proof should reason about it through a lemma
per keyword class (`TagClass`) rather than by unfolding; if that turns out to be unwieldy,
flattening the dispatch into an `if`/`else` chain over `equals_text(&chars_of(&keyword), …)`
is the candidate rewrite (not done here: the current form is the legacy shape and the
equivalence evidence is against it).

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

Revisit after M2b if the failure-flag idiom makes the refinement proofs markedly longer than the
legacy shape would; that is a measurement for the proof stage.

## 8. Notes for the next stages

- M2b scope: `Def<T>`, `get_directive`, `parse_include`, `Sudo::parse` beyond the named entries
  (`user_list`, `expect_user_list`, `permissions`), and the `Defaults` settings parser with the
  tokens only it uses (`Numeric`, `DefaultName`, `EnvVar`, `QuotedStringParameter`,
  `IncludePath`, `QuotedIncludePath`). The `Defaults` settings parser is the only remaining
  `unrecoverable!` user; every other message site of P1/P2 has an `ErrorKind` variant.
- The legacy snapshot's `Defaults` block is the legacy-style parser at the branch's base (with
  the data API); the printer in `equiv.rs` (`settings_modifier`) and `bases()` follow it.
- For the proof: `Status` is in the result, not in a separate error channel (`Result
  ((core.result.Result T Status) × CharStream)`); Aeneas `fail` arises only from arithmetic
  overflow, slice indexing, `chars_of`/`String::len` on texts beyond `usize`, the opaque
  character predicates, and the oracles (`canonical`, `compile_pattern`, `os_string`). The
  token text is a Lean `String` built by `String.push`, and the length check reads
  `utf8ByteSize`. `String::as_str` appears in `MetaOrTag::parse` (`match keyword.as_str()`), so
  the `Str` model of `as_str` is now on the parser path as well.
- `MetaOrTag::parse` (652 generated lines) and `Command::construct` (290) dominate; see section 6.
