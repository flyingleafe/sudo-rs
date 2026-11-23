# Plan: proving the sudoers parser

Status: the P1–P5 Lean chain is checked for the **stable, include-free text entry point**, from
[`parse_sudoers_refines`](../lean/SudoRsProofs/Parser/Directives/Main.lean) to
[`text_to_authorization`](../lean/SudoRsProofs/Parser/EndToEnd.lean), including Defaults and clean-file uniqueness.
This is not a claim that all plan gates passed: the [larger C comparison](C-SUDO.md#larger-corpus-limits-of-the-classification)
has unexplained differences. The [result index](README.md) separates theorems, assumptions and tests.
Feasibility measurements below are from `9c30990f` (Charon 0.1.321, Aeneas `8f4466db`).

## 1. Goal

At the baseline, `permission_flags_eq` started from a parsed policy. No statement connected
the text of a sudoers file to a decision; the parser (`src/sudoers/{char_stream,basic_parser,tokens,ast}.rs`)
and the pure part of `analyze` lay outside that proof.

The goal is a kernel-checked chain

```
sudoers text --parse_lines--> [Parsed<Sudo>] --analyze--> (rules, aliases) --permission_flags--> Option<Tag>
```

with a specification of the first two arrows, and these end-to-end statements:

- **General**: the decision on a text equals `authorize` on the policy built from exactly the
  lines the reference parser accepts.
- **Clean file**: if reading the text produces no diagnostic, every character of it is
  accounted for by the grammar, the alias tables are sorted and duplicate-free, and the decision
  equals `authorize` on the unique policy the grammar assigns to the text.

Non-goals: opening and trusting the file (`audit::secure_open_sudoers`), request construction,
Defaults semantics beyond parsing (stage P5), anything in C sudo.

## 2. What has to be proved

Non-test code, counted on `9c30990f`:

| Unit | File | Lines | Content |
|---|---|---|---|
| Character stream | `char_stream.rs` | 47 | `Peekable<Chars>` with line/column tracking |
| Combinators | `basic_parser.rs` | 233 | `Parse`, `Token`, `Many`; whitespace, comments, line continuation; token loop; lists; `parse_lines` with per-line error recovery |
| Tokens | `tokens.rs` | 349 | 16 `Token` impls: character classes, escapes, length limits, constructors (`Username`, `Hostname`, `Command`, `ChDir`, ...) |
| Grammar | `ast.rs` | 676 | 20 `Parse` impls: identifiers, `!`, user specifiers, runas, tags, command specs, aliases, Defaults, includes, `Sudo` |
| Analysis | `mod.rs` (`analyze`, `process`, `include`, `read_sudoers`) | 277 | collecting rules, aliases and Defaults; includes with a depth limit; file IO |

Constructs that matter for extraction: 29 `unrecoverable!` sites (each a `format!`), 11 loops of
which 6 contain `?` or an early return, 37 closures (8 take the stream), 20 uses of the `str`
pattern API (`contains`, `starts_with`, `strip_suffix`, `rsplitn`, `split_whitespace`,
`trim_end`), 9 kinds of `char` predicate (5 of them Unicode-aware), one `fn` pointer parameter,
`Box<dyn FnOnce(&mut Settings)>` for Defaults, and two environment calls made while parsing
(`common::resolve::canonicalize` and `glob::Pattern::new` in `SimpleCommand::construct`).

The AST therefore depends on the file system: an existing command path is canonicalized when
the file is parsed.

## 3. Evidence gathered

### 3.1 The parser as written does not extract

`proofs/extract.sh --start-from <root>` on the unmodified source:

| Root | Result |
|---|---|
| `basic_parser::try_syntax` | Aeneas fatal: `core::str::pattern::Pattern` is unimplemented (reached through `"\t ".contains(c)`) |
| `basic_parser::parse_list` | the same, plus "Early returns inside of loops are not supported yet" |
| `basic_parser::parse_lines` | the same |
| `read_sudoers` (whole grammar) | Charon: 76 type errors, all on closures of the Defaults DSL. Aeneas: 87 errors: 51 "Unexpected bound region" (closures over `&mut CharStream`, `Peekable::next_if`), 18 "Dynamic trait types are not supported yet", 8 "Unimplemented", 4 early returns inside loops, 2 "Arrow types are not supported yet" |
| `analyze` | the same classes, 90 errors |

### 3.2 A restricted style does extract

A 460-line scratch module re-expressed the core pattern without the unsupported constructs:
an index cursor over `&[char]`, flags instead of `?` inside loops, an error-kind enum instead of
`format!`, no closures, no `fn` pointers, no `str` pattern API. It kept the architecture:
`Token` with associated constants and a default method, the blanket `impl<T: Token> Parse for T`,
`impl<T: Token> Token for Meta<T>` with constants derived from `T`, generic `parse_list`,
`Qualified<T>`, `Option<T>`, tuple and `Vec<T>` impls, cursor copy for backtracking, and a
nested cursor over a token's text (the quoted-user case).

Result: Charon and Aeneas translated all of it and the generated Lean compiled. The generated
code is a state-passing parser, for example

```lean
structure sudoers.vspike.Parse (Self : Type _) where
  parse : Cursor → Result (core.result.Result Self Status × Cursor)
```

so one generic refinement lemma per combinator, parameterised by the instance, is the natural
proof shape.

Limits met on the way:

| Construct | Outcome | Way round |
|---|---|---|
| `92u8 as char`, `c as u32` | Aeneas "Unreachable" | `char::to_digit`, comparisons on `char` only |
| the literal `'\\'` | generated as `'\'`, which Lean rejects | post-process the generated file, or bump Aeneas |
| nested loop whose condition is `a() \|\| b()` on the stream | "Could not match the contexts" | one loop per function |
| `char::is_uppercase` and the other Unicode classes | external | oracle (section 5.3) |

### 3.3 Error recovery, observed

A scratch test called the real `parse_lines::<Sudo>`:

| Input | Items returned |
|---|---|
| `alice ALL = /bin/a, sha224:x \`⏎`bob ALL = (ALL) ALL`⏎ | fatal at 1:21, comment, **rule** |
| `alice ALL = /bin/a, /bin/b \`⏎`bob ALL = (ALL) ALL`⏎ | one rule |
| `alice ALL = ALL` (no final newline) | **rule**, fatal "missing line terminator" |
| `alice ALL = ALL ) junk`⏎`bob ALL = ALL`⏎ | **rule**, fatal "garbage at end of line", comment, rule |
| `alice ALL = ALL, !/usr/bin/su`⏎ | one rule: `ALL`, then the exclusion |
| `alice ALL = ALL !/usr/bin/su`⏎ (comma missing) | **rule with `ALL` only**, fatal "garbage at end of line" |
| `alice ALL = ALL, !sha224:x`⏎ (error inside the exclusion) | fatal, no rule |

Two properties follow and the specification must state them:

1. **Prefix acceptance.** When the grammar can end a rule before the end of the line, the rule
   is kept and the rest of the line is reported as garbage. An error inside a list element
   drops the whole line instead.
2. **Physical-line resynchronisation.** After a fatal error the parser skips to the next
   newline character, not to the end of the logical line. The rest of a continued line is then
   parsed as lines of its own; in the first row it becomes a rule for `bob`.

`sudo` prints the diagnostics and continues (`src/sudo/pipeline.rs`). They go to standard error
only (`src/sudo/diagnostic.rs`); C sudo also writes parse errors to its log
(`log_parse_error`).

C sudo 1.9.18 was run on three of these inputs through `testsudoers`, which lists the entries
its parser kept:

| Input | sudo-rs keeps | C sudo keeps |
|---|---|---|
| `alice ALL = ALL !/usr/bin/su`⏎ | `alice ALL = ALL` | nothing; syntax error at 1:17 |
| `alice ALL = ALL ) junk`⏎`bob ALL = ALL`⏎ | both rules | only the rule for `bob` |
| `alice ALL = /bin/a, sha224:x \`⏎`bob ALL = (ALL) ALL`⏎ | a rule for `bob` | nothing; syntax error at 2:1 |

On these inputs C sudo discards the whole logical line. That does not hold for every
construct. The next two tables compare outcomes: sudo-rs through `analyze` and `check` in a
scratch test, C sudo through the entries and the dump (`-d`) of `testsudoers`.

| Policy | Request | sudo-rs | C sudo 1.9.18 |
|---|---|---|---|
| `alice ALL = ALL, !/usr/bin/su`⏎ | alice, `/usr/bin/su` | denied | denied |
| `alice ALL = ALL !/usr/bin/su`⏎ | alice, `/usr/bin/su` | **allowed** | no rule kept |
| `Runas_Alias NOTROOT = ALL !root`⏎`alice ALL = (NOTROOT) /usr/bin/id`⏎ | alice as root, `/usr/bin/id` | **allowed**: alias kept as `ALL` | **allowed**: alias kept as `ALL` |
| `Cmnd_Alias SAFE = ALL !/usr/bin/su`⏎`alice ALL = SAFE`⏎ | alice, `/usr/bin/su` | denied: definition dropped | **allowed**: alias kept as `ALL` |
| `alice ALL = ALL`⏎`alice ALL !/usr/bin/su`⏎ | alice, `/usr/bin/su` | **allowed** | **allowed** |
| `Cmnd_Alias SHELLS /usr/bin/su, /usr/bin/bash`⏎`alice ALL = ALL, !SHELLS`⏎ | alice, `/usr/bin/su` | **allowed** | **allowed** |
| `alice ALL = /bin/a, sha224:x \`⏎`bob ALL = (ALL) ALL`⏎ | bob, `/usr/bin/su` | **allowed** | no rule kept |
| `alice ALL = INTERCEPT: ALL`⏎ | alice, `/usr/bin/su` | denied: tag not supported | allowed: valid for C sudo |

| `Defaults` line | sudo-rs applies | C sudo keeps |
|---|---|---|
| `Defaults secure_path="/usr/bin", timestamp_timeout=0, noexec`⏎ | all three | all three |
| the same with `, logfile="/var/log/sudo.log"` appended | none: `unknown setting: 'logfile'` | all four |
| `Defaults secure_path="/usr/bin" timestamp_timeout=0`⏎ (comma missing) | `secure_path` only | nothing; syntax error |

Three further properties follow:

3. **Prefix acceptance is not peculiar to sudo-rs.** C sudo keeps the prefix of an alias
   definition (`Runas_Alias`, `Cmnd_Alias` and `User_Alias` were tried) and drops rules and
   `Defaults` lines whole. sudo-rs keeps the prefix of rules, of `Defaults` lines and of the
   `Runas_Alias` tried, and drops the `Cmnd_Alias` tried.
4. **One unknown setting discards its whole `Defaults` line.** The settings that sudo-rs does
   know on that line are lost with it.
5. **A lost line can be a restriction**: a later rule that denies, an alias that an exclusion
   refers to, a `Defaults` line. Both implementations then allow more than the file says.

Only `testsudoers` was run, not the `sudo` front end, and only these inputs; stage P0 has to
compare systematically and per construct.

## 4. Target theorems

`O` bundles the oracles of section 5.3. `chars t` is the list of characters of the text.
Names are provisional.

| Id | Statement | Kind |
|---|---|---|
| PR | The extracted `parse_lines::<Sudo>` returns `ok r` and `abs r = Syntax.parseLines O (chars t)`, for every text within representability bounds | refinement, total correctness |
| PT1 | `parse_lines` never yields `Err(Reject)`, so `panic!("internal parser error")` in `process` is unreachable; no `unwrap`, slice or subtraction in the parser can fail | consequence of PR |
| PT2 | The contract written on the `Parse` trait: a production that rejects has consumed nothing. Stated per production; see finding F-P3 | reference parser |
| PT3 | Soundness: if a production returns `Ok a` having consumed `c`, then `Derives c a` | reference parser against the grammar |
| PT4 | Completeness: `Derives c a` and an admissible follow character imply the production returns `Ok a` on `c ++ rest`, leaving `rest`. Corollary: the grammar is unambiguous | reference parser against the grammar |
| PT5 | Round trip: `parse (print a ++ rest) = (Ok a, rest)` for every printable `a` | from PT4 |
| PT6 | Clean file: if `parseLines O (chars t)` contains no error, then `t` is a sequence of lines, each derived by the grammar, and the result is their ASTs in order | reference parser |
| PT7 | Recovery: the two properties of 3.3 as equations, and "every character not covered by an accepted item is covered by a diagnostic" | reference parser |
| PA | The pure part of `analyze` equals `policyOf`: rules and alias definitions in file order, then the sanitizer order | refinement |
| E2E | For a text without includes: `Sudoers::read` then `check` gives flags `r` with `r.map absTag = authorize O (policyOf (accepted (parseLines O (chars t)))) request` | PR + PA + `permission_flags_eq` |
| E2E-clean | If no diagnostic is produced: the same with the unique grammar-assigned policy, and alias references equal to their expansion | E2E + PT6 + sanitizer order theorem + `demonstration` |

**PT7, checked interpretation.** [`parseLines_iff_trace` and `source_partition`](../spec/SudoersSpec/Syntax/Recovery.lean)
account for the whole input: leading blanks, the attempted item, an optional comment, and
the terminator or text skipped on recovery. `garbage_point` shows why coverage by the
*reported diagnostic spans* is false: the span has zero width even when the parser discards
one or more characters. For PT6, [`parseSudoersWith_exact_iff` and `exactSudo_cleanFile_unique`](../spec/SudoersSpec/Grammar/SudoUnique.lean)
give equivalence and uniqueness for the exact stable grammar, which retains ignored spans
and recovery cursors. Uniqueness does not hold for every derivation of the broader grammar.

**E2E-clean, alias expansion.** Diagnostic-free sanitization proves the dependency order
needed for equivalence of an *item list* with its expansion. For a flattened *whole policy*,
[`authorize_expandAliases`](../spec/SudoersSpec/Expansion.lean) also requires expansion
not to empty a runas user list and no command-alias body to contain `ALL`. Clean syntax
alone does not justify dropping those hypotheses or claiming exact equality of all tags.

**E2E, boundary actually checked.** The Rust call chain starts at the same `analyze_text`
that `Sudoers::read` calls *after* reading and decoding. `text_to_authorization` supplies
the concrete parser refinement, policy invariants, tag and name bounds, modifier provenance
and settings range; it does not take an already correct policy as input. A single fixed
external environment, a resolved request, representable cursor and analysis counters, and
the diagnostic path/renderer agreements remain hypotheses. Includes have a separate [PA
theorem for finite snapshots](../lean/SudoRsProofs/Parser/Analysis/Includes.lean);
opening files, native identity resolution and executing a permitted command are not proved.

**Test boundary.** [P0](P0.md) records which dump format was compared; the original
two-settings-base observer could miss differences between modifiers. The
[C comparison](C-SUDO.md#larger-corpus-limits-of-the-classification) records unexplained
differences separately. Neither test establishes the full-file Rust refinement PR.

## 5. Specification design

### 5.1 Reference parser (structural form)

`Syntax.parseLines`, a total Lean function over `{ rest : List Char, line col : Nat }`, in the
shape `Stream → Except Status α × Stream`: the stream survives errors, as in Rust, because
recovery continues from where the failure left it. It mirrors the Rust productions one to one,
including the two position-dependent decisions (`Defaults` scope detection and `#` as uid,
include or comment). It is executable, so it can be tested before anything is proved.

### 5.2 Grammar (declarative form)

An inductive relation `Derives : List Char → α → Prop` per nonterminal, written from
`docs/man/sudoers.5.md`, with whitespace, comments, line continuation, escapes, quoting and
token limits explicit. Where the code and the man page disagree the grammar follows the code
and the disagreement is recorded, as in `proofs/spec/README.md`.

PT3 to PT5 relate the two forms. PT4 is the expensive one: maximal munch and the LL(1)
exceptions (`MetaOrTag`, directives parsed as user names) need follow-set side conditions.

### 5.3 Oracles

| Oracle | Stands for | Why not a model |
|---|---|---|
| `CharOracle` | `char::{is_alphanumeric,is_uppercase,is_numeric,is_control,is_whitespace}` | Unicode tables; ASCII classes are definitions |
| `FsOracle.canonicalize` | `common::resolve::canonicalize` at parse time | file-system state |
| `GlobCompile` | `glob::Pattern::new`, linked to `GlobAbs.pat` | the pattern type is opaque in the decision proof |
| `FsOracle.read`, `listDir` (stage P4) | `@include`, `@includedir` | file-system state |

For testing, `CharOracle` is instantiated from a table dumped from the same `rustc`.

### 5.4 AST

`SudoersSpec/Ast.lean` gains `Sudo`, `Directive`, `ConfigScope`, include items and spans.
`policyOf` maps accepted items to the existing `Policy`.

## 6. Rust changes

The architecture stays. Bodies change to the restricted style of 3.2:

| Today | Becomes |
|---|---|
| `CharStream` over `Peekable<Chars>` | cursor over `&[char]`; one conversion from `&str` at the entry point, outside the proof |
| `?` or `unrecoverable!` inside a loop (6 loops) | loop ends on a flag; the error is returned after the loop |
| `unrecoverable!(…, "…{x}…")` (29 sites) | error kind plus payload; one opaque function renders today's message text |
| closures over the stream, `fn(char) -> bool` parameter | named functions, a `first: bool` argument |
| `str` pattern API in constructors (20 uses) | character loops; a constructor may start as an opaque function with a Lean model and be discharged later |
| `Box<dyn FnOnce(&mut Settings)>` | a data type with an `apply` function, as was done for `Modifier` (stage P5) |
| `canonicalize`, `glob::Pattern::new` inside `construct` | calls through an oracle parameter |

This rewrites most parser bodies, so behaviour preservation needs its own evidence:

- the original parser is kept under `#[cfg(test)]` and compared with the new one on generated
  and mutated inputs: same items, same spans, same messages;
- the existing parser unit tests and the 863-test compliance suite;
- the three-way comparison of stage P0.

## 7. Stages

Each stage ends with the gate green and an explicit continue or stop decision.

| Stage | Deliverable | Exit criterion |
|---|---|---|
| **P0 Specification and testing.** No Rust change outside `#[cfg(test)]` | `Syntax.parseLines` in `proofs/spec`; AST dump in a test module; generator covering quoting, escapes, continuations, comments, tags, aliases, Defaults, includes; mutation of valid inputs for recovery; comparison Lean vs Rust at AST and span level; C sudo `cvtsudoers -f json` and `visudo -c` as a third opinion | no Lean/Rust disagreement on the corpus; every C sudo difference classified; 3.3 confirmed or corrected against C sudo |
| **P1 Tracer bullet.** Lexical layer and one production | cursor, whitespace, `try_syntax`, `expect_syntax`, token loop, `parse_list`, `Qualified`, `Meta`, tokens `Hostname` and `AliasName` in the restricted style; extraction; PR, PT2 to PT5 for `SpecList<Hostname>`; legacy-vs-new differential test | theorems checked; measured proof size per Rust line and list of toolchain workarounds; decision on the Aeneas pin |
| **P2 Permission lines** | users, quoted users, runas, tags (`MetaOrTag`), commands (`Command`, `SimpleCommand` with oracles), `PermissionSpec` | PR and PT3 for `PermissionSpec`; PT4/PT5 for the fragment the differential generator prints |
| **P3 Lines and directives** | alias definitions, `get_directive`, includes, `Sudo`, `parse_lines` | PR for `parse_lines`; PT1, PT6, PT7 |
| **P4 Analysis** | pure part of `analyze` with an include oracle; composition with the sanitizer and `permission_flags` | PA, E2E, E2E-clean for texts without Defaults |
| **P5 Defaults** | Defaults modifiers as data; settings parsing; composition with the `authorization` mapping | E2E including settings |

P0 is independent of the proof and is where most parser bugs would surface. P1 decides whether
the remaining stages are affordable: the decision core needed about 2,800 lines of Lean proof
for an extracted call tree of roughly 300 Rust lines; the parser is five times larger but is
built from about eight combinators.

Results the later stages build on, proved since this plan was written: P4 uses
`sanitize_alias_tables_sorted` (no diagnostic implies sorted and duplicate-free tables) and
`sanitize_alias_tables_returns`; P5 uses `authorization_eq`.

## 8. Risks and open decisions

| Risk | Consequence | Mitigation |
|---|---|---|
| The rewrite changes parser behaviour | a proved parser that is not sudo-rs's parser | legacy parser as test oracle; compliance suite; P0 corpus |
| The fork diverges from upstream | proofs do not transfer to upstream releases | keep the trait architecture and mechanical idioms; record every upstream behaviour finding instead of fixing it |
| PT4 (completeness) is expensive | no unambiguity or round-trip theorem | PT3 and PT6 first; PT4 per fragment |
| Toolchain defects (char literal printing, casts) | pipeline workarounds enter the trusted base | one documented post-processing rule, or a pinned upgrade after P1 |
| The grammar is transcribed by the same hands as the parser | common-mode error | man-page EBNF as the source of the grammar; C sudo comparison in P0 |
| File-system dependence of the AST | theorems hold for one fixed snapshot | state the snapshot assumption next to `InstOracle` |

Decisions for the project owner:

1. Run P0 alone first, or P0 and P1 together.
2. Whether a newer Aeneas (possibly supporting early returns in loops) is worth re-validating
   the existing proofs against. Not measured.
3. Whether prefix acceptance and physical-line resynchronisation should be raised upstream. The
   proof can specify either behaviour; it cannot make a file with diagnostics safe.

## 9. Findings to confirm in P0

| Id | Observation | Basis |
|---|---|---|
| F-P1 | Prefix acceptance (3.3) | observed; C sudo 1.9.18 drops rules and `Defaults` lines whole but keeps the prefix of alias definitions |
| F-P2 | Physical-line resynchronisation (3.3) | observed; differs from C sudo 1.9.18 on the input tried |
| F-P3 | `UserSpecifier::parse` can return `Reject` after consuming a quoted token whose content is not a user (`"@x"`), contrary to the contract documented on `Parse`. Every caller appears to end in a fatal error | reading the code; not tested |
| F-P4 | `Sudo::parse` treats any failure of `Identifier` after `#`, fatal ones included, as "not a user id" and retries the line as an include or comment | reading the code; not tested |
| F-P5 | A command path is canonicalized at parse time if it exists, so the same text can yield different ASTs on different hosts | reading the code |
| F-P6 | One unknown setting discards every setting on its `Defaults` line (3.3) | observed |
