# Sudoers policy analysis and Defaults scoping (P4–P5, Rust)

This change extracts the analysis of parsed items and the Defaults scoping that runs before the decision. The tests compare the restyle with the old Rust on a fixed corpus; the Lean build checks the translation and the existing decision proofs. Neither is a proof of PA, Defaults scoping, or E2E.

## Entry points and include oracle

`Sudoers::read` reads UTF-8 and converts it to `Vec<char>` once. `Sudoers::open` first uses `audit::secure_open_sudoers`, then reads the same way. Both call `analyze_text(&Path, &[char])`, which calls `parse_sudoers` (the `Sudo` instance of `parse_lines`) and then `analyze(&Path, Vec<Parsed<Sudo>>)`. The latter initializes the policy, calls `process` to add the items to it, and sanitizes the resulting alias tables once. Included files are parsed by the same `parse_sudoers` and added by the same `process`; they do not initialize or sanitize a policy of their own.

| Old code | Live code |
|---|---|
| `read_sudoers` reads and parses, `open`/`read` call `analyze` | `read_sudoers` reads characters; the call to `analyze_text` supplies the text-to-policy function the binary uses. |
| `process` iterates and dispatches | `process` uses an owning `Vec::IntoIter` with explicit `next` and a loop flag; `process_item` dispatches; no clone of parsed items. |
| `get_ignored_tags` applies each modifier to a fresh `Tag` and flattens `ignored` | `ignored_tags` / `ignored_modifiers` visit the same modifiers in the same order. Exactly `Modifier::Ignored(span)` would have added a span; no temporary `Tag`, cloning of modifier data, or ignored-span vector. |
| `Vec::append` for each alias declaration | `append_defs` keeps the same bulk move. |
| `map`/`collect` for `Defaults!` | `command_scope` moves each item and preserves its qualifier; `any_arguments_meta` adds the empty prefix only to concrete patterns. |
| `resolve_relative`, secure open and `read_dir` inline in the recursion | Two opaque calls, `include_file` and `include_dir_files`; iteration, recursion, counting and appending the diagnostics stay extracted. |
| `mem::take`, `match_scope` closure and `for` loops over customisers and modifiers | Replace each consumed vector with an empty one, match the scope directly, then use the modeled owning vector iterator and `apply_settings`. This preserves single-use scoping, including for unmatched customisers. |

`include_dir_files(cur_path, raw_path)` checks `%h` before resolving a relative path against the parent of `cur_path`. It returns one message if `%h` is present or `read_dir` fails; otherwise it returns the eligible entry paths in ascending `PathBuf` order. It skips individual directory-entry errors and names that are not UTF-8, contain `.` or end with `~`. It does not classify entries by file type. It finishes the listing and sort before any child is processed.

`include_file(cur_path, Named(raw) | Listed(path), refusal)` resolves only `Named`: absolute paths are used as written, relative paths are joined to `cur_path.parent()`, and lack of a parent panics with the legacy message. `Listed` already contains the entry's path and is not rejoined. In a regular file include `%h` is used literally. A refusal performs no open or parse and yields a message for the resolved path. Otherwise, the call opens, reads and parses the file, returning its path and parsed items, or returns an I/O error message (custom text for `NotFound`). The caller tags the failure with the including file's path and the directive's span. On success the returned path is the base and diagnostic source for the child.

The extracted count starts at zero, counts every attempted regular include including failed opens, and never decrements. It is shared by siblings and descendants: **128 attempts in the entire traversal**, not 128 per branch. Neither a listing nor a refused open counts. Listing takes place even after the budget is exhausted. Successful includes expand depth-first at their directive, using the shared accumulator. With `unstable-remote-sudoers` (not extracted), a relative socket path is rejected before the budget check; an allowed socket include does not count, and processes its items with includes forbidden. The caller's counter does not change.

The Lean oracle declarations are `opaque`, not axioms and not a filesystem implementation. The model is deterministic; a theorem for includes must give the two calls' answers under one filesystem/parser snapshot, including `Err` rather than children on refusal. It must relate the returned owned path, its `as_path` view, and `to_path_buf` for the source of diagnostics. No such hypothesis is needed about either include call for an item list without include items: the item dispatch never calls them. `to_path_buf` can still be reached in an include-free file with diagnostics. The existing opaque path types and byte-based `OsString` model are reused.

## Specification contracts

### Analysis (PA)

The reference builds four ordered definition lists, two ordered customiser lists, a rule list and a diagnostic list. Start them all empty; initialize settings from the system defaults, not from any of the customisers. For the no-include theorem, fold the parse stream left to right:

1. A comment changes nothing. A fatal item appends one diagnostic with the current path, given span, and rendering of the error kind. A `Reject` panics; use the separate no-`Reject` parser result for PA's successful-return statement. Do not filter away a recoverable accepted prefix on a line that also has a diagnostic.
2. A permission appends the rule intact. Its diagnostics are one per `Ignored` modifier, in host-group, command, then modifier order, before the next item's diagnostics. These carry the current path, the modifier span, and `this tag is ignored by sudo-rs`.
3. An alias declaration appends every definition, in declaration order, to its table. Definition indices remain positions in those unsorted lists. A Defaults declaration appends to the command list if command-scoped, otherwise to the common non-command list. Preserve the order of entries within each list and of all modifiers within an entry. A command scope preserves `Allow`/`Forbid` and `All`/alias membership as written; `Only pattern` becomes `Only (pattern, Prefix [])`. Alias references still use the ordinary command alias table, with its own argument conditions. No setting is applied in this phase.
4. After the fold, produce the order vectors and diagnostics by running the sanitizer on the user, host, command, then runas definitions. Within a table, scan definitions in order, report and skip later duplicate definitions, and visit dependencies in member order regardless of qualifier. A dependency lookup selects the first definition with that name; a missing reference gives an undefined diagnostic; a revisit to a seen but not yet ordered node gives a recursive diagnostic. Append each visited index after its dependencies. Append all sanitizer diagnostics after the item diagnostics, with neither path nor span; do not drop a definition from the underlying list. Use `sanitize_alias_tables_returns`, `sanitize_alias_tables_tableWF` and, when no diagnostic is added, `sanitize_alias_tables_sorted`.

Proof starting point: unfold `analyze`, rewrite the successful initial-settings result, and state an accumulator-generalized lemma for `process_loop` with a fold over the remaining `IntoIter.val`. `IntoIter` is a vector in the model and `next` is head/tail. The `more = false` branch leaves the accumulator alone. With the include cases excluded, the mutual recursion takes only the iterator step. Use the existing vector length bounds and sanitizer's aggregate diagnostic bound. For an exact diagnostic theorem, supply the owned path when needed, and relate `errorKindText` to the reference's render if the reference does not use the same opaque render. The Rust panic messages themselves are not part of Aeneas's `fail panic` result.

### Settings in force (P5)

1. Begin with the policy's current `settings`, not a new default value on each request. To evaluate the non-command list, form the host and invoking-user matchers and their alias verdicts; then form a runas user matcher and verdicts only if a target user was given. Each alias fold uses the table's sanitizer order, not its definition order. For each customiser in non-command file order, Generic always matches; Host/User match that list against the corresponding matcher and aliases; RunAs is false without a target, otherwise matches the target user (no target group test here). Every list uses `find_item`, the last applicable verdict, with its signed alias semantics. A command scope in this list would be an invariant violation and panic. For each match, apply modifiers left to right. Clear the non-command list regardless of which entries matched.
2. For commands, build `match_command` for the request's path and arguments, resolve its command aliases, and use `find_item` for each command scope. Apply matching customisers and their modifiers left to right, then the command list is empty. `check` always does the non-command pass first and the command pass second: any matching command customiser runs after all non-command customisers, even if it appeared before them in the file. Within each pass, there is no further ordering by scope kind. For scalar settings the later applicable write wins; list changes compose as set/insert/delete in order (see [DEFAULTS.md](DEFAULTS.md) and the spec Settings model). These operations do not modify rules or alias tables.
3. `check` does both passes even if the eventual request is forbidden. It calls `permission_flags` with the unchanged policy and request, and returns a copy of the settings in force and those flags in the judgement. `check_list_permission` does neither scoping pass for listing oneself. For another user, it uses that inspected user as runas and the pseudo-command `list` with no arguments. `check_validate_permission` does only the non-command pass, with no target. Both list and validate map the selected tag to authentication via `Settings::to_auth`, or return `Forbidden` if there is none. A later call uses whatever settings and unconsumed customisers remain.

Reuse the existing matcher and alias lemmas, `InstOracle`, `GlobOracle`, `ListPath` (also supplies the `Path::new("list")` used by the scoping pass), the host equality/representation conditions, and `authorization_eq` with `SettingsInRange`. The scoping theorem can quantify over initial settings; an E2E theorem from text additionally needs to relate the `Settings::default` external to the initial value in the settings spec. The extensional set model and clone do not expose hash seeding or key iteration order.

## Extracted interface

Names below are in `sudo_rs.sudoers` unless otherwise qualified. Write `V = alloc.vec.Vec`, `Item = core.result.Result sudoers.ast.Sudo sudoers.basic_parser.Status`, `Diags = V sudoers.Error`, `Scope T = V (sudoers.ast.Qualified (sudoers.tokens.Meta T))`, and `Cmd = glob.Pattern × sudoers.tokens.Args`. These are notation in this table, not extra Lean declarations. All arrows return `Aeneas.Std.Result` as shown; Rust mutable references become returned values.

| Lean name | Signature (using the notation above) |
|---|---|
| `analyze` | `std.path.Path → V Item → Result (Sudoers × Diags)` |
| `process`, `process_item` | `Sudoers → std.path.Path → V Item` (respectively `Item`) `→ Diags → IncludeState → Result (Sudoers × Diags × IncludeState)` |
| `include`, `include_dir` | `Sudoers → std.path.Path → IncludeFile` (respectively `String`) `→ basic_parser.Span → Diags → IncludeState → Result (Sudoers × Diags × IncludeState)` |
| `include_file` (opaque) | `std.path.Path → IncludeFile → Option IncludeState → Result (core.result.Result (std.path.PathBuf × V Item) String)` |
| `include_dir_files` (opaque) | `std.path.Path → String → Result (core.result.Result (V std.path.PathBuf) String)` |
| `ignored_tags` | `std.path.Path → ast.PermissionSpec → Diags → Result Diags` |
| `ignored_modifiers` | `std.path.Path → Slice ast.Modifier → Diags → Result Diags` |
| `report` | `Diags → std.path.Path → basic_parser.Span → String → Result Diags` |
| `fatal_message` | `basic_parser.ErrorKind → Result String` |
| `append_defs` | `{T : Type _} → V (ast.Def T) → V (ast.Def T) → Result (V (ast.Def T))` |
| `command_scope` | `Scope glob.Pattern → Result (Scope Cmd)` |
| `apply_settings` | `V defaults.SettingsModifier → defaults.Settings → Result defaults.Settings` |
| `Sudoers.specify_host_user_runas` | `{User G : Type _} → system.interface.UnixUser User G → core.cmp.PartialEq User User → Sudoers → system.Hostname → User → Option User → Result Sudoers` |
| `Sudoers.specify_command` | `Sudoers → std.path.Path → Slice std.ffi.os_str.OsString → Result Sudoers` |
| `Sudoers.check` | `{User Group G : Type _} → system.interface.UnixUser User G → core.cmp.PartialEq User User → system.interface.UnixGroup Group → Sudoers → User → system.Hostname → Request User Group G → Result (Judgement × Sudoers)` |
| `Sudoers.check_list_permission` | As `check` with `ListRequest User Group G` and result `Result (policy.Authorization Unit × Sudoers)`. |
| `Sudoers.check_validate_permission` | `{User G : Type _} → system.interface.UnixUser User G → core.cmp.PartialEq User User → Sudoers → User → system.Hostname → Result (policy.Authorization Unit × Sudoers)` |

`process`, `process_loop`, `process_item`, `include`, `include_dir` and `include_dir_loop` form a `partial_fixpoint` mutual block. `process_loop` takes the accumulator fields, an owning iterator and `more`. The generated `Sudoers` record has `rules`, `aliases`, `settings` and `customisers`; `CustomiserTable` has `non_cmnd` and `cmnd`. The decision core's existing definitions and theorem statements are not changed. The models for names newly emitted in `FunsExternal_Template.lean` are in `FunsExternal.lean`; their Rust justifications are in [ASSUMPTIONS.md](../lean/ASSUMPTIONS.md).

To extract the text entry point after the M2 parser lands, add `crate::sudoers::analyze_text` to `start_from` and regenerate. It calls `parse_sudoers`, so it will reach `CharStream::from_chars` and the concrete `Parse Sudo` instance of `parse_lines`, without adding any I/O edge to the call graph. The generic `parse_lines` already extracts; its `Sudo` instance is the missing prerequisite, not a new parser entry point. Keep the separate parsed-items root for PA. To prove E2E, compose the resulting text entry point with PR/PT1, PA, the scoping refinement, `permission_flags_eq` and `authorization_eq`; the no-include case does not require extraction of secure open or the include oracle's file reading. For a clean-file theorem also use PT6 and the no-diagnostics sanitizer premise.

## Test evidence

`src/sudoers/test/legacy_analysis.rs` keeps the old analysis and two scoping bodies from `d84ff98a` (the same analysis as `70fdb56b`, with the current data-valued modifiers and rendered error kind). The harness feeds both analyses the same live parser to isolate the restyle; the parser's own equivalence tests separately compare it with the original parser. It compares rules and every alias definition and order vector, customisers including Debug of each modifier, default settings, the ordered diagnostic triples, and the settings in force (`Settings::dump_fields`) plus decisions and ignored-specifier warning order for six requests. The requests include run, list-self, list-other and validate; a second scoping pass also checks consumption. It compares panic messages when both paths panic.

Successful includes use actual files in a per-thread temporary tree, with only the ownership gate bypassed in the test build for that tree. A separate fixture exercises the real audited path. The tree checks relative and absolute `@include`, nested includes, the sorted and filtered `@includedir` traversal, missing and unreadable input, `%h`, internal diagnostics, and both deep and wide use of the shared budget. None of these tests installs or executes a privileged binary. There is no new upstream-behaviour finding from this comparison.

## Measured sizes

| Measure (against `b6a9bbdb`) | Size |
|---|---:|
| `src/sudoers/mod.rs`, lines added / removed | 458 / 310 |
| New Rust analysis equivalence test / legacy snapshot, lines | 558 / 395 |
| Generated `Funs.lean` growth (including comments) | 935 lines; 40 new definitions |
| Generated `Types.lean` growth (including comments) | 86 lines; 7 new declarations |
| Hand-maintained `FunsExternal.lean` growth | 78 lines |

Compared generated declarations by name after excluding source locations: no pre-existing function or type body changed. Declaration order can change when adding roots. Extraction after rebase took 71 seconds wall clock including the dev wrapper and used 805 MiB peak memory as reported by the limiter.
