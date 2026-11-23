# Parser dump: format, conventions, harness

Stage P0 of `PLAN.md`. The current parser dump is a canonical text rendering of what
`parse_lines::<Sudo>` returns for a sudoers text. It is a contract between the Rust parser,
through `src/sudoers/test/parser_dump.rs` (`cfg(test)`), and the Lean reference parser
(`Syntax.parseSudoersWith`), through a Lean printer of the same format.

Two dumps of the same text are compared byte for byte. Evidence kind: test (only the inputs run).

## 1. Format (version 2)

ASCII, one record per line, one record per item of the vector `parse_lines` returns, in order.
Corpus files start with `parser-dump 2` on its own line, then each case starts with a
`case <label>` line. The comparators reject a missing or different header and a file with no
cases. Individual case dumps do not have headers.
Grammar (EBNF; `" "` is one space, `"\n"` one line feed; nothing else is whitespace):

```
dump       = { record "\n" } ;
record     = "ok " sudo | "fatal " span " " string | "reject" | "panic " string ;

sudo       = "(spec " list(spec(user)) " " list(perm) ")"
           | "(user_alias " list(def(user)) ")"
           | "(runas_alias " list(def(user)) ")"
           | "(host_alias " list(def(host)) ")"
           | "(cmnd_alias " list(def(command)) ")"
           | "(defaults " scope " " list(setting) ")"
           | "(include " string " " span ")"
           | "(includedir " string " " span ")"
           | "comment" ;
(* feature unstable-remote-sudoers only: *)
           | "(remote " string " (peer " ident " " ("none" | "(some " ident ")") ") " span ")"

list(x)    = "[" [ x { " " x } ] "]" ;
spec(x)    = "(allow " meta(x) ")" | "(forbid " meta(x) ")" ;
meta(x)    = "all" | "(alias " string ")" | "(only " x ")" ;
def(x)     = "(def " string " " list(spec(x)) ")" ;

ident      = "(name " string ")" | "(id " nat ")" ;
user       = "(user " ident ")" | "(group " ident ")" | "(nonunix " ident ")" ;
host       = string ;
perm       = "(perm " list(spec(host)) " " list(entry) ")" ;
entry      = "(entry " runas " " list(modifier) " " spec(command) ")" ;
runas      = "none" | "(runas " list(spec(user)) " " list(spec(ident)) ")" ;
modifier   = "passwd" | "nopasswd" | "setenv" | "nosetenv" | "exec" | "noexec" | "noop"
           | "(cwd " ("any" | "(path " string ")") ")"
           | "(apparmor " string ")"
           | "(ignored " span ")" ;
command    = "(cmd " string " (" ("prefix" | "exact") " " list(string) "))" ;
simplecmd  = string ;
scope      = "generic"
           | "(host " list(spec(host)) ")"
           | "(user " list(spec(user)) ")"
           | "(runas " list(spec(user)) ")"
           | "(command " list(spec(simplecmd)) ")" ;
setting    = "(setting " settingname " " payload ")" ;
payload    = "true" | "false" | nat | enumname | string | "none" | "(some " string ")"
           | "(" ("set" | "add" | "del") " " list(string) ")" ;

span       = nat ":" nat "-" nat ":" nat ;          (* start line:col - end line:col, 1-based *)
nat        = "0" | digit1-9 { digit } ;             (* decimal *)
string     = '"' { char } '"' ;                     (* section 2 *)
```

Mapping from the AST (`src/sudoers/ast.rs`, `tokens.rs`):

| Rust | Dump |
|---|---|
| `Ok(Sudo::Spec(PermissionSpec { users, permissions }))` | `ok (spec users permissions)`; a permission is one `Hostname`-list / entry-list pair |
| `(Option<RunAs>, CommandSpec(modifiers, cmd))` | `(entry runas modifiers cmd)` |
| `Qualified::Allow/Forbid`, `Meta::All/Alias/Only` | `(allow m)`/`(forbid m)`, `all`/`(alias "NAME")`/`(only x)` |
| `Identifier::Name(s)` / `ID(n)` | `(name "s")` / `(id n)` |
| `UserSpecifier::User/Group/NonunixGroup` | `(user i)` / `(group i)` / `(nonunix i)` |
| `Hostname(s)` | `"s"` |
| `Command = (SimpleCommand, Args)` | `(cmd "pattern" (prefix [args]))` or `(... (exact [args]))`; pattern = `glob::Pattern::as_str` (the text after canonicalization, section 5) |
| `Modifier::Cwd(ChDir::Any / Path(p))` | `(cwd any)` / `(cwd (path "p"))` |
| `Modifier::Ignored(span)` | `(ignored span)`: span of the tag keyword (`LOG_INPUT`, ...) |
| `Modifier::NoOp` | `noop` (`NOFOLLOW`, `NOINTERCEPT`) |
| `Directive::Defaults(modifiers, scope)` | `(defaults scope [settings])`, section 3 |
| `Sudo::Include(path, span)` / `IncludeDir` | `(include "path" span)` / `(includedir "path" span)` |
| `Sudo::LineComment` | `comment` |
| `Err(Status::Fatal(span, msg))` | `fatal span "msg"`: the span and message text exactly |
| `Err(Status::Reject)` | `reject` (not produced by `parse_lines`, which turns a rejection into a fatal error) |
| a panic of the parser | the whole dump of the text is the single record `panic "message"` |

`Defaults` modifiers are encoded injectively: the setting name identifies the variant and
the syntax for its payload identifies every value of that variant (section 3). Other records
retain the same observations as before, such as the rendered diagnostic message together with
its span, and command-pattern text after canonicalization.

## 2. Strings

`"` + characters + `"`. A character in U+0020..U+007E other than `"` and `\` is written as is;
`"` is written `\"`, `\` is written `\\`; every other Unicode scalar value `c` is written
`\u{h}` where `h` is the hexadecimal value of `c`, lowercase, without leading zeros (`\u{a}` for
a line feed, `\u{e9}` for `é`, `\u{10ffff}`). The output is printable ASCII; decoding is
unambiguous. Implementations: `dump_quoted` in `src/defaults/settings_dsl.rs` (used as `quote`
in `parser_dump.rs`), `Differential.Quote` in `proofs/differential`, and `unquote` in
`parser_compare.py`.

## 3. Settings modifiers

Version 2 prints each `defaults::SettingsModifier` directly as `(setting name payload)`
from one parse, without calling `apply`. The Rust observer is generated from the `defaults!`
DSL in `src/defaults/settings_dsl.rs`; the Lean observer matches on the corresponding
constructors of `SudoersSpec.Settings.SettingsModifier`.

- Booleans are `true` or `false`; integers are decimal; enums use the variant name.
- A text value is quoted. An optional text value is `none` or `(some "...")`, so `(some "")`
  is distinct from `none`.
- A list modifier carries its mode and the parsed strings in order, including duplicates:
  `(set ["B" "A" "B"])`, `(add ["B" "A" "B"])` or `(del ["B" "A" "B"])`. No set
  operations, sorting or deduplication are performed by the observer.

The dump observes parsed values, not source spellings that produce the same value.

**Historical format (version 1, no header).** The legacy parser used closures instead of
data. Its modifier record `(setting A B)` printed every field after applying the modifier
to two fixed bases, the default settings and a base chosen to differ from the default in
every field. The v1 harness parsed twice and emitted a separate `.bases` file. Two
modifiers that had the same effect on both bases were indistinguishable in that format.
Historical results using it do not establish identity of parsed modifiers.

`Settings::dump_fields` remains available to tests of effective settings; it prints booleans,
integers, enums and text as above and sets as lists of quoted strings in ascending order.

## 4. Character classes

Five Unicode-aware predicates decide tokens: `char::is_alphanumeric` (user names),
`is_uppercase` (`Meta` aliases), `is_numeric` (IPv4 check of host names), `is_control`,
`is_whitespace`. The test `write_char_table` writes their table to the path in
`SUDO_PARSER_DUMP_CHARTABLE` (nothing when unset). Format, one item per line:

```
unicode <major>.<minor>.<update>          (char::UNICODE_VERSION of the toolchain that ran it)
<predicate> <first> <last>                (lowercase hexadecimal code points, inclusive)
```

with `<predicate>` in `alphanumeric`, `uppercase`, `numeric`, `control`, `whitespace`, in this
order; per predicate the maximal ranges of scalar values in ascending order. Surrogates are not
scalar values and are never members, so no range crosses U+D800..U+DFFF. With the pinned
toolchain (rustc 1.99) the table is Unicode 17.0.0, 1,663 lines. Every other character test of
the parser is on ASCII or on fixed characters.

## 5. Environment dependence and corpus conventions

The dump is a function of the text, the character-class table, the file system, and the glob
compiler:

- **File system.** `SimpleCommand::construct` replaces a command path that exists by
  `common::resolve::canonicalize`: the canonical form of the parent directory joined with the
  final component (a symbolic link in the final component is kept), only if the result exists;
  a trailing `/` is removed first and `/*` appended afterwards. Rust `Path` rules apply: empty
  and `.` components are dropped, a final `..` has no file name (so `/d/..` becomes `/d`).
- **Glob compilation.** `glob::Pattern::new` (glob 0.3.4) is a pure function of the pattern
  text; only its failure is visible, as `fatal ... "wildcard pattern error Pattern syntax error
  near position P: MSG"` where `P` counts characters. Over the characters `c[0..n)`: a run of
  `*` longer than 2 fails at `start+2` with "wildcards are either regular `*` or recursive
  `**`"; a run of exactly 2 must be preceded by `/` or the start and followed by `/` or the end,
  else it fails at the end of the run (not followed) or at `start-1` (not preceded) with
  "recursive wildcards must form a single path component"; a `[` must be followed by either
  `!` + at least one character + `]` found from index `i+3`, or at least one character + `]`
  found from index `i+2` (with `c[i+1] != '!'`), else it fails at `i` with "invalid range
  pattern". Nothing else fails.

Corpus conventions that make the dump reproducible elsewhere:

1. Command paths of the generated corpus start with `/sudoers-nx/`, which must not exist (the
   harness checks it). Nothing under it is canonicalized.
2. The category `fixture` uses the fixture root `/tmp/sudo-rs-parser-dump-fixture`. The harness
   creates it once and checks it on reuse. A different owner, writable-by-others directory,
   or unexpected layout fails the run without deleting or replacing the existing tree:

   ```
   bin/             directory
   bin/tool         empty file
   bin/alias  -> tool   (symbolic link)
   link       -> bin    (symbolic link)
   sub/             directory
   incdir/          empty directory   (include target)
   include          empty file        (include target)
   ```

   Examples (input path -> dumped pattern): `bin/tool` -> `bin/tool`; `link/tool` and
   `sub/../bin/tool` and `bin//tool` -> `bin/tool`; `link/alias` -> `bin/alias`; `bin/alias` ->
   `bin/alias`; `bin/` -> `bin/*`; `link/` -> `link/*`; `bin/.` and `bin/..` -> `bin`;
   `bin/tool/` -> `bin/tool/*`; `missing` and `bin/*` unchanged (all under the root).
3. A mutated case can still name an existing host path (`/`, `/tmp`, `/etc/passwd`). The harness
   lists, in `<OUT>.hostdep`, `<label> <quoted pattern>` for every accepted command pattern
   (rules, `Cmnd_Alias`, `Defaults!`) outside the fixture root that names an existing path,
   with `/*` removed: such a case may have been canonicalized and its dump holds for this host
   only. (Conservative: a non-existing path never appears; seed 1, N=200: 1 case.)
4. Include targets are the fixture's `include` and `incdir`, or paths under `/sudoers-nx/`; the
   parser does not open them (`analyze` does).

## 6. Harness and corpus

`src/sudoers/test/parser_dump.rs` (`cfg(test)`):

| Item | Use |
|---|---|
| `dump(text)` | the dump of a text |
| `dump_catching(text, on_host_path)` | the same, reporting host-dependent paths from that parse or recording a panic as `panic "message"` |
| test `dump_corpus` | with `SUDO_PARSER_DUMP_CORPUS` set: reads the corpus (a file of lines `<label> <quoted text>`, or a directory with one case per file, label = file name, in name order), writes the versioned `SUDO_PARSER_DUMP_OUT` and `<OUT>.hostdep`; creates the fixture. Does nothing when unset |
| test `write_char_table` | `SUDO_PARSER_DUMP_CHARTABLE` |
| tests `plan_3_3_recovery_rows`, `finding_f_p3_quoted_non_user`, `finding_f_p4_hash_identifier` | the rows of PLAN.md 3.3 (first table) and F-P3, F-P4 pinned as dump expectations |

Corpus generator: `proofs/differential/Differential/ParserCorpus.lean`, executable `parser`.

```
cd proofs/differential && lake build parser
.lake/build/bin/parser corpus SEED N > corpus.txt      # N cases per category and mutation operator
.lake/build/bin/parser categories SEED N               # cases per category
```

Every case is a pure function of `(seed, category, index)` (SplitMix64, `Differential/Rng.lean`)
and carries its label `<category>:<index>`. Grammar categories (each generator draws from
"valid" forms and, where the category is about a construct, from rejected or borderline forms):
`blank`, `user`, `host`, `runas`, `tag`, `command`, `alias`, `defaults`, `include`, `rule`
(valid rules), `valid` (valid lines of every kind), `mixed`, `continuation` (backslash-newline at
random points, stray backslashes), `whitespace` (tabs, VT, FF, CR, NBSP, U+2028, U+3000, NEL,
ZWSP, BOM, CRLF), `unicode` (multi-byte, non-ASCII upper case and digits, controls, in every
token), `eof` (missing final newline), `maxlen` (every `MAX_LEN`: 10, 18, 255, 1024, at -2..+2
characters, with multi-byte endings), `listlimit` (lists of 1, 126, 127, 128, 129 items of every
list kind, tags, quoted variable lists), `fixture`. Mutation categories `mut.<op>.<source>`:
`delete-char`, `insert-char`, `replace-char`, `duplicate-char`, `swap-char`, `delete-token`,
`duplicate-token`, `swap-token`, `truncate`, `splice-lines`, applied one to three times to a case
of a grammar category, positions biased towards `,:=!()"\#@%+` and newline. Category `known`:
the inputs of PLAN.md 3.3 and F-P1 to F-P6, verbatim.

Run the dump on a corpus (from the repository root, dev shell):

```
SUDO_PARSER_DUMP_CORPUS=corpus.txt SUDO_PARSER_DUMP_OUT=sudo-rs.dump \
SUDO_PARSER_DUMP_CHARTABLE=chartable.txt \
  cargo test --lib sudoers::test::parser_dump:: -- --test-threads=1
```

The whole stage-P0 pipeline (corpus, dump, C sudo, comparison) is `proofs/differential/
parser-run.sh`; see `C-SUDO.md`.
