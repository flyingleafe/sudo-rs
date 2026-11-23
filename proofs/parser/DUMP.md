# Parser dump: format, conventions, harness

Stage P0 of `PLAN.md`. The dump is a canonical text rendering of what the legacy parser
(`parse_lines::<Sudo>` at `70fdb56b`) returns for a sudoers text. It is a contract between three
producers:

1. the legacy parser, through `src/sudoers/test/parser_dump.rs` (`cfg(test)`);
2. the Lean reference parser (`Syntax.parseLines`), through a Lean printer of the same format;
3. the restyled Rust parser, which must produce the same dump as the legacy one.

Two dumps of the same text are compared byte for byte. Evidence kind: test (only the inputs run).

## 1. Format

ASCII, one record per line, one record per item of the vector `parse_lines` returns, in order.
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
setting    = "(setting " fields " " fields ")" ;
fields     = "[" field { " " field } "]" ;          (* all 35 fields, section 3 *)
field      = "(" fieldname " " value ")" ;
value      = "true" | "false" | nat | enumname | string | "none" | "(some " string ")"
           | "[" [ string { " " string } ] "]" ;

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

Injectivity: the format is a prefix-free tree encoding with injective string quoting, so two
values with different dumps differ, and every field of every AST node is printed, with one
exception: a settings modifier is printed by its effect on two fixed bases (section 3), not by
its identity.

## 2. Strings

`"` + characters + `"`. A character in U+0020..U+007E other than `"` and `\` is written as is;
`"` is written `\"`, `\` is written `\\`; every other Unicode scalar value `c` is written
`\u{h}` where `h` is the hexadecimal value of `c`, lowercase, without leading zeros (`\u{a}` for
a line feed, `\u{e9}` for `é`, `\u{10ffff}`). The output is printable ASCII; decoding is
unambiguous. Implementations: `quote` in `parser_dump.rs`, `dump_quoted` in
`src/defaults/settings_dsl.rs`, `Differential.Quote` in `proofs/differential`, `unquote` in
`parser_compare.py`.

## 3. Settings modifiers

`defaults::SettingsModifier` is data (`proofs/parser/DEFAULTS.md`); it was a
`Box<dyn FnOnce(&mut Settings)>` in the legacy parser, so the format describes a modifier by
what both forms can show. A modifier is dumped by its effect: `(setting A B)`, where `A` is
`Settings::default()` after `apply` and `B` is base B after `apply`. `apply` consumes the
modifier and the type is not `Clone`, so the harness parses the text twice and applies the n-th
modifier of the first parse to base A and the n-th of the second parse to base B.

Fields are printed by `Settings::dump_fields` (`cfg(any(test, fuzzing))`,
`src/defaults/settings_dsl.rs`), every field in declaration order (that of `defaults!` in
`src/defaults/mod.rs`): `true`/`false`; integers in decimal; enums by variant name; `Box<str>`
as a string; `Option<Box<str>>` as `none` or `(some "...")`; `HashSet<String>` as `[...]` of
strings in ascending order (Rust `String` order, i.e. by bytes).

**Base A** is `Settings::default()`. On Linux:

```
always_query_group_plugin false, always_set_home false, env_reset true, fqdn false,
ignore_dot true, lecture never, mailerpath none, mail_badpass true, match_group_by_gid false,
use_pty true, visiblepw false, pwfeedback true, rootpw false, targetpw false, noexec false,
noninteractive_auth false, log_allowed true, log_denied true, insults false, setenv false,
runcwd none, apparmor_profile none, umask 18, umask_override false, passwd_tries 3,
secure_path none, verifypw all, passwd_timeout 300, timestamp_timeout 900, timestamp_type tty,
editor "/usr/bin/editor:/usr/bin/nano:/usr/bin/vi" (other targets: "/usr/bin/vi"),
env_editor true, env_keep (11 names), env_check (7 names), env_delete (37 names)
```

**Base B** differs from base A in every field. It is base A with these modifiers applied, in
this order (`BASE_B` in `parser_dump.rs`; flags set, `!` negated, others assigned, lists set):

```
always_query_group_plugin, always_set_home, !env_reset, fqdn, !ignore_dot, lecture=always,
mailerpath=/b/mailer, !mail_badpass, match_group_by_gid, !use_pty, visiblepw, !pwfeedback,
rootpw, targetpw, noexec, noninteractive_auth, !log_allowed, !log_denied, insults, setenv,
runcwd=/b/cwd, apparmor_profile=b_profile, umask=077, umask_override, passwd_tries=7,
secure_path=/b/bin, verifypw=any, passwd_timeout=2, timestamp_timeout=3, timestamp_type=ppid,
editor=/b/editor, !env_editor, env_keep="B_KEEP", env_check="B_CHECK", env_delete="B_DELETE"
```

giving `umask 63`, `passwd_timeout 120`, `timestamp_timeout 180` and the lists `["B_KEEP"]`,
`["B_CHECK"]`, `["B_DELETE"]`. The test `base_b_differs_from_default_everywhere` checks the
"every field differs" property. The corpus harness writes both bases to `<OUT>.bases`
(`a [fields]`, `b [fields]`).

Limit: two modifiers that agree on both bases have the same dump. This happens only for list
removals (`-=`) of names that are in neither base: `env_keep -= "FOO"` and `env_keep -= "BAR"`
both leave both bases unchanged. Every other modifier of the 35 settings is identified by its
two effects.

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
2. The category `fixture` uses the fixture root `/tmp/sudo-rs-parser-dump-fixture`, which the
   harness recreates before every run (and checks to be its own canonical path):

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
| `dump_catching(text)` | the same, a panic recorded as `panic "message"` |
| test `dump_corpus` | with `SUDO_PARSER_DUMP_CORPUS` set: reads the corpus (a file of lines `<label> <quoted text>`, or a directory with one case per file, label = file name, in name order), writes `SUDO_PARSER_DUMP_OUT` (per case `case <label>` and its dump), `<OUT>.hostdep`, `<OUT>.bases`; creates the fixture. Does nothing when unset |
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
