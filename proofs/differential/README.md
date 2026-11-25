# Differential test of the sudoers decision: spec, sudo-rs, C sudo; property search on sudo-rs

A three-way differential test of the authorization decision:

1. the Lean specification `SudoersSpec.authorize` (`../spec`), run as an executable oracle;
2. sudo-rs: the real sudoers parser (`Sudoers::read`) and the real decision (`Sudoers::check`);
3. C sudo 1.9.18 (`/tmp/fi/src/sudo`, git `d58e85d`): `plugins/sudoers/testsudoers`, which runs
   the real sudoers parser and `sudoers_lookup`.

and a search for counterexamples to seven properties of the real sudo-rs code, each stated in
Lean as a predicate over test cases (`Differential/Props.lean`).

The comparisons below are **test** evidence on the inputs tried.
`CModel.decide_off` and `Differential.OrdinaryPolicyRange` are kernel-checked
results, not sampled tests.
`ordinaryPolicy_range` proves that, for every starting `Rng`, the unchanged
`Generate.policy {}` returns one to four structurally printable permission rules.
The proof follows the generator's list lengths, weighted choices and literal
pools. `ordinaryPolicy_roundTrip` then proves that the reference `Syntax.sudo`
recovers each rule from the shared renderer followed by a newline, preserving
the suffix and final position. The character oracle is the reference Latin-1
table; the fixed path snapshot must leave each generated command path unchanged
(or report canonicalization failure) and compile it successfully as a glob.
The theorem does not cover hazard-mode generation, alias-definition rendering
or authorization. To build just this proof and its axiom report, run
`lake build Differential.OrdinaryPolicyRange` from this directory.

For `./run.sh 20000 1`, the spec and sudo-rs agree on all 20,000 cases, on the verdict with
every tag field and on the alias diagnostics of `Sudoers::read`. 7,629 of the cases contain
alias hazards (names spelled like aliases, references to undefined aliases, cycles, duplicate
definitions). C sudo rejects 2,665 policies (all of them with a duplicate alias definition);
on the other 17,335 cases a model of C (the spec with C's runas, argument and alias rules
switched in) agrees with `testsudoers` on every case, and the spec and C sudo disagree on 171
(see *Findings*). This is empirical evidence, not a proof of the C code.

The property search (`./props.sh`) ran every property on at least 10,000 instances whose
precondition holds; see *Properties of the real code*.

The separate [command-path glob comparison](#command-path-glob-conformance) exercises
path patterns that the three-way policy generator does not produce.

## Running

```
cd proofs/differential && nix develop ../.. -c ./run.sh [N] [SEED]      # defaults: 20000 1
cd proofs/differential && nix develop ../.. -c ./props.sh [N] [SEED] [PROPS]   # defaults: 10000 1 "a b c d e f g"
```

`run.sh` does the following:

1. builds `testsudoers` from a scratch copy of the C sources (`build-testsudoers.sh`) and the Lean
   package (`lake build`);
2. checks that none of the generated command paths exists on the machine;
3. generates the cases (`oracle gen N SEED`);
4. runs sudo-rs (`cargo test --lib differential_cases` with `SUDO_DIFF_CASES` / `SUDO_DIFF_OUT`);
5. runs `testsudoers` on every case (`oracle csudo`);
6. prints the feature coverage (`oracle coverage`);
7. compares, saves the disagreements and minimises them (`oracle compare`).

The exit status is non-zero if the spec and sudo-rs disagree on any case.

Environment variables:
- `DIFF_SCRATCH` (default `/tmp/sudo-differential`) holds the cases, the engine outputs, the
  private `CARGO_TARGET_DIR` and the `testsudoers` build. It takes about 100 MB. Delete it when
  done. `TS_BUILD` and `CARGO_TARGET_DIR` move the last two elsewhere (to reuse a build).
- `SUDO_SRC` (default `/tmp/fi/src/sudo`) is the C source tree. It is read-only; the build
  happens in a copy.
- `JOBS` (default `nproc`) is the number of parallel `testsudoers` workers.
- `MINIMIZE` (default 20) is how many disagreements of each cause and kind are minimised.

The run takes about 6 minutes on 4 CPUs. The outputs go to `disagreements/` (git-ignored,
replaced on every run):

| Path | Content |
|---|---|
| `sudo-rs/case-I.case` | spec vs sudo-rs disagreements (none at seed 1) |
| `c-model/case-I.case` | C model vs `testsudoers` disagreements (none at seed 1) |
| `c-sudo/CAUSE/KIND/case-I.case` | every spec vs C sudo disagreement |
| `c-sudo-minimized/CAUSE/KIND/case-I.case` | the same cases, minimised |
| `c-sudo-minimized/summary.txt` | the distinct minimised policies and requests for each cause and kind |

Each ignored `.case` file contains a synthetic policy, synthetic user/group data, and the
oracle outputs. These are policy-evaluation fixtures, not tests of the privileged runtime.

`props.sh` builds the oracle and the sudo-rs unit-test binary, checks the generated paths,
and runs `oracle prop` for each property: it draws N instances, runs their probes on the test
binary in batches, checks each instance, shrinks the first `CAP` (default 5) failures of every
class, runs each shrunk instance twice more, and writes it with its probe records and results to
`PROPS_OUT/NAME/CLASS/inst-I.txt` (default `PROPS_OUT=/tmp/sudo-props`, outside the
repository). The summary goes to standard output.

## Design

### Oracle (`Differential/*.lean`, `Main.lean`)

A Lake package. It depends only on `../spec` (by path) and has no Mathlib or Aeneas dependency.
The spec decision is `SudoersSpec.authorize (oracleOf db) policy request`, unchanged.

- **`Rng.lean`**: SplitMix64. Case `i` of a run with seed `s` is drawn from its own generator,
  seeded with `(s, i)`, so every case can be regenerated on its own (`oracle show s i`).
- **`Db.lean`**: the per-case passwd and group database, and the oracle it induces. The oracle
  instantiates `SudoersSpec.Oracle` the way the real `User` and `Group` types behave
  (`src/system/interface.rs`):
  - names and uids are compared literally, and `is_root` is `uid == 0`;
  - a user's group vector is the primary gid plus every group that lists the user as a member
    (`getgrouplist`);
  - `in_group_by_name` resolves the name through the database;
  - user equality is equality of the whole passwd entry (`#[derive(PartialEq)]`);
  - host matching is string equality, and so is glob matching (no generated path contains a
    metacharacter).

  `Cli.resolve` mirrors `resolve_target_user_and_group` (`src/common/resolve.rs`): `-g` alone
  runs as the invoking user, `-u` alone uses the target's primary group, and no flags means
  `root:root`.
- **`Generate.lean`**: the generator. The database is fixed: `root` and `toor` (both uid 0),
  `alice`, `bob`, `carol`, `dave`, the accounts `UA1` and `RA0`, ten groups (two of them, `RA1`
  and `UA0`, spelled like aliases) and the hosts `h1`-`h3` and `HA1`. Primary groups and
  memberships are random. Each policy has 0-3 aliases of each kind (`User_Alias`,
  `Runas_Alias`, `Host_Alias`, `Cmnd_Alias`, named `UA0`, `RA0`, `HA0`, `CA0`, ...). Aliases are
  nested: a definition may refer to earlier ones. Members may be negated. The definitions are
  printed in random order, so sudo-rs's topological sort and C's lazy lookup are both
  exercised.

  Each policy also has 1-4 lines with 1-2 host groups each. A line holds:
  - user lists with `user`, `#uid`, `%group`, `%#gid`, `ALL`, alias references and `!`;
  - runas `(users)`, `(users : groups)`, `(: groups)`, `()`, or none;
  - the tags `NOPASSWD`, `PASSWD`, `SETENV`, `NOSETENV`, `NOEXEC`, `EXEC`;
  - commands: a bare path, `path ""`, `path args`, `path args *`, `ALL`, `Cmnd_Alias`
    references, and `!`.

  Half of the cases also have **alias hazards**, each with its own probability:
  - names spelled like aliases in user, host, runas-user and runas-group positions: the
    accounts, groups and host above, which coincide with the names of generated aliases of
    some tables and not of others, and names that no table defines (`UA7`, `RA7`, `HA7`, `CA7`,
    and a `Host_Alias` name in a user list or a command list);
  - references to undefined aliases, in rules and in alias bodies;
  - cyclic definitions (a body may refer to its own or a later definition);
  - duplicate definitions (a second definition of an existing name, with another body).

  The request (invoking user, host, `-u`/`-g`, command, arguments) is biased towards the names,
  hosts, runas specs and commands that occur in the policy. This gives about 16% allows.
- **`Sanitize.lean`**: alias definitions as written (`AnyDef`, in file order) and a
  transcription of `sanitize_alias_table` (`src/sudoers/mod.rs`): the processing order of each
  table and the diagnostics `undefined alias`, `recursive alias` and `multiple occurrences`, in
  the order sudo-rs reports them. The spec takes alias tables in processing order and leaves the
  sort out of scope, so this is part of the oracle; the comparison checks its diagnostics
  against sudo-rs's.
- **`Print.lean`**: the AST-to-sudoers printer, one function per AST node. Each function inverts
  one parser production; the table in the module docstring lists them. An upper-case name is
  generated as an alias reference (`Meta.alias`), which is what both parsers make of it (see
  *Upper-case names*).
- **`Case.lean`**: the case record (rules, alias definitions in file order, database,
  request) and `Probe`, the record the sudo-rs harness reads. This line-based text format is
  shared with the harness and `repro.sh`. The spec verdict line has the form
  `allow auth=… env=… exec=… cwd=… apparmor=…` or `deny`, followed by ` ;; MESSAGE` for every
  predicted diagnostic.
- **`CSudo.lean`**: the C driver. It writes the case's `passwd` and `group` files, runs
  `testsudoers -p passwd -P group -h HOST [-u U] [-g G] USER CMD ARGS < sudoers` and parses
  the verdict:
  - `Command allowed` means allow; `Command denied` and `Command unmatched` mean deny;
    `Parse error` means C rejects the policy;
  - `testsudoers-flags.patch` adds one output line: the values of `def_authenticate`,
    `def_setenv` and `def_noexec` after `apply_cmndspec`. Nothing else in C sudo is changed;
  - `testsudoers` stops before `check_user`, so `effectivePasswd` applies the password
    exemptions of `check.c` 166-182: authentication off, invoking uid 0, or
    `running_as_user`.
- **`CModel.lean`**: the attribution model. `decide toggles case` is the spec decision, built
  from the spec's own functions, with three switchable components:
  - `cRunas` replaces sudo-rs's runas test with a transcription of C's `runaslist_matches`,
    `runas_userlist_matches` and `runas_grouplist_matches` (`match.c` 151-331);
  - `cArgs` replaces argument matching with C's `fnmatch`-based `command_args_match`
    (`match_command.c` 80-112);
  - `cAliases` replaces the `get_aliases` tables with C's evaluation of an alias reference
    (`alias_get` in `alias.c`, the `ALIAS` cases of `match.c`): a recursive evaluation of the
    first definition of the name, with C's handling of a name that `alias_get` does not return
    (undefined, or already being evaluated).

  `decide_off` proves that with all switches off, `decide` is the spec decision.
- **`Compare.lean`**: the comparison.
  - Spec vs sudo-rs compares the full result line: verdict with every tag field, and the
    diagnostics.
  - Spec vs C sudo compares allow/deny. For allows it also compares "password asked",
    "SETENV in effect" and "NOEXEC in effect". `cKind` names the difference (the kind). A policy
    that `testsudoers` rejects is not compared (cause `c-parse-error`).
  - The cause of a disagreement is the first switch set (`{cArgs}`, `{cAliases}`, `{cRunas}`,
    then the pairs, then all three) under which `CModel.decide` agrees with `testsudoers`.
  - Runas causes are refined by `runasLabels`: for each candidate entry on which the two runas
    tests differ, the label records the situation (no runas spec; running as oneself or as
    another user; target group one of the target's groups or not). Alias causes are refined by
    `aliasLabels`: which referenced aliases get different values in sudo-rs and in C, and
    whether they are undefined or on a cycle.
- **`Minimize.lean`**: a greedy 1-minimiser. It drops rules, host groups, entries, list items,
  tags, alias definitions, arguments, `-u`/`-g` and group memberships, as long as the
  disagreement keeps its cause and kind. `minimizeBatch` does the same with one run of the
  sudo-rs harness per step (for the property search).
- **`Coverage.lean`**: counts how many cases contain each generated feature.
- **`Engine.lean`**, **`Inline.lean`**, **`Props.lean`**, **`PropRun.lean`**: the property
  search (see *Properties of the real code*).

### sudo-rs harness (`src/sudoers/test/differential.rs`)

A `#[cfg(test)]` module, registered by one `mod differential;` line in
`src/sudoers/test/mod.rs`. It reads the records and builds fake `UnixUser`/`UnixGroup` values
over each record's database. These behave like `impl UnixUser for User` and
`impl UnixGroup for Group`. The harness resolves `-u`/`-g` as `resolve_target_user_and_group`
does, including `#uid`/`#gid` (`NameOrId::parse`: the text after `#` is parsed as a `u32` with
`str::parse`; the first passwd or group entry with that id is taken, as `getpwuid`/`getgrgid`
do). It parses the policy with `Sudoers::read`, calls `Sudoers::check`, and prints the verdict
followed by every diagnostic. With `mode list` it prints instead the entries that `sudo -l`
prints for the invoking user on the host (`Sudoers::matching_entries` and
`impl Display for Entry`, as `src/sudo/pipeline/list.rs` prints them). Without
`SUDO_DIFF_CASES` the test does nothing.

An entry whose runas user list is empty (`()`, `(: groups)`) prints the name of the real user of
the process (`CurrentUser::resolve` in `src/sudoers/entry.rs`); in `sudo -l` that is the invoking
user, so the harness replaces the test process's own name there by the invoking user's name.

### Lean hygiene

`lake build` builds the package with no `sorry`, no `axiom` and no `native_decide`.
`CModel.decide_off` (with helper `CModel.ite_isSome`) proves the all-switches-off case;
the separate generator proof and axiom report are in `Differential.OrdinaryPolicyRange`.

## Upper-case names

Both parsers read a word of the form `[A-Z][A-Z0-9_]*` other than `ALL` (and the tag keywords
in a command position) as a reference to an alias, in user lists, host lists, runas user lists
and runas group lists, and in command lists:

| | sudo-rs | C sudo 1.9.18 |
|---|---|---|
| user, host, runas user, runas group position | `Meta::Alias` (`Meta::construct`, `src/sudoers/tokens.rs`; `parse_meta`, `src/sudoers/ast.rs`) | `ALIAS` token (`toke.l` line 697), member of type `ALIAS` |
| command position | `Meta::Alias` (`MetaOrTag::parse`, `ast.rs`); `NAME=` is an error | `ALIAS` token |
| `%NAME`, `%#gid` | a group (`UserSpecifier::parse`), not an alias | a group (`USERGROUP`) |
| `"NAME"` (quoted) | a plain user name (checked with the harness: `"UA0" ALL = /bin/ls` allows the account `UA0`) | a plain user name (checked with `testsudoers`) |
| alias table looked up | the table of the position (user list: `User_Alias`; host list: `Host_Alias`; runas user and group lists: `Runas_Alias`; command: `Cmnd_Alias`) | the same |

So an account, group or host whose name is spelled like an alias can only be named in a policy
by quoting it (users), by `%` (groups) or by `#id`. sudo-rs never matches a reference to an
alias that its table does not define (spec README, finding 17); the generated hazards exercise
how C treats such references (class N1 below).

## Results (`./run.sh 20000 1`)

| Comparison | Agree | Disagree | Not compared |
|---|---|---|---|
| spec vs sudo-rs (verdict, every tag field, alias diagnostics) | 20000 / 20000 | 0 | 0 |
| spec vs C sudo (`testsudoers`) | 17164 / 20000 | 171 | 2665 (C rejects the policy) |
| C model (spec + C runas + C args + C aliases) vs C sudo | 17335 / 17335 | 0 | 2665 |

The spec allows 3178 cases and denies 16822. 7629 cases contain an alias hazard; 5869 of them
have alias diagnostics (sudo-rs reports them and continues with the policy). The spec, with
the processing order of `Sanitize.lean`, predicts every diagnostic and every verdict of these
cases.

Spec vs C sudo disagreements by cause and kind. "Tags differ" means both allow, but the
password, SETENV or NOEXEC verdict differs.

| Cause | spec allows, C denies | spec denies, C allows | tags differ | total |
|---|---|---|---|---|
| `args-prefix` (F1) | 32 | 0 | 4 | 36 |
| `runas-default-root` (F2) | 49 | 1 | 0 | 50 |
| `runas-own-group-list` (F3) | 12 | 0 | 2 | 14 |
| `runas-self-own-group` (F4) | 0 | 10 | 0 | 10 |
| `runas-self-foreign-group` (F5) | 4 | 0 | 0 | 4 |
| `runas-default-root+self-own-group` (F2 and F4 in one case) | 0 | 1 | 0 | 1 |
| F5 together with N1 in a runas group list | 1 | 0 | 0 | 1 |
| N1 (alias hazards, not yet published) | 2 | 45 | 0 | 47 |
| N2 (alias hazards, not yet published) | 0 | 6 | 0 | 6 |
| N1 and N2 in one case | 0 | 2 | 0 | 2 |
| **total compared** | 100 | 65 | 6 | **171** |
| N3: C rejects the policy (`Parse error`), not compared | | | | 2665 |

Classes N1-N3 are new and are described in the report to the coordinator, not here. 84 of the
171 disagreements are in cases without alias hazards; they fall in F1-F5 as before.

Every "tags differ" case comes from a different deciding entry, not from different tag
semantics. The C model computes tags with the spec's rules and still matches `testsudoers` on
every case.

Feature coverage counts the cases, out of 20000, whose policy or request contains the feature:

| Feature | Cases | Feature | Cases |
|---|---|---|---|
| user list: `name` | 18365 | runas omitted | 17685 |
| user list: `#uid` | 11584 | runas `(users)` | 16743 |
| user list: `%group` | 14465 | runas `(users : groups)` | 12506 |
| user list: `%#gid` | 7053 | runas `(: groups)` | 12525 |
| user list: `ALL` | 9565 | runas `()` | 8027 |
| negated item | 19633 | `NOPASSWD` / `PASSWD` | 9316 / 9379 |
| `User_Alias` / `Runas_Alias` | 13365 / 13372 | `SETENV` / `NOSETENV` | 9359 / 9501 |
| `Host_Alias` / `Cmnd_Alias` | 13204 / 13327 | `NOEXEC` / `EXEC` | 9358 / 9357 |
| nested alias | 12466 | command without arguments | 18488 |
| negated alias member | 14746 | command `""` | 13596 |
| negated alias reference | 8998 | command with exact arguments | 16151 |
| two or more lines | 14943 | command with arguments and `*` | 8844 |
| two host groups in a line | 15273 | command `ALL` | 15411 |
| request: no `-u`/`-g` | 9317 | request: `-u` only | 5565 |
| request: `-g` only | 2856 | request: `-u` and `-g` | 2262 |
| invoked by `toor` (uid 0) | 2852 | runs as `toor` (uid 0) | 895 |
| upper-case name of an account, group or host referenced | 17013 | ... and also an alias of that table | 16380 |
| reference to an undefined alias | 6140 | undefined alias in a definition | 3089 |
| duplicate definition | 2665 | cyclic definition | 2566 |
| invoked by an upper-case account | 2856 | upper-case host | 2233 |
| `-u`/`-g` with an upper-case name | 2774 | | |

## Findings: sudo-rs vs C sudo

The explanations below are based on the C model and source inspection. They describe
compatibility differences, not findings about exploitability in deployed configurations.

| Finding | Semantic difference | Source |
|---|---|---|
| F1 | With a trailing wildcard in the arguments, sudo-rs compares a prefix of the argument vector; C sudo matches the concatenated argument string. | Rust `src/sudoers/tokens.rs`, `src/sudoers/mod.rs`; C `match_command.c` |
| F2 | With no explicit runas user, sudo-rs checks the root UID; C sudo checks the configured default runas user by name. | Rust `src/system/interface.rs`, `src/sudoers/mod.rs`; C `match.c` |
| F3 | When the requested group is already one of the target user's groups, sudo-rs uses membership directly. C sudo consults the explicit group list before falling back to membership. | Rust `src/sudoers/mod.rs`; C `match.c` |
| F4 | For a same-user group request where the user belongs to the group, the implementations differ on an unmatched, nonempty runas user list. | Rust `src/sudoers/mod.rs`; C `match.c` |
| F5 | For a same-user group request where the user is not a member of the requested group, the implementations differ on whether they consult the runas user list. | Rust `src/sudoers/mod.rs`; C `match.c` |

### Upstream status of the differences

Looked up on 2026-11-19 in the sudo-rs documentation, tests and issue tracker (upstream `main`
equals the merge-base `81dff9a1`). Nothing was filed upstream. "None found" means a search
found nothing, not that nothing exists.

| Finding | Status in sudo-rs upstream | Evidence |
|---|---|---|
| F1 | Intended and documented. | `docs/man/sudoers.5.md`: `*` as the final argument means "zero or more subsequent arguments"; issue #1455; PR #1463. |
| F2 | No test or discussion found. The man page says a rule without a Runas_Spec allows "only" root and that names are matched as strings. | `docs/man/sudoers.5.md` lines 128 and 222. |
| F3 | The target user's own groups are accepted by design. The effect on an explicitly negated group is not discussed. | Issue #210, closed as not planned. |
| F4 | No documentation, test or discussion found for the case where the user is already in the group. | Related: issue #403, PR #501. |
| F5 | The case where the user list merely omits the invoker is intended. The case where it excludes the invoker is not discussed. | Issue #403, PR #501, issue #1561 (closed as invalid). |

### Parts where the engines agree

Because the C model differs from the spec only in F1-F5 and in alias evaluation, and matches
`testsudoers` on every compared case, the generated cases found no difference between sudo-rs
and C sudo in:

- user and host lists, including `#uid`, `%#gid`, `ALL` and `!`;
- nested and negated aliases with well-formed tables: substitution semantics, finding 14 of the
  spec README;
- alias references whose names are also names of accounts, groups or hosts, when the alias is
  defined in the table of the position;
- last match wins across lines and host groups;
- runas specs propagating along a `Cmnd_Spec_List` and resetting at `:` (finding 11);
- tag accumulation, and the implicit SETENV of a literal `ALL` but not of `ALL` reached
  through a `Cmnd_Alias` (finding 3; C `gram.y` 505-508);
- `Runas_Alias` members used as groups (finding 15: a `%group` member never matches in either);
- `()` and `(: groups)`;
- `""` and exact argument lists;
- the password exemptions for a root invoker and for running as oneself.

## Spec vs sudo-rs

The two agreed on all 20,000 cases, on every field of the returned `Tag` and on the list of
alias diagnostics, so there is nothing to triage. A sudo-rs harness fault would have shown up as
a disagreement, because the harness resolves users and groups independently of the oracle.
The agreement on cases with cycles and duplicates rests on `Sanitize.lean`, which is a
transcription, not part of the proved spec.

## Properties of the real code

`Props.lean` states seven properties as Lean propositions over an `EngineFn`, the function from
a probe (policy text and request) to the result line of the real code (`Sudoers::read`, then
`Sudoers::check` or, for `sudo -l`, `Sudoers::matching_entries`). The propositions are what is
tested; none is proved. For each, `Prop'.check` checks one instance, and `PropRun.run` searches
(see *Running*). Instances are drawn by the differential generator (with hazards) and then
transformed as the property says. Preconditions are computed in Lean; the one semantic
precondition, "the last line decides the request" in (e), is computed with the spec.

Results for `./props.sh N 1` (evidence: test):

| | Property (Lean) | Instances | Precondition met | Holds | Violated |
|---|---|---|---|---|---|
| a | `OtherUsersLineIrrelevant`: inserting a line whose user list names only others (plain users, uids, groups that do not match the invoker), anywhere in the text, never changes the invoker's verdict | 10500 | 10500 | 10500 | 0 |
| b | `AppendNeverRevokes`: appending a line with no command-side `!` (and no reference to a `Cmnd_Alias` containing `!`) never turns an allow into a deny | 75000 | 10067 | 10065 | 2 |
| c | `UnmentionedNeverAllowed`: an invoking user, host or command that the user lists, host lists or command lists (with their aliases) never mention, `ALL` included, is refused | 11000 | 10757 | 10757 | 0 |
| d | `AliasExpansionPreserves`: for alias tables without diagnostics, textual expansion of every alias (negations flipped, definitions deleted) preserves the verdict, tags included | 16000 | 11223 | 11001 | 222 |
| e | `PrependIrrelevant`: if the last line decides the request, inserting rules, definitions of fresh aliases and unparsable lines before it changes nothing | 80000 | 10594 | 10594 | 0 |
| f | `ListingFaithful`: the entries `sudo -l` prints for the invoker on the host, read back as a policy (with the `Runas_Alias` definitions, for the invoker as `#uid`, on `ALL` hosts), decide every request of the invoker on the host like the policy (allow, deny, password) | 10500 | 10500 | 10146 | 354 |
| g | `UidSpellingsLikeRoot`: under `(ALL, !root)` or `(ALL, !#0)`, `-u '#0'`, `#00`, `#+0`, `#000`, `#+00`, `#0000000000` behave like `-u root`, and `#-0`, `#0x0`, `#4294967296`, `#` are refused as unknown; likewise `-g '#0'`, `#00`, `#+0` like `-g root` | 13500 | 10217 | 10217 | 0 |

Classes of the violations and of the instances outside the precondition. Classes that follow
from findings already published in the spec README are explained; the others (P1-P3) are new
and are described in the report to the coordinator, not here.

| | Class | Instances | Explanation |
|---|---|---|---|
| b | P1 | 2 | New; in the report. Appended rule lines never revoked. |
| d | `Cmnd_Alias` whose body contains `ALL` | 49 | The expansion turns `ALL` reached through an alias into a literal `ALL`, which implies SETENV (spec README finding 3). Only the `env` field differs. |
| d | `Runas_Alias` with a `%group` member used in a runas group list | 173 | The expansion writes `%group` into a group list, where the grammar has no `%group`; the line does not parse and is dropped. In the policy such a member never matches (spec README finding 15). |
| e | outside the precondition: an inserted definition reuses a name the policy defines or refers to | 869 (24 differ) | A duplicate definition before the original one takes its place (spec README finding 17: the first definition counts), and P1. |
| f | the target user is a uid-0 account other than `root` and the deciding entry has no runas spec | 190 | The listing prints `(root)`, a name test; no runas spec is a uid test (spec README finding 4). |
| f | P2 | 48 | New; in the report. Only with accounts whose names are spelled like aliases. |
| f | P3 | 116 | New; in the report. Only with alias hazards. |
| g | outside the precondition: another uid-0 account precedes `root` in the passwd file | 3283 (1524 differ) | `#0` resolves to the first uid-0 entry (`getpwuid`), here `toor`, which `!root` does not exclude and whose groups differ. |

The counterexamples were shrunk (to policies of one to three lines) and confirmed twice on the
real code; they are kept outside the repository with the report, together with kernel-checked
certificates (`decide` on the spec ASTs) of those that do not depend on parsing.

`Inline.lean` defines the expansion of (d); `Engine.lean` runs probes on the harness.

## Runtime checks (`src/sudoers/test/runtime.rs`)

`#[cfg(test)]` unit tests of the real code, part of `cargo test --lib sudoers::` (evidence:
test):

- `command_path_spellings_are_canonicalised`: in a scratch directory with `real/x`, a symlink
  `real/y -> x` and a directory symlink `lnk -> real`, the spellings `real/x`,
  `real/../real/x`, `real/./x`, `<dir>//real/x`, `lnk/x`, `lnk/../real/x` and a leading `//`
  name the same command on both sides, in every combination: the policy pattern is
  canonicalised by `Sudoers::read`, the request by `CommandAndArguments::build_from_args`;
- `command_symlink_itself_is_not_followed`: a symlink to a file is a command of its own
  (`canonicalize` resolves the directories, not the file);
- `nonexistent_command_paths_are_compared_as_text`: a path that does not exist is not
  canonicalised on either side;
- `unsupported_tags_are_rejected_at_parse`: `NOTBEFORE=`, `NOTAFTER=`, `TIMEOUT=`, `CHROOT=`,
  `INTERCEPT:`, `ROLE=`, `TYPE=` produce their diagnostic and drop the whole line, so it
  grants nothing, also for the other entries of the line;
- `digests_are_rejected_at_parse`: `sha224:`, `sha256:`, `sha384:`, `sha512:` digests are
  rejected the same way, in a rule and in a `Cmnd_Alias` (which then matches nothing).

## Command-path glob conformance

[`glob-fnmatch.sh`](glob-fnmatch.sh) runs the opt-in
[`glob_fnmatch_conformance`](../../src/sudoers/test/glob_fnmatch.rs) test. It compares
sudo-rs's actual `compile_pattern` and `match_command` (no arguments, `glob` 0.3.4)
with libc `fnmatch(3)` (`FNM_PATHNAME`, GNU libc 2.34, C locale), not with C sudo.

In job `assurance-glob-fixed-9d3cb6`, the 802 patterns × 156 paths gave 125,112
comparisons: 9,474 matches, 115,638 nonmatches and no disagreements. Both invalid-syntax
controls were rejected by `compile_pattern` and excluded from the comparison.
This is test evidence for the bounded ASCII fragment of literals, `/`, `?`, `*` and
closed bracket expressions (lists, `!` negation and ranges). It does not cover `**`,
other bracket dialects, escapes, other locales, non-ASCII paths, path canonicalization,
or command-argument matching.

## Environment rebuild and validation conformance

[`env/rebuild-run.sh`](env/rebuild-run.sh) compares sudo-rs's environment decision with
C sudo 1.9.18's own environment code, as an ordinary user and in one process. The C side
links the actual `rebuild_env`, `validate_env_vars` and `insert_env_vars` routines from a
pinned source tree (`d58e85d8…`, `plugins/sudoers/env.c` sha256 `e5145d71…`); the Rust side
observes the real `get_target_environment` through an opt-in test hook. Both sides read the
same fixture: `sudoers`-style `env_keep`/`env_check` lists, `secure_path`, the invoking
environment and explicit `NAME=value` assignments. The default fixture in the tree is six
ordinary cases; `SUDO_RS_ENV_CASES` selects another file.

Job `assurance-env-public-186b35` compared the default fixture: four inherited cases
(7 observations) and two assignment cases (2 observations) all agreed, with no incomplete
observation. A larger ordinary fixture kept outside the tree (22 cases: 18 inherited, 4
assignments; sha256 `249479b1…`) was compared in `assurance-env-rebuild-b9bd83`: all
observations were complete, 26 of 27 inherited-key rows agreed and all four assignment rows
agreed (two accepted, two rejected). The single differing row is a compatibility difference
on that input; the run exits 1 for a complete comparison with a difference and 2 when the
evidence is invalid or incomplete. This is in-process comparison, not a test of PAM,
credential changes, `sudoers` evaluation, or command execution.

A matcher-level comparison ([`env/pattern-run.sh`](env/pattern-run.sh)) drove sudo-rs's
`entry_matches` and C sudo's own `check_env_pattern` over 40,404 ordinary cases
(job `assurance-env-pattern-e7d46b`): 39,630 agreed, 774 matched only in sudo-rs and
none only in C. That is evidence about pattern matching, not about filtering or assembly.

## What limits coverage

- **Fragment.** The three-way policy generator never produces:
  - glob metacharacters in paths, directories (`/dir/`), `sudoedit`, `list` or digests;
  - `Defaults`, `@include`, netgroups, `%:group`, or host wildcards and IP addresses;
  - `CWD=`, `APPARMOR_PROFILE=` and the ignored or unsupported tags (so the `cwd` and
    `apparmor` fields are only compared between the spec and sudo-rs, and are always `none`);
  - quoting or escapes.
  Property (e) inserts a fixed pool of unparsable lines (unsupported tags, digests, unbalanced
  parentheses, lower-case alias names, includes of missing files), never one that ends in a
  backslash (which would continue onto the next line by design).
- **Alias tables.** Duplicate definitions are only compared with sudo-rs and the spec: C sudo
  rejects every policy that has one.
- **File system.** Generated command paths must not exist on the test machine (`run.sh` and
  `props.sh` check this). Neither engine therefore canonicalises paths (sudo-rs) or compares
  inodes (C) in the differential test; `runtime.rs` checks the sudo-rs side on real files.
- **Database.** Names are fixed. `toor` is the only uid shared by two accounts, and it is uid
  0, where every invoker is exempt from the password anyway. A difference in the "running as
  oneself" password exemption therefore cannot show: C compares uids (`check.c` 116-125),
  sudo-rs compares whole `User` values. Duplicate group names and gids are not generated
  either.
- **Request.** The command-line front end is not exercised beyond `-u`/`-g` (`-i`, `-s`, path
  resolution). `#uid`/`#gid` spellings are only exercised by property (g), not in the
  differential test. sudo-rs's user and group types are fakes over the case database, not NSS.
- **`sudo -l`.** Property (f) checks the default listing (`impl Display for Entry`), not the
  verbose one (`-l -l`), and only the invoker's own listing, not `-U other`.
- **C side.** `testsudoers` stops after `sudoers_lookup`. The `check_user` password exemptions
  are applied by `CSudo.effectivePasswd` (a transcription of `check.c`), not by running C.
  The tag flags come from `testsudoers-flags.patch`. Only allow/deny, password, SETENV and
  NOEXEC are compared with C.
- **Distribution.** About 16% of the cases are allowed. The coverage table counts features
  present in a case, not features that decided it.
- **Attribution.** It rests on the C model. Its agreement with `testsudoers` is empirical: on
  every compared case of this run, but not proved.
