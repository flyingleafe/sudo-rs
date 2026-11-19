# Differential test of the sudoers decision: spec, sudo-rs, C sudo

A three-way differential test of the authorization decision:

1. the Lean specification `SudoersSpec.authorize` (`../spec`), run as an executable oracle;
2. sudo-rs: the real sudoers parser (`Sudoers::read`) and the real decision (`Sudoers::check`);
3. C sudo 1.9.18 (`/tmp/fi/src/sudo`, git `d58e85d`): `plugins/sudoers/testsudoers`, which runs
   the real sudoers parser and `sudoers_lookup`.

For `./run.sh 20000 1`, the spec and sudo-rs agree on all 20,000 cases.
The spec and C sudo disagree on 213 cases. Replacing the runas and command-argument
semantics in the spec with transcriptions of the C code accounts for those differences
on this corpus (see *Findings*). This is empirical evidence, not a proof of the C code.

## Running

```
cd proofs/differential && nix develop ../.. -c ./run.sh [N] [SEED]      # defaults: 20000 1
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
  done.
- `SUDO_SRC` (default `/tmp/fi/src/sudo`) is the C source tree. It is read-only; the build
  happens in a copy.
- `JOBS` (default `nproc`) is the number of parallel `testsudoers` workers.
- `MINIMIZE` (default 20) is how many disagreements of each cause and kind are minimised.

The run takes about 90 seconds. The outputs go to `disagreements/` (git-ignored, replaced on
every run):

| Path | Content |
|---|---|
| `sudo-rs/case-I.case` | spec vs sudo-rs disagreements (none at seed 1) |
| `c-model/case-I.case` | C model vs `testsudoers` disagreements (none at seed 1) |
| `c-sudo/CAUSE/KIND/case-I.case` | every spec vs C sudo disagreement |
| `c-sudo-minimized/CAUSE/KIND/case-I.case` | the same cases, minimised |
| `c-sudo-minimized/summary.txt` | the distinct minimised policies and requests for each cause and kind |

Each ignored `.case` file contains a synthetic policy, synthetic user/group data, and the
oracle outputs. These are policy-evaluation fixtures, not tests of the privileged runtime.

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
  `alice`, `bob`, `carol`, `dave`, and eight groups. Primary groups and memberships are random.
  Each policy has 0-3 aliases of each kind (`User_Alias`, `Runas_Alias`, `Host_Alias`,
  `Cmnd_Alias`). Aliases are nested: a definition may refer to earlier ones. Members may be
  negated. The definitions are printed in random order, so sudo-rs's topological sort and C's
  lazy lookup are both exercised. The spec gets them in dependency order; by
  `getAliases_fixpoint`, the order does not matter for an acyclic table.

  Each policy also has 1-4 lines with 1-2 host groups each. A line holds:
  - user lists with `user`, `#uid`, `%group`, `%#gid`, `ALL`, alias references and `!`;
  - runas `(users)`, `(users : groups)`, `(: groups)`, `()`, or none;
  - the tags `NOPASSWD`, `PASSWD`, `SETENV`, `NOSETENV`, `NOEXEC`, `EXEC`;
  - commands: a bare path, `path ""`, `path args`, `path args *`, `ALL`, `Cmnd_Alias`
    references, and `!`.

  The request (invoking user, host, `-u`/`-g`, command, arguments) is biased towards the names,
  hosts, runas specs and commands that occur in the policy. This gives about 19% allows.
- **`Print.lean`**: the AST-to-sudoers printer, one function per AST node. Each function inverts
  one parser production; the table in the module docstring lists them.
- **`Case.lean`**: the case record. This line-based text format is shared with the sudo-rs
  harness and `repro.sh`. The spec verdict line has the form
  `allow auth=… env=… exec=… cwd=… apparmor=…` or `deny`.
- **`CSudo.lean`**: the C driver. It writes the case's `passwd` and `group` files, runs
  `testsudoers -p passwd -P group -h HOST [-u U] [-g G] USER CMD ARGS < sudoers` and parses
  the verdict:
  - `Command allowed` means allow; `Command denied` and `Command unmatched` mean deny;
  - `testsudoers-flags.patch` adds one output line: the values of `def_authenticate`,
    `def_setenv` and `def_noexec` after `apply_cmndspec`. Nothing else in C sudo is changed;
  - `testsudoers` stops before `check_user`, so `effectivePasswd` applies the password
    exemptions of `check.c` 166-182: authentication off, invoking uid 0, or
    `running_as_user`.
- **`CModel.lean`**: the attribution model. `decide toggles case` is the spec decision, built
  from the spec's own functions, with two switchable components:
  - `cRunas` replaces sudo-rs's runas test with a transcription of C's `runaslist_matches`,
    `runas_userlist_matches` and `runas_grouplist_matches` (`match.c` 151-331);
  - `cArgs` replaces argument matching with C's `fnmatch`-based `command_args_match`
    (`match_command.c` 80-112).

  `decide_off` proves that with both switches off, `decide` is the spec decision.
- **`Compare.lean`**: the comparison.
  - Spec vs sudo-rs compares the full verdict line, with every tag field.
  - Spec vs C sudo compares allow/deny. For allows it also compares "password asked",
    "SETENV in effect" and "NOEXEC in effect". `cKind` names the difference (the kind).
  - The cause of a disagreement is the first switch set (`{cArgs}`, `{cRunas}`, both) under
    which `CModel.decide` agrees with `testsudoers`.
  - Runas causes are refined by `runasLabels`: for each candidate entry on which the two runas
    tests differ, the label records the situation (no runas spec; running as oneself or as
    another user; target group one of the target's groups or not).
- **`Minimize.lean`**: a greedy 1-minimiser. It drops rules, host groups, entries, list items,
  tags, unreferenced alias definitions, arguments, `-u`/`-g` and group memberships, as long as
  the disagreement keeps its cause and kind.
- **`Coverage.lean`**: counts how many cases contain each generated feature.

### sudo-rs harness (`src/sudoers/test/differential.rs`)

A `#[cfg(test)]` module, registered by one `mod differential;` line in
`src/sudoers/test/mod.rs`. It reads the case records and builds fake `UnixUser`/`UnixGroup`
values over each case's database. These behave like `impl UnixUser for User` and
`impl UnixGroup for Group`. The harness resolves `-u`/`-g` as `resolve_target_user_and_group`
does, parses the policy with `Sudoers::read`, and calls `Sudoers::check`. Any parser
diagnostic is reported as `error …`; none occurred. Without `SUDO_DIFF_CASES` the test does
nothing.

### Lean hygiene

`lake build` builds the package with no `sorry`, no `axiom` and no `native_decide`. The only
theorems, `CModel.decide_off` and its helper `CModel.ite_isSome`, are proved.

## Results (`./run.sh 20000 1`)

| Comparison | Agree | Disagree |
|---|---|---|
| spec vs sudo-rs | 20000 / 20000 | 0 |
| spec vs C sudo (`testsudoers`) | 19787 / 20000 | 213 |
| C model (spec + C runas + C args) vs C sudo | 20000 / 20000 | 0 |

The spec allows 3853 cases and denies 16147.

Spec vs C sudo disagreements by cause and kind. "Tags differ" means both allow, but the
password, SETENV or NOEXEC verdict differs.

| Cause | spec allows, C denies | spec denies, C allows | tags differ | total |
|---|---|---|---|---|
| `args-prefix` (F1) | 51 | 4 | 12 | 67 |
| `runas-default-root` (F2) | 100 | 1 | 7 | 108 |
| `runas-own-group-list` (F3) | 13 | 0 | 2 | 15 |
| `runas-self-own-group` (F4) | 1 | 9 | 5 | 15 |
| `runas-self-foreign-group` (F5) | 5 | 0 | 2 | 7 |
| `runas-default-root+own-group-list` (F2 and F3 in one case) | 1 | 0 | 0 | 1 |
| **total** | 171 | 14 | 28 | **213** |

Every "tags differ" case comes from a different deciding entry, not from different tag
semantics. The C model computes tags with the spec's rules and still matches `testsudoers` on
every case.

Feature coverage counts the cases, out of 20000, whose policy or request contains the feature:

| Feature | Cases | Feature | Cases |
|---|---|---|---|
| user list: `name` | 18455 | runas omitted | 17724 |
| user list: `#uid` | 11678 | runas `(users)` | 16726 |
| user list: `%group` | 14708 | runas `(users : groups)` | 12394 |
| user list: `%#gid` | 7348 | runas `(: groups)` | 12440 |
| user list: `ALL` | 9776 | runas `()` | 8051 |
| negated item | 19631 | `NOPASSWD` / `PASSWD` | 9611 / 9412 |
| `User_Alias` / `Runas_Alias` | 13270 / 13223 | `SETENV` / `NOSETENV` | 9395 / 9454 |
| `Host_Alias` / `Cmnd_Alias` | 13242 / 13391 | `NOEXEC` / `EXEC` | 9593 / 9418 |
| nested alias | 10428 | command without arguments | 18645 |
| negated alias member | 14578 | command `""` | 13956 |
| negated alias reference | 7800 | command with exact arguments | 16350 |
| two or more lines | 14968 | command with arguments and `*` | 9017 |
| two host groups in a line | 15323 | command `ALL` | 15678 |
| request: no `-u`/`-g` | 9785 | request: `-u` only | 5227 |
| request: `-g` only | 2865 | request: `-u` and `-g` | 2123 |
| invoked by `toor` (uid 0) | 3377 | runs as `toor` (uid 0) | 1210 |

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

### Parts where the engines agree

Because the C model differs from the spec only in F1-F5 and matches `testsudoers` on every
case, the generated cases found no difference between sudo-rs and C sudo in:

- user and host lists, including `#uid`, `%#gid`, `ALL` and `!`;
- nested and negated aliases: substitution semantics, finding 14 of the spec README;
- last match wins across lines and host groups;
- runas specs propagating along a `Cmnd_Spec_List` and resetting at `:` (finding 11);
- tag accumulation, and the implicit SETENV of a literal `ALL` but not of `ALL` reached
  through a `Cmnd_Alias` (finding 3; C `gram.y` 505-508);
- `Runas_Alias` members used as groups (finding 15: a `%group` member never matches in either);
- `()` and `(: groups)`;
- `""` and exact argument lists;
- the password exemptions for a root invoker and for running as oneself.

## Spec vs sudo-rs

The two agreed on all 20,000 cases, on every field of the returned `Tag`, so there is nothing
to triage. sudo-rs reported no parser diagnostic on any generated policy. A sudo-rs harness
fault would have shown up as a disagreement, because the harness resolves users and groups
independently of the oracle.

## What limits coverage

- **Fragment.** The generator never produces:
  - glob metacharacters in paths, directories (`/dir/`), `sudoedit`, `list` or digests;
  - `Defaults`, `@include`, netgroups, `%:group`, or host wildcards and IP addresses;
  - `CWD=`, `APPARMOR_PROFILE=` and the ignored or unsupported tags (so the `cwd` and
    `apparmor` fields are only compared between the spec and sudo-rs, and are always `none`);
  - quoting or escapes.
- **Alias tables.** They are acyclic, uniquely named, and every reference is defined, so
  error recovery (finding 17) is not exercised.
- **File system.** Command paths must not exist on the test machine (`run.sh` checks this).
  Neither engine therefore canonicalises paths (sudo-rs) or compares inodes (C).
- **Database.** Names are fixed. `toor` is the only uid shared by two accounts, and it is uid
  0, where every invoker is exempt from the password anyway. A difference in the "running as
  oneself" password exemption therefore cannot show: C compares uids (`check.c` 116-125),
  sudo-rs compares whole `User` values. Duplicate group names and gids are not generated
  either.
- **Request.** The command-line front end is not exercised (`-u #uid`, `-g #gid`, `-i`, `-s`,
  path resolution). The request is built from names as `resolve_target_user_and_group` would
  build it. sudo-rs's user and group types are fakes over the case database, not NSS.
- **C side.** `testsudoers` stops after `sudoers_lookup`. The `check_user` password exemptions
  are applied by `CSudo.effectivePasswd` (a transcription of `check.c`), not by running C.
  The tag flags come from `testsudoers-flags.patch`. Only allow/deny, password, SETENV and
  NOEXEC are compared with C.
- **Distribution.** About 19% of the cases are allowed. The coverage table counts features
  present in a case, not features that decided it.
- **Attribution.** It rests on the C model. Its agreement with `testsudoers` is empirical: on
  every case of this run, but not proved.
