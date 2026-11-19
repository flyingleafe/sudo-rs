# SudoersSpec: a Lean 4 specification of the sudoers authorization decision

A standalone Lean 4 package (core and Std only, toolchain `leanprover/lean4:v4.36.0-rc2`) that
specifies the decision sudo-rs takes in `Sudoers::check` (`src/sudoers/mod.rs`): given a parsed
policy and a request, is the command allowed, and with which tag (`NOPASSWD`, `CWD=`, ...)?
Everything is proved; there is no `sorry`, no `native_decide` and no added axiom.

```
cd proofs/spec && nix shell nixpkgs#elan -c lake build
```

The build also prints `#print axioms` for every main theorem (`SudoersSpec/Axioms.lean`); each
depends on at most `propext`, `Classical.choice`, `Quot.sound`.

Sources of truth, in order: `docs/man/sudoers.5.md`, the Rust in `src/sudoers/mod.rs`,
`ast.rs`, `tokens.rs` (upstream commit 81dff9a1), and the Why3 development `proofs/sudoers.mlw`.
Where the man page and the code disagree, the spec follows the code; the disagreements are
listed under *Findings* below.

## Files

| File | Content |
|---|---|
| `SudoersSpec/Ast.lean` | Parsed abstract syntax: `Meta` (`ALL` / item / alias), `Qualified` (allow / forbid), `Identifier`, `UserSpecifier`, `Command` + `Args`, `RunAs`, `Tag` and its enums, `Modifier` with `Modifier.apply`, `CommandSpec`, `PermissionSpec`, `Def`, `AliasTable`, `Policy`. |
| `SudoersSpec/Oracle.lean` | `Oracle`: the decidable predicates the decision is parameterised by; `Request`; transcriptions of `match_user`, `match_group`, `match_group_alias`, `in_group`, `match_command`. |
| `SudoersSpec/FindItem.lean` | `find_item` as a fold (`findItem`) and as "the final matching entry decides" (`findItemSpec`), proved equal; the Why3 postconditions. |
| `SudoersSpec/Aliases.lean` | `get_aliases` (`getAliases`), full alias expansion, and the port of the Why3 `demonstration` theorem. |
| `SudoersSpec/Distribute.lean` | `distribute_tags` as a scan (`distributeTags`) and per-prefix (`distributeTagsSpec`), proved equal. |
| `SudoersSpec/Authorize.lean` | `checkPermission` and `authorize` in structural form (b) and declarative form (a), proved equal. |
| `SudoersSpec/Theorems.lean` | Meta-theorems. |
| `SudoersSpec/Examples.lean` | 99 `#guard`s, most mirroring `pass!`/`FAIL!` cases of `src/sudoers/test/mod.rs` `permission_test`, the rest pinning down the findings below; 6 kernel-checked `example ... := by decide`. |
| `SudoersSpec/ListValidate.lean` | The flags of `sudo -v` and `sudo -l` (`mod.rs` `validate_flags`, `list_flags`): `maxByKey` (`Iterator::max_by_key` with a `Bool` key), `entryTags`/`applicableEntries`, `validateFlags`, `listFlags`; their meta-theorems; 11 `#guard`s for the findings below. |
| `SudoersSpec/Axioms.lean` | `#print axioms` audit. |

## What the spec covers

* The full flag computation of `Sudoers::check`: `check_permission` (lines 494-526),
  `matching_user_specs` (267-287), `distribute_tags` (531-554), `find_item` (564-597),
  `get_aliases` (693-712), the matchers (631-689), and the `skip_passwd` wrapper (173-182).
* `authorize O p r : Option Tag`; `none` is deny. Form (b) (`authorize`, `checkPermission`)
  follows the Rust iterators one to one (folds, `filterMap`, `flatten`, the scan of
  `distribute_tags` as structural recursion) and is the target for a refinement proof from the
  Aeneas extraction. Form (a) (`authorizeSpec`, `checkPermissionSpec`) is declarative: the
  candidate entries are all command entries of applicable lines (runas and tags taken from
  the prefix of the line), filtered by the runas rules, and the final entry whose command spec
  takes part decides (`lastMatch` / `IsFinalMatch`, as in the Why3 `final_match`).
* Last match wins, negation (`!`, folded by the parser into `forbid`), alias membership through
  the precomputed table including explicitly negated members, the runas rules (when the user
  and group lists are skipped; no runas spec = root only), distribution of runas specs and
  tags along a `Cmnd_Spec_List`, the implicit `SETENV` of a literal `ALL`, the NOPASSWD
  exception for root and for running as oneself with one's own group.

## What the spec abstracts

* **Matching** is an `Oracle User Group` of `Bool`-valued functions, exactly the trait methods
  the Rust calls: `has_name`, `has_uid`, `is_root`, `in_group_by_name`, `in_group_by_gid`,
  `PartialEq` on users, `as_gid`, `try_as_name`, the glob matcher of `match_command`, and host
  matching. No OS, user database or glob semantics is modelled. sudo-rs matches hosts with string
  equality (`Oracle.SudoRsHosts`); the spec allows any host predicate.
* **Parsing and analysis** are not modelled: the input is the AST. Alias tables are taken in
  processing order (the iteration order of the `VecOrd` produced by `sanitize_alias_table`);
  the topological sort, duplicate and cycle detection are outside the spec. Tag modifiers,
  boxed closures in Rust, are first-order data (`Modifier`) with `Modifier.apply` as meaning.
* The flags of `sudo -v` and `sudo -l` (`validate_flags`, `list_flags`), see
  `ListValidate.lean`; for `sudo -l -U` the primary group of the inspected user
  (`UnixUser::group`) is a parameter `grp : User → Group`.
* Out of scope: `Defaults` and settings (`specify_host_user_runas`, `specify_command` only
  change `Judgement.settings`, never the flags; the `Authentication` that
  `check_list_permission` / `check_validate_permission` build from the flags), include
  directives, command path resolution, the numeric width of ids (`u32` in Rust, `Nat` here).

## Theorems

`O : Oracle User Group`, `p : Policy`, `r : Request User Group`.

| Theorem | Statement |
|---|---|
| `findItem_eq_spec` | (a) = (b) for `find_item`: the fold equals "the final participating entry decides". |
| `findItem_eq_some_iff`, `findItem_eq_none_iff` | Why3 postconditions of `find_item`, stated with `IsFinalMatch`. |
| `findItem_of_no_match` | No participating entry: `find_item` returns `none`. |
| `findItem_congr` | `find_item` only reads the alias table at the aliases the list references. |
| `distributeTags_eq_spec` | (a) = (b) for `distribute_tags`: entry i gets the last explicit runas and all modifiers of the prefix ending at i (plus implicit SETENV for a literal ALL). |
| `distributeTagsSpec_allow_all_env` | Every literal `ALL` entry carries `SETENV` or an explicit `NOSETENV`. |
| `checkPermission_eq_spec`, `authorize_eq_spec` | (a) = (b) for `check_permission` and for the full decision. |
| `getAliases_fixpoint` | For a uniquely named, sorted table, every alias holds the verdict of its own body under the final table (the Why3 `get_aliases` postconditions). |
| `getAliases_undefined` | An alias the table does not define is never in the table. |
| `demonstration` | Port of Why3 `Correctness.demonstration`: for a table with a uniquely named permutation in which every reference points to an earlier definition, and items referencing only defined aliases, full expansion leaves no alias and deciding on the expansion equals deciding with `get_aliases`. |
| `checkPermission_eq_some_iff`, `checkPermission_eq_none_iff` | Last match wins: granted with `t` iff the final participating allowed entry grants `t`; denied iff there is none or it denies. |
| `default_deny` | No allowed entry takes part for the command: `authorize = none`. |
| `default_deny_no_rules`, `default_deny_no_applicable_line` | No lines, or no line whose user list accepts the invoking user: deny. |
| `checkPermission_addRule_singleLine` | Appending an accepted single-entry line: its command spec decides if it takes part, otherwise the decision is unchanged. |
| `trailing_forbid_denies` | Appending `users hosts = runas !cmd` that accepts the request, with `cmd` matching, denies whatever came before. |
| `trailing_forbid_all_denies` | Same for `!ALL`. |
| `trailing_allow_grants` | Appending an accepted `users hosts = runas mods cmd` with matching `cmd` grants exactly the tag `mods` build. |
| `authorize_nopasswd` | Invoking user root, or target user = invoking user and target group one of the invoking user's groups: every granted tag is `NOPASSWD`. |
| `authorize_of_skipPasswd`, `authorize_of_not_skipPasswd` | The wrapper only rewrites `authenticate`, and only under `skip_passwd`. |
| `authorize_isSome_iff` | The wrapper never changes allow/deny. |
| `authorize_congr` | Policies with equal alias tables and equal candidate lists decide alike. |
| `inapplicable_line_irrelevant` | Deleting a line whose user list does not accept the invoking user changes nothing: negation in a user list cannot revoke another line's grant. |
| `allow_all_setenv` | If the deciding entry is a literal `ALL`, the result is its tag and that tag has `SETENV` or `NOSETENV`. |
| `maxByKey_eq` | `Iterator::max_by_key` with a `Bool` key returns the last element whose key is `true`, otherwise the last element. |
| `entryTags_eq`, `applicableEntries_eq_nil_iff` | The tags `sudo -v`/`sudo -l` choose from are those of `applicableEntries`: every entry of every applicable host group of every applicable line (runas, command and negation are not consulted); there is none iff every such group is empty. |
| `validateFlags_eq`, `validateFlags_eq_none_iff`, `validateFlags_needsPasswd`, `validateFlags_of_entry` | `sudo -v`: the last applicable entry that needs a password, else the last one; refused iff no entry applies; a password is needed iff the invoker is not root and some applicable entry needs one. |
| `listFlags_other`, `listFlags_other_of_not_root`, `listFlags_other_root` | `sudo -l -U other`: `authorize` of the request to run `list` (no arguments) as `other` with `grp other`; if denied, root still gets the default tag with NOPASSWD. |
| `listFlags_self_eq_none_iff`, `listFlags_self_needsPasswd`, `listFlags_self_of_entry` | `sudo -l` (own entries): refused iff no entry applies; a password is needed iff `skip_passwd` (root, or `-u` self with one of one's groups) fails and every applicable entry needs one. |

Differences from the Why3 development: the alias table is a function `String → Option Bool`
instead of an abstract hash map; "sorted" is one hypothesis (`Sorted`: every reference points
to a strictly earlier definition), which combines the Why3 "topologically sorted" and "all
referenced aliases are defined" preconditions; undefined aliases expand to nothing, which is
also how the table treats them.

## Findings: man page vs. code

Man page = `docs/man/sudoers.5.md`; code = `src/sudoers/mod.rs` unless stated otherwise. Line
numbers refer to upstream commit 81dff9a1.

### Disagreements

1. **Password exception for "same user".** Man 17: no password is needed "if the target user is
   the same as the invoking user". Code 174-175 also requires the target group to be one of
   the invoking user's groups (`in_group(am_user, request.group)`): `sudo -g wheel cmd` by a
   non-member asks for a password. (`authorize_nopasswd`; test file line 241.)
2. **Wildcards in host names.** Man 308: wildcards may be used in host names. Code 671-675
   (`match_token`) compares host names by string equality; `*` in a host list only matches a
   host literally called `*`.
3. **Implicit SETENV.** Man 297: "If the command matched is ALL, the SETENV tag is implied".
   Code 543 only adds it when the entry is the literal `ALL` token; `ALL` reached through a
   `Cmnd_Alias` (e.g. `Cmnd_Alias EVERY = ALL`, `user ALL = EVERY`) gets no SETENV
   (`Examples.lean`, "Further behaviour").
4. **Root without a Runas_Spec is a uid test.** Man 222 (last sentence) says the command may
   only be run "as root"; man 128 says users are matched as strings. Code 518 uses `is_root`,
   which is `has_uid(0)` (`src/system/interface.rs` 136-137), so any uid-0 account (e.g.
   `toor`) qualifies, by uid, not by name.
5. **Order inside a Cmnd_Spec.** Man 204: `Runas_Spec? Chdir_Spec? Tag_Spec* Cmnd`, i.e. `CWD=`
   before the tags. `ast.rs` 420-438 accepts `CWD=`, `APPARMOR_PROFILE=` and tags in any order
   (test file line 195: "original sudo does not allow the below").
6. **Supported tags.** Man 270 lists only PASSWD, NOPASSWD, SETENV, NOSETENV as supported; the
   code also implements EXEC/NOEXEC (man 273 documents them), `CWD=`, `APPARMOR_PROFILE=`
   (`ast.rs` 354-400). Man 212 writes `'NOEXEC'` without the colon the parser requires
   (`ast.rs` 348-351). `AppArmor_Spec` (man 214) does not occur in the `Cmnd_Spec` production.
7. **Alias names.** Man 95: `NAME ::= [A-Z]([A-Z][0-9]_)*` (a letter followed by repeated
   "letter digit underscore" triples); man 101 and `tokens.rs` 163-169 accept any sequence of
   `[A-Z0-9_]` after the first letter.

### Places where the man page is silent

8. **Runas specs that reject the request do not take part.** Man 49 ("the last match is used")
   leaves open whether a "match" includes the runas spec. Code 509-525 drops entries whose
   runas spec rejects the request before command matching, so `user ALL = (bob) !/bin/sh`
   does not revoke an earlier `user ALL = (root) /bin/sh` for `sudo -u root /bin/sh`.
9. **Negation in user/host/runas lists vs. command lists.** Man 362-370 ("`!root` would
   explicitly deny root") does not say what the denial applies to. In code a negated user or
   host only makes that line inapplicable (279, 284) and can never revoke a grant from another
   line (`inapplicable_line_irrelevant`), while a negated command is an entry of the global
   last-match list and revokes earlier grants of any line (`trailing_forbid_denies`).
10. **Running as oneself with a foreign group.** Man 222 says that with both lists the command
    may be run with "any combination of users and groups listed". Code 512: when the target
    user is the invoking user and the target group is not one of their groups, the user list
    is not consulted at all, so `alice ALL = (root : wheel) /bin/ls` lets alice run
    `sudo -g wheel /bin/ls` as alice although alice is not in `(root)` (consistent with man
    243-256 for the `-g` examples, but not stated for this case). Conversely, when the target
    user is the invoking user, the group is one of theirs and the user list is non-empty, the
    invoking user must be in the list: `alice ALL = (root) /bin/ls` denies `sudo -u alice`.
11. **Runas and tags reset at `:`.** Man 224-236 and 271 say runas specs and tags carry over to
    the following commands; in code the carry-over is per `Host_List = Cmnd_Spec_List` group
    (`distribute_tags` is applied per group, 283-286), so after `:` in
    `user host1 = (bob) NOPASSWD: /a : host2 = /b`, `/b` is back to root and PASSWD.
12. **CWD and APPARMOR_PROFILE distribute.** Man 264-266 and 299-304 do not say whether
    `CWD=` and `APPARMOR_PROFILE=` carry over like tags; in code they do (534-541; test file
    line 190).
13. **Ignored and rejected tags.** `LOG_INPUT`, `NOLOG_INPUT`, `LOG_OUTPUT`, `NOLOG_OUTPUT`,
    `MAIL`, `NOMAIL`, `FOLLOW` are accepted and ignored with a diagnostic; `NOFOLLOW`,
    `NOINTERCEPT` are no-ops; `INTERCEPT`, `CHROOT`, `TIMEOUT`, `NOTBEFORE`, `NOTAFTER`, `ROLE`,
    `TYPE` are parse errors (`ast.rs` 369-394, `mod.rs` 873-877). There is consequently no
    CHROOT in `Tag`.
14. **Negated members inside aliases.** Man 117 and 362-370 do not describe how `!` inside an
    alias definition interacts with a reference to the alias. Code 584-591 uses substitution
    semantics: with `User_Alias FOO = !user`, the line `ALL, FOO ALL = ALL` denies `user`
    (test file 317) and `!FOO ALL = ALL` grants `user` (318); an alias that does not mention the
    item does not take part at all.
15. **Runas_Alias used as a group list.** In `(: ALIAS)` the members of a `Runas_Alias` are
    matched against the target group (`match_group_alias`, 659-669): a member written as a
    user name (`sudo`) matches the group named `sudo`, while a member written as a group
    (`%wheel`) never matches (test file 308-312).
16. **`%:group` (non-unix groups).** Not in the man page grammar (110-126); the parser accepts
    it (`ast.rs` 267-271) and it never matches (637-644).
17. **Erroneous alias tables and error recovery.** Undefined aliases (1069-1073) never match,
    recursive aliases (1077-1080) are evaluated in depth-first order with references to
    not-yet-evaluated aliases treated as absent, and of duplicate definitions only the first
    counts (1069, 1091-1097). All of these, and unparsable lines, are only diagnostics:
    `src/sudo/pipeline.rs` 46-58 prints them and continues with the rest of the policy. Man 560
    ("you may lock yourself out") does not describe this. The spec's `demonstration` theorem
    covers exactly the well-formed tables.

### `sudo -v` and `sudo -l` (`ListValidate.lean`)

Man = `docs/man/sudoers.5.md` and `docs/man/sudo.8.md` at the fork's head; code =
`list_flags`, `validate_flags`, `Sudoers::check_list_permission`,
`Sudoers::check_validate_permission` in `src/sudoers/mod.rs`.

18. **The `list` privilege needs a Runas_Spec for the inspected user.** sudoers.5 158-159:
    "A user with the “list” privilege is able to list another user's privileges even if they
    don't have permission to run commands as that user." In code `sudo -l -U bob` is the
    decision for running the command `list` as bob with bob's primary group
    (`listFlags_other`), so the entry's runas spec must accept bob: `alice ALL = list` (no
    Runas_Spec) lets alice list only root's privileges, `alice ALL = (bob) list` lets her list
    bob's.
19. **Running any command as root does not grant `-U`.** sudoers.5 159-160: by default "root
    or a user with the ability to run any command as either root or the specified user on the
    current host may use the -U option". In code `alice ALL = (root) ALL` does not let alice run
    `sudo -l -U bob`; only entries whose runas spec accepts bob and whose command matches `list`
    (`ALL` or `list`) do. Root may always, even against `root ALL = (bob) !list`
    (`listFlags_other_root`).
20. **Password for `sudo -l -U`.** sudoers.5 293 ("if the NOPASSWD tag is applied to any of a
    user's entries for the current host, the user will be able to run “sudo -l” without a
    password") holds for listing one's own entries (`listFlags_self_needsPasswd`). For
    `sudo -l -U other` the tag of the deciding `list` entry counts instead (`listFlags_other`),
    and for one's own entries `sudo -l -u self -g own-group` needs no password either (the
    `skip_passwd` exception of `Sudoers::check`); the man page mentions neither.
21. **All entries count, including negated ones and any runas spec.** For `sudo -v` and own
    `sudo -l` an "entry for the current host" (sudoers.5 293) is any command entry of an
    applicable host group of an applicable line: `alice ALL = !ALL` lets alice run `sudo -v`
    and `sudo -l`, with a password (`validateFlags_eq_none_iff`, `listFlags_self_eq_none_iff`).
22. **Root and its own entries.** Root without an applicable entry is refused `sudo -l` for its
    own entries (and `sudo -v`), while `sudo -l -U other` is always granted to root. The man pages
    do not say.
23. **Defaults for `sudo -l` (Rust, not in the spec).** `check_list_permission` applies user-,
    host- and runas-specific Defaults (and `Defaults!list`) only for `-U` with another user;
    listing one's own entries uses the global Defaults only, so `Defaults:alice passwd_tries=4`
    or `Defaults:alice rootpw` affect alice's `sudo -v` and `sudo -l -U bob` but not her
    `sudo -l` (unit test `list_and_validate_apply_defaults_then_decide`). `sudo -v` applies
    user- and host-specific Defaults but no runas-specific ones, and its decision takes no
    target user, although sudo.8 13 lists `-u`/`-g` for `sudo -v`.
