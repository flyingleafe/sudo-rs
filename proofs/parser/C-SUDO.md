# C sudo 1.9.18 as a third opinion on the parser (stage P0)

Evidence kind: test. Unless a section says otherwise, the tables are the **local seed-1 run**
(200 cases per category, 5,824 cases, NixOS laptop); section 5 reports the cluster run.
The numbers below hold for the corpus they were measured on (seed 1, 200
cases per category, 5,824 cases) and for nothing else. The comparison is between the legacy
sudo-rs parser (`parse_lines::<Sudo>` at `70fdb56b`, read through the dump of `DUMP.md`) and the
sudoers parser of C sudo 1.9.18, at the level both expose.
All reported counts use the historical v1 dump, not the current v2 format.

## 1. Method

**C side.** `proofs/differential/build-csudo-tools.sh` builds `visudo`, `cvtsudoers` and
`testsudoers` from the sudo 1.9.18 sources unprivileged, with the configuration of
`build-testsudoers.sh` (nothing installed, no setuid). For every case `parser csudo` writes the
text to `sudoers` in a private directory and runs, with `LC_ALL=C`:

- `visudo -c -f sudoers`: the verdict (exit status) and the diagnostics `sudoers:L:C: message`
  (syntax errors, and the checks `visudo` adds: alias definitions and references, Defaults
  values, include targets);
- `testsudoers -p passwd -P group -d < sudoers`: the entries the parser kept, printed back in
  sudoers syntax (the C grammar resynchronises at the next newline after an error, `error '\n'`
  in `gram.y`);
- `cvtsudoers -f json sudoers` when `visudo` accepted the file: the entries as JSON.

**sudo-rs side.** The dump records. The records of one text are grouped into the iterations of
`parse_lines`; each iteration starts at a physical line, which is reconstructed from the spans
and the rules of `parse_lines` (after an error the rest of the physical line is skipped; a
comment or newline at the stopping point is consumed; otherwise the next iteration reads the
newline as a comment). The reconstruction is checked against the records; the historical
run had 0 inconsistencies.

**Lines.** Both sides are mapped to logical lines: physical lines joined where a line ends in a
backslash and optional blanks outside a comment, which is C sudo's continuation rule. A logical
line is *kept* by C if `visudo` reports no error on it; an iteration of sudo-rs is kept if it is
an accepted item. Agreement: both keep the line, or both report an error on it. Every other
logical line is one difference.

**Content.** Where both accept the whole file, the entries are compared as multisets: rules as
(users, hosts, commands with their argument semantics), the members of each alias, and each
`Defaults` line as (binding, setting names). With dump v2, the comparator takes each name
directly from the parsed modifier (`DUMP.md` section 3); the historical v1 run inferred names
from fields changed on either of two fixed bases. Neither version compares tags, options
and runas lists of rules (C attaches them per command group, sudo-rs per entry), setting
values or list modes, or whether a binding is `:` or `>` (the JSON does not record it).

**Classification.** Each difference gets the first matching rule of `parser_compare.py`, in this
order:

1. a panic of sudo-rs;
2. the shape of the difference: sudo-rs reads an item starting inside a C logical line that
   failed (F-P2); sudo-rs keeps an item and reports garbage after it (F-P1, with whether C kept
   the alias prefix, from the `-d` output); sudo-rs reads a `#` line as a comment that C rejects
   (F-P4); a file without final newline;
3. for a line sudo-rs rejects and C accepts: rules on the logical line (list length, line
   continuation inside the consumed text), then on the text before and after the error position
   (`RS_CONTEXT_RULES`: netgroup, `#-N`, escapes, quoting, host forms, regular expressions,
   Defaults values), then on the error message (`RS_RULES`), then the class of the character at
   which sudo-rs stopped;
4. for a line C rejects and sudo-rs accepts: the C message (`C_RULES`), then the text before and
   after C's error column (`C_CONTEXT_RULES`: separated `!`, `!` followed by blanks in a
   Defaults binding, option after tag, keyword used as a name, runas list forms, directory with
   arguments), then the class of the character at which C stopped;
5. for content: the named cause (`EXPLANATIONS`) whose transformation makes both multisets
   equal, tried one at a time and then all together.

A difference that no rule matches counts as "unclassified". Rules are heuristics on text and
messages, checked by reading the cases of every category; they say which construct is involved,
not why each implementation decides as it does.

## 2. Corpus

`parser corpus 1 200` (`DUMP.md` section 6): 200 cases in each of 29 categories and the 24 fixed
inputs of PLAN.md, 5,824 cases.

| Category | Cases | | Category | Cases |
|---|---|---|---|---|
| blank, user, host, runas, tag | 200 each | | mut.delete-char, mut.insert-char | 200 each |
| command, alias, defaults, include | 200 each | | mut.replace-char, mut.duplicate-char | 200 each |
| rule, valid, mixed | 200 each | | mut.swap-char, mut.delete-token | 200 each |
| continuation, whitespace, unicode, eof | 200 each | | mut.duplicate-token, mut.swap-token | 200 each |
| maxlen, listlimit, fixture | 200 each | | mut.truncate, mut.splice-lines | 200 each |
| known | 24 | | | |

sudo-rs panicked on none of them. One case names an existing host path outside the fixture
(`<OUT>.hostdep`).

## 3. Historical results (dump v1)

| sudo-rs | C sudo (`visudo -c`) | Cases |
|---|---|---|
| no diagnostic | accepts | 1,657 |
| no diagnostic | rejects | 695 |
| diagnostics | accepts | 612 |
| diagnostics | rejects | 2,860 |

Agreement on lines: both keep 3,030 rules, 878 `Defaults` lines, 593 alias definitions and 413
include lines; both reject 3,702 lines. Content: of the 1,657 files both accept, 1,463 have equal
entries.

3,719 differences, **0 unclassified**:

**Findings of PLAN.md section 9** (387)

| Category | Differences | Cases |
|---|---|---|
| F-P1: prefix acceptance (rule; C reports an error) | 111 | 108 |
| F-P1: prefix acceptance (defaults; C reports an error) | 34 | 34 |
| F-P1: prefix acceptance (host_alias; C keeps the prefix too) | 21 | 20 |
| F-P1: prefix acceptance (user_alias; C keeps the prefix too) | 18 | 18 |
| F-P1: prefix acceptance (runas_alias; C keeps the prefix too) | 17 | 17 |
| F-P1: prefix acceptance (cmnd_alias; C keeps nothing) | 3 | 3 |
| F-P1: prefix acceptance (include; C reports an error) | 3 | 3 |
| F-P1: prefix acceptance (cmnd_alias; C keeps the prefix too) | 1 | 1 |
| F-P1: prefix acceptance (runas_alias; C keeps nothing) | 1 | 1 |
| F-P2: sudo-rs reads the continuation of a failed line as a line of its own | 16 | 16 |
| F-P3: quoted user whose content is not a user name | 21 | 21 |
| F-P4: '#' line read as a comment by sudo-rs, rejected by C | 41 | 41 |
| F-P4: '#' line read as a comment by sudo-rs, a rule for C (content) | 11 | 11 |
| F-P5: command path canonicalized by sudo-rs at parse time (content) | 89 | 89 |

**Features sudo-rs does not support** (133)

| Category | Differences | Cases |
|---|---|---|
| unsupported by sudo-rs: netgroup | 66 | 65 |
| unsupported by sudo-rs: ROLE/TYPE option | 28 | 26 |
| unsupported by sudo-rs: INTERCEPT option | 17 | 17 |
| unsupported by sudo-rs: NOTBEFORE option | 6 | 6 |
| unsupported by sudo-rs: TIMEOUT option | 6 | 6 |
| unsupported by sudo-rs: regular expression | 6 | 6 |
| unsupported by sudo-rs: NOTAFTER option | 3 | 3 |
| unsupported by sudo-rs: command digest | 1 | 1 |

**Checks C sudo does while reading the file, sudo-rs later or not at all** (1,231)

| Category | Differences | Cases |
|---|---|---|
| alias: checked by C at parse time (sudo-rs: in analysis) | 981 | 783 |
| Defaults or option: value check stricter in C | 105 | 101 |
| include: target does not exist or has the wrong type | 90 | 85 |
| path check stricter in C | 46 | 46 |
| command: sudoedit argument check in C | 9 | 9 |

**Checks stricter in sudo-rs** (518)

| Category | Differences | Cases |
|---|---|---|
| host: IPv4 address rejected by sudo-rs | 99 | 96 |
| end of file: last line without newline | 91 | 91 |
| limit: list length (sudo-rs 127) | 77 | 77 |
| Defaults: value or kind check stricter in sudo-rs | 63 | 60 |
| limit: token length (sudo-rs MAX_LEN) | 47 | 47 |
| Defaults: setting unknown to sudo-rs | 39 | 39 |
| option: quoted value rejected by sudo-rs | 27 | 27 |
| Defaults: quoted list item rejected by sudo-rs | 17 | 17 |
| command: wildcard in arguments rejected by sudo-rs | 12 | 12 |
| host: IPv6 address rejected by sudo-rs | 12 | 12 |
| host: wildcard host name rejected by sudo-rs | 11 | 11 |
| Defaults: value syntax rejected by sudo-rs | 10 | 10 |
| command: glob syntax rejected by sudo-rs | 5 | 5 |
| limit: numeric id does not fit u32 | 3 | 3 |
| user id: '#-N' rejected by sudo-rs | 3 | 3 |
| host: network/mask rejected by sudo-rs | 1 | 1 |
| option: CWD path rejected by sudo-rs | 1 | 1 |

**Syntax accepted by one side only** (1,207)

| Category | Differences | Cases |
|---|---|---|
| negation: '!' separated by whitespace rejected by C | 602 | 516 |
| command: directory with arguments rejected by C | 160 | 155 |
| escape: sequence rejected by sudo-rs | 135 | 135 |
| negation: '!' followed by whitespace in a Defaults binding rejected by C | 71 | 70 |
| continuation: inside a token (C joins or splits differently) | 43 | 40 |
| include: path or directive syntax | 40 | 39 |
| runas: trailing ',' accepted by sudo-rs | 40 | 39 |
| keyword as a name: reserved by C, a name or alias for sudo-rs | 39 | 38 |
| continuation: backslash after whitespace not followed by newline | 36 | 36 |
| runas: empty list after ':' accepted by sudo-rs | 28 | 28 |
| option after tag rejected by C | 9 | 9 |
| quoted user: escaped '"' inside quotes rejected by sudo-rs | 2 | 2 |
| command: 'list' with arguments rejected by C | 1 | 1 |
| continuation: inside a quoted string (C) | 1 | 1 |

**Same text, different reading** (content of files both accept, except where noted) (96)

| Category | Differences | Cases |
|---|---|---|
| user id: '#N' that C reads as a name, sudo-rs as an id | 44 | 44 |
| quoted upper-case word: a user name for sudo-rs, an alias for C | 12 | 12 |
| Defaults: list removal without effect on either settings base (the dump records effects) | 11 | 11 |
| command: '=' inside a path (C ends the path there) (8 content, 2 syntax) | 10 | 10 |
| content: several of the causes above | 10 | 10 |
| quoted '%:' group: sudo-rs reads a Unix group whose name starts with ':' | 9 | 9 |

**Token classes: the character where one parser stops and the other continues** (147)

| Category | Differences | Cases |
|---|---|---|
| token class: non-ASCII character (sudo-rs stops) | 51 | 51 |
| token class: end of line (C stops) | 35 | 35 |
| token class: control character (sudo-rs stops) | 18 | 18 |
| token class: '$' inside a user name | 13 | 13 |
| token class: carriage return (sudo-rs stops) | 8 | 8 |
| token class: sudo-rs stops at '%' where C continues | 4 | 4 |
| token class: sudo-rs stops at `"`, `,` (2 each), `#`, `$`, `+`, `=` (1 each) where C continues | 8 | 8 |
| token class: C stops at `,`, `=`, `s` (2 each), `#`, `)`, `a` (1 each) where sudo-rs continues | 9 | 9 |
| token class: end of line (sudo-rs stops) | 1 | 1 |

The listed Defaults category is an observation of the v1 dump: a modifier whose effect
left both fixed bases unchanged did not reveal its setting name. Version 2 records the
name directly and no longer needs this classification. The counts above are unchanged
historical observations.

## 4. PLAN.md section 3.3 and findings F-P1 to F-P6

Fixed inputs (category `known`), run with both implementations:

| PLAN.md row | Result |
|---|---|
| 3.3 table 1, row 1 (`sha224:x \` + `bob ...`) | **confirmed**: fatal 1:21, comment, rule for `bob`. C: syntax error 2:1, nothing kept |
| row 2 (`/bin/b \` + `bob ...`) | **confirmed, with detail**: one rule, whose second command is `/bin/b` with exact arguments `bob ALL = (ALL) ALL`. C rejects the joined line (2:9) |
| row 3 (no final newline) | **confirmed**: rule, then "missing line terminator at end of file". C accepts |
| row 4 (`) junk`) | **confirmed**: rule, garbage, comment, rule. C: only `bob` |
| row 5 (`ALL, !/usr/bin/su`) | **confirmed**: one rule, `ALL` then the exclusion. C the same |
| row 6 (comma missing) | **confirmed, corrected**: rule with `ALL` only, "garbage at end of line", then a `comment` item that the row does not list. C: syntax error 1:17, nothing kept |
| row 7 (`!sha224:x`) | **confirmed, corrected**: fatal, then a `comment` item. C rejects |
| 3.3 table 1, all rows | every fatal error in the middle of a line is followed by a `comment` item for the newline, unless a comment or the newline is at the stopping point (pinned in `parser_dump.rs`) |
| 3.3 table "C sudo keeps" | **confirmed** for its three rows: nothing / `bob` only / nothing |
| 3.3 table 3, `Runas_Alias NOTROOT = ALL !root` | **confirmed** at parse level: both keep the alias as `ALL` (C also reports a syntax error) |
| `Cmnd_Alias SAFE = ALL !/usr/bin/su` | **confirmed**: sudo-rs drops it ("fully qualified path needed" on the token `ALL !/usr/bin/su`), C keeps `SAFE = ALL` |
| `alice ALL = ALL` + `alice ALL !/usr/bin/su` | **confirmed**: both keep the first rule only |
| `Cmnd_Alias SHELLS /usr/bin/su, ...` (`=` missing) | **confirmed**: both drop the alias and keep the rule `ALL, !SHELLS` |
| `INTERCEPT: ALL` | **confirmed**: sudo-rs "not supported", C accepts |
| 3.3 Defaults rows 1 to 3 | **confirmed**: all three / none (`unknown setting: 'logfile'`) vs all four / `secure_path` only vs nothing |

| Finding | Systematic data (seed 1, N=200) |
|---|---|
| F-P1 prefix acceptance | **confirmed**, 209 lines. On the 111 rule and 34 `Defaults` lines C reports an error. In 119 of the 142 cases that hold them, the number of rules and `Defaults` lines `testsudoers -d` keeps equals the number of such lines both accept, so C keeps nothing of the prefix lines; in the other 23 the counts also differ on other lines (the 3 inspected: continuations), and the check says nothing. C keeps the prefix of alias definitions in 57 of 61 alias lines (not kept: 3 `Cmnd_Alias`, 1 `Runas_Alias`); 3 further lines are includes followed by garbage, on which C reports an error |
| F-P2 physical-line resynchronisation | **confirmed**, 16 lines on which sudo-rs reads an item from a continuation line of a logical line that failed |
| F-P3 `UserSpecifier::parse` rejects after consuming | **confirmed by test** (`finding_f_p3_quoted_non_user`): the first user of a line and a later list element end in fatal "expected elem" over the consumed range; in a runas list the rejection is discarded and the line fails at the missing `)`. 21 corpus lines where C accepts the quoted text as a user |
| F-P4 `#` + failed user id | **confirmed by test** (`finding_f_p4_hash_identifier`) for "value too large" and "token exceeds maximum length": the line is read as a comment. 41 corpus lines that C rejects and 11 that C reads as a rule (no diagnostic on either side) |
| F-P5 parse-time canonicalization | **confirmed**, 89 cases of the fixture category where the sudo-rs pattern is the canonicalized path and C keeps the written path |
| F-P6 unknown setting drops its line | **confirmed**: `Defaults env_reset, nosuchsetting, !use_pty` yields one fatal error and no setting; C reports the unknown entry and keeps the line in its parsed policy. 39 lines "Defaults: setting unknown to sudo-rs" |

Further categories in section 3 not described in PLAN.md are recorded neutrally; details are in
the local findings file of this stage.

## 5. Larger corpus: dump v1 history (superseded)

*Superseded by section 6; kept as history.* Sections 3 and 4 are the local seed-1 run at dump
version 1. At `d84ff98a` (dump v1) job `parser-p0-e3e4b7` on `uni-cpu` ran eight seeds of 1,000
cases per category: 232,192 cases, 146,539 differences and 201 rows without a named cause, of
which a review of the messages alone attributed 29. That version had no model of C's word
splitting and no rule for the constructs listed in section 6, so its counts are not comparable
with the current ones.

| Seed | Cases | Differences | Without an explanation |
|---:|---:|---:|---:|
| 1 | 29,024 | 18,411 | 26 |
| 2 | 29,024 | 18,673 | 33 |
| 3 | 29,024 | 18,168 | 25 |
| 4 | 29,024 | 18,073 | 22 |
| 5 | 29,024 | 18,249 | 15 |
| 6 | 29,024 | 18,060 | 24 |
| 7 | 29,024 | 18,519 | 35 |
| 8 | 29,024 | 18,386 | 21 |
| **Total** | **232,192** | **146,539** | **201** |

Dump version 2 (`059c08cf`) prints a settings modifier as a typed `(setting name payload)`
record, so the version-1 category "Defaults: list removal without effect on either settings
base" no longer exists: a removal is named, not inferred from two base values.


## 6. Head run: eight seeds, dump v2 (superseded numbers in section 5)

Input commit `58a225fe`, dump v2, C sudo 1.9.18 (`d58e85d8`), job `parser-p0-head-593602` on the
cluster (Red Hat, GCC 11.5, where some command paths of the corpus exist) and the same inputs
re-classified offline with `parser_compare.py`. Counts are **test** evidence: a difference is a
reported line or content difference, not a distinct bug.

### Method

**Message severities.** `visudo -c` writes errors (the file is rejected), `Warning: …` lines, and
messages without severity that occur in files it *accepts*. The comparator derives the last group
from the data of the run (every shape that occurs where the exit status is 0) and calls it an
advisory. Warnings and advisories get a named row per logical line; the comparator prints the
complete table of shapes with treatment and count, so a new shape cannot pass unnoticed. On a
line where sudo-rs read a comment or nothing, an advisory row is named `F-P4: '#' line read as a
comment by sudo-rs, a rule for C` — C's advisory proves C read a line sudo-rs did not; otherwise
the advisory's own category names it (`alias: checked by C at parse time`, `unused alias: C
warns, sudo-rs has no counterpart`).

| Advisory message shape (occurs where `visudo -c` exits 0, so never a rejection) | Occurrences |
|---|---:|
| `"…" is deprecated` | 592 |
| `Cmnd_Alias "…" referenced but not defined` | 13,485 |
| `Host_Alias "…" referenced but not defined` | 12,389 |
| `Runas_Alias "…" referenced but not defined` | 10,782 |
| `User_Alias "…" referenced but not defined` | 7,249 |
| `cycle in Cmnd_Alias "…"` | 14 |
| `cycle in Host_Alias "…"` | 10 |
| `cycle in Runas_Alias "…"` | 20 |
| `cycle in User_Alias "…"` | 7 |

**Content comparison scope.** `cvtsudoers -f json` exists for every file C accepts. Where both
parsers accept the whole file the entry multisets must be equal (the categories of the full-file
content rows). Where C accepts and sudo-rs does not, every sudo-rs item that the line pass treats
as the reading of a whole logical line (not prefix acceptance, not F-P2) must have an equal C
entry directly or under a named explanation, and a missing one is a row with that explanation's
name; C's remaining entries are counted.

| Seed | Cases | Differences | Unclassified | Reconstruction | Host-dependent | Accounting: cases | Accounting: lines | Content full | Content subset | No JSON | Subset under an explanation | C entries without a reading | Both reject (agreement) | Advisory rows without an item |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | 29,024 | 20,407 | 0 | 0 | 6 | 0 | 0 | 8,342 | 3,040 | 17,642 | 124 | 10,398 | 17,812 | 1 |
| 2 | 29,024 | 20,673 | 0 | 0 | 7 | 0 | 0 | 8,381 | 3,072 | 17,571 | 122 | 12,440 | 17,601 | 6 |
| 3 | 29,024 | 20,192 | 0 | 0 | 6 | 0 | 0 | 8,307 | 3,093 | 17,624 | 120 | 10,954 | 17,762 | 1 |
| 4 | 29,024 | 20,059 | 0 | 0 | 4 | 0 | 0 | 8,452 | 3,046 | 17,526 | 144 | 11,582 | 17,644 | 3 |
| 5 | 29,024 | 20,140 | 0 | 0 | 6 | 0 | 0 | 8,301 | 3,082 | 17,641 | 136 | 11,730 | 17,792 | 2 |
| 6 | 29,024 | 19,971 | 0 | 0 | 6 | 0 | 0 | 8,341 | 3,055 | 17,628 | 142 | 11,211 | 17,754 | 3 |
| 7 | 29,024 | 20,562 | 0 | 0 | 7 | 0 | 0 | 8,363 | 3,153 | 17,508 | 138 | 9,213 | 17,630 | 2 |
| 8 | 29,024 | 20,328 | 0 | 0 | 5 | 0 | 0 | 8,374 | 3,099 | 17,551 | 106 | 10,718 | 17,560 | 2 |
| **Total** | **232,192** | **162,332** | **0** | | | **0** | **0** | **66,861** | **24,640** | **140,691** | **1,032** | **88,246** | **141,555** | **20** |
The 1,032 "subset under an explanation" rows are readings whose C counterpart has the same entry
only after one of the named transformations (word split at `=` or an escape, quoted forms, `#N`
ids, escaped space, a command token cut by a continuation). 88,246 C entries have no sudo-rs
reading; they belong to lines sudo-rs rejected or read as comments, which the line rows cover.
**They cannot be attributed one by one to lines:** the JSON carries no line numbers and one line
can produce several C entries (a rule split at `:`, an alias with several definitions). In 2,372
of the 24,640 subset files (about 10%) C has more entries than there are row-bearing lines without
a reading; that number is a coarse bound, not a defect, and no cause is claimed from it.

### Limits of the comparison, next to the "0 unclassified"

- **Agreements.** A logical line on which both parsers report a rejection is an agreement and gets
  no row, whatever the two reasons are: 141,555 lines over the eight seeds.
- **Order.** List members are compared as multisets; a difference only in their order is not
  counted. Both readers preserve file order, so nothing measured was hidden; stated as a limit.
- **Alias-shaped names and binding kinds.** A C `username`/`hostname` shaped like an alias name is
  read as an alias reference (that is how `cvtsudoers` prints one), and a `Defaults` binding's `:`
  and `>` are merged because the JSON does not record which it is.
- **C messages.** Every shape is counted with its treatment (table above for the most frequent;
  the comparator prints all of them). A `Warning:` line is a row, not an exclusion.
- **Host dependence.** 47 `hostdep` cases hold 43 rows; none needs the canonicalization model, and
  none falls into the comparison-limit category, so the totals do not depend on the host here.
- **Lossy transport.** The harness decodes C's bytes lossily, so a non-UTF-8 byte in a member
  arrives as U+FFFD; the JSON is taken from its first `{`. No file of these seeds failed to parse.

### Totals per category (all eight seeds)

| Category | Differences | Cases |
|---|---:|---:|
| alias: checked by C at parse time (sudo-rs: in analysis) | 37,246 | 30,098 |
| negation: '!' separated by whitespace rejected by C | 25,817 | 22,018 |
| end of file: last line without newline | 7,716 | 7,716 |
| unused alias: C warns, sudo-rs has no counterpart | 7,673 | 6,929 |
| command: directory with arguments rejected by C | 6,254 | 6,042 |
| escape: sequence rejected by sudo-rs | 5,622 | 5,560 |
| host: IPv4 address rejected by sudo-rs | 4,092 | 3,813 |
| include: target does not exist or has the wrong type | 4,072 | 3,802 |
| F-P1: prefix acceptance (rule; C reports an error) | 3,920 | 3,797 |
| Defaults or option: value check stricter in C | 3,798 | 3,686 |
| F-P5: command path canonicalized by sudo-rs at parse time | 3,500 | 3,500 |
| limit: list length (sudo-rs 127) | 3,154 | 3,154 |
| negation: '!' followed by whitespace in a Defaults binding rejected by C | 2,875 | 2,796 |
| unsupported by sudo-rs: netgroup | 2,759 | 2,701 |
| limit: token length (sudo-rs MAX_LEN) | 2,725 | 2,724 |
| Defaults: value or kind check stricter in sudo-rs | 2,448 | 2,353 |
| token class: non-ASCII character (sudo-rs stops) | 2,263 | 2,172 |
| continuation: inside a token (C joins or splits differently) | 2,090 | 1,863 |
| user id: '#N' that C reads as a name, sudo-rs as an id | 2,031 | 2,031 |
| keyword as a name: reserved by C, a name or alias for sudo-rs | 1,803 | 1,780 |
| continuation: backslash after whitespace not followed by newline | 1,748 | 1,739 |
| include: path or directive syntax | 1,511 | 1,493 |
| token class: end of line (C stops) | 1,508 | 1,506 |
| runas: trailing ',' accepted by sudo-rs | 1,479 | 1,434 |
| path check stricter in C | 1,473 | 1,464 |
| F-P1: prefix acceptance (defaults; C reports an error) | 1,422 | 1,408 |
| Defaults: setting unknown to sudo-rs | 1,407 | 1,386 |
| F-P4: '#' line read as a comment by sudo-rs, rejected by C | 1,284 | 1,274 |
| unsupported by sudo-rs: ROLE/TYPE option | 1,245 | 1,226 |
| unsupported by sudo-rs: CHROOT option | 1,144 | 1,126 |
| runas: empty list after ':' accepted by sudo-rs | 1,001 | 979 |
| option: quoted value rejected by sudo-rs | 757 | 748 |
| F-P3: quoted user whose content is not a user name | 745 | 700 |
| token class: control character (sudo-rs stops) | 708 | 688 |
| F-P1: prefix acceptance (user_alias; C keeps the prefix too) | 683 | 682 |
| host: wildcard host name rejected by sudo-rs | 653 | 645 |
| F-P1: prefix acceptance (host_alias; C keeps the prefix too) | 628 | 627 |
| F-P2: sudo-rs reads the continuation of a failed line as a line of its own | 624 | 617 |
| F-P1: prefix acceptance (runas_alias; C keeps the prefix too) | 591 | 589 |
| command: wildcard in arguments rejected by sudo-rs | 539 | 536 |
| token class: '$' inside a user name | 536 | 532 |
| quoted '%:' group: sudo-rs reads a Unix group whose name starts with ':' | 521 | 521 |
| host: IPv6 address rejected by sudo-rs | 517 | 508 |
| quoted upper-case word: a user name for sudo-rs, an alias for C | 504 | 504 |
| option after tag rejected by C | 474 | 470 |
| Defaults: quoted list item rejected by sudo-rs | 441 | 436 |
| unsupported by sudo-rs: INTERCEPT option | 411 | 404 |
| command: sudoedit argument check in C | 362 | 361 |
| user id: '#-N' rejected by sudo-rs | 350 | 350 |
| Defaults: value syntax rejected by sudo-rs | 328 | 326 |
| token class: carriage return (sudo-rs stops) | 299 | 297 |
| limit: numeric id does not fit u32 | 285 | 284 |
| F-P4: '#' line read as a comment by sudo-rs, a rule for C | 280 | 270 |
| unsupported by sudo-rs: TIMEOUT option | 269 | 268 |
| unsupported by sudo-rs: regular expression | 256 | 255 |
| command: C splits a word at '=' or after an escape, sudo-rs keeps it whole | 252 | 252 |
| content: several of the causes above | 247 | 247 |
| token class: end of line (sudo-rs stops) | 238 | 238 |
| runas: an error inside the user list is discarded and the list ends early (F-P3) | 237 | 237 |
| token class: C stops at 's' where sudo-rs continues | 189 | 189 |
| command: glob syntax rejected by sudo-rs | 186 | 186 |
| unsupported by sudo-rs: NOTBEFORE option | 150 | 150 |
| quoted user: escaped '"' inside quotes rejected by sudo-rs | 138 | 138 |
| unsupported by sudo-rs: NOTAFTER option | 138 | 138 |
| option: CWD path rejected by sudo-rs | 129 | 129 |
| token class: sudo-rs stops at '%' where C continues | 127 | 126 |
| F-P1: prefix acceptance (cmnd_alias; C keeps the prefix too) | 126 | 124 |
| continuation: inside a quoted string (C) | 94 | 93 |
| quoting: sudo-rs requires the closing quote before the next token | 80 | 80 |
| F-P1: prefix acceptance (cmnd_alias; C keeps nothing) | 75 | 75 |
| F-P1: prefix acceptance (include; C reports an error) | 74 | 74 |
| token class: sudo-rs stops at '/' where C continues | 69 | 69 |
| Defaults keyword glued to a word: a user name for C, a Defaults line for sudo-rs | 62 | 62 |
| token class: sudo-rs stops at '+' where C continues | 58 | 58 |
| token class: sudo-rs stops at ',' where C continues | 54 | 54 |
| token class: sudo-rs stops at '@' where C continues | 52 | 52 |
| command: '=' inside a path (C ends the path there) | 51 | 51 |
| token class: C stops at '=' where sudo-rs continues | 51 | 51 |
| F-P1: prefix acceptance (host_alias; C keeps nothing) | 45 | 45 |
| token class: C stops at '#' where sudo-rs continues | 41 | 41 |
| token class: sudo-rs stops at '#' where C continues | 38 | 38 |
| token class: sudo-rs stops at '!' where C continues | 35 | 35 |
| F-P1: prefix acceptance (user_alias; C keeps nothing) | 33 | 33 |
| F-P1: prefix acceptance (runas_alias; C keeps nothing) | 31 | 31 |
| command: 'list' with arguments rejected by C | 29 | 29 |
| quoted "ALL": the ALL keyword for C, a name for sudo-rs | 27 | 27 |
| token class: C stops at ',' where sudo-rs continues | 27 | 27 |
| F-P1: prefix acceptance (includedir; C reports an error) | 26 | 26 |
| token class: C stops at ':' where sudo-rs continues | 26 | 26 |
| quoted '%:#N': sudo-rs and C read the non-unix group name differently | 25 | 25 |
| token class: sudo-rs stops at '$' where C continues | 18 | 18 |
| token class: sudo-rs stops at '=' where C continues | 18 | 18 |
| user: '%' without a group name | 15 | 15 |
| token class: sudo-rs stops at '"' where C continues | 11 | 11 |
| token class: C stops at '(' where sudo-rs continues | 10 | 10 |
| unsupported by sudo-rs: command digest | 9 | 9 |
| token class: C stops at ' ' where sudo-rs continues | 8 | 8 |
| token class: sudo-rs stops at '(' where C continues | 8 | 8 |
| quoted name: sudo-rs keeps the part before a character its unquoted token does not accept | 7 | 7 |
| token class: C stops at 'N' where sudo-rs continues | 7 | 7 |
| token class: C stops at 'a' where sudo-rs continues | 7 | 7 |
| token class: sudo-rs stops at ''' where C continues | 7 | 7 |
| quoted '%:' group: sudo-rs reads no non-unix group name, C reads the name (or a gid) | 6 | 6 |
| token class: sudo-rs stops at ' ' where C continues | 6 | 6 |
| Defaults! scope: a second '!' with no item after it | 5 | 5 |
| token class: C stops at '-' where sudo-rs continues | 5 | 5 |
| token class: sudo-rs stops at ':' where C continues | 5 | 5 |
| user: empty netgroup rejected by C | 5 | 5 |
| command path: C ends the path at the escape or '=', sudo-rs keeps it | 4 | 4 |
| token class: C stops at 'A' where sudo-rs continues | 4 | 4 |
| token class: C stops at 'L' where sudo-rs continues | 4 | 4 |
| Defaults! binding: sudo-rs reads a command pattern, C a path with an argument list | 3 | 3 |
| command: path form rejected by sudo-rs | 3 | 3 |
| host: network/mask rejected by sudo-rs | 3 | 3 |
| include: empty path after the directive (C reports the open failure) | 3 | 3 |
| token class: C stops at ')' where sudo-rs continues | 3 | 3 |
| token class: C stops at '1' where sudo-rs continues | 3 | 3 |
| token class: C stops at 'E' where sudo-rs continues | 3 | 3 |
| token class: C stops at 'P' where sudo-rs continues | 3 | 3 |
| token class: C stops at '\' where sudo-rs continues | 3 | 3 |
| token class: sudo-rs stops at ')' where C continues | 3 | 3 |
| token class: sudo-rs stops at ']' where C continues | 3 | 3 |
| token class: C stops at ''' where sudo-rs continues | 2 | 2 |
| token class: C stops at '/' where sudo-rs continues | 2 | 2 |
| token class: C stops at '>' where sudo-rs continues | 2 | 2 |
| token class: C stops at 'd' where sudo-rs continues | 2 | 2 |
| token class: C stops at 'e' where sudo-rs continues | 2 | 2 |
| token class: C stops at 'w' where sudo-rs continues | 2 | 2 |
| token class: control character (C stops) | 2 | 2 |
| comment ending in a backslash: sudo-rs loses the next line, C keeps it | 1 | 1 |
| directive: keyword in a user list | 1 | 1 |
| quoted user id: sudo-rs keeps the leading '#N', C keeps the rest of the text | 1 | 1 |
| token class: C stops at '"' where sudo-rs continues | 1 | 1 |
| token class: C stops at '%' where sudo-rs continues | 1 | 1 |
| token class: C stops at '*' where sudo-rs continues | 1 | 1 |
| token class: C stops at '+' where sudo-rs continues | 1 | 1 |
| token class: C stops at '0' where sudo-rs continues | 1 | 1 |
| token class: C stops at 'D' where sudo-rs continues | 1 | 1 |
| token class: C stops at 'R' where sudo-rs continues | 1 | 1 |
| token class: C stops at 'b' where sudo-rs continues | 1 | 1 |
| token class: C stops at 'h' where sudo-rs continues | 1 | 1 |
| token class: C stops at 'u' where sudo-rs continues | 1 | 1 |
| token class: C stops at 'x' where sudo-rs continues | 1 | 1 |
| token class: non-ASCII character (C stops) | 1 | 1 |
### Regression against the rows of `93218068`

All 154,141 rows of that run are kept at their logical line (the comparator's own keys):

| Regression group (rows of the earlier classifier) | Rows |
|---|---:|
| kept at its logical line | 154,141 |
The 8,191 new rows are: 7,673 `unused alias: C warns, sudo-rs has no counterpart` (the
`Warning:` lines, previously dropped), 1,032 content rows for a reading that matches only under a
named explanation, and 20 advisory rows on lines where sudo-rs read a comment or nothing (named
F-P4), plus the redistribution of about 500 rows into the category that now names their cause
(`user id: '#N'`, `continuation: inside a token`, `quoted '%:' group`, `quoted upper-case word`,
`content: several of the causes above`). The old categories all keep a row: no row was dropped.

## 7. Running

Local (about 35 s wall, 1.6 CPU-minutes):

```
cd proofs/differential && nix develop ../.. -c ./parser-run.sh 200 1
```

Larger run for a cluster (each seed is independent; 1,000 per category is 29,024 cases):

```
cd proofs/differential
for seed in 1 2 3 4 5 6 7 8; do
  PARSER_SCRATCH=/scratch/sudo-parser-p0-$seed JOBS=16 nix develop ../.. -c ./parser-run.sh 1000 $seed
done
```

With `PARSER_KEEP=1` the run also writes `corpus.txt.gz`, `sudo-rs.dump.gz` and
`c-sudo.out.gz`; after `gzip -d`, `python3 parser_compare.py corpus.txt sudo-rs.dump
c-sudo.out differences.tsv` re-classifies them without C sudo.

Each run writes `report.md` (these tables) and `differences.tsv` (one line per difference:
label, line, category, messages) to `$PARSER_SCRATCH`. A run whose report shows unclassified
differences needs new rules in `parser_compare.py`; a run whose dump shows `panic` records is a
finding.
