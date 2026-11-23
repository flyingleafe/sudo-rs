# `SudoersSpec.Settings`: the `Defaults` settings

A transcription of `src/defaults` (the `defaults!` table in `mod.rs` and what
`settings_dsl.rs` generates from it; `proofs/parser/DEFAULTS.md` describes the Rust design). Core
Lean only, total, reducible in the kernel. Names, constructor order and field order are those of
the Rust code, so that the refinement proofs over the extracted code (`proofs/lean`) unfold.

| File | Content |
|---|---|
| `Values.lean` | `bytes` (the UTF-8 bytes of a text), `fromStrRadix` (`u32`/`u64::from_str_radix`), `decimal`, `integerInRange`, `octalMode`, `findDot`, `fractionalMinutesRun` (with panics), `fractionalMinutes` (without); `fractionalMinutesRun_eq` |
| `Model.lean` | `Setting`, `IntegerSetting`, `TextSetting`, `ListSetting`, `ListMode`, `SettingKind`, `Lecture`, `Verifypw`, `Settings`, `Settings.default`, `SettingsModifier`, `apply`, `applyList`, `StrSet`, the name table, `negate`, `set`, `checkInteger`, `checkIntegerRun`, `checkText`, `buildList`, `Settings.toDefaults` |
| `Properties.lean` | the list modes as set operations, the name table, the ranges of the checkers, `Reachable`, `reachable_inRange` |
| `Dump.lean` | `Settings.dumpFields` as `Settings::dump_fields` (`proofs/parser/DUMP.md`), `showEffect` |
| `Tests.lean` | kernel-checked examples (`defaults::test::check`) and `#guard` tests against values printed by the Rust code |

## Rust to Lean

| Rust (`src/defaults`) | Lean |
|---|---|
| `enum Setting`, `IntegerSetting`, `TextSetting`, `ListSetting`, `ListMode` | the inductives of the same names, same constructors |
| `enums::lecture`, `enums::verifypw`, `enums::timestamp_type` | `Lecture`, `Verifypw`, `SudoersSpec.TimestampType` |
| `struct Settings`, `impl Default` | `Settings`, `Settings.default` |
| `u64` | `Nat` (the checkers keep values below `u64::MAX`) |
| `Box<str>`, `Option<Box<str>>` | `String`, `Option String` |
| `HashSet<String>` | `StrSet` (= `List String`) |
| `enum SettingsModifier`, `apply` | `SettingsModifier`, `SettingsModifier.apply` |
| `apply_list` | `applyList` |
| `setting_at`, `setting_named` | `settingAt`, `settingNamed` (over `Setting.all`, `Setting.name`) |
| the arms of `negate` and `set` | `Setting.negation`, `Setting.kind` |
| `negate`, `set`, `check_integer`, `check_text`, `build_list` | `negate`, `set`, `checkInteger` (`checkIntegerRun` with panics), `checkText`, `buildList` |
| `integer_in_range`, `octal_mode`, `fractional_minutes`, `find_dot`, `decimal` | `integerInRange`, `octalMode`, `fractionalMinutes`(`Run`), `findDot`, `decimal` |
| `u32::from_str_radix`, `u64::from_str_radix` (core library) | `fromStrRadix u32Max`, `fromStrRadix u64Max` |
| the `Defaults` values `Judgement::authorization` reads | `Settings.toDefaults : Settings → SudoersSpec.Defaults StrSet` |

Texts enter as `String`; the integer parsers read `bytes s`, the UTF-8 bytes, as the Rust code
reads the bytes of a `&str` (`as_bytes`, `split_at`, `len`). Keyword settings compare whole
strings, case-sensitive.

## The table

The values (defaults, negations, kinds, ranges, keys) are copied from the `defaults!` table of
`src/defaults/mod.rs`, with `SYSTEM_EDITOR` as on Linux. `proofs/parser/DEFAULTS.md` lists them.
`Tests.lean` checks the defaults, every negation and kind, and the checkers on the inputs of the
old-against-new tests of `src/defaults/legacy.rs` against the output of the Rust code.

## Equality

`Settings` values are compared with `=`. For the three list settings the meaningful notion is
`StrSet.Equiv` (the same elements): `Settings.default` lists the table's strings in table order,
while Rust collects them into a `HashSet`. The list operations mirror the list model of
`HashSet` in `proofs/lean` (`insert` prepends a new key, `remove` filters), so refinement
theorems hold with `=` on the lists; `mem_applyList` states what the modes do to the elements
and `applyList_equiv` that this does not depend on the representation.

## Panics

`fractional_minutes` panics on arithmetic overflow, which needs an input longer than a `Numeric`
token. `fractionalMinutesRun` (and `checkIntegerRun`) model the panic; `fractionalMinutes` (and
`checkInteger`) are the panic-free values, equal to the Rust ones on inputs of at most 18 bytes
(`fractionalMinutesRun_eq`). `from_str_radix` panics unless `2 ≤ radix ≤ 36`; every caller passes
8 or 10.
