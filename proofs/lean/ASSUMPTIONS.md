# Trusted assumptions of the Lean refinement proofs

The generated code (`SudoRs/Types.lean`, `SudoRs/Funs.lean`) refers to items outside the crate
(Rust `std`, the `glob` crate) and to items kept opaque for Charon (`Cargo.toml`
`[package.metadata.charon] opaque`). Their meaning is given by hand in `SudoRs/TypesExternal.lean`
and `SudoRs/FunsExternal.lean`. **No external is an `axiom`**: each one is either a definition
(a model whose faithfulness to Rust is trusted) or an `opaque` constant (nothing is known about
it, so a theorem that depends on its behaviour has to take that behaviour as a hypothesis).
`SudoRsProofs/Axioms.lean` checks that every main theorem depends only on `propext`,
`Classical.choice` and `Quot.sound`.

## What the translation itself assumes

The generated code is a pure function into Aeneas's `Result` type. Every trait method and
external function is therefore a deterministic function of its arguments, whatever a theorem
assumes on top: the model cannot express a call that has a side effect or that answers
differently the second time. Aeneas uses this. Two calls of the same function on the same
arguments are emitted as one call whose result is reused; a scratch extraction of
`let a = u.is_root(); … if u.is_root() { … }` produced a single `is_root u`, and `list_flags`
below shows the same. The number and order of such calls in the Rust source is not part of the
model. For the real `system::User`, `in_group_by_name` performs a group database lookup on each
call, so the proofs describe a run in which those lookups give consistent answers.

## External types (`SudoRs/TypesExternal.lean`)

| Lean name | Model | Justification |
|---|---|---|
| `core.ffi.c_str.CStr` | `structure { str : String }` | Only ever produced by `SudoString::as_cstr` in the extracted code; represented by its text without the trailing NUL. |
| `std.ffi.os_str.OsString` | `opaque` type | Command arguments; only compared for equality. |
| `std.ffi.os_str.OsStr` | `opaque` type | Only the argument of `Path::new("list")` in `list_flags`; never inspected. |
| `std.path.Path` | `opaque` type | Command path; only passed to the glob matcher (and produced by `Path::new("list")` in `list_flags`). |
| `std.path.PathBuf` | `opaque` type | The sanitizer's diagnostics have no source path. |
| `std.collections.hash.set.HashSet` | list of keys | The sanitizer observes only `new` and `insert`, not bucket layout or key order. |
| `std.hash.random.RandomState`, `std.hash.random.DefaultHasher` | `opaque` types | Hash seeding and hash states are not observed by the extensional set model. |
| `glob.Pattern` | `opaque` type | Glob semantics is not modelled. |
| `common.string.SudoString` | `structure { str : String }` | Opaque for Charon; Rust `struct SudoString { inner: String }` where `inner` = text + NUL; modelled by the text its `Deref<Target = str>` exposes. |
| `core.time.Duration` | `structure { secs : U64, nanos : U32 }` | Rust `struct Duration { secs: u64, nanos: Nanoseconds }` (`core/src/time.rs`); only built by `Duration::from_secs`. |

`glob.MatchOptions` is a plain struct that Aeneas extracts itself (`SudoRs/Types.lean`).

## External functions (`SudoRs/FunsExternal.lean`)

Helpers: `sudo_rs.stringBytes s` = the UTF-8 bytes of `s` as `U8`s; `sudo_rs.strOfString s` = the
`Str` (`Slice U8`) with those bytes, failing with `maximumSizeExceeded` if there are more than
`usize::MAX` bytes (a Rust `String` never is: allocations are capped at `isize::MAX`).

| Lean name | Model / status | Justification |
|---|---|---|
| `alloc.string.String.as_str` | `strOfString` | `String` is UTF-8 bytes; `as_str` borrows them. |
| `alloc.string.String.Insts.CoreOpsDerefDerefStr.deref` | `strOfString` | Same as `as_str`. |
| `alloc.string.String.Insts.CoreCloneClone.clone` | `ok s` | Clone of plain data. |
| `Str.Insts.CoreCmpPartialEqStr.eq` | `ok (decide (a = b))` | `str ==` is byte equality. |
| `alloc.string.String.Insts.CoreCmpPartialEqString.eq` | `ok (a == b)` | Rust `String` equality compares the text. |
| `core.option.Option.as_ref` | `ok x` | Borrows are erased. |
| `core.option.Option.Insts.CoreCloneClone.clone` | clone the payload with the given `Clone` instance | `#[derive(Clone)]` semantics. |
| `core.option.Option.Insts.CoreDefaultDefault.default` | `ok none` | `Option::default() = None`. |
| `alloc.vec.Vec.Insts.CoreDefaultDefault.default` | `ok (Vec.new T)` | `Vec::default()` is empty. |
| `core.slice.Slice.starts_with` | `len ≥ needle.len` and `List.allM eq (zip needle self)` | `self.len() >= n && needle == &self[..n]`; slice `==` compares element-wise in order and stops at the first difference. Uses the instance's `eq`; the std code calls `ne`, which `PartialEq` requires to be `!eq`. |
| `std.ffi.os_str.OsString.Insts.CoreCmpPartialEqOsString.eq` | `ok (decide (a = b))` (classical) | Equality of the abstract values. |
| `Box.Insts.CoreConvertAsRef.as_ref` | `ok x` | Boxes and borrows are erased. |
| `glob.MatchOptions.new` | `{ case_sensitive := true, require_literal_separator := false, require_literal_leading_dot := false }` | glob 0.3.4 `src/lib.rs` lines 1102-1108. |
| `glob.Pattern.matches_path_with` | **`opaque`**, `Pattern → Path → MatchOptions → Result Bool` | Glob semantics is not modelled. A theorem about `match_command` has to assume its behaviour (e.g. `∀ pat path opts, matches_path_with pat path opts = ok (g pat path opts)`). |
| `Str.Insts.CoreConvertAsRefOsStr.as_ref` | **`opaque`**, `Str → Result OsStr` | `impl AsRef<OsStr> for str`; the trait dictionary `Path::new` receives. Nothing is assumed about it. |
| `std.path.Path.new` | **`opaque`**, `AsRef S OsStr → S → Result Path` | `Path` is abstract, so is its constructor. Its only call, `Path::new("list")` in `list_flags`, is described by the hypothesis `ListPath A` of `list_flags_spec`. |
| `common.string.SudoString.as_cstr` | `ok ⟨s.str⟩` | The `unwrap` cannot fail: a `SudoString` has no interior NUL and ends in one. |
| `common.string.SudoString.Insts.CoreOpsDerefDerefStr.deref` | `strOfString s.str` | The text without the trailing NUL. |
| `common.string.SudoString.Insts.CoreCmpPartialEqStr.eq` | `deref` then `str ==` | Rust: `let s: &str = self; s == other`. |
| `sudoers.warn_ignored` | `ok ()` | Opaque for Charon; its only effect is a log line. |
| `std.collections.hash.set.HashSetTRandomStateGlobal.new`, `std.collections.hash.set.HashSet.insert` | empty set; test key equality and insert if absent | `usize` and `&String` have lawful equality and hashing; buckets and hashing affect neither membership nor the insertion flag. Relied on by the order theorems of `SanitizeOrder.lean` (the insertion flag is `key ∉ set`, the set grows by the key). |
| `Usize.Insts.CoreHashHash.hash`, `alloc.string.String.Insts.CoreHashHash.hash`, `Shared0T.Insts.CoreHashHash.hash`, `std.hash.random.*.Insts.CoreHash*.{finish,write,build_hasher}` | hash state and seeding operations opaque; reference hashing delegates to the referent | These operations only populate trait dictionaries ignored by the extensional set model. |
| `sudoers.alias_diagnostic` | append the corresponding message with no source or location | Opaque for Charon to isolate formatting. The input `&str` borrows a definition or dependency name and is valid UTF-8. Relied on by the order theorems of `SanitizeOrder.lean`: each call appends exactly one error, so "no diagnostic added" means no undefined, recursive or duplicate alias was met. |
| `sudo_rs.stringOfStr` (helper) | `String.fromUTF8Lossy` of the bytes | The text of a `&str`. A Rust `&str` is valid UTF-8, so the decoding is lossless on every value with a Rust counterpart. Used to read `Box<str>` Defaults (`runcwd`, `secure_path`) in `absDefaults`/`absRestrictions` and by `String::from(&str)`. |
| `alloc.string.String.Insts.CoreConvertFromShared0Str.from` | `ok (stringOfStr s)` | `String::from(&str)` copies the bytes. |
| `U16.Insts.CoreConvertTryFromU64TryFromIntError.try_from`, `U32.Insts.CoreConvertTryFromU64TryFromIntError.try_from` | `core.num.tryFromUScalar` (Aeneas library): `Ok` with the same value iff it fits, else `Err ()` | `TryFrom<u64>` for `u16`/`u32` (`core/src/convert/num.rs`); same model as the library's `TryFrom<usize> for u32`. |
| `core.num.error.TryFromIntError.Insts.CoreFmtDebug.fmt` | **`opaque`** | Only fills the `Debug` dictionary of `unwrap`/`expect`, whose library models ignore it (`Err` is a panic). |
| `core.option.Option.as_deref`, `and_then`, `or_else`, `core.result.Result.ok` | the `core::option` / `core::result` definitions (`as_deref` = `deref` of the payload; `or_else` calls the closure only on `None`; `ok` drops the error) | Plain combinators. |
| `core.time.Duration.from_secs` | `ok { secs, nanos := 0 }` | `Duration { secs, nanos: Nanoseconds::ZERO }`; cannot panic. |
| `sudoers.tokens.ChDir.Insts.Sudo_rsSudoersBasic_parserToken.construct` | `"*"` ↦ `Ok(Any)`; text containing `'*'` ↦ `Err("path cannot contain '*'")`; text containing `'\x00'` ↦ `Err(chdirPathErrorText s)`; otherwise `Ok(Path { inner: s })` | Opaque for Charon (`Cargo.toml`): it reaches `str::contains`, whose `Pattern` trait Aeneas cannot translate. **A trusted transcription, not a proof**, of `tokens.rs` lines 440-450 and `SudoPath::try_from`/`SudoPath::new` (`path.rs` lines 19-34, 86-92: reject a NUL byte; the UTF-8 check cannot fail on a `String`; keep the text). In UTF-8 the bytes `*` and NUL occur only as those characters. Pinned by `policy.rs` `runcwd_test`. |
| `sudo_rs.chdirPathErrorText` | **`opaque`** `String → String` | The text of `Error::PathValidation(..).to_string()`. Its only caller in the extracted code (`runcwd` in `authorization`) discards it with `.ok()`. |

## Hypotheses of the theorems

The theorems in `SudoRsProofs/` take these hypotheses instead of axioms:

| Hypothesis | Where | Why it is needed |
|---|---|---|
| `hp : ∀ x, Good x → inst.call pred x = ok (p (f x))` with `ItemsGood Good items` / `TableGood Good table` | `item_verdict`, `find_item(_after)`, `get_aliases` | The predicate is a generic Rust closure (`Fn(&T) -> bool`); the theorems hold for every closure that is pure and total on the items the lists name directly (`Meta::Only`). `Good` is that domain: the concrete matchers deref names and so are total only on names that fit in memory. |
| `FoundFits v` (`∀ (k, _) ∈ v, Fits k`) | `FoundAliases::get`, `item_verdict`, `find_item(_after)` | `get` calls `String::as_str` on every stored name; `Fits` holds for every Rust `String` (see `strOfString`). `get_aliases` establishes it for its result. |
| `Fits k` for alias names (`ItemsFit items`, `TableFits table`) | `item_verdict`, `find_item(_after)`, `get_aliases` | `item_verdict` derefs the alias name of `Meta::Alias`; same reason. |
| `a.val = stringBytes k` | `FoundAliases::get` | Links the `&str` argument to the alias name `k` of the abstract map. |
| `v.val.length < Usize.max` | `FoundAliases::insert` | `Vec::push` fails on capacity overflow. Inside `get_aliases` this is discharged (the set grows by at most one entry per alias). |
| `TableWF table` (`∀ i ∈ order, i < defs.len`) | `get_aliases` | `defs[order[i]]` is bounds-checked; the caller must supply this for arbitrary tables. `sanitize_alias_table_tableWF` discharges it for outputs of the extracted producer. |
| `(lineMods line).length ≤ Usize.max` (with `t.ignored.len + …` for the inner loops) | `apply_modifiers`, `distribute_tags` | `Modifier::Ignored` pushes onto `Tag::ignored`; the total number of modifiers of a line, all of which are in memory, bounds that vector. |
| `SettingsInRange s` (`s.passwd_tries ≤ u16::MAX`, `s.umask ≤ u32::MAX`) | `authorization_eq`, `authorization_permission_flags_*` (`to_auth_eq` takes only the first) | `authorization` converts these `u64` Defaults with `try_into().unwrap()` / `.expect(..)`; out of range it panics (`authorization_panics_of_passwd_tries`, `authorization_panics_of_umask`). **Not proved from the Defaults DSL** (its modifiers are boxed closures): `Settings` fields are private to `crate::defaults` and change only through `Settings::default`, `negate` and `set` (`src/defaults/settings_dsl.rs`). `passwd_tries = 3 [0..=1000]`: initial 3, `set` keeps values in `0..=1000`, `negate` rejects it (no `!=` clause, not a flag or list). `umask = 0o022 (!= 0o777) {octal_mode}`: initial `0o22`, negation `0o777`, `set` stores `octal_mode`, a parsed `libc::mode_t` widened to `u64`; `mode_t` is `u32` on Linux (the extraction platform). |

The tag layer is generic in the abstraction of runas specs and commands (`fr`, `fc` in
`SudoRsProofs/AbsTags.lean`): `distribute_tags` never looks inside them.

The producer theorem `sanitize_alias_table_tableWF` only assumes a successful return
from the extracted `sanitize_alias_table`. It does not rely on any returned hash-set
membership flag, the outcome of dependency lookup, or the contents of diagnostics.
`AliasTableOK.of_sanitize` combines four such return equations with the caller's
`TableFits` and `TableGood` premises. It does not prove that parsing or `analyze`
establish these premises or even that the sanitizer returns.

The order theorems of `SudoRsProofs/SanitizeOrder.lean` (`sanitize_alias_table_distinct`,
`sanitize_alias_table_sorted`, `sanitize_alias_table_demonstration`,
`sanitize_find_item_expanded`) also assume only a successful return, but they rely on the
`HashSet` model (membership flag of `insert`), on `Slice::contains` and `String ==` as
modelled by Aeneas and above, and on `alias_diagnostic` appending exactly one error. The
"clean" premise `diags'.val.length = diags.val.length` (no diagnostic added) is what makes
the order a sorted permutation; it is not discharged for any concrete sudoers file.

## Hypotheses of the top-level theorems

`check_permission_spec` / `check_permission_eq` (against `SudoersSpec.checkPermission`) and
`permission_flags_spec` / `permission_flags_eq` (against `SudoersSpec.authorize`), in
`SudoRsProofs/Permission.lean`, carry exactly these hypotheses; everything else in the table
above is discharged inside the proofs.

| Hypothesis | Meaning | Why it is needed |
|---|---|---|
| `hO : InstOracle uInst eqInst gInst O` (`AbsMatch.lean`) | The `UnixUser`/`PartialEq`/`UnixGroup` instances of the Rust user and group types are pure, total and agree with the spec oracle `O` (whose user and group types are the Rust ones): `has_name` (text linked by UTF-8 bytes), `has_uid`, `is_root`, `in_group_by_name` (on the `CStr` content), `in_group_by_gid`, `eq`, `ne` (= `!eq`), `as_gid`, `try_as_name`. | The decision is generic in these traits; the spec takes their answers as an oracle. |
| `hG : GlobOracle A O` (`AbsMatch.lean`) | `glob::Pattern::matches_path_with` with the options of `match_command` (`require_literal_separator: true`, other fields as `MatchOptions::new()`) returns `ok (O.globMatches (A.pat pat) (A.path path))`; `A.os` (the reading of an `OsString` as text) is injective. | `matches_path_with` is `opaque`; `Pattern`, `Path`, `OsString` are opaque types read as text through `A : GlobAbs`. |
| `hH : O.SudoRsHosts` | `O.hostMatches p h = (p == h)`. | sudo-rs (`match_token`) compares host names by string equality; the spec allows any host predicate. |
| `hpol : PolicyOK rules aliases` (`AbsPolicy.lean`) | Alias tables: valid processing orders (`TableWF`), names that fit (`TableFits`), identifier names that fit (`TableGood`). Rules: user/host lists and runas user/group lists with names that fit (`ItemsFit`, `ItemsGood UserSpecFits / IdentFits / Fits`), command alias names that fit (`CmdOK`), and modifier counts per line that fit in `usize`. | This collects the side conditions required by the decision proof. There is no checked theorem here that parsing and `analyze` establish them. |
| `hhost : Fits onHost.inner` | The current host name fits in memory. | `Deref<str>` of `system::Hostname`. |

## Hypotheses of the `sudo -v` / `sudo -l` theorems

`validate_flags_spec` / `validate_flags_eq` (against `SudoersSpec.validateFlags`), in
`SudoRsProofs/ListValidate.lean`, take `hO`, `hH`, `hpol`, `hhost` as above and nothing else;
`validate_flags` never reaches the glob matcher, so there is no `GlobOracle` (the command
abstraction `A` only appears through `absPolicy`). `list_flags_self_spec` (listing one's own
entries, `O.userEq inspected invoking = true`) takes the same four. `list_flags_spec` /
`list_flags_eq` (against `SudoersSpec.listFlags`) take the hypotheses of `permission_flags_eq`
plus the two below; `hO` is stated for `gInst := uInst.UnixGroupInst`, i.e. for a `ListRequest`
whose group type is `User::Group` (the only instantiation in sudo-rs: `system::User`,
`system::Group`).

| Hypothesis | Meaning | Why it is needed |
|---|---|---|
| `hgrp : GroupOracle uInst grp` | `∀ u, uInst.group u = ok (grp u)`: `UnixUser::group` is pure and total; `grp` is the primary group the spec uses for the `list` request. | `list_flags` asks for `request.inspected_user.group()` to build the request `Sudoers::check` decides for `sudo -l -U`. `InstOracle` does not cover `group`. |
| `hpath : ListPath A` | `∃ p, Path::new("list") = ok p ∧ A.path p = "list"`. | `Path::new` and `Path` are opaque; the spec's `list` request has the command text `"list"`. |

The extracted `list_flags` calls `UnixUser::is_root` once in the other-user branch, where the
Rust calls it twice (for `skip_passwd` and for the root fallback): the translation shares the two
calls. Under `InstOracle` (`is_root` is a function of the user) this changes nothing, but it is a
point where the model is not a literal transcription of the source.

The theorems quantify over the oracle `O`, the abstraction `A`, the instances and all inputs, so
they hold for every OS user database and glob semantics consistent with the hypotheses.

`authorization_eq` (`SudoRsProofs/Authorization.lean`, against `SudoersSpec.authorization`)
carries only `SettingsInRange j.settings`, for an arbitrary `Judgement j`.
`authorization_permission_flags_eq` / `authorization_permission_flags_props` carry the five
hypotheses above plus `SettingsInRange settings`. The `env_keep`/`env_check` sets are passed
through and compared in the extensional list model of `HashSet`. The `apparmor` feature is not
enabled during extraction, so its `apparmor_profile` restriction is not covered.
