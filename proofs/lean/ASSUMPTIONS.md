# Trusted assumptions of the Lean refinement proofs

The generated code (`SudoRs/Types.lean`, `SudoRs/Funs.lean`) refers to items outside the crate
(Rust `std`, the `glob` crate) and to items kept opaque for Charon (`Cargo.toml`
`[package.metadata.charon] opaque`). Their meaning is given by hand in `SudoRs/TypesExternal.lean`
and `SudoRs/FunsExternal.lean`. **No external is an `axiom`**: each one is either a definition
(a model whose faithfulness to Rust is trusted) or an `opaque` constant (nothing is known about
it, so a theorem that depends on its behaviour has to take that behaviour as a hypothesis).
`SudoRsProofs/Axioms.lean` checks that every main theorem depends only on `propext`,
`Classical.choice` and `Quot.sound`.

## External types (`SudoRs/TypesExternal.lean`)

| Lean name | Model | Justification |
|---|---|---|
| `core.ffi.c_str.CStr` | `structure { str : String }` | Only ever produced by `SudoString::as_cstr` in the extracted code; represented by its text without the trailing NUL. |
| `std.ffi.os_str.OsString` | `opaque` type | Command arguments; only compared for equality. |
| `std.path.Path` | `opaque` type | Command path; only passed to the glob matcher. |
| `glob.Pattern` | `opaque` type | Glob semantics is not modelled. |
| `common.string.SudoString` | `structure { str : String }` | Opaque for Charon; Rust `struct SudoString { inner: String }` where `inner` = text + NUL; modelled by the text its `Deref<Target = str>` exposes. |

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
| `core.option.Option.as_ref` | `ok x` | Borrows are erased. |
| `core.option.Option.Insts.CoreCloneClone.clone` | clone the payload with the given `Clone` instance | `#[derive(Clone)]` semantics. |
| `core.option.Option.Insts.CoreDefaultDefault.default` | `ok none` | `Option::default() = None`. |
| `alloc.vec.Vec.Insts.CoreDefaultDefault.default` | `ok (Vec.new T)` | `Vec::default()` is empty. |
| `core.slice.Slice.starts_with` | `len ≥ needle.len` and `List.allM eq (zip needle self)` | `self.len() >= n && needle == &self[..n]`; slice `==` compares element-wise in order and stops at the first difference. Uses the instance's `eq`; the std code calls `ne`, which `PartialEq` requires to be `!eq`. |
| `std.ffi.os_str.OsString.Insts.CoreCmpPartialEqOsString.eq` | `ok (decide (a = b))` (classical) | Equality of the abstract values. |
| `Box.Insts.CoreConvertAsRef.as_ref` | `ok x` | Boxes and borrows are erased. |
| `glob.MatchOptions.new` | `{ case_sensitive := true, require_literal_separator := false, require_literal_leading_dot := false }` | glob 0.3.4 `src/lib.rs` lines 1102-1108. |
| `glob.Pattern.matches_path_with` | **`opaque`**, `Pattern → Path → MatchOptions → Result Bool` | Glob semantics is not modelled. A theorem about `match_command` has to assume its behaviour (e.g. `∀ pat path opts, matches_path_with pat path opts = ok (g pat path opts)`). |
| `common.string.SudoString.as_cstr` | `ok ⟨s.str⟩` | The `unwrap` cannot fail: a `SudoString` has no interior NUL and ends in one. |
| `common.string.SudoString.Insts.CoreOpsDerefDerefStr.deref` | `strOfString s.str` | The text without the trailing NUL. |
| `common.string.SudoString.Insts.CoreCmpPartialEqStr.eq` | `deref` then `str ==` | Rust: `let s: &str = self; s == other`. |
| `sudoers.warn_ignored` | `ok ()` | Opaque for Charon; its only effect is a log line. |

## Hypotheses of the theorems

The theorems in `SudoRsProofs/` take these hypotheses instead of axioms:

| Hypothesis | Where | Why it is needed |
|---|---|---|
| `hp : ∀ x, Good x → inst.call pred x = ok (p (f x))` with `ItemsGood Good items` / `TableGood Good table` | `item_verdict`, `find_item(_after)`, `get_aliases` | The predicate is a generic Rust closure (`Fn(&T) -> bool`); the theorems hold for every closure that is pure and total on the items the lists name directly (`Meta::Only`). `Good` is that domain: the concrete matchers deref names and so are total only on names that fit in memory. |
| `FoundFits v` (`∀ (k, _) ∈ v, Fits k`) | `FoundAliases::get`, `item_verdict`, `find_item(_after)` | `get` calls `String::as_str` on every stored name; `Fits` holds for every Rust `String` (see `strOfString`). `get_aliases` establishes it for its result. |
| `Fits k` for alias names (`ItemsFit items`, `TableFits table`) | `item_verdict`, `find_item(_after)`, `get_aliases` | `item_verdict` derefs the alias name of `Meta::Alias`; same reason. |
| `a.val = stringBytes k` | `FoundAliases::get` | Links the `&str` argument to the alias name `k` of the abstract map. |
| `v.val.length < Usize.max` | `FoundAliases::insert` | `Vec::push` fails on capacity overflow. Inside `get_aliases` this is discharged (the set grows by at most one entry per alias). |
| `TableWF table` (`∀ i ∈ order, i < defs.len`) | `get_aliases` | `defs[order[i]]` is bounds-checked; `sanitize_alias_table` only stores valid positions. |
| `(lineMods line).length ≤ Usize.max` (with `t.ignored.len + …` for the inner loops) | `apply_modifiers`, `distribute_tags` | `Modifier::Ignored` pushes onto `Tag::ignored`; the total number of modifiers of a line, all of which are in memory, bounds that vector. |

The tag layer is generic in the abstraction of runas specs and commands (`fr`, `fc` in
`SudoRsProofs/AbsTags.lean`): `distribute_tags` never looks inside them.

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

The theorems quantify over the oracle `O`, the abstraction `A`, the instances and all inputs, so
they hold for every OS user database and glob semantics consistent with the hypotheses.
