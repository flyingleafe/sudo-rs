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
| `std.ffi.os_str.OsString` | `structure { inner : alloc.vec.Vec U8 }` | `std/src/ffi/os_str.rs`: `struct OsString { inner: Buf }`; on Unix `sys/os_str/mod.rs` selects `sys/os_str/bytes.rs`, `struct Buf { inner: Vec<u8> }`. The bytes. Command arguments in the decision (compared for equality and read as text through `GlobAbs.os`); the input of `escaped`. |
| `std.ffi.os_str.OsStr` | `structure { inner : Slice U8 }` | `struct OsStr { inner: Slice }`, on Unix `struct Slice { inner: [u8] }` (`#[repr(transparent)]` wrappers of `[u8]`). The argument of `Path::new("list")` in `list_flags` (never inspected) and the `Deref` target read by `escaped`. |
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
| `std.ffi.os_str.OsString.Insts.CoreCmpPartialEqOsString.eq` | `ok (decide (a = b))` (classical) | Equality of the values, i.e. of the bytes (`OsString ==` compares the underlying byte slices on Unix). |
| `std.ffi.os_str.OsString.Insts.CoreOpsDerefDerefOsStr.deref` | `ok ⟨Vec.deref s.inner⟩` (the same bytes) | `os_str.rs` 668-674: `deref` is `&self[..]`; `Index<RangeFull>` (650-657) is `OsStr::from_inner(self.inner.as_slice())`; `bytes.rs` 160-165 `Buf::as_slice` transmutes `self.inner.as_slice()` (`&[u8]`) to `&Slice`, and `OsStr::from_inner` (879-883) casts `&Slice` to `&OsStr`. No copy, no check. |
| `std.ffi.os_str.OsStr.as_encoded_bytes` | `ok s.inner` | `os_str.rs` 1121-1123: `self.inner.as_encoded_bytes()`; `bytes.rs` 229-231: `&self.inner`. |
| `std.ffi.os_str.OsString.Insts.StdOsUnixFfiOs_strOsStringExt.from_vec` | `ok ⟨v⟩` | `std/src/os/unix/ffi/os_str.rs` 27-29: `FromInner::from_inner(Buf { inner: vec })`; `os_str.rs` 1784-1789: `OsString { inner: buf }`. Takes the vector as is. |
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
| `sudoers.tokens.ChDir.Insts.Sudo_rsSudoersBasic_parserToken.construct` | `"*"` ↦ `Ok(Any)`; text containing `'*'` ↦ `Err(Message "path cannot contain '*'")`; text containing `'\x00'` ↦ `Err(Message (chdirPathErrorText s))`; otherwise `Ok(Path { inner: s })` | Opaque for Charon (`Cargo.toml`): it reaches `str::contains`, whose `Pattern` trait Aeneas cannot translate. **A trusted transcription, not a proof**, of `tokens.rs` lines 521-531 and `SudoPath::try_from`/`SudoPath::new` (`path.rs` lines 19-34, 86-92: reject a NUL byte; the UTF-8 check cannot fail on a `String`; keep the text). In UTF-8 the bytes `*` and NUL occur only as those characters. The errors are `ErrorKind::Message` with the formatted text (the parser's transitional error kind). Pinned by `policy.rs` `runcwd_test`. |
| `sudo_rs.chdirPathErrorText` | **`opaque`** `String → String` | The text of `Error::PathValidation(..).to_string()`. Its only caller in the extracted code (`runcwd` in `authorization`) discards it with `.ok()`. |
| `core.char.methods.Char.is_ascii_uppercase`, `is_ascii_digit`, `is_ascii_alphanumeric` | `ok c.isUpper`, `ok c.isDigit`, `ok c.isAlphanum` | `core/src/char/methods.rs`: `matches!(*self, 'A'..='Z')`, `matches!(*self, '0'..='9')`, and digit, upper or lower ASCII letter. Lean's `Char.isUpper`/`isDigit`/`isAlphanum` test the same code point ranges. Used by the token classes of `Hostname` and `AliasName`. |
| `core.char.methods.Char.len_utf8` | 1 below `0x80`, 2 below `0x800`, 3 below `0x10000`, else 4 | `core/src/char/methods.rs` `len_utf8(code)`: `..MAX_ONE_B => 1, ..MAX_TWO_B => 2, ..MAX_THREE_B => 3, _ => 4` with the bounds `0x80`, `0x800`, `0x10000`. Used by the IPv4 test of `Hostname::construct` (`part.len()` in bytes). |
| `core.char.methods.Char.is_uppercase`, `is_numeric`, `is_whitespace` | **`opaque`** `Char → Result Bool` | Unicode properties (`Uppercase`; categories `Nd`/`Nl`/`No`; `White_Space`) whose tables are not modelled. A theorem about the parser takes their values as hypotheses (the character oracle of `proofs/parser/PLAN.md` 5.3). Used by `Meta<T>` (accept classes, `trim_end`) and `Hostname::construct` (`is_numeric`). |
| `alloc.string.String.new`, `alloc.string.String.push` | `ok ""`, `ok (s.push c)` | A Rust `String` is the UTF-8 encoding of its characters; Lean's `String` is the character sequence, and `push` appends one. Rust's `push` panics only when the capacity would pass `isize::MAX` bytes; the model never fails (`String::len` fails first, see below). The token loop builds the token text with them. |
| `alloc.string.String.len` | `utf8ByteSize` as `usize`; fails if it does not fit | `String::len` is the length of the UTF-8 encoding. The token loop compares it with `MAX_LEN`, exactly as the legacy parser did. A Rust `String` never exceeds `isize::MAX` bytes, so the failure case has no Rust counterpart. |
| `sudoers.char_stream.chars_of` | `ok (Vec of s.toList)`; fails above `usize::MAX` characters | Opaque for Charon (`Cargo.toml`): `text.chars().collect()` in `char_stream.rs`, and `str::chars`/`collect` have no Aeneas model. Rust `char` and Lean `Char` are both Unicode scalar values and `chars()` yields them in order. Used at the parser entry point (outside the extracted code), by `Hostname::construct` and by `Meta<T>::construct`. |
| `sudoers.basic_parser.escape_char` | `ok '\\'` | Opaque for Charon (`Cargo.toml`): `fn escape_char() -> char { '\\' }`. The pinned Aeneas prints the character literal `'\\'` as `'\'`, which Lean rejects; this one-line definition is the only place the backslash enters the extracted code (`proofs/parser/RESTYLE.md`). |
| `BoxStr.Insts.CoreConvertFromShared0Str.from` | `ok s` | `impl From<&str> for Box<str>` copies the bytes; boxes are erased. Builds the text values of `check_text`. |
| `core.str.Str.as_bytes`, `core.str.Str.len` | `ok s`, `ok (Slice.len s)` | A `&str` is represented by its UTF-8 bytes (`Str = Slice U8`); `str::len` is their number. |
| `core.str.Str.split_at` | the first `mid` bytes and the rest if `strIsCharBoundary s mid`, else `fail .panic` | `core/src/str/mod.rs`: `split_at` panics (`slice_error_fail`) when `split_at_checked` returns `None`, i.e. unless `is_char_boundary(mid)`: `mid = 0`, `mid = len`, or `mid < len` and the byte at `mid` is not a continuation byte (`(b as i8) >= -0x40`). `octal_mode` and `fractional_minutes` split only next to an ASCII byte. |
| `core.num.U32.from_str_radix`, `core.num.U64.from_str_radix` | `sudo_rs.fromStrRadix`: `fail .panic` unless `2 ≤ radix ≤ 36`; empty ↦ `Err Empty`; a lone `+` or `-` ↦ `Err InvalidDigit`; one leading `+` skipped; then the bytes left to right: a non-digit ↦ `Err InvalidDigit`, a value above the maximum ↦ `Err PosOverflow` | `from_ascii_bytes_radix_impl` (`core/src/num/mod.rs`, Charon toolchain `1.100.0-nightly-2026-09-17`) for unsigned types: the same checks in the same order; `(b as char).to_digit(radix)` accepts `0-9`, `a-z`, `A-Z` below `radix` (`sudo_rs.asciiDigit`); the unchecked loop runs only where no overflow is possible, the checked one tests the digit before the overflow. `ParseIntError`/`IntErrorKind` are modelled as the Rust struct and enum (`TypesExternal.lean`). The checkers only use `Ok`/`Err`. |
| `core.num.U64.pow` | `UScalar.tryMk .U64 (x ^ exp)`: overflow is `fail .integerOverflow` | `pow` is `strict_pow` (panics on overflow) with overflow checks, as the other arithmetic of the extraction; release builds would wrap. Reached by `fractional_minutes` with at most 17 fractional digits through the parser (`Numeric` holds at most 18 characters), where it cannot overflow. |
| `std.collections.hash.set.HashSet.remove` | drop the keys whose `borrow` equals the argument (`List.filterM`); the flag is whether one was dropped | Extensional, as `insert`: `HashSet::remove` returns whether the value was present; the list model holds each key once. Used by `apply_list` (`ListMode::Del`). |

## Hypotheses of the theorems

The theorems in `SudoRsProofs/` take these hypotheses instead of axioms:

| Hypothesis | Where | Why it is needed |
|---|---|---|
| `hp : ∀ x, Good x → inst.call pred x = ok (p (f x))` with `ItemsGood Good items` / `TableGood Good table` | `item_verdict`, `find_item(_after)`, `get_aliases` | The predicate is a generic Rust closure (`Fn(&T) -> bool`); the theorems hold for every closure that is pure and total on the items the lists name directly (`Meta::Only`). `Good` is that domain: the concrete matchers deref names and so are total only on names that fit in memory. |
| `FoundFits v` (`∀ (k, _) ∈ v, Fits k`) | `FoundAliases::get`, `item_verdict`, `find_item(_after)` | `get` calls `String::as_str` on every stored name; `Fits` holds for every Rust `String` (see `strOfString`). `get_aliases` establishes it for its result. |
| `Fits k` for alias names (`ItemsFit items`, `TableFits table`) | `item_verdict`, `find_item(_after)`, `get_aliases`, `sanitize_alias_table(s)_returns` | `item_verdict` derefs the alias name of `Meta::Alias`; same reason. The sanitizer derefs definition names and undefined alias names to build diagnostics. |
| `a.val = stringBytes k` | `FoundAliases::get` | Links the `&str` argument to the alias name `k` of the abstract map. |
| `v.val.length < Usize.max` | `FoundAliases::insert` | `Vec::push` fails on capacity overflow. Inside `get_aliases` this is discharged (the set grows by at most one entry per alias). |
| `TableWF table` (`∀ i ∈ order, i < defs.len`) | `get_aliases` | `defs[order[i]]` is bounds-checked; the caller must supply this for arbitrary tables. `sanitize_alias_table_tableWF` discharges it for outputs of the extracted producer. |
| `diags.len + defs.len + Σ members ≤ Usize.max` (summed over the four tables for `sanitize_alias_tables_returns`, `tableSize`) | `sanitize_alias_table(s)_returns` | `alias_diagnostic` pushes onto the diagnostics `Vec`; at most one diagnostic per definition (duplicate, or recursive on revisit) and one per member is added (`sanitize_alias_table_distinct`). Every Rust `Vec<Error>` has far fewer elements than `usize::MAX`; the hypothesis is representability only. |
| `(lineMods line).length ≤ Usize.max` (with `t.ignored.len + …` for the inner loops) | `apply_modifiers`, `distribute_tags` | `Modifier::Ignored` pushes onto `Tag::ignored`; the total number of modifiers of a line, all of which are in memory, bounds that vector. |
| `SettingsInRange s` (`s.passwd_tries ≤ u16::MAX`, `s.umask ≤ u32::MAX`) | `authorization_eq`, `authorization_permission_flags_*` (`to_auth_eq` takes only the first) | `authorization` converts these `u64` Defaults with `try_into().unwrap()` / `.expect(..)`; out of range it panics (`authorization_panics_of_passwd_tries`, `authorization_panics_of_umask`). **Not proved from the Defaults DSL** (its modifiers are data and extracted, `SettingsModifier.apply`, `check_integer`; no theorem about them yet): `Settings` fields are private to `crate::defaults` and change only through `Settings::default` and `SettingsModifier::apply` on the modifiers of `negate`, `set`, `check_integer`, `check_text` and `build_list` (`src/defaults`, `proofs/parser/DEFAULTS.md`). `passwd_tries = 3 [0..=1000]`: initial 3, `check_integer` keeps values in `0..=1000`, `negate` rejects it (no `!=` clause, not a flag or list). `umask = 0o022 (!= 0o777) {octal_mode}`: initial `0o22`, negation `0o777`, `check_integer` stores `octal_mode`, a parsed `libc::mode_t` widened to `u64`; `mode_t` is `u32` on Linux (the extraction platform). |

The tag layer is generic in the abstraction of runas specs and commands (`fr`, `fc` in
`SudoRsProofs/AbsTags.lean`): `distribute_tags` never looks inside them.

The producer theorem `sanitize_alias_table_tableWF` only assumes a successful return
from the extracted `sanitize_alias_table`. It does not rely on any returned hash-set
membership flag, the outcome of dependency lookup, or the contents of diagnostics.
`AliasTableOK.of_sanitize` combines four such return equations with the caller's
`TableFits` and `TableGood` premises. It does not prove that parsing or `analyze`
establish these premises.

The order theorems of `SudoRsProofs/SanitizeOrder.lean` (`sanitize_alias_table_distinct`,
`sanitize_alias_table_sorted`, `sanitize_alias_table_demonstration`,
`sanitize_find_item_expanded`) also assume only a successful return, but they rely on the
`HashSet` model (membership flag of `insert`), on `Slice::contains` and `String ==` as
modelled by Aeneas and above, and on `alias_diagnostic` appending exactly one error. The
"clean" premise `diags'.val.length = diags.val.length` (no diagnostic added) is what makes
the order a sorted permutation; it is not discharged for any concrete sudoers file.

`SudoRsProofs/SanitizeTables.lean` lifts both kinds of result to
`sanitize_alias_tables` (the four calls at the end of `analyze`). In
`sanitize_alias_tables_tableWF` the `TableWF` conjuncts and therefore
`AliasTableOK.of_sanitize_alias_tables` need only what `sanitize_alias_table_tableWF` needs;
its diagnostics-prefix conjunct comes from `sanitize_alias_table_distinct` and has the same
reliance as the order theorems. `sanitize_alias_tables_sorted` takes the clean premise on the
whole call. Parsing and the rest of `analyze` are not covered.

`SudoRsProofs/SanitizeTotal.lean` proves termination and absence of panics:
`sanitize_alias_table_returns` and `sanitize_alias_tables_returns` give `∃ r, … = ok r` under
`TableFits`-style name conditions and the diagnostics-length bound above, nothing else. They
use the same models as the order theorems (the termination measure counts `seen`, which
relies on the `HashSet` model) and `alias_diagnostic` failing only through `Vec::push`.

## Hypotheses of the top-level theorems

`check_permission_spec` / `check_permission_eq` (against `SudoersSpec.checkPermission`) and
`permission_flags_spec` / `permission_flags_eq` (against `SudoersSpec.authorize`), in
`SudoRsProofs/Permission.lean`, carry exactly these hypotheses; everything else in the table
above is discharged inside the proofs.

| Hypothesis | Meaning | Why it is needed |
|---|---|---|
| `hO : InstOracle uInst eqInst gInst O` (`AbsMatch.lean`) | The `UnixUser`/`PartialEq`/`UnixGroup` instances of the Rust user and group types are pure, total and agree with the spec oracle `O` (whose user and group types are the Rust ones): `has_name` (text linked by UTF-8 bytes), `has_uid`, `is_root`, `in_group_by_name` (on the `CStr` content), `in_group_by_gid`, `eq`, `ne` (= `!eq`), `as_gid`, `try_as_name`. | The decision is generic in these traits; the spec takes their answers as an oracle. |
| `hG : GlobOracle A O` (`AbsMatch.lean`) | `glob::Pattern::matches_path_with` with the options of `match_command` (`require_literal_separator: true`, other fields as `MatchOptions::new()`) returns `ok (O.globMatches (A.pat pat) (A.path path))`; `A.os` (the reading of an `OsString` as text) is injective. | `matches_path_with` is `opaque`; `Pattern` and `Path` are opaque types, and the decision proofs read them and `OsString` (whose model is its bytes) as text through `A : GlobAbs`. |
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

## Hypotheses of the argument-escaping theorems

`SudoRsProofs/Escape.lean` (`escaped` of `src/common/command.rs` against
`SudoersSpec.Escape.escapeArgs`) uses the `OsString`/`OsStr` models and the three function
models `deref`, `as_encoded_bytes`, `from_vec` above (line numbers from the `rust-src` of the
Charon toolchain, `1.100.0-nightly-2026-09-17`), plus the Aeneas library models of `Vec::new`,
`Vec::len`, `Vec::push`, `Vec` and slice indexing and `usize` addition. The only hypothesis
is in `escaped_spec`: the line has at most `usize::MAX` bytes, which is when the Aeneas model of
`Vec::push` does not fail (`escaped_ok_iff`; `escaped_overflow` gives the failure otherwise).
Real Rust aborts earlier, at `isize::MAX` bytes of capacity; that bound is not modelled.
`escaped_flatMap`, `escaped_injective`, `escaped_unescape` assume only that `escaped` returned.
Arguments are read through `osBytes` (bytes as Lean `UInt8`s), an injective abstraction.
