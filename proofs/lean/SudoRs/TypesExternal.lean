-- Hand-maintained models of external definitions used by the generated code.
-- Seeded from TypesExternal_Template.lean by proofs/extract.sh; never overwritten by it.
-- Every entry is listed in `proofs/lean/ASSUMPTIONS.md`.
-- [sudo_rs]: external types.
module
public import Aeneas
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.internalConstructors false

/-- [core::ffi::c_str::CStr]. In the extracted code a `CStr` is only ever produced by
`SudoString::as_cstr`, so it is modelled by its content (without the terminating NUL). -/
structure core.ffi.c_str.CStr where
  str : String

/-- The sanitizer only inserts into its sets: model their keys, not hash buckets. -/
abbrev std.collections.hash.set.HashSet (T : Type) (_S _A : Type) := List T

/-- Hash seeding and hashing internals are not observed by the sanitizer. -/
opaque std.hash.random.RandomState : Type
opaque std.hash.random.DefaultHasher : Type

/-- [std::ffi::os_str::OsString]: `struct OsString { inner: Buf }` with, on Unix,
`sys::os_str::bytes::Buf { inner: Vec<u8> }`: the bytes. -/
structure std.ffi.os_str.OsString where
  inner : alloc.vec.Vec U8

/-- [std::ffi::os_str::OsStr]: `struct OsStr { inner: Slice }` with, on Unix,
`sys::os_str::bytes::Slice { inner: [u8] }`: the bytes. -/
structure std.ffi.os_str.OsStr where
  inner : Slice U8

/-- [std::path::Path]: abstract. -/
opaque std.path.Path : Type

/-- Abstract: sanitizer diagnostics never carry a source path. -/
opaque std.path.PathBuf : Type

/-- [glob::Pattern]: abstract. -/
opaque glob.Pattern : Type

/-- [sudo_rs::common::string::SudoString] (`src/common/string.rs`), kept opaque for Charon.
Modelled by the text its `Deref<Target = str>` exposes, i.e. the Rust `inner` field without its
trailing NUL byte. -/
structure common.string.SudoString where
  str : String

/-- [core::time::Duration]: `{ secs: u64, nanos: Nanoseconds }` (`core/src/time.rs`), with the
nanoseconds below one billion. -/
structure core.time.Duration where
  secs : U64
  nanos : U32

/-- [core::num::error::IntErrorKind] (`core/src/num/error.rs`): why parsing an integer failed. -/
inductive core.num.error.IntErrorKind where
  | Empty
  | InvalidDigit
  | PosOverflow
  | NegOverflow
  | Zero

/-- [core::num::error::ParseIntError]: `struct ParseIntError { kind: IntErrorKind }`
(`core/src/num/error.rs`). -/
structure core.num.error.ParseIntError where
  kind : core.num.error.IntErrorKind
