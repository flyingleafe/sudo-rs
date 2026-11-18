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

/-- [std::ffi::os_str::OsString]: abstract. -/
opaque std.ffi.os_str.OsString : Type

/-- [std::path::Path]: abstract. -/
opaque std.path.Path : Type

/-- [glob::Pattern]: abstract. -/
opaque glob.Pattern : Type

/-- [sudo_rs::common::string::SudoString] (`src/common/string.rs`), kept opaque for Charon.
Modelled by the text its `Deref<Target = str>` exposes, i.e. the Rust `inner` field without its
trailing NUL byte. -/
structure common.string.SudoString where
  str : String
