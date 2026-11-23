-- Hand-maintained models of external definitions used by the generated code.
-- Seeded from FunsExternal_Template.lean by proofs/extract.sh; never overwritten by it.
-- Every entry is listed in `proofs/lean/ASSUMPTIONS.md`.
-- [sudo_rs]: external functions.
module
public import Aeneas
public import SudoRs.Types
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.internalConstructors false

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048
open sudo_rs

namespace sudo_rs

/-- The UTF-8 encoding of a string, as Rust `u8`s. -/
def stringBytes (s : String) : List U8 :=
  s.toByteArray.data.toList.map fun b => ⟨b.toBitVec⟩

/-- The `&str` view of a Rust `String`: its UTF-8 bytes. A Rust `String` never exceeds
`isize::MAX` bytes; a Lean `String` longer than `usize::MAX` bytes has no Rust counterpart and
fails here. -/
def strOfString (s : String) : Result Str :=
  if h : (stringBytes s).length ≤ Usize.max then ok (Slice.from (stringBytes s) h)
  else fail .maximumSizeExceeded

end sudo_rs

/-- [core::option::{core::option::Option<T>}::as_ref]: `&Option<T> → Option<&T>`; borrows are
erased. -/
def core.option.Option.as_ref {T : Type _} (x : Option T) : Result (Option T) := ok x

/-- [core::option::{impl core::clone::Clone for core::option::Option<T>}::clone] -/
def core.option.Option.Insts.CoreCloneClone.clone
  {T : Type _} (cloneCloneInst : core.clone.Clone T) : Option T → Result (Option T)
  | none => ok none
  | some x => do
    let y ← cloneCloneInst.clone x
    ok (some y)

/-- [core::option::{impl core::default::Default for core::option::Option<T>}::default] -/
def core.option.Option.Insts.CoreDefaultDefault.default (T : Type _) : Result (Option T) :=
  ok none

/-- [core::slice::{[T]}::starts_with]: `self.len() >= n && needle == &self[..n]` with
`n = needle.len()`; slice equality compares `needle[i]` with `self[i]` in order and stops at the
first difference. -/
def core.slice.Slice.starts_with
  {T : Type _} (cmpPartialEqInst : core.cmp.PartialEq T T) (s needle : Slice T) : Result Bool :=
  if s.val.length < needle.val.length then ok false
  else List.allM (fun (p : T × T) => cmpPartialEqInst.eq p.1 p.2) (List.zip needle.val s.val)

/-- [core::str::traits::{impl core::cmp::PartialEq<str> for str}::eq]: byte equality. -/
def Str.Insts.CoreCmpPartialEqStr.eq (a b : Str) : Result Bool := ok (decide (a = b))

def alloc.string.String.Insts.CoreCmpPartialEqString.eq (a b : String) : Result Bool :=
  ok (a == b)

opaque Usize.Insts.CoreHashHash.hash
  {H : Type} (hasher : core.hash.Hasher H) : Usize → H → Result H

def Shared0T.Insts.CoreHashHash.hash
  {T H : Type} (hash : core.hash.Hash T) (hasher : core.hash.Hasher H) :
  T → H → Result H := hash.hash hasher

opaque alloc.string.String.Insts.CoreHashHash.hash
  {H : Type} (hasher : core.hash.Hasher H) : String → H → Result H

opaque std.hash.random.DefaultHasher.Insts.CoreHashHasher.finish :
  std.hash.random.DefaultHasher → Result U64

opaque std.hash.random.DefaultHasher.Insts.CoreHashHasher.write :
  std.hash.random.DefaultHasher → Slice U8 → Result std.hash.random.DefaultHasher

opaque std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher.build_hasher :
  std.hash.random.RandomState → Result std.hash.random.DefaultHasher

def std.collections.hash.set.HashSetTRandomStateGlobal.new (T : Type) :
    Result (std.collections.hash.set.HashSet T std.hash.random.RandomState alloc.alloc.Global) :=
  ok []

/-- Extensional insertion for the lawful key types used here (`usize` and `&String`).
No caller observes the ordering of these keys. -/
def std.collections.hash.set.HashSet.insert
    {T S A H : Type} (eq : core.cmp.Eq T) (_ : core.hash.Hash T)
    (_ : sudo_rs.core.hash.BuildHasher S H)
    (keys : std.collections.hash.set.HashSet T S A) (key : T) :
    Result (Bool × std.collections.hash.set.HashSet T S A) := do
  let found ← keys.anyM (eq.partialEqInst.eq key)
  if found then
    ok (false, keys)
  else
    ok (true, key :: keys)

open Classical in
/-- [std::ffi::os_str::{impl core::cmp::PartialEq<std::ffi::os_str::OsString> for std::ffi::os_str::OsString}::eq]:
equality of the values, i.e. of their bytes. -/
noncomputable def std.ffi.os_str.OsString.Insts.CoreCmpPartialEqOsString.eq
  (a b : std.ffi.os_str.OsString) : Result Bool := ok (decide (a = b))

/-- [std::ffi::os_str::{impl core::convert::AsRef<std::ffi::os_str::OsStr> for str}::as_ref]:
the `OsStr` view of a `&str`. Opaque (no axiom): nothing is known about it. -/
opaque Str.Insts.CoreConvertAsRefOsStr.as_ref : Str → Result std.ffi.os_str.OsStr

/-- [std::ffi::os_str::{impl core::ops::deref::Deref<std::ffi::os_str::OsStr> for std::ffi::os_str::OsString}::deref]:
`&self[..]`, i.e. `OsStr::from_inner(self.inner.as_slice())`; on Unix `Buf::as_slice` reinterprets
the `Vec<u8>` as `Slice`. The same bytes. -/
def std.ffi.os_str.OsString.Insts.CoreOpsDerefDerefOsStr.deref
  (s : std.ffi.os_str.OsString) : Result std.ffi.os_str.OsStr :=
  ok ⟨alloc.vec.Vec.deref s.inner⟩

/-- [std::ffi::os_str::{std::ffi::os_str::OsStr}::as_encoded_bytes]:
`self.inner.as_encoded_bytes()`, on Unix `&self.inner`. The same bytes. -/
def std.ffi.os_str.OsStr.as_encoded_bytes (s : std.ffi.os_str.OsStr) : Result (Slice U8) :=
  ok s.inner

/-- [std::os::unix::ffi::os_str::{impl std::os::unix::ffi::os_str::OsStringExt for std::ffi::os_str::OsString}::from_vec]:
`FromInner::from_inner(Buf { inner: vec })`, i.e. `OsString { inner: Buf { inner: vec } }`. -/
def std.ffi.os_str.OsString.Insts.StdOsUnixFfiOs_strOsStringExt.from_vec
  (v : alloc.vec.Vec U8) : Result std.ffi.os_str.OsString :=
  ok ⟨v⟩

/-- [std::path::{std::path::Path}::new]: `Path` is abstract, so is its constructor. Opaque (no
axiom): `list_flags` calls it once, as `Path::new("list")`; theorems about that call take its
result as a hypothesis (`SudoRsProofs.ListPath`). -/
opaque std.path.Path.new {S : Type _}
    (coreconvertAsRefSOsStrInst : core.convert.AsRef S std.ffi.os_str.OsStr) :
    S → Result std.path.Path

/-- [alloc::boxed::{impl core::convert::AsRef<T> for alloc::boxed::Box<T>}::as_ref]: boxes and
borrows are erased. -/
def Box.Insts.CoreConvertAsRef.as_ref {T : Type _} (A : Type _) (x : T) : Result T := ok x

/-- [alloc::string::{alloc::string::String}::as_str] -/
def alloc.string.String.as_str (s : String) : Result Str := strOfString s

/-- [alloc::string::{impl core::clone::Clone for alloc::string::String}::clone] -/
def alloc.string.String.Insts.CoreCloneClone.clone (s : String) : Result String := ok s

/-- [alloc::string::{impl core::ops::deref::Deref<str> for alloc::string::String}::deref] -/
def alloc.string.String.Insts.CoreOpsDerefDerefStr.deref (s : String) : Result Str :=
  strOfString s

/-- [alloc::vec::{impl core::default::Default for alloc::vec::Vec<T>}::default] -/
def alloc.vec.Vec.Insts.CoreDefaultDefault.default (T : Type _) : Result (alloc.vec.Vec T) :=
  ok (alloc.vec.Vec.new T)

/-- [glob::{glob::Pattern}::matches_path_with]: glob semantics is not modelled. Opaque (no axiom):
theorems that reach it take its behaviour as a hypothesis. -/
opaque glob.Pattern.matches_path_with :
  glob.Pattern → std.path.Path → glob.MatchOptions → Result Bool

/-- [glob::{glob::MatchOptions}::new] (glob 0.3.4). -/
def glob.MatchOptions.new : Result glob.MatchOptions :=
  ok { case_sensitive := true, require_literal_separator := false,
       require_literal_leading_dot := false }

/-- [sudo_rs::common::string::{sudo_rs::common::string::SudoString}::as_cstr]: the
`unwrap` cannot fail because a `SudoString` has no interior NUL and ends in one. -/
def common.string.SudoString.as_cstr (s : common.string.SudoString) :
    Result core.ffi.c_str.CStr :=
  ok ⟨s.str⟩

/-- [sudo_rs::common::string::{impl core::ops::deref::Deref<str> for sudo_rs::common::string::SudoString}::deref] -/
def common.string.SudoString.Insts.CoreOpsDerefDerefStr.deref (s : common.string.SudoString) :
    Result Str :=
  strOfString s.str

/-- [sudo_rs::common::string::{impl core::cmp::PartialEq<str> for sudo_rs::common::string::SudoString}::eq]:
`let s: &str = self; s == other`. -/
def common.string.SudoString.Insts.CoreCmpPartialEqStr.eq (s : common.string.SudoString)
    (other : Str) : Result Bool := do
  let a ← common.string.SudoString.Insts.CoreOpsDerefDerefStr.deref s
  Str.Insts.CoreCmpPartialEqStr.eq a other

/-- [sudo_rs::sudoers::warn_ignored]: only writes a diagnostic to the log. -/
def sudoers.warn_ignored (_ : sudoers.Ignored) : Result Unit := ok ()

/-- The opaque Rust formatting leaf only appends a diagnostic. `name` comes from
a Rust `String`, so decoding its bytes is lossless on these calls. -/
def sudoers.alias_diagnostic (diagnostics : alloc.vec.Vec sudoers.Error)
    (kind : sudoers.AliasDiagnostic) (aliasBytes : Str) : Result (alloc.vec.Vec sudoers.Error) :=
  let aliasName := String.fromUTF8Lossy ⟨(aliasBytes.val.map fun b => UInt8.ofNat b.val).toArray⟩
  let message := match kind with
    | .Undefined => s!"undefined alias: '{aliasName}'"
    | .Recursive => s!"recursive alias: '{aliasName}'"
    | .Duplicate => s!"multiple occurrences of '{aliasName}'"
  diagnostics.push { source := none, location := none, message }

/-! ### Models used by `Judgement::authorization` and `Settings::to_auth` -/

namespace sudo_rs

/-- The text of a `&str`: its bytes decoded as UTF-8. A Rust `&str` is always valid UTF-8, so
the decoding is lossless on every value that has a Rust counterpart. -/
def stringOfStr (b : Str) : String :=
  String.fromUTF8Lossy ⟨(b.val.map fun u => UInt8.ofNat u.val).toArray⟩

/-- The message of `Error::PathValidation(path).to_string()` for a rejected `ChDir` path. Its
text is not modelled; the only caller in the extracted code discards it (`.ok()`). -/
opaque chdirPathErrorText : String → String

end sudo_rs

/-- [core::convert::num::{impl core::convert::TryFrom<u64> for u16}::try_from]: `Ok` iff the
value fits. Same model as the Aeneas library's `TryFrom<usize> for u32`. -/
def U16.Insts.CoreConvertTryFromU64TryFromIntError.try_from (i : U64) :
    Result (core.result.Result U16 core.num.error.TryFromIntError) :=
  core.num.tryFromUScalar .U16 i

/-- [core::convert::num::{impl core::convert::TryFrom<u64> for u32}::try_from]. -/
def U32.Insts.CoreConvertTryFromU64TryFromIntError.try_from (i : U64) :
    Result (core.result.Result U32 core.num.error.TryFromIntError) :=
  core.num.tryFromUScalar .U32 i

/-- [core::num::error::{impl core::fmt::Debug for core::num::error::TryFromIntError}::fmt]: only
fills the trait dictionary that `unwrap`/`expect` take; their models ignore it. -/
opaque core.num.error.TryFromIntError.Insts.CoreFmtDebug.fmt :
  core.num.error.TryFromIntError → core.fmt.Formatter →
    Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)

/-- [core::option::{core::option::Option<T>}::as_deref]: `self.as_ref().map(|t| t.deref())`. -/
def core.option.Option.as_deref {T : Type _} {Target : Type _}
    (derefInst : core.ops.deref.Deref T Target) : Option T → Result (Option Target)
  | none => ok none
  | some x => do
    let y ← derefInst.deref x
    ok (some y)

/-- [core::option::{core::option::Option<T>}::and_then]. -/
def core.option.Option.and_then {T : Type _} {U : Type _} {F : Type _}
    (fnInst : core.ops.function.FnOnce F T (Option U)) : Option T → F → Result (Option U)
  | none, _ => ok none
  | some x, f => fnInst.call_once f x

/-- [core::option::{core::option::Option<T>}::or_else]. -/
def core.option.Option.or_else {T : Type _} {F : Type _}
    (fnInst : core.ops.function.FnOnce F Unit (Option T)) : Option T → F → Result (Option T)
  | some x, _ => ok (some x)
  | none, f => fnInst.call_once f ()

/-- [core::result::{core::result::Result<T, E>}::ok]. -/
def core.result.Result.ok {T : Type _} {E : Type _} :
    core.result.Result T E → Result (Option T)
  | .Ok x => Aeneas.Std.Result.ok (some x)
  | .Err _ => Aeneas.Std.Result.ok none

/-- [core::time::{core::time::Duration}::from_secs]: `Duration { secs, nanos: 0 }`; cannot
panic. -/
def core.time.Duration.from_secs (secs : U64) : Result core.time.Duration :=
  ok { secs, nanos := 0#u32 }

/-- [alloc::string::{impl core::convert::From<&str> for alloc::string::String}::from]: copies the
bytes. -/
def alloc.string.String.Insts.CoreConvertFromShared0Str.from (s : Str) : Result String :=
  ok (stringOfStr s)

/-- [sudo_rs::sudoers::tokens::{impl Token for ChDir}::construct] (`src/sudoers/tokens.rs`
lines 521-531), kept opaque for Charon (it reaches `str::contains`, whose `Pattern` trait Aeneas
cannot translate). `"*"` is `Any`; any other text with a `*` is rejected; otherwise
`SudoPath::try_from` (`src/common/path.rs` lines 19-34, 86-92) rejects text with a NUL byte
(the UTF-8 check cannot fail on a `String`) and keeps the text unchanged. In UTF-8 the bytes
`*` and NUL only occur as the characters `'*'` and `'\x00'`. The errors are formatted messages
(`ErrorKind::Message`). -/
def sudoers.tokens.ChDir.Insts.Sudo_rsSudoersBasic_parserToken.construct (s : String) :
    Result (core.result.Result sudoers.tokens.ChDir sudoers.basic_parser.ErrorKind) :=
  if s = "*" then ok (.Ok .Any)
  else if s.toList.contains '*' then ok (.Err (.Message "path cannot contain '*'"))
  else if s.toList.contains (Char.ofNat 0) then ok (.Err (.Message (chdirPathErrorText s)))
  else ok (.Ok (.Path ⟨s⟩))

/-! ## Sudoers parser: characters and strings

Externals of the restricted-style lexical layer (`proofs/parser/RESTYLE.md`). ASCII classes and
string building are definitions; the Unicode classes are `opaque`. -/

/-- [core::char::methods::{char}::is_ascii_uppercase]: `matches!(*self, 'A'..='Z')`. -/
def core.char.methods.Char.is_ascii_uppercase (c : Char) : Result Bool := ok c.isUpper

/-- [core::char::methods::{char}::is_ascii_digit]: `matches!(*self, '0'..='9')`. -/
def core.char.methods.Char.is_ascii_digit (c : Char) : Result Bool := ok c.isDigit

/-- [core::char::methods::{char}::is_ascii_alphanumeric]:
`matches!(*self, '0'..='9') | matches!(*self, 'A'..='Z') | matches!(*self, 'a'..='z')`. -/
def core.char.methods.Char.is_ascii_alphanumeric (c : Char) : Result Bool := ok c.isAlphanum

/-- [core::char::methods::{char}::len_utf8]: `len_utf8(self as u32)`, i.e. 1 below `0x80`, 2
below `0x800`, 3 below `0x10000`, otherwise 4 (`core/src/char/methods.rs`). -/
def core.char.methods.Char.len_utf8 (c : Char) : Result Std.Usize :=
  ok (if c.val < 0x80 then 1#usize
    else if c.val < 0x800 then 2#usize
    else if c.val < 0x10000 then 3#usize
    else 4#usize)

/-- [core::char::methods::{char}::is_uppercase]: the Unicode `Uppercase` property. Opaque: a
theorem that depends on it takes its values as a hypothesis (character oracle). -/
opaque core.char.methods.Char.is_uppercase : Char → Result Bool

/-- [core::char::methods::{char}::is_numeric]: general categories `Nd`, `Nl`, `No`. Opaque. -/
opaque core.char.methods.Char.is_numeric : Char → Result Bool

/-- [core::char::methods::{char}::is_whitespace]: the Unicode `White_Space` property. Opaque. -/
opaque core.char.methods.Char.is_whitespace : Char → Result Bool

/-- [alloc::string::{alloc::string::String}::new]: the empty string. -/
def alloc.string.String.new : Result String := ok ""

/-- [alloc::string::{alloc::string::String}::push]: appends the character (its UTF-8 bytes).
Rust panics only when the capacity would exceed `isize::MAX` bytes; the model does not fail, and
`String::len` below fails instead once the length leaves `usize`. -/
def alloc.string.String.push (s : String) (c : Char) : Result String := ok (s.push c)

/-- [alloc::string::{alloc::string::String}::len]: the length in bytes (UTF-8). A Rust `String`
never exceeds `isize::MAX` bytes; a longer Lean `String` has no Rust counterpart and fails. -/
def alloc.string.String.len (s : String) : Result Std.Usize :=
  if h : s.utf8ByteSize < 2 ^ UScalarTy.Usize.numBits then ok (Usize.ofNatCore s.utf8ByteSize h)
  else fail .maximumSizeExceeded

/-- [sudo_rs::sudoers::char_stream::chars_of]: `text.chars().collect()`, kept opaque for Charon
(`str::chars` and `collect` have no Aeneas model). The characters of the text, in order: Rust
`char` and Lean `Char` are both Unicode scalar values. A text with more than `usize::MAX`
characters has no Rust counterpart and fails. -/
def sudoers.char_stream.chars_of (s : String) : Result (alloc.vec.Vec Char) :=
  if h : s.toList.length ≤ Usize.max then ok ⟨Slice.from s.toList h⟩
  else fail .maximumSizeExceeded

/-- [sudo_rs::sudoers::basic_parser::escape_char]: `'\\'`, kept opaque for Charon because the
pinned Aeneas prints this literal as `'\'`, which Lean rejects. -/
def sudoers.basic_parser.escape_char : Result Char := ok '\\'
