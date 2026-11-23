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

/-- Plain UTF-8 byte equality and membership for ASCII `*`. A model over the Lean
`String` is total, as required by the existing `construct_ok_eq` theorem. -/
def sudoers.tokens.classify_chdir (s : String) : Result sudoers.tokens.ChDirForm :=
  if s = "*" then ok .Any
  else if s.toList.contains '*' then ok .ContainsStar
  else ok .Path

/-- `SudoPath::try_from(String)`: the input is already UTF-8. The only invalid
character is NUL; otherwise the resulting path retains the string. -/
def sudoers.tokens.sudo_path (s : String) :
    Result (core.result.Result common.path.SudoPath sudoers.basic_parser.ErrorKind) :=
  if s.toList.contains (Char.ofNat 0) then ok (.Err (.NulInPath s))
  else ok (.Ok ⟨s⟩)

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

/-! ### Permission-line parser externals -/

/-- `char::is_alphanumeric`, the union of the Unicode alphabetic and numeric classes. -/
opaque core.char.methods.Char.is_alphanumeric : Char → Result Bool

/-- Unicode `Cc`: the C0, DEL and C1 code points. -/
def core.char.methods.Char.is_control (c : Char) : Result Bool :=
  ok (c.toNat ≤ 0x1f || (0x7f ≤ c.toNat && c.toNat ≤ 0x9f))

/-- Boxing a vector as a slice retains its elements and their order. -/
def alloc.vec.Vec.into_boxed_slice {T : Type _} (_A : Type _) (v : alloc.vec.Vec T) :
    Result (Slice T) := ok v.slice

/-- `SudoString::new`: reject interior NUL and otherwise append the terminator, which the
existing `SudoString` model deliberately omits. -/
def sudoers.tokens.sudo_string (s : String) :
    Result (core.result.Result common.string.SudoString sudoers.basic_parser.ErrorKind) :=
  if s.toList.contains (Char.ofNat 0) then ok (.Err (.NulInString s)) else ok (.Ok ⟨s⟩)

/-- File-system canonicalization, retaining the distinction between failure and non-UTF-8. -/
opaque sudoers.tokens.canonical : String → Result sudoers.tokens.Canonical

/-- Pattern compilation with the error payload used by the Rust diagnostic renderer. -/
opaque sudoers.tokens.compile_pattern :
  String → Result (core.result.Result glob.Pattern sudoers.basic_parser.ErrorKind)

/-- Native argument conversion. The oracle speaks about the existing Unix byte model. -/
opaque sudoers.tokens.os_string : String → Result std.ffi.os_str.OsString

/-! ### Models used by the `Defaults` modifiers and value checkers (`src/defaults`) -/

/-- [alloc::boxed::convert::{impl From<&str> for Box<str>}::from]: copies the bytes; boxes are
erased. -/
def BoxStr.Insts.CoreConvertFromShared0Str.from (s : Str) : Result Str := ok s

/-- [core::str::{str}::as_bytes]: a `&str` is represented by its bytes. -/
def core.str.Str.as_bytes (s : Str) : Result (Slice U8) := ok s

/-- [core::str::{str}::len]: the number of bytes. -/
def core.str.Str.len (s : Str) : Result Usize := ok (Slice.len s)

namespace sudo_rs

/-- `str::is_char_boundary` (`core/src/str/mod.rs`): `0`, the length, or an index whose byte is not
a UTF-8 continuation byte (`u8::is_utf8_char_boundary`: `(b as i8) >= -0x40`, i.e. `b < 0x80` or
`b ≥ 0xC0`). -/
def strIsCharBoundary (s : Str) (i : Nat) : Bool :=
  i == 0 || i == s.length ||
    (match s.val[i]? with
     | some b => b.val < 0x80 || 0xC0 ≤ b.val
     | none => false)

/-- `(b as char).to_digit(radix)` for a byte `b` and `2 ≤ radix ≤ 36` (`core/src/char/methods.rs`):
`0`-`9`, then `a`-`z` and `A`-`Z` from 10, if below `radix`. -/
def asciiDigit (b radix : Nat) : Option Nat :=
  let d :=
    if 48 ≤ b ∧ b ≤ 57 then some (b - 48)
    else if 97 ≤ b ∧ b ≤ 122 then some (b - 87)
    else if 65 ≤ b ∧ b ≤ 90 then some (b - 55)
    else none
  match d with
  | some x => if x < radix then some x else none
  | none => none

/-- The digit loop of `from_ascii_bytes_radix_impl` for an unsigned type with maximum `max`:
the first byte that is not a digit is `InvalidDigit`; a value above `max` is `PosOverflow`. Both
loops of the Rust code (the unchecked one runs only where no overflow is possible; the checked one
tests the digit before the overflow of the multiplication) give these results. -/
def parseDigits (radix max : Nat) : List Nat → Nat → core.result.Result Nat core.num.error.IntErrorKind
  | [], acc => .Ok acc
  | b :: rest, acc =>
    match asciiDigit b radix with
    | none => .Err .InvalidDigit
    | some x =>
      if acc * radix + x ≤ max then parseDigits radix max rest (acc * radix + x)
      else .Err .PosOverflow

/-- `from_ascii_bytes_radix_impl` for an unsigned type (`core/src/num/mod.rs`): panics unless
`2 ≤ radix ≤ 36`; the empty input is `Empty`; a lone `+` or `-` is `InvalidDigit`; one leading
`+` is skipped (a leading `-` is not a digit of an unsigned type); then the digits. -/
def fromStrRadix (ty : UScalarTy) (src : Str) (radix : U32) :
    Result (core.result.Result (UScalar ty) core.num.error.ParseIntError) :=
  if radix.val < 2 ∨ 36 < radix.val then fail .panic
  else
    let digits : core.result.Result Nat core.num.error.IntErrorKind :=
      match src.val.map (·.val) with
      | [] => .Err .Empty
      | [43] => .Err .InvalidDigit
      | [45] => .Err .InvalidDigit
      | 43 :: rest => parseDigits radix.val (UScalar.max ty) rest 0
      | bytes => parseDigits radix.val (UScalar.max ty) bytes 0
    match digits with
    | .Err kind => ok (.Err { kind })
    | .Ok n => do
      -- `n ≤ UScalar.max ty` by `parseDigits`, so this cannot fail
      let x ← UScalar.tryMk ty n
      ok (.Ok x)

end sudo_rs

/-- Digit values of Unicode scalar values are ASCII-only, as for the byte
inputs to `fromStrRadix`. -/
def core.char.methods.Char.to_digit (c : Char) (radix : U32) : Result (Option U32) :=
  if radix.val < 2 ∨ 36 < radix.val then fail .panic
  else ok ((sudo_rs.asciiDigit c.toNat radix.val).map (fun d => ⟨BitVec.ofNat 32 d⟩))

/-- [core::str::{str}::split_at]: the first `mid` bytes and the rest; panics unless `mid` is a
char boundary (`split_at_checked`, else `slice_error_fail`). -/
def core.str.Str.split_at (s : Str) (mid : Usize) : Result (Str × Str) :=
  if sudo_rs.strIsCharBoundary s mid.val then
    ok (Slice.from (s.val.take mid.val)
          (by have := s.property; simp only [List.length_take]; omega),
        Slice.from (s.val.drop mid.val)
          (by have := s.property; simp only [List.length_drop]; omega))
  else fail .panic

/-- [core::num::{u32}::from_str_radix] -/
def core.num.U32.from_str_radix (src : Str) (radix : U32) :
    Result (core.result.Result U32 core.num.error.ParseIntError) :=
  sudo_rs.fromStrRadix .U32 src radix

/-- [core::num::{u64}::from_str_radix] -/
def core.num.U64.from_str_radix (src : Str) (radix : U32) :
    Result (core.result.Result U64 core.num.error.ParseIntError) :=
  sudo_rs.fromStrRadix .U64 src radix

/-- [core::num::{u64}::pow]: with overflow checks (`strict_pow`) an overflow panics; modelled as
the integer overflow of the other arithmetic operations. -/
def core.num.U64.pow (x : U64) (exp : U32) : Result U64 :=
  UScalar.tryMk .U64 (x.val ^ exp.val)

/-- [std::collections::hash::set::{HashSet<T, S, A>}::remove]: drops the keys whose borrow equals
`key`; `true` iff there was one. Extensional, as `insert`. -/
def std.collections.hash.set.HashSet.remove
    {T S A Q H : Type} (_ : core.cmp.Eq T) (_ : core.hash.Hash T)
    (_ : sudo_rs.core.hash.BuildHasher S H) (borrow : core.borrow.Borrow T Q)
    (_ : core.hash.Hash Q) (eqQ : core.cmp.Eq Q)
    (keys : std.collections.hash.set.HashSet T S A) (key : Q) :
    Result (Bool × std.collections.hash.set.HashSet T S A) := do
  let kept ← keys.filterM fun k => do
    let q ← borrow.borrow k
    let same ← eqQ.partialEqInst.eq q key
    ok (!same)
  ok (kept.length != keys.length, kept)

/-! ### Models used by the analysis of the parsed items and the `Defaults` scoping
(`analyze`, `Sudoers::check`, `proofs/parser/ANALYSIS.md`) -/

/-- [std::path::{std::path::Path}::to_path_buf]: `Path` and `PathBuf` are abstract, so is the
copy. Opaque (no axiom): the `source` of a diagnostic of the analysis is `to_path_buf` of the
path of the file; a theorem that needs its value takes it as a hypothesis. -/
opaque std.path.Path.to_path_buf : std.path.Path → Result std.path.PathBuf

/-- [std::path::{std::path::PathBuf}::as_path]: abstract. Opaque: only the path of an included
file, which the include oracle returns, is turned back into a `Path`. -/
opaque std.path.PathBuf.as_path : std.path.PathBuf → Result std.path.Path

/-- [sudo_rs::sudoers::include_file]: the include oracle, part 1 (`src/sudoers/mod.rs`), kept
opaque for Charon: it resolves a path against the including file, reads the file system and
parses the included file. Opaque (no axiom); the analysis calls it only for include items. -/
opaque sudoers.include_file :
  std.path.Path → sudoers.IncludeFile → Option sudoers.IncludeState →
    Result (core.result.Result (std.path.PathBuf × (alloc.vec.Vec
      (core.result.Result sudoers.ast.Sudo sudoers.basic_parser.Status))) String)

/-- [sudo_rs::sudoers::include_dir_files]: the include oracle, part 2, kept opaque for Charon: the
listing of an `@includedir` directory, or a message. Opaque (no axiom). -/
opaque sudoers.include_dir_files :
  std.path.Path → String → Result (core.result.Result (alloc.vec.Vec std.path.PathBuf) String)

namespace sudo_rs

/-- The text of `kind.to_string()` for the error kind of a fatal parse error (`Display for
ErrorKind`, `src/sudoers/basic_parser.rs`). Not modelled. -/
opaque errorKindText : sudoers.basic_parser.ErrorKind → String

end sudo_rs

/-- [sudo_rs::sudoers::fatal_message]: `kind.to_string()`, kept opaque for Charon (formatting).
Total: `Display for ErrorKind` writes into a `String` and cannot fail; its text is
`errorKindText`. -/
def sudoers.fatal_message (kind : sudoers.basic_parser.ErrorKind) : Result String :=
  ok (sudo_rs.errorKindText kind)

/-- [sudo_rs::defaults::{impl Default for Settings}::default], kept opaque for Charon: the
initializers of the list settings (`[..].into_iter().map(..).collect::<HashSet<_>>()` in
`initializer_of!`, `src/defaults/settings_dsl.rs`) have no Aeneas model. Opaque (no axiom): a
theorem about the settings in force starts from `Settings::default()` as a hypothesis. -/
opaque defaults.Settings.Insts.CoreDefaultDefault.default : Result defaults.Settings

/-- [alloc::boxed::{impl Default for Box<[T]>}::default]: the empty slice; boxes are erased. -/
def BoxSlice.Insts.CoreDefaultDefault.default (T : Type _) : Result (Slice T) :=
  ok (Slice.new T)

/-- [alloc::boxed::{impl Clone for Box<str>}::clone]: copies the bytes; boxes are erased. -/
def BoxStr.Insts.CoreCloneClone.clone {A : Type _} (_ : core.clone.Clone A) (s : Str) :
    Result Str :=
  ok s

/-- [std::collections::hash::set::{impl Clone for HashSet<T, S, A>}::clone]: the same keys,
each cloned with the key's `Clone` (the table is cloned element by element); extensional, as
`insert`. -/
def std.collections.hash.set.HashSet.Insts.CoreCloneClone.clone {T S A : Type}
    (cloneT : core.clone.Clone T) (_ : core.clone.Clone S) (_ : core.clone.Clone A)
    (keys : std.collections.hash.set.HashSet T S A) :
    Result (std.collections.hash.set.HashSet T S A) :=
  keys.mapM cloneT.clone

/-- [std::hash::random::{impl Clone for RandomState}::clone]: hash seeding is not observed by
the set model; only fills the dictionary of the `HashSet` clone. -/
opaque std.hash.random.RandomState.Insts.CoreCloneClone.clone :
  std.hash.random.RandomState → Result std.hash.random.RandomState
