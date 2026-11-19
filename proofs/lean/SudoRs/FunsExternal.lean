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
equality of the (abstract) values. -/
noncomputable def std.ffi.os_str.OsString.Insts.CoreCmpPartialEqOsString.eq
  (a b : std.ffi.os_str.OsString) : Result Bool := ok (decide (a = b))

/-- [std::ffi::os_str::{impl core::convert::AsRef<std::ffi::os_str::OsStr> for str}::as_ref]:
the `OsStr` view of a `&str`. Opaque (no axiom): nothing is known about it. -/
opaque Str.Insts.CoreConvertAsRefOsStr.as_ref : Str → Result std.ffi.os_str.OsStr

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
