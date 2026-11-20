import SudoRsProofs.Util
import SudoersSpec.Escape

/-!
# `escaped` (`src/common/command.rs`) refines `SudoersSpec.Escape.escapeArgs`

The extraction of `escaped`, `escape_arg_into` and `is_unescaped`, with the `OsString` models
of `SudoRs/{Types,Funs}External.lean` (an `OsString` is its bytes; `deref`,
`as_encoded_bytes` and `OsStringExt::from_vec` keep them), is proved equal to the
specification for every input:

* `escaped_eq`: the exact outcome. `escaped args` returns the line `escapeArgs` gives when that
  line fits in a `Vec` (at most `usize::MAX` bytes), and fails with `maximumSizeExceeded` (the
  `Vec::push` overflow of the model) otherwise; it never panics on an index and always
  terminates.
* `escaped_spec` (total correctness), `escaped_ok_iff`, `escaped_ok_eq` (partial correctness);
* `escaped_flatMap`: each byte kept iff `keep`, else preceded by a backslash, arguments joined
  by one space;
* `escaped_injective`: two argument vectors with the same line are equal, except that `[]` and
  `[""]` both give the empty line;
* `escaped_unescape`: the line reads back to the arguments (`unescapeArgs`), except for `[""]`.

`osBytes` maps an `OsString` to its bytes as `UInt8`s, the type of the specification.
-/

open Aeneas Aeneas.Std Result
open SudoersSpec.Escape

namespace SudoRsProofs.Escape

/-! ## Abstraction -/

/-- A Rust `u8` as a Lean `UInt8`. -/
def byteOf (c : U8) : UInt8 := UInt8.ofNat c.val

/-- Rust bytes as Lean bytes. -/
def bytesOf (l : List U8) : List UInt8 := l.map byteOf

/-- The bytes of an `OsString` (`as_encoded_bytes`). -/
def osBytes (s : std.ffi.os_str.OsString) : List UInt8 := bytesOf s.inner.val

/-- The argument list of a `Vec<OsString>`. -/
def osArgs (args : alloc.vec.Vec std.ffi.os_str.OsString) : List (List UInt8) :=
  args.val.map osBytes

@[simp] theorem toNat_byteOf (c : U8) : (byteOf c).toNat = c.val := by
  have hc : c.val < 256 := by scalar_tac
  simp [byteOf, Nat.mod_eq_of_lt hc]

theorem byteOf_injective {a b : U8} (h : byteOf a = byteOf b) : a = b := by
  apply UScalar.eq_of_val_eq
  have := congrArg UInt8.toNat h
  rwa [toNat_byteOf, toNat_byteOf] at this

theorem bytesOf_injective {a b : List U8} (h : bytesOf a = bytesOf b) : a = b :=
  List.map_injective_iff.mpr (fun _ _ => byteOf_injective) h

theorem osBytes_injective {s t : std.ffi.os_str.OsString} (h : osBytes s = osBytes t) :
    s = t := by
  have h1 := bytesOf_injective h
  cases s; cases t
  simp only [std.ffi.os_str.OsString.mk.injEq]
  exact (alloc.vec.Vec.eq_iff _ _).2 h1

theorem osArgs_injective {a b : alloc.vec.Vec std.ffi.os_str.OsString} (h : osArgs a = osArgs b) :
    a = b := by
  apply (alloc.vec.Vec.eq_iff _ _).2
  exact List.map_injective_iff.mpr (fun _ _ => osBytes_injective) h

@[simp] theorem length_bytesOf (l : List U8) : (bytesOf l).length = l.length := by
  simp [bytesOf]

theorem byteOf_backslash : byteOf 92#u8 = backslash := rfl
theorem byteOf_space : byteOf 32#u8 = space := rfl

/-! ## The byte-level image of the specification -/

/-- `escapeArg` on Rust bytes. -/
def escU (a : List U8) : List U8 :=
  a.flatMap fun c => if keep (byteOf c) then [c] else [92#u8, c]

/-- `escapeArgs` on Rust bytes, in the shape of the loop of `escaped`. -/
def escArgsU : List (List U8) → List U8
  | [] => []
  | a :: rest => escU a ++ rest.flatMap fun b => 32#u8 :: escU b

theorem bytesOf_escU (a : List U8) : bytesOf (escU a) = escapeArg (bytesOf a) := by
  rw [escapeArg_eq_flatMap]
  induction a with
  | nil => rfl
  | cons c cs ih =>
    simp only [escU, List.flatMap_cons, bytesOf, List.map_append, List.map_cons] at ih ⊢
    rw [ih]
    split <;> simp [byteOf_backslash]

theorem bytesOf_escArgsU (l : List (List U8)) :
    bytesOf (escArgsU l) = escapeArgs (l.map bytesOf) := by
  cases l with
  | nil => rfl
  | cons a rest =>
    rw [List.map_cons, escapeArgs_cons, escArgsU]
    simp only [bytesOf, List.map_append, List.map_flatMap, List.flatMap_map]
    congr 1
    · exact bytesOf_escU a
    · congr 1
      funext b
      have := bytesOf_escU b
      simp only [bytesOf] at this
      simp [this, byteOf_space]

/-! ## Results that fit in a `Vec` -/

/-- `ok` with the `Vec` of `l` if `l` has at most `usize::MAX` elements, else the overflow
failure of `Vec::push`. -/
def okIfFits (l : List U8) : Result (alloc.vec.Vec U8) :=
  if h : l.length ≤ Usize.max then ok (alloc.vec.Vec.from l h) else fail .maximumSizeExceeded

theorem okIfFits_val (v : alloc.vec.Vec U8) : okIfFits v.val = ok v := by
  simp [okIfFits, alloc.vec.Vec.val_from]

theorem okIfFits_bind (l m : List U8) :
    Aeneas.Std.bind (okIfFits l) (fun v => okIfFits (v.val ++ m)) = okIfFits (l ++ m) := by
  by_cases h : l.length ≤ Usize.max
  · simp [okIfFits, h, alloc.vec.Vec.from_val]
  · simp [okIfFits, h]
    omega

theorem push_eq (v : alloc.vec.Vec U8) (x : U8) : v.push x = okIfFits (v.val ++ [x]) := by
  have hU : U32.max ≤ Usize.max := by scalar_tac
  unfold alloc.vec.Vec.push okIfFits
  dsimp only
  simp only [List.length_append, List.length_singleton, List.concat_eq_append]
  by_cases h : v.val.length + 1 ≤ Usize.max
  · have h' : (decide (v.val.length + 1 ≤ U32.max) ||
        decide (v.val.length + 1 ≤ Usize.max)) = true := by
      simp [h]
    simp only [h', h, ↓reduceDIte]
  · have h' : ¬ (decide (v.val.length + 1 ≤ U32.max) ||
        decide (v.val.length + 1 ≤ Usize.max)) = true := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or]
      omega
    simp only [h', h, ↓reduceDIte]

/-! ## `is_unescaped` -/

theorem keep_byteOf (c : U8) :
    keep (byteOf c) = decide (48 ≤ c.val ∧ c.val ≤ 57 ∨ 65 ≤ c.val ∧ c.val ≤ 90 ∨
      97 ≤ c.val ∧ c.val ≤ 122 ∨ c.val = 95 ∨ c.val = 45 ∨ c.val = 36) := by
  have := keep_iff (byteOf c)
  rw [toNat_byteOf] at this
  apply Bool.eq_iff_iff.2
  rw [this]
  simp only [decide_eq_true_eq]
  rfl

theorem is_unescaped_eq (c : U8) :
    sudo_rs.common.command.is_unescaped c = ok (keep (byteOf c)) := by
  rw [keep_byteOf]
  have h95 : (95#8#uscalar : U8).val = 95 := rfl
  have h45 : (45#8#uscalar : U8).val = 45 := rfl
  have h36 : (36#8#uscalar : U8).val = 36 := rfl
  unfold sudo_rs.common.command.is_unescaped
  split_ifs <;> (try split) <;> simp_all

theorem escU_cons (c : U8) (t : List U8) :
    escU (c :: t) = (if keep (byteOf c) then [c] else [92#u8, c]) ++ escU t := by
  simp [escU]

theorem escape_arg_into_loop_eq (arg : Slice U8) (line : alloc.vec.Vec U8) (i : Usize) :
    sudo_rs.common.command.escape_arg_into_loop arg line i =
      okIfFits (line.val ++ escU (arg.val.drop i.val)) := by
  unfold sudo_rs.common.command.escape_arg_into_loop
  dsimp only
  split
  · rename_i hlt
    have hi : i.val < arg.val.length := by scalar_tac
    obtain ⟨c, hc, hcv⟩ := exists_eq_ok_of_spec (Slice.index_usize_spec arg i hi)
    obtain ⟨i2, hi2, hi2v⟩ := exists_eq_ok_of_spec
      (UScalar.add_spec (x := i) (y := 1#usize) (by scalar_tac))
    have hd2 : arg.val.drop i2.val = arg.val.drop (i.val + 1) := by simp [hi2v]
    have ih : ∀ v, sudo_rs.common.command.escape_arg_into_loop arg v i2 =
        okIfFits (v.val ++ escU (arg.val.drop (i.val + 1))) := by
      intro v
      rw [escape_arg_into_loop_eq arg v i2, hd2]
    rw [List.drop_eq_getElem_cons hi, ← hcv, escU_cons]
    simp only [hc, is_unescaped_eq, Aeneas.Std.bind_ok, hi2, ih]
    by_cases hk : keep (byteOf c) = true
    · simp only [hk, ↓reduceIte, Aeneas.Std.bind_ok, push_eq, okIfFits_bind, List.append_assoc,
        List.singleton_append]
    · simp only [hk, Bool.false_eq_true, ↓reduceIte, push_eq, okIfFits_bind, List.append_assoc,
        List.cons_append, List.nil_append]
  · rename_i hge
    have : arg.val.length ≤ i.val := by scalar_tac
    simp [List.drop_eq_nil_of_le this, escU, okIfFits_val]
termination_by arg.val.length - i.val
decreasing_by all_goals scalar_tac

theorem escape_arg_into_eq (arg : Slice U8) (line : alloc.vec.Vec U8) :
    sudo_rs.common.command.escape_arg_into arg line = okIfFits (line.val ++ escU arg.val) := by
  simp [sudo_rs.common.command.escape_arg_into, escape_arg_into_loop_eq]

@[simp] theorem from_vec_eq (v : alloc.vec.Vec U8) :
    std.ffi.os_str.OsString.Insts.StdOsUnixFfiOs_strOsStringExt.from_vec v = ok ⟨v⟩ := rfl

@[simp] theorem deref_val (v : alloc.vec.Vec U8) : (alloc.vec.Vec.deref v).val = v.val := by
  simp [alloc.vec.Vec.deref]

/-- The part of the line from argument `i ≥ 1` on. -/
def tailU (args : List std.ffi.os_str.OsString) : List U8 :=
  args.flatMap fun s => 32#u8 :: escU s.inner.val

theorem flatMap_map_inner (l : List std.ffi.os_str.OsString) :
    (l.map fun s => s.inner.val).flatMap (fun b => 32#u8 :: escU b) = tailU l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.map_cons, List.flatMap_cons, ih]
    simp only [tailU, List.flatMap_cons]

theorem escaped_loop_eq (args : alloc.vec.Vec std.ffi.os_str.OsString)
    (line : alloc.vec.Vec U8) (i : Usize) (hi : 0 < i.val) :
    sudo_rs.common.command.escaped_loop args line i =
      okIfFits (line.val ++ tailU (args.val.drop i.val)) := by
  unfold sudo_rs.common.command.escaped_loop
  dsimp only
  split
  · rename_i hlt
    have hi' : i.val < args.val.length := by scalar_tac
    obtain ⟨s, hs, hsv⟩ := exists_eq_ok_of_spec
      (alloc.vec.Vec.index_usize_spec args i hi')
    obtain ⟨i2, hi2, hi2v⟩ := exists_eq_ok_of_spec
      (UScalar.add_spec (x := i) (y := 1#usize) (by scalar_tac))
    have hd2 : args.val.drop i2.val = args.val.drop (i.val + 1) := by simp [hi2v]
    have ih : ∀ v, sudo_rs.common.command.escaped_loop args v i2 =
        okIfFits (v.val ++ tailU (args.val.drop (i.val + 1))) := by
      intro v
      rw [escaped_loop_eq args v i2 (by scalar_tac), hd2]
    have hpos : i > 0#usize := by scalar_tac
    rw [List.drop_eq_getElem_cons hi', ← hsv]
    simp only [hpos, ↓reduceIte, alloc.vec.Vec.index_slice_index, hs, Aeneas.Std.bind_ok,
      std.ffi.os_str.OsString.Insts.CoreOpsDerefDerefOsStr.deref,
      std.ffi.os_str.OsStr.as_encoded_bytes, escape_arg_into_eq, hi2, ih, push_eq, deref_val,
      okIfFits_bind, List.append_assoc, List.singleton_append]
    simp [tailU]
  · rename_i hge
    have : args.val.length ≤ i.val := by scalar_tac
    simp [List.drop_eq_nil_of_le this, tailU, okIfFits_val]
termination_by args.val.length - i.val
decreasing_by all_goals scalar_tac

/-! ## `escaped` -/

/-- The line on Rust bytes. -/
def lineU (args : alloc.vec.Vec std.ffi.os_str.OsString) : List U8 :=
  escArgsU (args.val.map fun s => s.inner.val)

theorem bytesOf_lineU (args : alloc.vec.Vec std.ffi.os_str.OsString) :
    bytesOf (lineU args) = escapeArgs (osArgs args) := by
  rw [lineU, bytesOf_escArgsU, List.map_map]
  rfl

theorem length_lineU (args : alloc.vec.Vec std.ffi.os_str.OsString) :
    (lineU args).length = (escapeArgs (osArgs args)).length := by
  rw [← bytesOf_lineU, length_bytesOf]

theorem okIfFits_bind_from_vec (l : List U8) :
    Aeneas.Std.bind (okIfFits l)
        std.ffi.os_str.OsString.Insts.StdOsUnixFfiOs_strOsStringExt.from_vec =
      if h : l.length ≤ Usize.max then ok ⟨alloc.vec.Vec.from l h⟩
      else fail .maximumSizeExceeded := by
  unfold okIfFits
  split <;> simp

/-- **Exact behaviour of `escaped`**: the line of the specification as an `OsString` if it fits
in a `Vec`, the overflow failure of `Vec::push` otherwise. -/
theorem escaped_eq (args : alloc.vec.Vec std.ffi.os_str.OsString) :
    sudo_rs.common.command.escaped args =
      if h : (lineU args).length ≤ Usize.max then ok ⟨alloc.vec.Vec.from (lineU args) h⟩
      else fail .maximumSizeExceeded := by
  unfold sudo_rs.common.command.escaped sudo_rs.common.command.escaped_loop
  dsimp only
  split
  · rename_i hlt
    have h0 : 0 < args.val.length := by scalar_tac
    obtain ⟨s, hs, hsv⟩ := exists_eq_ok_of_spec
      (alloc.vec.Vec.index_usize_spec args 0#usize (by simpa using h0))
    obtain ⟨i2, hi2, hi2v⟩ := exists_eq_ok_of_spec
      (UScalar.add_spec (x := 0#usize) (y := 1#usize) (by scalar_tac))
    have hnpos : ¬ (0#usize > 0#usize) := by scalar_tac
    have hloop : ∀ v, sudo_rs.common.command.escaped_loop args v i2 =
        okIfFits (v.val ++ tailU (args.val.drop 1)) := by
      intro v
      rw [escaped_loop_eq args v i2 (by scalar_tac)]
      simp [hi2v]
    have hargs : args.val = s :: args.val.drop 1 := by
      have := List.drop_eq_getElem_cons h0
      rw [hsv]
      simpa using this
    have hl : lineU args = escU s.inner.val ++ tailU (args.val.drop 1) := by
      conv => lhs; rw [lineU, hargs]
      rw [List.map_cons, escArgsU, flatMap_map_inner]
    simp only [hnpos, ↓reduceIte, Aeneas.Std.bind_ok, alloc.vec.Vec.index_slice_index, hs,
      std.ffi.os_str.OsString.Insts.CoreOpsDerefDerefOsStr.deref,
      std.ffi.os_str.OsStr.as_encoded_bytes, escape_arg_into_eq, hi2, hloop, deref_val,
      okIfFits_bind, alloc.vec.Vec.from_val, List.nil_append]
    rw [okIfFits_bind_from_vec, hl]
  · rename_i hge
    have hnil : args.val = [] := by
      have : args.val.length = 0 := by scalar_tac
      exact List.eq_nil_of_length_eq_zero this
    have : lineU args = [] := by simp [lineU, hnil, escArgsU]
    simp [this]

/-- **(a) Total correctness.** If the line has at most `usize::MAX` bytes, `escaped` returns it. -/
theorem escaped_spec (args : alloc.vec.Vec std.ffi.os_str.OsString)
    (h : (escapeArgs (osArgs args)).length ≤ Usize.max) :
    ∃ r, sudo_rs.common.command.escaped args = ok r ∧ osBytes r = escapeArgs (osArgs args) := by
  have h' : (lineU args).length ≤ Usize.max := by rw [length_lineU]; exact h
  refine ⟨⟨alloc.vec.Vec.from (lineU args) h'⟩, ?_, ?_⟩
  · simp [escaped_eq, h']
  · simp [osBytes, alloc.vec.Vec.from_val, bytesOf_lineU]

/-- Otherwise it fails with the `Vec` overflow (and never returns a wrong line). -/
theorem escaped_overflow (args : alloc.vec.Vec std.ffi.os_str.OsString)
    (h : Usize.max < (escapeArgs (osArgs args)).length) :
    sudo_rs.common.command.escaped args = fail .maximumSizeExceeded := by
  have h' : ¬ (lineU args).length ≤ Usize.max := by rw [length_lineU]; omega
  simp [escaped_eq, h']

theorem escaped_ok_iff (args : alloc.vec.Vec std.ffi.os_str.OsString) :
    (∃ r, sudo_rs.common.command.escaped args = ok r) ↔
      (escapeArgs (osArgs args)).length ≤ Usize.max := by
  constructor
  · rintro ⟨r, hr⟩
    by_contra h
    rw [escaped_overflow args (by omega)] at hr
    exact fail_not_ok hr
  · intro h
    obtain ⟨r, hr, _⟩ := escaped_spec args h
    exact ⟨r, hr⟩

/-- Partial correctness: whatever `escaped` returns is the line of the specification. -/
theorem escaped_ok_eq {args : alloc.vec.Vec std.ffi.os_str.OsString}
    {r : std.ffi.os_str.OsString} (hr : sudo_rs.common.command.escaped args = ok r) :
    osBytes r = escapeArgs (osArgs args) := by
  obtain ⟨r', hr', h⟩ := escaped_spec args ((escaped_ok_iff args).1 ⟨r, hr⟩)
  rw [hr] at hr'
  rw [Result.ok_injective hr']
  exact h

/-- **(b) Exact characterization.** Each byte of each argument is kept iff `keep` (ASCII
alphanumerics, `_`, `-`, `$`), else preceded by a backslash; the arguments are joined with one
space. -/
theorem escaped_flatMap {args : alloc.vec.Vec std.ffi.os_str.OsString}
    {r : std.ffi.os_str.OsString} (hr : sudo_rs.common.command.escaped args = ok r) :
    osBytes r = [space].intercalate ((osArgs args).map fun a =>
      a.flatMap fun c => if keep c then [c] else [backslash, c]) := by
  rw [escaped_ok_eq hr, escapeArgs_eq_intercalate]
  congr 1
  apply List.map_congr_left
  intro a _
  exact escapeArg_eq_flatMap a

/-- **(c) Injectivity.** Two argument vectors for which `escaped` returns the same line are
equal, except for the pair `[]` / `[""]` (both give the empty line). -/
theorem escaped_injective {a b : alloc.vec.Vec std.ffi.os_str.OsString}
    {r : std.ffi.os_str.OsString} (ha : sudo_rs.common.command.escaped a = ok r)
    (hb : sudo_rs.common.command.escaped b = ok r) :
    a = b ∨ (osArgs a = [] ∧ osArgs b = [[]]) ∨ (osArgs a = [[]] ∧ osArgs b = []) := by
  have h := (escaped_ok_eq ha).symm.trans (escaped_ok_eq hb)
  rcases (escapeArgs_eq_iff _ _).1 h with h | h | h
  · exact .inl (osArgs_injective h)
  · exact .inr (.inl h)
  · exact .inr (.inr h)

/-- The collision is real: `[]` and `[""]` both give the empty line. -/
theorem escaped_collision :
    sudo_rs.common.command.escaped (alloc.vec.Vec.new _) = ok ⟨alloc.vec.Vec.new U8⟩ ∧
    sudo_rs.common.command.escaped
        (alloc.vec.Vec.from [⟨alloc.vec.Vec.new U8⟩] (by simp; scalar_tac)) =
      ok ⟨alloc.vec.Vec.new U8⟩ := by
  constructor <;> simp [escaped_eq, lineU, escArgsU, escU]

/-- **(d) Reading the line back.** `unescapeArgs` (a backslash quotes the next byte, any other
space separates arguments) recovers the arguments from the line, for every argument vector
except `[""]`; in particular no argument contributes an unescaped space or backslash. -/
theorem escaped_unescape {args : alloc.vec.Vec std.ffi.os_str.OsString}
    {r : std.ffi.os_str.OsString} (hr : sudo_rs.common.command.escaped args = ok r)
    (hne : osArgs args ≠ [[]]) :
    unescapeArgs (osBytes r) = osArgs args := by
  rw [escaped_ok_eq hr, unescapeArgs_escapeArgs hne]

end SudoRsProofs.Escape
