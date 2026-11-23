import SudoRsProofs.Parser.SimpleCommand

/-! The text comparisons of stable alias, Defaults and include dispatch. -/

open Aeneas Aeneas.Std Result SudoersSpec
open sudo_rs

namespace SudoRsProofs.Parser

/-- `equals_str` compares Unicode scalar sequences, not byte offsets. -/
theorem equals_str_eq (text : String) (word : Slice Char) (h : text.utf8ByteSize ≤ Usize.max) :
    sudoers.ast.equals_str text word = ok (text.toList == word.val) := by
  obtain ⟨v, hv, he⟩ := chars_of_eq text h
  simp only [sudoers.ast.equals_str, hv, bind_ok, equals_text_eq, he]

/-- `starts_with_str` compares the prefix against the same character sequence as Lean. -/
theorem starts_with_str_eq (text : String) (pre : Slice Char) (h : text.utf8ByteSize ≤ Usize.max) :
    sudoers.ast.starts_with_str text pre = ok (pre.val.isPrefixOf text.toList) := by
  obtain ⟨v, hv, he⟩ := chars_of_eq text h
  simp only [sudoers.ast.starts_with_str, hv, bind_ok, starts_with_text_eq, he]

/-- Equality of a Rust keyword slice and a reference word lifts to the comparison result. -/
theorem equals_keyword_eq (text word : String) (kw : Slice Char) (hk : kw.val = word.toList)
    (h : text.utf8ByteSize ≤ Usize.max) : sudoers.ast.equals_str text kw = ok (text == word) := by
  rw [equals_str_eq text kw h, hk]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  exact ⟨fun he => by simpa using congrArg String.ofList he, congrArg String.toList⟩

@[simp] theorem include_val : sudoers.ast.INCLUDE.val = "include".toList := by
  simp [sudoers.ast.INCLUDE, Array.to_slice, Array.make]

@[simp] theorem includedir_val : sudoers.ast.INCLUDEDIR.val = "includedir".toList := by
  simp [sudoers.ast.INCLUDEDIR, Array.to_slice, Array.make]

@[simp] theorem alias_kw_user_val : sudoers.ast.ALIAS_KW_USER.val = "User_Alias".toList := by
  simp [sudoers.ast.ALIAS_KW_USER, Array.to_slice, Array.make]

@[simp] theorem alias_kw_host_val : sudoers.ast.ALIAS_KW_HOST.val = "Host_Alias".toList := by
  simp [sudoers.ast.ALIAS_KW_HOST, Array.to_slice, Array.make]

@[simp] theorem alias_kw_cmnd_val : sudoers.ast.ALIAS_KW_CMND.val = "Cmnd_Alias".toList := by
  simp [sudoers.ast.ALIAS_KW_CMND, Array.to_slice, Array.make]

@[simp] theorem alias_kw_cmd_val : sudoers.ast.ALIAS_KW_CMD.val = "Cmd_Alias".toList := by
  simp [sudoers.ast.ALIAS_KW_CMD, Array.to_slice, Array.make]

@[simp] theorem alias_kw_runas_val : sudoers.ast.ALIAS_KW_RUNAS.val = "Runas_Alias".toList := by
  simp [sudoers.ast.ALIAS_KW_RUNAS, Array.to_slice, Array.make]

@[simp] theorem defaults_val : sudoers.ast.DEFAULTS.val = "Defaults".toList := by
  simp [sudoers.ast.DEFAULTS, Array.to_slice, Array.make]

/-- The eight reserved words of Rust `Def<T>::parse`. -/
theorem is_reserved_alias_eq (nm : String) (h : nm.utf8ByteSize ≤ Usize.max) :
    sudoers.ast.is_reserved_alias nm = ok (Syntax.isReservedAlias nm) := by
  have all := equals_keyword_eq nm "ALL" sudoers.ast.ALIAS_ALL
    (by simp [sudoers.ast.ALIAS_ALL, Array.to_slice, Array.make]) h
  have chroot := equals_keyword_eq nm "CHROOT" sudoers.ast.ALIAS_CHROOT
    (by simp [sudoers.ast.ALIAS_CHROOT, Array.to_slice, Array.make]) h
  have cwd := equals_keyword_eq nm "CWD" sudoers.ast.ALIAS_CWD
    (by simp [sudoers.ast.ALIAS_CWD, Array.to_slice, Array.make]) h
  have after := equals_keyword_eq nm "NOTAFTER" sudoers.ast.ALIAS_NOTAFTER
    (by simp [sudoers.ast.ALIAS_NOTAFTER, Array.to_slice, Array.make]) h
  have before := equals_keyword_eq nm "NOTBEFORE" sudoers.ast.ALIAS_NOTBEFORE
    (by simp [sudoers.ast.ALIAS_NOTBEFORE, Array.to_slice, Array.make]) h
  have role := equals_keyword_eq nm "ROLE" sudoers.ast.ALIAS_ROLE
    (by simp [sudoers.ast.ALIAS_ROLE, Array.to_slice, Array.make]) h
  have time := equals_keyword_eq nm "TIMEOUT" sudoers.ast.ALIAS_TIMEOUT
    (by simp [sudoers.ast.ALIAS_TIMEOUT, Array.to_slice, Array.make]) h
  have ty := equals_keyword_eq nm "TYPE" sudoers.ast.ALIAS_TYPE
    (by simp [sudoers.ast.ALIAS_TYPE, Array.to_slice, Array.make]) h
  simp only [sudoers.ast.is_reserved_alias, all, chroot, cwd, after, before, role, time, ty,
    bind_ok, Syntax.isReservedAlias]
  split_ifs <;> simp_all

end SudoRsProofs.Parser
