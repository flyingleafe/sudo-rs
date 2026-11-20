module

public import Arm64.Trusted.Object.Labels
public import Arm64.Trusted.Surface.IncludeBytes

/-! # Extracted Relocatable Objects (sudo-rs `NameOrId::<UserId>::parse` (`proofs/machine-code/rust`))

Generated directly from `.o` inputs by `rust-obj2lean` (`trusted_extractor`) without
static linking. DO NOT EDIT MANUALLY: this file is a generated build product.
-/

@[expose] public section

namespace SudoRsMachineCode

open Arm64

set_option maxHeartbeats 20000000
set_option maxRecDepth 2000000

/-- Extracted relocatable object `sudo_rs_machine_code`. -/
def sudoRsParseUidExtractedObj0 : Obj.ExtractedObj where
  name := "sudo_rs_machine_code"
  sections := [
    { name := ".text", bytes := [], size := 0, align := 4, isExec := true, readOnly := true, isNobits := false },
    { name := ".text._RNvXs2_Cs4L6F7yIgbcd_20sudo_rs_machine_codeNtB5_10SudoStringNtNtNtCskxtBwYRO61I_4core3ops5deref5Deref5deref", bytes := include_bytes% "SudoRsParseUidExtractedObj.bin" 0 60, size := 60, align := 4, isExec := true, readOnly := true, isNobits := false, relocs := [{ off := 0x2c, kind := some .adrpHi21, symIdx := 12 }, { off := 0x30, kind := some .addLo12, symIdx := 12 }, { off := 0x38, kind := some .call26, symIdx := 17 }] },
    { name := ".text._RNvXs3_Cs4L6F7yIgbcd_20sudo_rs_machine_codeNtB5_10SudoStringNtNtCskxtBwYRO61I_4core3fmt5Debug3fmt", bytes := include_bytes% "SudoRsParseUidExtractedObj.bin" 60 68, size := 68, align := 4, isExec := true, readOnly := true, isNobits := false, relocs := [{ off := 0x24, kind := some .jump26, symIdx := 19 }, { off := 0x30, kind := some .adrpHi21, symIdx := 12 }, { off := 0x34, kind := some .addLo12, symIdx := 12 }, { off := 0x40, kind := some .call26, symIdx := 17 }] },
    { name := ".text._RNvXsf_Cs4L6F7yIgbcd_20sudo_rs_machine_codeNtB5_6UserIdNtNtNtCskxtBwYRO61I_4core3str6traits7FromStr8from_str", bytes := include_bytes% "SudoRsParseUidExtractedObj.bin" 128 420, size := 420, align := 4, isExec := true, readOnly := true, isNobits := false },
    { name := ".text.sudo_rs_name_or_id_parse_uid", bytes := include_bytes% "SudoRsParseUidExtractedObj.bin" 548 344, size := 344, align := 4, isExec := true, readOnly := true, isNobits := false, relocs := [{ off := 0x144, kind := some .adrpHi21, symIdx := 12 }, { off := 0x148, kind := some .addLo12, symIdx := 12 }, { off := 0x154, kind := some .call26, symIdx := 17 }] },
    { name := ".rodata.str1.1", bytes := include_bytes% "SudoRsParseUidExtractedObj.bin" 892 35, size := 35, align := 1, isExec := false, readOnly := true, isNobits := false },
    { name := ".rodata..Lanon.e8f4017197bd23f4310a6aeae1c9895e.1", bytes := include_bytes% "SudoRsParseUidExtractedObj.bin" 927 24, size := 24, align := 8, isExec := false, readOnly := true, isNobits := false, relocs := [{ off := 0x0, kind := some .abs64, symIdx := 10 }] }]
  symbols := [
    { rawName := "", name := "", sec := .undef, value := 0x0, size := 0, kind := .other, bind := .local },
    { rawName := "sudo_rs_machine_code.3770b8305fe32363-cgu.0", name := "sudo_rs_machine_code.3770b8305fe32363-cgu.0", sec := .other, value := 0x0, size := 0, kind := .other, bind := .local },
    { rawName := "", name := ".text._RNvXs2_Cs4L6F7yIgbcd_20sudo_rs_machine_codeNtB5_10SudoStringNtNtNtCskxtBwYRO61I_4core3ops5deref5Deref5deref", sec := .sec 1, value := 0x0, size := 0, kind := .section, bind := .local },
    { rawName := "$x", name := "$x", sec := .sec 1, value := 0x0, size := 0, kind := .other, bind := .local },
    { rawName := "", name := ".text._RNvXs3_Cs4L6F7yIgbcd_20sudo_rs_machine_codeNtB5_10SudoStringNtNtCskxtBwYRO61I_4core3fmt5Debug3fmt", sec := .sec 2, value := 0x0, size := 0, kind := .section, bind := .local },
    { rawName := "$x", name := "$x", sec := .sec 2, value := 0x0, size := 0, kind := .other, bind := .local },
    { rawName := "", name := ".text._RNvXsf_Cs4L6F7yIgbcd_20sudo_rs_machine_codeNtB5_6UserIdNtNtNtCskxtBwYRO61I_4core3str6traits7FromStr8from_str", sec := .sec 3, value := 0x0, size := 0, kind := .section, bind := .local },
    { rawName := "$x", name := "$x", sec := .sec 3, value := 0x0, size := 0, kind := .other, bind := .local },
    { rawName := "", name := ".text.sudo_rs_name_or_id_parse_uid", sec := .sec 4, value := 0x0, size := 0, kind := .section, bind := .local },
    { rawName := "$x", name := "$x", sec := .sec 4, value := 0x0, size := 0, kind := .other, bind := .local },
    { rawName := "", name := ".rodata.str1.1", sec := .sec 5, value := 0x0, size := 0, kind := .section, bind := .local },
    { rawName := "$d", name := "$d", sec := .sec 5, value := 0x0, size := 0, kind := .other, bind := .local },
    { rawName := "", name := ".rodata..Lanon.e8f4017197bd23f4310a6aeae1c9895e.1", sec := .sec 6, value := 0x0, size := 0, kind := .section, bind := .local },
    { rawName := "$d", name := "$d", sec := .sec 6, value := 0x0, size := 0, kind := .other, bind := .local },
    { rawName := "$d", name := "$d", sec := .other, value := 0x0, size := 0, kind := .other, bind := .local },
    { rawName := "$d", name := "$d", sec := .other, value := 0x0, size := 0, kind := .other, bind := .local },
    { rawName := "_RNvXs2_Cs4L6F7yIgbcd_20sudo_rs_machine_codeNtB5_10SudoStringNtNtNtCskxtBwYRO61I_4core3ops5deref5Deref5deref", name := "<sudo_rs_machine_code::SudoString as core::ops::deref::Deref>::deref", sec := .sec 1, value := 0x0, size := 60, kind := .func, bind := .global },
    { rawName := "_RNvNtCskxtBwYRO61I_4core3str16slice_error_fail", name := "core::str::slice_error_fail", sec := .undef, value := 0x0, size := 0, kind := .other, bind := .global },
    { rawName := "_RNvXs3_Cs4L6F7yIgbcd_20sudo_rs_machine_codeNtB5_10SudoStringNtNtCskxtBwYRO61I_4core3fmt5Debug3fmt", name := "<sudo_rs_machine_code::SudoString as core::fmt::Debug>::fmt", sec := .sec 2, value := 0x0, size := 68, kind := .func, bind := .global },
    { rawName := "_RNvXsh_NtCskxtBwYRO61I_4core3fmteNtB5_5Debug3fmt", name := "<str as core::fmt::Debug>::fmt", sec := .undef, value := 0x0, size := 0, kind := .other, bind := .global },
    { rawName := "_RNvXsf_Cs4L6F7yIgbcd_20sudo_rs_machine_codeNtB5_6UserIdNtNtNtCskxtBwYRO61I_4core3str6traits7FromStr8from_str", name := "<sudo_rs_machine_code::UserId as core::str::traits::FromStr>::from_str", sec := .sec 3, value := 0x0, size := 420, kind := .func, bind := .global },
    { rawName := "sudo_rs_name_or_id_parse_uid", name := "sudo_rs_name_or_id_parse_uid", sec := .sec 4, value := 0x0, size := 344, kind := .func, bind := .global }]
  groups := []

/-- All extracted relocatable objects of sudo-rs `NameOrId::<UserId>::parse` (`proofs/machine-code/rust`). -/
def sudoRsParseUidExtractedObjs : List Obj.ExtractedObj := [sudoRsParseUidExtractedObj0]

end SudoRsMachineCode
