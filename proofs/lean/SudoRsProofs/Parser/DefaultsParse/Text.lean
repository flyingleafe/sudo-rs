import SudoRsProofs.Parser.DefaultsParse.Tokens
import SudoRsProofs.Parser.Parameters

/-! `join_var` and `parse_defaults_text`: the quoted branch requires a closing quote after
reading a quoted parameter; either token may reject or fail at the reference cursor. -/

open Aeneas Aeneas.Std Result sudo_rs
open SudoersSpec

namespace SudoRsProofs.Parser.DefaultsParse

open Syntax Syntax.Parser

private theorem join_loop_eq (chars : alloc.vec.Vec Char) (i : Usize) (entry : String) :
    sudoers.ast.join_var_loop entry chars i =
      ok (String.ofList (entry.toList ++ chars.val.drop i.val)) := by
  rw [sudoers.ast.join_var_loop]
  split
  · rename_i hlt
    have hi : i.val < chars.val.length := by scalar_tac
    obtain ⟨j, hj, hjv⟩ := Defaults.usize_add_one i (lt_of_lt_of_le hi chars.slice.property)
    have he := eq_ok_of_spec (alloc.vec.Vec.index_usize_spec chars i hi)
    simp only [alloc.vec.Vec.index_slice_index, he, bind_ok, alloc.string.String.push, hj]
    rw [join_loop_eq chars j (entry.push chars.val[i.val]), hjv]
    have hdrop := List.drop_eq_getElem_cons (l := chars.val) hi
    conv => rhs; rw [hdrop]
    simp [String.toList_push, List.append_assoc]
  · have hn : chars.val.length ≤ i.val := by scalar_tac
    simp [List.drop_eq_nil_of_le hn, String.ofList_toList]
termination_by chars.val.length - i.val

/-- The `VAR=value` materialization is concatenation. The `StringParameter` bounds discharge
`value.utf8ByteSize ≤ Usize.max` for every actual caller. -/
theorem join_var_eq (nm value : String) (hv : value.utf8ByteSize ≤ Usize.max) :
    sudoers.ast.join_var nm value = ok (nm ++ "=" ++ value) := by
  obtain ⟨chars, hc, hcv⟩ := chars_of_eq value hv
  rw [SudoRsProofs.Vec.deref_val] at hcv
  simp only [sudoers.ast.join_var, alloc.string.String.push, hc, bind_ok, join_loop_eq,
    hcv, String.toList_push]
  simp [String.ofList_append, String.ofList_toList, String.append_assoc]

/-- The reference text-value parser returns at most 1028 UTF-8 bytes. -/
theorem textItem_size_le {O : Oracles} {s t : Stream} {v : String}
    (h : (textItem O .release).run s = (.ok v, t)) : v.utf8ByteSize ≤ 1028 := by
  unfold textItem at h
  obtain ⟨_, _, _, h⟩ := run_bind_eq_ok.mp h
  split at h
  · obtain ⟨a, _, ha, h⟩ := run_bind_eq_ok.mp h
    obtain ⟨_, _, _, h⟩ := run_bind_eq_ok.mp h
    have e := Except.ok.inj (Prod.mk.inj h).1
    cases e
    obtain ⟨_, h⟩ := token_before_ws (Grammar.expectNonterminal_ok_iff.mp ha)
    exact token_size_le (quotedStringParameterToken O.char) (fun _ => rfl) h
  · obtain ⟨_, h⟩ := token_before_ws (Grammar.expectNonterminal_ok_iff.mp h)
    exact token_size_le (stringParameterToken O.char) (fun _ => rfl) h

/-- The helper for quoted or bare Defaults text, refining both value and error with the final
cursor. -/
theorem parse_defaults_text_refines {O : Oracles} (hO : P2CharOracle O.char)
    {s : CS} (hs : StreamOK s) :
    Refines id (sudoers.ast.parse_defaults_text s) ((textItem O .release).run (absStream s)) := by
  obtain ⟨s1, e, hs1, a1⟩ := eat_char_eq hs '"'
  simp only [sudoers.ast.parse_defaults_text, e, bind_ok, uncurry_apply_pair, textItem, run_bind,
    run_eatChar]
  rcases hb : (absStream s).eatChar '"' with ⟨b, t1⟩
  rw [hb] at a1
  change absStream s1 = t1 at a1
  subst t1
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    obtain ⟨r, s2, er, hr, hs2, a2⟩ := expect_nonterminal_refines
      (string_parameter_parse_refines hO) string_parameter_description hs1
    simp only [er, bind_ok, uncurry_apply_pair]
    rcases hR : (expectNonterminal Descriptions.release.stringParameter
      (token (stringParameterToken O.char))).run (absStream s1) with ⟨r', t2⟩
    rw [hR] at hr a2
    change absStream s2 = t2 at a2
    cases r <;> cases r' <;> simp_all [ResultRel]
  | true =>
    simp only [↓reduceIte]
    obtain ⟨r, s2, er, hr, hs2, a2⟩ := expect_nonterminal_refines
      (quotedStringParameter_parse_refines hO) quotedStringParameter_description hs1
    simp only [er, bind_ok, uncurry_apply_pair]
    rcases hR : (expectNonterminal Descriptions.release.quotedStringParameter
      (token (quotedStringParameterToken O.char))).run (absStream s1) with ⟨r', t2⟩
    rw [hR] at hr a2
    simp only [run_bind, hR]
    change absStream s2 = t2 at a2
    subst t2
    cases r with
    | Err st =>
      cases r' <;> simp_all [ResultRel]
    | Ok v =>
      cases r' with
      | error _ => cases hr
      | ok val =>
        have e : v = val := hr
        subst val
        obtain ⟨q, s3, eq, hq, hs3, a3⟩ := expect_syntax_refines hs2 '"'
        simp only [branch_Ok, bind_ok, eq, uncurry_apply_pair]
        rcases hQ : (expectSyntax '"').run (absStream s2) with ⟨q', t3⟩
        rw [hQ] at hq a3
        cases q <;> cases q' <;> simp only [ResultRel, Prod.fst] at hq <;>
          simp [hq, hs3, a3]

end SudoRsProofs.Parser.DefaultsParse
