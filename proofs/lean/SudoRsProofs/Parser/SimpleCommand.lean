import SudoRsProofs.Parser.P2Oracle
import SudoRsProofs.Parser.Tokens

/-! The character classes and constructor of `SimpleCommand` (`glob::Pattern`). -/

open Aeneas Aeneas.Std Result
open sudo_rs

namespace SudoRsProofs.Parser

open SudoersSpec

private theorem char_beq (c d : Char) : (c == d) = decide (c = d) := rfl

private theorem char_beq_comm (c d : Char) : (c == d) = (d == c) := by
  rw [char_beq, char_beq, decide_eq_decide]
  exact eq_comm

theorem simple_command_escaped_eq (c : Char) :
    sudo_rs.glob.Pattern.Insts.Sudo_rsSudoersBasic_parserToken.escaped c =
      ok (Syntax.SimpleCommand.escaped c) := by
  simp only [sudo_rs.glob.Pattern.Insts.Sudo_rsSudoersBasic_parserToken.escaped,
    sudoers.basic_parser.escape_char, bind_ok, Syntax.SimpleCommand.escaped, char_beq]
  split_ifs <;> simp_all

theorem simple_command_accept_1st_eq (c : Char) :
    sudo_rs.glob.Pattern.Insts.Sudo_rsSudoersBasic_parserToken.accept_1st c =
      ok (Syntax.SimpleCommand.accept1st c) := by
  simp only [sudo_rs.glob.Pattern.Insts.Sudo_rsSudoersBasic_parserToken.accept_1st,
    Syntax.SimpleCommand.accept1st, char_beq]
  split_ifs <;> simp_all

theorem simple_command_accept_eq {A : GlobAbs} {O : Syntax.Oracles} (hO : P2Oracle A O)
    (c : Char) :
    sudo_rs.glob.Pattern.Insts.Sudo_rsSudoersBasic_parserToken.accept c =
      ok (Syntax.SimpleCommand.accept O.char c) := by
  cases he : Syntax.SimpleCommand.escaped c <;> cases hc : O.char.isControl c <;>
    simp [sudo_rs.glob.Pattern.Insts.Sudo_rsSudoersBasic_parserToken.accept,
      simple_command_escaped_eq, hO.chars.is_control, Syntax.SimpleCommand.accept, he, hc, char_beq]

private theorem isPrefixOf_eq_false_of_not_length {α : Type} [BEq α] [LawfulBEq α]
    {l1 l2 : List α} (h : ¬ l1.length ≤ l2.length) : l1.isPrefixOf l2 = false := by
  cases hp : l1.isPrefixOf l2
  · rfl
  · exact absurd (List.isPrefixOf_iff_prefix.mp hp).length_le h

private theorem starts_with_text_loop_false (text pre : Slice Char) (i : Usize) :
    sudoers.tokens.starts_with_text_loop text pre false i = ok false := by
  unfold sudoers.tokens.starts_with_text_loop
  simp

private theorem starts_with_text_loop_eq (text pre : Slice Char)
    (hlen : pre.val.length ≤ text.val.length) (b : Bool) (i : Usize) :
    sudoers.tokens.starts_with_text_loop text pre b i =
      ok (b && (pre.val.drop i.val).isPrefixOf (text.val.drop i.val)) := by
  unfold sudoers.tokens.starts_with_text_loop
  split
  · rename_i hb
    subst hb
    dsimp only
    split
    · rename_i hlt
      have hp : i.val < pre.val.length := by
        simpa only [UScalar.lt_equiv, Slice.len_val] using hlt
      have ht : i.val < text.val.length := lt_of_lt_of_le hp hlen
      have hmax : i.val + (1#usize : Usize).val ≤ UScalar.max .Usize := by
        have h : i.val + 1 ≤ Usize.max := by
          have := pre.property
          omega
        simpa [UScalar.max_USize_eq] using h
      obtain ⟨j, hj, hjv⟩ :=
        exists_eq_ok_of_spec (UScalar.add_spec (ty := .Usize) (x := i) (y := 1#usize) hmax)
      have hjv' : j.val = i.val + 1 := by simpa using hjv
      rw [eq_ok_of_spec (Slice.index_usize_spec text i ht), bind_ok,
        eq_ok_of_spec (Slice.index_usize_spec pre i hp), bind_ok, hj, bind_ok]
      rw [starts_with_text_loop_eq text pre hlen _ j]
      simp only [Bool.true_and, hjv', List.drop_eq_getElem_cons hp, List.drop_eq_getElem_cons ht,
        List.isPrefixOf_cons_cons, char_beq]
      have hd : decide (text.val[i.val] = pre.val[i.val]) =
          decide (pre.val[i.val] = text.val[i.val]) :=
        by simpa only [char_beq] using char_beq_comm (text.val[i.val]) (pre.val[i.val])
      rw [hd]
    · rename_i hge
      have hp : pre.val.length ≤ i.val := by
        have h : ¬ i.val < (Slice.len pre).val :=
          (UScalar.lt_equiv i (Slice.len pre)).not.mp hge
        rw [Slice.len_val] at h
        exact Nat.le_of_not_lt h
      have hnil : pre.val.drop i.val = [] := List.drop_eq_nil_of_le (by simpa using hp)
      simp only [Bool.true_and, hnil, List.isPrefixOf_nil_left]
  · rename_i hb
    cases b
    · rfl
    · exact absurd rfl hb
termination_by pre.val.length - i.val
decreasing_by omega

private theorem starts_with_text_eq (text pre : Slice Char) :
    sudoers.tokens.starts_with_text text pre = ok (pre.val.isPrefixOf text.val) := by
  have hle : Slice.len pre ≤ Slice.len text ↔ pre.val.length ≤ text.val.length := by
    simp only [UScalar.le_equiv, Slice.len_val]
  unfold sudoers.tokens.starts_with_text
  dsimp only
  by_cases h : pre.val.length ≤ text.val.length
  · rw [show decide (pre.len ≤ text.len) = true by simpa using (hle.mpr h),
      starts_with_text_loop_eq text pre h]
    simp
  · have hp : pre.val.isPrefixOf text.val = false := isPrefixOf_eq_false_of_not_length h
    rw [show decide (pre.len ≤ text.len) = false by simpa using (mt hle.mp h),
      starts_with_text_loop_false, hp]

private theorem equals_text_eq (text word : Slice Char) :
    sudoers.tokens.equals_text text word = ok (text.val == word.val) := by
  unfold sudoers.tokens.equals_text
  dsimp only
  split_ifs with h
  · have hlen : text.val.length = word.val.length := by
      simpa only [Slice.len_val] using congrArg UScalar.val h
    rw [starts_with_text_eq]
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [List.isPrefixOf_iff_prefix, beq_iff_eq]
    exact ⟨fun hp => (hp.eq_of_length hlen.symm).symm, fun he => ⟨[], by simp [he]⟩⟩
  · have hb : (text.val == word.val) = false := by
      cases he : (text.val == word.val)
      · rfl
      · exact absurd (by
          apply UScalar.eq_of_val_eq
          simpa only [Slice.len_val] using congrArg List.length (beq_iff_eq.mp he)) h
    rw [hb]

private theorem singleton_prefix_eq (c : Char) (cs : List Char) :
    [c].isPrefixOf cs = (cs.head? == some c) := by
  cases cs with
  | nil => rfl
  | cons d ds =>
    simp only [List.isPrefixOf_cons_cons, List.isPrefixOf_nil_left, Bool.and_true,
      List.head?_cons]
    exact char_beq_comm c d

private theorem compile_with_suffix_refines {A : GlobAbs} {O : Syntax.Oracles}
    (hO : P2Oracle A O) (s : String) (dir : Bool) :
    ∃ r, (do
      let cmd ← if dir then do
        let s1 ← alloc.string.String.push s '/'
        alloc.string.String.push s1 '*'
      else ok s
      sudoers.tokens.compile_pattern cmd) = ok r ∧
      ConstructRel A.pat r
        (Syntax.SimpleCommand.compile O (if dir then s.toList ++ "/*".toList else s.toList)) := by
  cases dir
  · simpa only [Bool.false_eq_true, ↓reduceIte, bind_ok] using hO.compile s
  · have hs : ((s.push '/').push '*').toList = s.toList ++ "/*".toList := by
      rw [String.toList_push, String.toList_push, List.append_assoc]
      rfl
    simpa only [↓reduceIte, alloc.string.String.push, bind_ok, hs] using
      hO.compile ((s.push '/').push '*')

private theorem canonical_compile_refines {A : GlobAbs} {O : Syntax.Oracles}
    (hO : P2Oracle A O) (base : String) (dir : Bool) :
    let compile (s : String) := do
      let cmd ← if dir then do
        let s1 ← alloc.string.String.push s '/'
        alloc.string.String.push s1 '*'
      else ok s
      sudoers.tokens.compile_pattern cmd
    ∃ r, (do
      let canon ← sudoers.tokens.canonical base
      match canon with
      | .Unresolved => compile base
      | .Resolved real => compile real
      | .NotUtf8 => ok (core.result.Result.Err (sudoers.basic_parser.ErrorKind.NonUtf8Path)))
      = ok r ∧
      ConstructRel A.pat r
        (let canon : Except Syntax.ErrKind (List Char) :=
          match O.fs.canonicalize base with
          | .ok real => .ok real.toList
          | .okNonUtf8 => .error .nonUtf8Filesystem
          | .err => .ok base.toList
        match canon with
        | .error e => .error e
        | .ok cs => Syntax.SimpleCommand.compile O (if dir then cs ++ "/*".toList else cs)) := by
  dsimp only
  rw [hO.canonical, bind_ok]
  cases hc : O.fs.canonicalize base with
  | err => exact compile_with_suffix_refines hO base dir
  | ok real => exact compile_with_suffix_refines hO real dir
  | okNonUtf8 => exact ⟨_, rfl, KindRel.nonUtf8Path⟩

/-- `SimpleCommand::construct` returns a related result on every representable input string.
The modeled `String::push` is total, and the compilation oracle applies to every string, so
no further byte bound is needed for canonicalized paths in the extracted model. -/
theorem simple_command_construct_refines {A : GlobAbs} {O : Syntax.Oracles}
    (hO : P2Oracle A O) (s : String) (hs : s.utf8ByteSize ≤ Usize.max) :
    ∃ r, sudo_rs.glob.Pattern.Insts.Sudo_rsSudoersBasic_parserToken.construct s = ok r ∧
      ConstructRel A.pat r (Syntax.SimpleCommand.construct O s.toList) := by
  obtain ⟨v, hv, hd⟩ := chars_of_eq s hs
  have hlistChars : ['l', 'i', 's', 't'] = "list".toList := rfl
  have heditChars : ['s', 'u', 'd', 'o', 'e', 'd', 'i', 't'] = "sudoedit".toList := rfl
  have hshaChars : ['s', 'h', 'a'] = "sha".toList := rfl
  simp only [sudo_rs.glob.Pattern.Insts.Sudo_rsSudoersBasic_parserToken.construct, hv, bind_ok,
    lift, starts_with_text_eq, equals_text_eq, Array.val_to_slice, Array.make_val, hd,
    Syntax.SimpleCommand.construct]
  simp only [hlistChars, heditChars, hshaChars, singleton_prefix_eq]
  simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne]
  by_cases hl : s.toList = "list".toList
  · simpa only [hl, true_or, ↓reduceIte] using hO.compile s
  simp only [hl, false_or, ↓reduceIte]
  by_cases he : s.toList = "sudoedit".toList
  · simpa only [he, ↓reduceIte] using hO.compile s
  simp only [he, ↓reduceIte]
  by_cases hsha : "sha".toList.isPrefixOf s.toList = true
  · simp only [hsha]
    exact ⟨_, rfl, KindRel.digestNotSupported⟩
  simp only [hsha, Bool.false_eq_true, ↓reduceIte]
  by_cases hregex : s.toList.head? = some '^'
  · simp only [hregex]
    exact ⟨_, rfl, KindRel.regexNotSupported⟩
  simp only [hregex, ↓reduceIte]
  by_cases habs : s.toList.head? = some '/'
  · simp only [habs, ne_eq, not_true_eq_false, ↓reduceIte]
    have hval : v.val = s.toList := by simpa only [SudoRsProofs.Vec.deref_val] using hd
    have hpos : 0 < s.toList.length := by
      cases hc : s.toList with
      | nil => simp [hc] at habs
      | cons x xs => simp
    have hSub : (1#usize : Usize).val ≤ (alloc.vec.Vec.len v).val := by
      simp only [alloc.vec.Vec.len_val, alloc.vec.Vec.length, hval]
      simp
      omega
    obtain ⟨i, hi, hiv⟩ := exists_eq_ok_of_spec (UScalar.sub_spec hSub)
    have hiVal : i.val = s.toList.length - 1 := by
      have h := hiv.1
      simp only [alloc.vec.Vec.len_val, alloc.vec.Vec.length, hval] at h
      simpa using h
    have hiLt : i.val < v.val.length := by rw [hval, hiVal]; omega
    have hIndex : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Char) v i =
        ok v.val[i.val] := by
      rw [alloc.vec.Vec.index_slice_index]
      exact eq_ok_of_spec (alloc.vec.Vec.index_usize_spec v i hiLt)
    have hLast : s.toList.getLast? = some v.val[i.val] := by
      rw [List.getLast?_eq_getElem?, ← hiVal, ← hval, List.getElem?_eq_getElem hiLt]
    have hString : sudoers.tokens.string_of (alloc.vec.Vec.deref v) i =
        ok (String.ofList s.toList.dropLast) := by
      have hle : i.val ≤ (alloc.vec.Vec.deref v).val.length := by rw [hd, hiVal]; omega
      simpa only [hd, hiVal, List.dropLast_eq_take] using string_of_eq _ _ hle
    simp only [hi, bind_ok, hIndex, hLast, Option.some.injEq]
    by_cases hdir : v.val[i.val] = '/'
    · simp only [hdir, ↓reduceIte, hString, bind_ok]
      obtain ⟨r, hr, hrel⟩ :=
        canonical_compile_refines hO (String.ofList s.toList.dropLast) true
      refine ⟨r, hr, ?_⟩
      simp only [String.toList_ofList, ↓reduceIte] at hrel
      exact hrel
    · simp only [hdir, ↓reduceIte, bind_ok, String.ofList_toList]
      obtain ⟨r, hr, hrel⟩ := canonical_compile_refines hO s false
      simp only [Bool.false_eq_true, ↓reduceIte, bind_ok] at hr
      refine ⟨r, hr, ?_⟩
      simp only [Bool.false_eq_true, ↓reduceIte] at hrel
      exact hrel
  · simp only [habs, ne_eq, not_false_eq_true, ↓reduceIte]
    exact ⟨_, rfl, KindRel.fullyQualifiedPath⟩

/-- Extraction specializes the `SimpleCommand` calls in `Command` rather than emitting the
whole trait record. Assemble the extracted methods with the Rust token's 1024-byte limit. -/
noncomputable def simpleCommandInstance : sudoers.basic_parser.Token glob.Pattern where
  MAX_LEN := ok 1024#usize
  ALLOW_ESCAPE := ok sudo_rs.glob.Pattern.Insts.Sudo_rsSudoersBasic_parserToken.ALLOW_ESCAPE
  construct := sudo_rs.glob.Pattern.Insts.Sudo_rsSudoersBasic_parserToken.construct
  accept := sudo_rs.glob.Pattern.Insts.Sudo_rsSudoersBasic_parserToken.accept
  accept_1st := sudo_rs.glob.Pattern.Insts.Sudo_rsSudoersBasic_parserToken.accept_1st
  escaped := sudo_rs.glob.Pattern.Insts.Sudo_rsSudoersBasic_parserToken.escaped

theorem simple_command_token_refines {A : GlobAbs} {O : Syntax.Oracles} (hO : P2Oracle A O) :
    TokenRefines simpleCommandInstance A.pat (Syntax.simpleCommandToken O) (fun _ => True) where
  max_len := ⟨_, rfl, by simp [Syntax.simpleCommandToken]⟩
  max_len_le := by
    simp only [Syntax.simpleCommandToken]
    scalar_tac
  allow_escape := by
    simp [simpleCommandInstance, sudo_rs.glob.Pattern.Insts.Sudo_rsSudoersBasic_parserToken.ALLOW_ESCAPE,
      Syntax.simpleCommandToken]
  accept := simple_command_accept_eq hO
  accept_1st := simple_command_accept_1st_eq
  escaped := simple_command_escaped_eq
  construct s hs _ := simple_command_construct_refines hO s hs

end SudoRsProofs.Parser
