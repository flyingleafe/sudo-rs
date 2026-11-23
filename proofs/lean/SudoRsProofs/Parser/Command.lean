import SudoRsProofs.Parser.CommandArgs
import SudoRsProofs.Parser.SimpleCommand

/-! `Command` pairs a compiled executable pattern with the argument mode and words. The
constructor needs a nonempty result of `splitWhitespace`: its very first word is required.
Only the actual call site, after whitespace has been skipped, supplies that premise. -/

open Aeneas Aeneas.Std Result
open SudoersSpec.Syntax (Oracles CharOracle)

namespace SudoRsProofs.Parser

open sudo_rs

/-- The constructor domain is exactly that there is a first word. -/
def CommandText (O : CharOracle) (cs : List Char) : Prop :=
  SudoersSpec.Syntax.splitWhitespace O cs ≠ []

private theorem stringFits_of_bound {s : String} (h : s.utf8ByteSize ≤ Usize.max) : Fits s := by
  simpa only [Fits, sudo_rs.stringBytes, List.length_map, Array.length_toList,
    ByteArray.size_data, String.size_toByteArray] using h

private theorem command_word_list_test (s : String) (h : s.utf8ByteSize ≤ Usize.max) :
    ∃ str, alloc.string.String.as_str s = ok str ∧
      Str.Insts.CoreCmpPartialEqStr.eq str (toStr "list") = ok (decide (s = "list")) := by
  have hh := stringFits_of_bound h
  refine ⟨strOf s hh, strOfString_eq hh, ?_⟩
  apply eq_ok_of_spec
  have hs := Str.eq_spec (strOf s hh) (toStr "list")
  simpa [toStr_val, stringBytes_inj] using hs

private theorem compile_source {O : Oracles} {cs : List Char} {out : String}
    (h : SudoersSpec.Syntax.SimpleCommand.compile O cs = .ok out) : out = String.ofList cs := by
  unfold SudoersSpec.Syntax.SimpleCommand.compile at h
  split at h <;> simp_all

/-- The Rust `is_list` test uses the input word, before path resolution. The reference uses the
pattern's source text, after resolution. These tests agree: a successful canonicalization is
absolute, and the non-canonicalized path branch only returns an absolute pattern. -/
private theorem simple_command_list_test {A : GlobAbs} {O : Oracles} (hO : P2Oracle A O)
    (cs : List Char) {out : String}
    (h : SudoersSpec.Syntax.SimpleCommand.construct O cs = .ok out) :
    (out = "list" ↔ String.ofList cs = "list") := by
  have key : ∀ ys : List Char, ys.head? = some '/' → String.ofList ys ≠ "list" := by
    intro ys hy e
    have he := congrArg (fun s : String => s.toList.head?) e
    simp [hy] at he
  unfold SudoersSpec.Syntax.SimpleCommand.construct at h
  split at h
  · rw [compile_source h]
  · rename_i hn
    have hnot : String.ofList cs ≠ "list" := by
      intro he
      have hc := congrArg String.toList he
      simp at hc
      simp [hc] at hn
    simp only [hnot, iff_false]
    split at h
    · simp at h
    split at h
    · simp at h
    split at h
    · simp at h
    rename_i hs
    have hhead : cs.head? = some '/' := by simpa using hs
    by_cases hd : cs.getLast? = some '/'
    · simp only [hd, beq_self_eq_true, ↓reduceIte] at h
      cases hc : O.fs.canonicalize (String.ofList cs.dropLast) with
      | err =>
        simp only [hc] at h
        rw [compile_source h]
        apply key
        cases cs with
        | nil => simp
        | cons c tail =>
          have : c = '/' := by simpa using hhead
          subst c
          cases tail <;> simp
      | ok real =>
        simp only [hc] at h
        rw [compile_source h]
        have ha := hO.canonical_absolute _ _ hc
        apply key
        cases hh : real.toList with
        | nil => simp [hh] at ha
        | cons c tail => simpa [hh] using ha
      | okNonUtf8 => simp [hc] at h
    · have hdb : (cs.getLast? == some '/') = false := by simpa using hd
      simp only [hdb, Bool.false_eq_true, ↓reduceIte] at h
      cases hc : O.fs.canonicalize (String.ofList cs) with
      | err => simp only [hc] at h; rw [compile_source h]; exact key cs hhead
      | ok real =>
        simp only [hc] at h
        rw [compile_source h, String.ofList_toList]
        simpa [String.ofList_toList] using key real.toList (hO.canonical_absolute _ _ hc)
      | okNonUtf8 => simp [hc] at h

private theorem argsRange_full (text : Slice Char) (words : alloc.vec.Vec WordRange)
    (stop : Usize) (hs : stop.val = words.val.length) :
    rangeWords text (alloc.vec.Vec.deref words) 1#usize stop =
      (words.val.drop 1).map (rangeChars text) := by
  simp [rangeWords, hs]

private theorem argsRange_trim (text : Slice Char) (words : alloc.vec.Vec WordRange)
    (stop : Usize) (hs : stop.val = words.val.length - 1) :
    rangeWords text (alloc.vec.Vec.deref words) 1#usize stop =
      ((words.val.drop 1).map (rangeChars text)).dropLast := by
  simp [rangeWords, hs, List.dropLast_eq_take, List.map_take, Nat.sub_sub]

set_option maxHeartbeats 5000000 in
/-- On its exact domain `Command::construct` returns the corresponding parse result, not an
Aeneas failure. In the nonempty-word case every indexed range and scalar operation is in bounds. -/
theorem command_construct_refines {A : GlobAbs} {O : Oracles} (hO : P2Oracle A O)
    (s : String) (hs : s.utf8ByteSize ≤ Usize.max) (hText : CommandText O.char s.toList) :
    ∃ r, PairPatternArgs.Insts.Sudo_rsSudoersBasic_parserToken.construct s = ok r ∧
      ConstructRel (absCommand A) r (SudoersSpec.Syntax.Command.construct O s.toList) := by
  obtain ⟨chars, echar, echars⟩ := chars_of_eq s hs
  let text := alloc.vec.Vec.deref chars
  have htext : text.val = s.toList := echars
  have hBudget : SudoersSpec.Syntax.utf8Len text.val ≤ Usize.max := by
    rw [htext, ← utf8Len_toList]
    exact hs
  obtain ⟨words, ew, hBounds, hWords, _⟩ := split_words_refines hO.chars.unicode text
  have hWords' : words.val.map (rangeChars text) =
      SudoersSpec.Syntax.splitWhitespace O.char s.toList := by
    rw [← htext, ← hWords]
    apply List.map_congr_left
    rintro ⟨a, b⟩ _
    rfl
  rcases hW : words.val with _ | ⟨⟨a, b⟩, tail⟩
  · have : SudoersSpec.Syntax.splitWhitespace O.char s.toList = [] := by simpa [hW] using hWords'.symm
    exact (hText this).elim
  · have hw0 : 0 < words.val.length := by simp [hW]
    have hab : WordInBounds text (a,b) := hBounds _ (by simp [hW])
    have hfirst : words.val[0]'hw0 = (a,b) := by simp [hW]
    have hidx : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice WordRange) words 0#usize =
        ok (a,b) := by
      simpa [hfirst] using vecIndex_eq words 0#usize (by simpa using hw0)
    let cmd := String.ofList (rangeChars text (a,b))
    have hcmd : sudo_rs.sudoers.tokens.word_text text a b = ok cmd := word_text_eq text a b hab.2
    have hbCmd : cmd.utf8ByteSize ≤ Usize.max :=
      (rangeChars_utf8ByteSize_le text (a,b)).trans hBudget
    let rawArgs := tail.map (rangeChars text)
    have hr : SudoersSpec.Syntax.splitWhitespace O.char s.toList = cmd.toList :: rawArgs := by
      simpa [hW, cmd, rawArgs] using hWords'.symm
    obtain ⟨n, en, hnv⟩ := usizeSub_eq (alloc.vec.Vec.len words) 1#usize (by simp; omega)
    have hn : n.val = tail.length := by simpa [hW] using hnv
    obtain ⟨r, er, hR⟩ := simple_command_construct_refines hO cmd hbCmd
    obtain ⟨cmdStr, hAsStr, hList⟩ := command_word_list_test cmd hbCmd
    have hEmp : alloc.vec.Vec.is_empty words = ok false := by simp [alloc.vec.Vec.is_empty, hW]
    unfold PairPatternArgs.Insts.Sudo_rsSudoersBasic_parserToken.construct
    simp only [echar, bind_ok, ← show text = alloc.vec.Vec.deref chars from rfl, ew, hEmp,
      Bool.false_eq_true, ↓reduceIte, hidx, uncurry_apply_pair, hcmd]
    have hUnwrap : core.option.Option.unwrap (some cmd) = ok cmd := rfl
    simp only [hUnwrap, bind_ok, hAsStr, hList, en, er]
    rcases hSC : SudoersSpec.Syntax.SimpleCommand.construct O cmd.toList with e | patSrc <;>
      rcases r with pat | k <;> simp only [hSC, ConstructRel] at hR
    · exact ⟨.Err k, by simp, by simpa [SudoersSpec.Syntax.Command.construct, hr, hSC, ConstructRel] using hR⟩
    · have hPat : A.pat pat = patSrc := hR
      have hEqList : (cmd = "list" ↔ patSrc = "list") := by
        simpa [String.ofList_toList] using (simple_command_list_test hO cmd.toList hSC).symm
      cases htail : tail with
      | nil =>
        have hzero : n = 0#usize := by apply UScalar.eq_of_val_eq; simp [hn, htail]
        simp [hzero, SudoersSpec.Syntax.Command.construct, hr, hSC, rawArgs, htail,
          SudoersSpec.Syntax.Command.argPattern, alloc.vec.Vec.into_boxed_slice, ConstructRel,
          absCommand, absArgs, hPat]
        rfl
      | cons arg rest =>
        have hn' : 1 ≤ n.val := by simp [hn, htail]
        have hArgsNonEmpty : rawArgs ≠ [] := by simp [rawArgs, htail]
        have hArgsIsEmpty : rawArgs.isEmpty = false := by simpa using hArgsNonEmpty
        have hn0 : n ≠ 0#usize := by intro hz; simp [hz] at hn'
        have hnWords : n.val + 1 = words.val.length := by simp [hW, hn, Nat.add_comm]
        have hfirstArg : 1 < words.val.length := by simp [hW, htail]
        have hidxArg : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice WordRange)
            words 1#usize = ok (arg.1, arg.2) := by
          have he := vecIndex_eq words 1#usize (by simpa using hfirstArg)
          simpa [hW, htail] using he
        have hArg := hBounds arg (by simp [hW, htail])
        have hArgIdx : arg.1.val < chars.val.length := by
          rw [← Vec.deref_val chars]
          exact Nat.lt_of_lt_of_le hArg.1 hArg.2
        have heArg := vecIndex_eq chars arg.1 hArgIdx
        have hCaret : rawArgs.head?.bind List.head? = some chars.val[arg.1.val] := by
          have he := rangeChars_eq_cons text arg.1 arg.2 hArg
          simp [rawArgs, htail, he, text, Vec.deref_val]
        simp only [branch_Ok, bind_ok, hn0, ↓reduceIte, hidxArg, uncurry_apply_pair, heArg]
        by_cases hRegex : chars.val[arg.1.val] = '^'
        · exact ⟨.Err .RegexNotSupported, by simp [hRegex], by
            simp [SudoersSpec.Syntax.Command.construct, hr, hSC, SudoersSpec.Syntax.Command.argPattern,
              hArgsIsEmpty, hCaret, hRegex, ConstructRel, KindRel.regexNotSupported]⟩
        · simp only [hRegex, ↓reduceIte]
          have hnlt : n.val < words.val.length := by omega
          let last := words.val[n.val]
          have hl := hBounds last (List.getElem_mem hnlt)
          have hLast : rawArgs.getLast? = some (rangeChars text last) := by
            have hLs : (words.val.map (rangeChars text)).getLast? = some (rangeChars text last) := by
              rw [List.getLast?_map, List.getLast?_eq_getElem?]
              have he : words.val.length - 1 = n.val := by omega
              simp [he, List.getElem?_eq_getElem hnlt, last]
            rw [hW, List.map_cons] at hLs
            rw [List.getLast?_cons_of_ne_nil hArgsNonEmpty] at hLs
            exact hLs
          obtain ⟨len, elen, hlen⟩ := usizeSub_eq last.2 last.1 (Nat.le_of_lt hl.1)
          have hLen : len.val = (rangeChars text last).length := hlen.trans (rangeChars_length hl).symm
          have hidxLast : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice WordRange)
              words n = ok (last.1, last.2) := vecIndex_eq words n hnlt
          have hlidx : last.1.val < chars.val.length := by
            rw [← Vec.deref_val chars]
            exact Nat.lt_of_lt_of_le hl.1 hl.2
          have hlfirst := vecIndex_eq chars last.1 hlidx
          obtain ⟨kept, eKept, hKept⟩ := usizeSub_eq n 1#usize (by simpa using hn')
          obtain ⟨endCut, eCut, hCut⟩ := usizeAdd_eq kept 1#usize (by
            have : n.val ≤ Usize.max := by scalar_tac
            scalar_tac)
          obtain ⟨endFull, eFull, hFull⟩ := usizeAdd_eq n 1#usize (by
            have := words.len_ineq
            scalar_tac)
          have hCut' : endCut.val = words.val.length - 1 := by scalar_tac
          have hFull' : endFull.val = words.val.length := by simpa using hFull.trans hnWords
          have hB : ∀ r ∈ words.deref.val, WordInBounds text r := by
            intro r hm
            exact hBounds r (by simpa using hm)
          have hEndCut : endCut.val ≤ words.deref.val.length := by simp [hCut']
          have hEndFull : endFull.val ≤ words.deref.val.length := by simp [hFull']
          have hCutPos : 1 ≤ endCut.val := by scalar_tac
          have hFullPos : 1 ≤ endFull.val := by scalar_tac
          have hArgsFull : rangeWords text words.deref 1#usize endFull = rawArgs := by
            simp [argsRange_full text words endFull hFull', hW, rawArgs]
          have hArgsCut : rangeWords text words.deref 1#usize endCut = rawArgs.dropLast := by
            simp [argsRange_trim text words endCut hCut', hW, rawArgs]
          have hGlobFull := any_glob_eq text words.deref endFull hEndFull hB
          have hGlobCut := any_glob_eq text words.deref endCut hEndCut hB
          rw [hArgsFull] at hGlobFull
          rw [hArgsCut] at hGlobCut
          obtain ⟨vFull, evFull, hvFull⟩ :=
            os_strings_eq hO text hBudget words.deref endFull hFullPos hEndFull hB
          obtain ⟨vCut, evCut, hvCut⟩ :=
            os_strings_eq hO text hBudget words.deref endCut hCutPos hEndCut hB
          rw [hArgsFull] at hvFull
          rw [hArgsCut] at hvCut
          have hsliceFull : vFull.slice.val.map A.os = rawArgs.map String.ofList := hvFull
          have hsliceCut : vCut.slice.val.map A.os = rawArgs.dropLast.map String.ofList := hvCut
          have hGlobPred : (fun c : Char => c == '?' || c == '*' || c == '[') = argGlobChar := rfl
          simp only [SudoersSpec.Syntax.Command.construct, hr, hSC, SudoersSpec.Syntax.Command.argPattern,
            hArgsIsEmpty, Bool.false_eq_true, ↓reduceIte, hCaret, hGlobPred]
          have hkept0 : kept = 0#usize ↔ rawArgs.dropLast = [] := by
            rw [← List.length_eq_zero_iff]
            simp only [List.length_dropLast, rawArgs, List.length_map]
            constructor
            · intro he; have := congrArg UScalar.val he; scalar_tac
            · intro he; apply UScalar.eq_of_val_eq; scalar_tac
          have hMap : (rawArgs.map String.ofList).dropLast = [] ↔ kept = 0#usize := by
            rw [← List.map_dropLast, List.map_eq_nil_iff]
            exact hkept0.symm
          have hfirstLast := rangeChars_eq_cons text last.1 last.2 hl
          -- Use the word length to keep the generated short-circuit index checks in scope.
          by_cases hlen1 : len = 1#usize
          · have hh : last.2.val - (last.1.val + 1) = 0 := by scalar_tac
            have hword : rangeChars text last = [chars.val[last.1.val]] := by
              rw [hfirstLast, hh]
              simp [text]
            by_cases hStar : chars.val[last.1.val] = '*'
            · have hword' : rawArgs.getLast? = some ['*'] := by simp [hLast, hword, hStar]
              simp only [hidxLast, bind_ok, uncurry_apply_pair, elen, hlen1, ↓reduceIte,
                hlfirst, hStar, eKept, eCut, hGlobCut, evCut, alloc.vec.Vec.into_boxed_slice]
              simp only [hword', beq_self_eq_true, ↓reduceIte]
              cases rawArgs.dropLast.any (·.any argGlobChar) <;>
                by_cases hIsList : cmd = "list" <;> by_cases hk : kept = 0#usize <;>
                simp [hRegex, hIsList, ← hEqList, hk, hMap, hsliceCut, ConstructRel,
                  absCommand, absArgs, hPat, KindRel.globInArguments, KindRel.listArguments]
            · have hnotStar : rawArgs.getLast? ≠ some ['*'] := by simpa [hLast, hword] using hStar
              have hnotQuotes : rawArgs.getLast? ≠ some ['"','"'] := by simp [hLast, hword]
              simp only [hidxLast, bind_ok, uncurry_apply_pair, elen, hlen1, ↓reduceIte,
                hlfirst, hStar, eFull, hGlobFull, evFull, alloc.vec.Vec.into_boxed_slice]
              simp only [show (rawArgs.getLast? == some ['*']) = false by simpa using hnotStar,
                show (rawArgs.getLast? == some ['\"','\"']) = false by simpa using hnotQuotes,
                Bool.false_eq_true, ↓reduceIte]
              cases rawArgs.any (·.any argGlobChar) <;> by_cases hIsList : cmd = "list" <;>
                simp [hRegex, hIsList, ← hEqList, hsliceFull, ConstructRel, absCommand,
                  absArgs, hPat, KindRel.globInArguments, KindRel.listArguments]
          · by_cases hlen2 : len = 2#usize
            · have htwo : last.1.val + 1 < last.2.val := by scalar_tac
              obtain ⟨second, ehSecond, hSecond⟩ := usizeAdd_eq last.1 1#usize (by
                have := text.property
                scalar_tac)
              have hSecond' : second.val = last.1.val + 1 := by simpa using hSecond
              have hStop : last.2.val ≤ chars.val.length := by simpa [text] using hl.2
              have h2Idx : second.val < chars.val.length := by omega
              have h2Char := vecIndex_eq chars second h2Idx
              have hword : rangeChars text last = [chars.val[last.1.val], chars.val[second.val]] := by
                have hb : last.1.val + 1 < text.val.length := by have := hl.2; omega
                have hh : last.2.val - (last.1.val + 1) = 1 := by scalar_tac
                rw [hfirstLast, List.drop_eq_getElem_cons hb, hh, List.take_succ_cons]
                simp [text, hSecond']
              have hnotStar : rawArgs.getLast? ≠ some ['*'] := by simp [hLast, hword]
              by_cases hq1 : chars.val[last.1.val] = '"' <;>
                by_cases hq2 : chars.val[second.val] = '"' <;>
                simp only [hidxLast, bind_ok, uncurry_apply_pair, elen, hlen2, ↓reduceIte,
                  hlfirst, hq1, ehSecond, h2Char, hq2, eKept, eCut, eFull, hGlobCut, hGlobFull,
                  evCut, evFull, alloc.vec.Vec.into_boxed_slice] <;>
                simp only [hLast, hword, hq1, hq2, beq_iff_eq, List.cons.injEq, Option.some.injEq,
                  reduceCtorEq, and_false, and_true, ↓reduceIte] <;>
                cases rawArgs.dropLast.any (·.any argGlobChar) <;>
                cases rawArgs.any (·.any argGlobChar) <;>
                by_cases hIsList : cmd = "list" <;>
                simp [hRegex, hIsList, ← hEqList, hsliceCut, hsliceFull,
                  ConstructRel, absCommand, absArgs, hPat, KindRel.globInArguments, KindRel.listArguments]
            · have hnotStar : rawArgs.getLast? ≠ some ['*'] := by
                intro he; rw [hLast] at he
                have hh := congrArg List.length (Option.some.inj he)
                apply hlen1
                apply UScalar.eq_of_val_eq
                simp only [List.length_cons, List.length_nil, Nat.zero_add] at hh
                scalar_tac
              have hnotQuotes : rawArgs.getLast? ≠ some ['"','"'] := by
                intro he; rw [hLast] at he
                have hh := congrArg List.length (Option.some.inj he)
                apply hlen2
                apply UScalar.eq_of_val_eq
                simp only [List.length_cons, List.length_nil, Nat.zero_add] at hh
                scalar_tac
              simp only [hidxLast, bind_ok, uncurry_apply_pair, elen, hlen1, hlen2, ↓reduceIte,
                eFull, hGlobFull, evFull, alloc.vec.Vec.into_boxed_slice]
              simp only [show (rawArgs.getLast? == some ['*']) = false by simpa using hnotStar,
                show (rawArgs.getLast? == some ['\"','\"']) = false by simpa using hnotQuotes,
                Bool.false_eq_true, ↓reduceIte]
              cases rawArgs.any (·.any argGlobChar) <;> by_cases hIsList : cmd = "list" <;>
                simp [hRegex, hIsList, ← hEqList, hsliceFull, ConstructRel, absCommand, absArgs,
                  hPat, KindRel.globInArguments, KindRel.listArguments]

abbrev commandTokenInst := PairPatternArgs.Insts.Sudo_rsSudoersBasic_parserToken

theorem command_token_refines {A : GlobAbs} {O : Oracles} (hO : P2Oracle A O) :
    TokenRefines commandTokenInst (absCommand A) (SudoersSpec.Syntax.commandToken O)
      (CommandText O.char) where
  max_len := ⟨_, rfl, by
    simp [PairPatternArgs.Insts.Sudo_rsSudoersBasic_parserToken.MAX_LEN,
      SudoersSpec.Syntax.commandToken]⟩
  max_len_le := by simp only [SudoersSpec.Syntax.commandToken]; scalar_tac
  allow_escape := by
    simp [PairPatternArgs.Insts.Sudo_rsSudoersBasic_parserToken.ALLOW_ESCAPE,
      sudo_rs.glob.Pattern.Insts.Sudo_rsSudoersBasic_parserToken.ALLOW_ESCAPE,
      SudoersSpec.Syntax.commandToken]
  accept c := by
    change PairPatternArgs.Insts.Sudo_rsSudoersBasic_parserToken.accept c = _
    simp only [PairPatternArgs.Insts.Sudo_rsSudoersBasic_parserToken.accept,
      simple_command_accept_eq hO, bind_ok, SudoersSpec.Syntax.commandToken]
    have char_eq (x y : Char) : (x == y) = decide (x = y) := rfl
    cases SudoersSpec.Syntax.SimpleCommand.accept O.char c <;>
      by_cases hs : c = ' ' <;> simp [hs, char_eq]
  accept_1st c := simple_command_accept_1st_eq c
  escaped c := simple_command_escaped_eq c
  construct := command_construct_refines hO

private theorem splitWhen_ne_nil (p : Char → Bool) (cs : List Char) :
    SudoersSpec.Syntax.splitWhen p cs ≠ [] := by
  cases cs with
  | nil => simp [SudoersSpec.Syntax.splitWhen]
  | cons c cs =>
    simp only [SudoersSpec.Syntax.splitWhen]
    split <;> try simp
    split <;> simp

theorem commandText_of_head {O : CharOracle} {cs : List Char} {c : Char}
    (hh : cs.head? = some c) (hn : O.isWhitespace c = false) : CommandText O cs := by
  cases cs with
  | nil => simp at hh
  | cons d ds =>
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst d
    unfold CommandText SudoersSpec.Syntax.splitWhitespace
    unfold SudoersSpec.Syntax.splitWhen
    simp only [hn, Bool.false_eq_true, ↓reduceIte]
    rcases hw : SudoersSpec.Syntax.splitWhen O.isWhitespace ds with _ | ⟨w, ws⟩
    · exact (splitWhen_ne_nil O.isWhitespace ds hw).elim
    · simp

/-- A bare command token reached just after successful trailing-whitespace handling. -/
theorem command_parse_refines_at {A : GlobAbs} {O : Oracles} (hO : P2Oracle A O)
    (s : CS) (hS : StreamOK s) (hNext : NoBlankNext (absStream s)) :
    Refines (absCommand A)
      ((sudo_rs.sudoers.basic_parser.Parse.Blanket commandTokenInst).parse s)
      ((SudoersSpec.Syntax.token (SudoersSpec.Syntax.commandToken O)).run (absStream s)) := by
  apply token_refines_at (command_token_refines hO) s hS
  intro cs c s1 hh hfirst _
  have ha := (acceptEscaped_at_noBlankNext hNext hfirst).2
  change SudoersSpec.Syntax.SimpleCommand.accept1st c = true at ha
  have hs := hO.chars.command_start_nonWhitespace c (by simp [ha])
  exact commandText_of_head hh hs

/-- The real `Meta<Command>` instance reached from the command grammar. `NoBlankNext` rules
out starting with an escape, so a successful first-character test establishes a first
non-whitespace word for the fallback constructor. -/
theorem meta_command_parse_refines_at {A : GlobAbs} {O : Oracles} (hO : P2Oracle A O)
    (s : CS) (hS : StreamOK s) (hNext : NoBlankNext (absStream s)) :
    Refines (absMeta (absCommand A))
      ((sudo_rs.sudoers.basic_parser.Parse.Blanket
        (sudo_rs.sudoers.tokens.Meta.Insts.Sudo_rsSudoersBasic_parserToken commandTokenInst)).parse s)
      ((SudoersSpec.Syntax.token
        (SudoersSpec.Syntax.metaToken O.char (SudoersSpec.Syntax.commandToken O))).run (absStream s)) := by
  apply token_refines_at (meta_token_refines hO.chars.unicode (command_token_refines hO)) s hS
  intro cs c s1 hh hfirst _
  have ha := (acceptEscaped_at_noBlankNext hNext hfirst).2
  exact commandText_of_head hh (hO.chars.command_start_nonWhitespace c ha)

end SudoRsProofs.Parser
