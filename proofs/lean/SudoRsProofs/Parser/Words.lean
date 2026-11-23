import SudoRsProofs.Parser.Abs

/-!
# Parser refinement: whitespace-delimited word ranges

The two class scans stop at the end of a maximal run. A word scan consumes at least one character,
so the cursor both supplies a termination measure and pays for the corresponding `Vec::push`.
-/

open Aeneas Aeneas.Std Result

namespace SudoRsProofs.Parser

open SudoersSpec.Syntax (CharOracle splitWhen splitWhitespace)

private theorem word_cursor_add_one (i : Usize) (hi : i.val < Usize.max) :
    ∃ j : Usize, i + 1#usize = ok j ∧ j.val = i.val + 1 := by
  have h : i.val + 1 ≤ Usize.max := by omega
  obtain ⟨j, hj, hjv⟩ := exists_eq_ok_of_spec
    (Usize.add_spec (x := i) (y := 1#usize) (by simpa using h))
  exact ⟨j, hj, by simpa using hjv⟩

private theorem skip_word_class_loop_false (text : Slice Char) (pos : Usize) (ws : Bool) :
    sudo_rs.sudoers.tokens.skip_word_class_loop text pos ws false = ok pos := by
  rw [sudo_rs.sudoers.tokens.skip_word_class_loop]
  simp

private theorem skip_word_class_loop_eq {O : CharOracle} (hO : UnicodeOracle O)
    (text : Slice Char) (ws : Bool) (p : Char → Bool)
    (hp : ∀ c, p c = true ↔ O.isWhitespace c = ws) (pos : Usize) :
    ∃ stop : Usize, sudo_rs.sudoers.tokens.skip_word_class_loop text pos ws true = ok stop ∧
      stop.val = pos.val + ((text.val.drop pos.val).takeWhile p).length := by
  rw [sudo_rs.sudoers.tokens.skip_word_class_loop]
  simp only [↓reduceIte]
  split
  · rename_i hlt
    have hi : pos.val < text.val.length := by scalar_tac
    have hd := List.drop_eq_getElem_cons hi
    rw [eq_ok_of_spec (Slice.index_usize_spec text pos hi), bind_ok, hO.is_whitespace, bind_ok]
    by_cases hc : O.isWhitespace text.val[pos.val] = ws
    · obtain ⟨next, hadd, hnext⟩ := word_cursor_add_one pos (by have := text.property; omega)
      obtain ⟨stop, hr, hv⟩ := skip_word_class_loop_eq hO text ws p hp next
      refine ⟨stop, by simpa only [hc, ↓reduceIte, hadd, bind_ok] using hr, ?_⟩
      rw [hd, List.takeWhile_cons_of_pos ((hp _).2 hc), List.length_cons]
      rw [hnext] at hv
      omega
    · have hn : ¬ p text.val[pos.val] := fun h => hc ((hp _).1 h)
      refine ⟨pos, ?_, ?_⟩
      · simp only [hc, ↓reduceIte, skip_word_class_loop_false]
      · rw [hd, List.takeWhile_cons_of_neg hn]
        simp
  · have hge : text.val.length ≤ pos.val := by scalar_tac
    refine ⟨pos, rfl, ?_⟩
    simp [List.drop_eq_nil_of_le hge]
termination_by text.val.length - pos.val
decreasing_by omega

private theorem skip_word_class_eq {O : CharOracle} (hO : UnicodeOracle O)
    (text : Slice Char) (pos : Usize) (ws : Bool) (p : Char → Bool)
    (hp : ∀ c, p c = true ↔ O.isWhitespace c = ws) (hi : pos.val ≤ text.val.length) :
    ∃ stop : Usize, sudo_rs.sudoers.tokens.skip_word_class text pos ws = ok stop ∧
      pos.val ≤ stop.val ∧ stop.val ≤ text.val.length ∧
      (text.val.drop pos.val).take (stop.val - pos.val) = (text.val.drop pos.val).takeWhile p ∧
      text.val.drop stop.val = (text.val.drop pos.val).dropWhile p := by
  obtain ⟨stop, hr, hv⟩ := skip_word_class_loop_eq hO text ws p hp pos
  have hparts := List.takeWhile_append_dropWhile (p := p) (l := text.val.drop pos.val)
  have hlen := congrArg List.length hparts
  simp only [List.length_append, List.length_drop] at hlen
  have hspan : stop.val - pos.val = ((text.val.drop pos.val).takeWhile p).length := by omega
  refine ⟨stop, hr, by omega, by omega, ?_, ?_⟩
  · rw [hspan]
    exact (congrArg (List.take ((text.val.drop pos.val).takeWhile p).length) hparts).symm.trans
      List.take_left
  · rw [hv, ← List.drop_drop]
    exact (congrArg (List.drop ((text.val.drop pos.val).takeWhile p).length) hparts).symm.trans
      List.drop_left

private theorem dropWhile_head {p : Char → Bool} (l : List Char) {c : Char}
    (hc : (l.dropWhile p).head? = some c) : p c = false := by
  simpa only [hc] using List.head?_dropWhile_not p l

/-- The first piece of `splitWhen` is the maximal run before the next separator. -/
private theorem splitWhen_runs (p : Char → Bool) (l : List Char) :
    splitWhen p l = l.takeWhile (fun c => !p c) ::
      (match l.dropWhile (fun c => !p c) with
       | [] => []
       | _ :: cs => splitWhen p cs) := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    cases hc : p c with
    | true => simp [splitWhen, hc]
    | false => simp [splitWhen, hc, ih]

private theorem splitWhitespace_dropWhile (O : CharOracle) (l : List Char) :
    splitWhitespace O (l.dropWhile O.isWhitespace) = splitWhitespace O l := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    by_cases hc : O.isWhitespace c = true
    · rw [List.dropWhile_cons_of_pos hc, ih]
      simp [splitWhitespace, splitWhen, hc]
    · rw [List.dropWhile_cons_of_neg hc]

private theorem splitWhitespace_word (O : CharOracle) (l : List Char)
    (hw : l.takeWhile (fun c => !O.isWhitespace c) ≠ []) :
    splitWhitespace O l = l.takeWhile (fun c => !O.isWhitespace c) ::
      splitWhitespace O (l.dropWhile (fun c => !O.isWhitespace c)) := by
  have he := List.isEmpty_eq_false_iff.mpr hw
  have hf : (!((l.takeWhile (fun c => !O.isWhitespace c)).isEmpty)) = true := by simp [he]
  unfold splitWhitespace
  rw [splitWhen_runs O.isWhitespace l]
  simp only [List.filter_cons, hf, ↓reduceIte]
  cases hr : l.dropWhile (fun c => !O.isWhitespace c) with
  | nil => simp [splitWhen]
  | cons c cs =>
    have hn : (!O.isWhitespace c) = false :=
      dropWhile_head (p := fun d => !O.isWhitespace d) l (by simp [hr])
    have hc : O.isWhitespace c = true := by cases h : O.isWhitespace c <;> simp [h] at hn ⊢
    simp [splitWhen, hc]

private theorem split_words_loop_eq {O : CharOracle} (hO : UnicodeOracle O)
    (text : Slice Char) (words : alloc.vec.Vec (Usize × Usize)) (start : Usize)
    (hbound : start.val ≤ text.val.length) (hbudget : words.val.length ≤ start.val)
    (hstart : ∀ c, (text.val.drop start.val).head? = some c → O.isWhitespace c = false)
    (hvalid : ∀ r ∈ words.val, r.1.val < r.2.val ∧ r.2.val ≤ text.val.length) :
    ∃ ranges : alloc.vec.Vec (Usize × Usize),
      sudo_rs.sudoers.tokens.split_words_loop text words start = ok ranges ∧
      (∀ r ∈ ranges.val, r.1.val < r.2.val ∧ r.2.val ≤ text.val.length) ∧
      ranges.val.map (fun (a, b) => (text.val.drop a.val).take (b.val - a.val)) =
        words.val.map (fun (a, b) => (text.val.drop a.val).take (b.val - a.val)) ++
          splitWhitespace O (text.val.drop start.val) ∧
      ranges.val.length ≤ words.val.length + (text.val.length - start.val) := by
  unfold sudo_rs.sudoers.tokens.split_words_loop
  dsimp only
  split
  · rename_i hlt
    have hi : start.val < text.val.length := by scalar_tac
    have hd := List.drop_eq_getElem_cons hi
    have hc : O.isWhitespace text.val[start.val] = false :=
      hstart _ (by simp only [hd, List.head?_cons])
    have hword : (text.val.drop start.val).takeWhile (fun c => !O.isWhitespace c) ≠ [] := by
      rw [hd, List.takeWhile_cons_of_pos (by simp [hc])]
      simp
    obtain ⟨stop, hstop, _, hstopBound, htake, hstopDrop⟩ :=
      skip_word_class_eq hO text start false (fun c => !O.isWhitespace c)
        (by intro c; cases O.isWhitespace c <;> decide) hbound
    have hforward : start.val < stop.val := by
      by_contra hn
      have hz : stop.val - start.val = 0 := by omega
      exact hword (by simpa only [hz, List.take_zero] using htake.symm)
    have hcap : words.val.length < Usize.max := by have := text.property; omega
    obtain ⟨words1, hpush, hwords1⟩ :=
      exists_eq_ok_of_spec (alloc.vec.Vec.push_spec words (start, stop) hcap)
    have hwordsLen : words1.val.length = words.val.length + 1 := by simp [hwords1]
    have hvalid1 (r : Usize × Usize) (hr : r ∈ words1.val) :
        r.1.val < r.2.val ∧ r.2.val ≤ text.val.length := by
      rw [hwords1, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact hvalid r hr
      · exact ⟨hforward, hstopBound⟩
    obtain ⟨next, hnext, hnextLower, hnextBound, _, hnextDrop⟩ :=
      skip_word_class_eq hO text stop true O.isWhitespace (by intro c; rfl) hstopBound
    have hnextHead (c : Char) (hr : (text.val.drop next.val).head? = some c) :
        O.isWhitespace c = false :=
      dropWhile_head (text.val.drop stop.val) (hnextDrop ▸ hr)
    obtain ⟨ranges, hr, hvalid', hmap, hlen⟩ :=
      split_words_loop_eq hO text words1 next hnextBound (by omega) hnextHead hvalid1
    refine ⟨ranges, ?_, hvalid', ?_, by omega⟩
    · simpa only [hstop, bind_ok, hpush, hnext] using hr
    · rw [hmap, hwords1, List.map_append, List.append_assoc]
      simp only [List.map_cons, List.map_nil, List.singleton_append]
      rw [htake, hnextDrop, splitWhitespace_dropWhile O (text.val.drop stop.val), hstopDrop,
        splitWhitespace_word O (text.val.drop start.val) hword]
  · have hge : text.val.length ≤ start.val := by scalar_tac
    refine ⟨words, rfl, hvalid, ?_, by omega⟩
    simp [List.drop_eq_nil_of_le hge, splitWhitespace, splitWhen]
termination_by text.val.length - start.val
decreasing_by omega

/-- `split_words` returns one nonempty, in-bounds range per specification word, in order. -/
theorem split_words_refines {O : CharOracle} (hO : UnicodeOracle O) (text : Slice Char) :
    ∃ ranges : alloc.vec.Vec (Usize × Usize),
      sudo_rs.sudoers.tokens.split_words text = ok ranges ∧
      (∀ r ∈ ranges.val, r.1.val < r.2.val ∧ r.2.val ≤ text.val.length) ∧
      ranges.val.map (fun (a, b) => (text.val.drop a.val).take (b.val - a.val)) =
        splitWhitespace O text.val ∧
      ranges.val.length ≤ text.val.length := by
  obtain ⟨start, hs, _, hbound, _, hd⟩ :=
    skip_word_class_eq hO text 0#usize true O.isWhitespace (by intro c; rfl) (by simp)
  have hd' : text.val.drop start.val = text.val.dropWhile O.isWhitespace := by simpa using hd
  obtain ⟨ranges, hr, hv, hm, hl⟩ :=
    split_words_loop_eq hO text (alloc.vec.Vec.new _) start hbound (by simp)
      (fun _ hc => dropWhile_head text.val (hd' ▸ hc)) (by simp)
  refine ⟨ranges, ?_, hv, ?_, ?_⟩
  · simpa only [sudo_rs.sudoers.tokens.split_words, hs, bind_ok] using hr
  · simpa [hd', splitWhitespace_dropWhile] using hm
  · have hlen : ranges.val.length ≤ text.val.length - start.val := by simpa using hl
    omega

private theorem word_text_loop_eq (text : Slice Char) (stop : Usize)
    (hstop : stop.val ≤ text.val.length) (i : Usize) (word : String) :
    sudo_rs.sudoers.tokens.word_text_loop text i stop word =
      ok (String.ofList (word.toList ++ (text.val.take stop.val).drop i.val)) := by
  unfold sudo_rs.sudoers.tokens.word_text_loop
  split
  · rename_i hlt
    have hi : i.val < stop.val := by scalar_tac
    have hi' : i.val < text.val.length := by omega
    obtain ⟨next, hadd, hnext⟩ := word_cursor_add_one i (by have := text.property; omega)
    rw [eq_ok_of_spec (Slice.index_usize_spec text i hi')]
    simp only [bind_ok, alloc.string.String.push, hadd]
    rw [word_text_loop_eq text stop hstop next]
    have hd : (text.val.take stop.val).drop i.val =
        text.val[i.val] :: (text.val.take stop.val).drop (i.val + 1) := by
      rw [List.drop_eq_getElem_cons (by simp [List.length_take_of_le hstop]; omega)]
      simp
    simp [hd, hnext, String.toList_push]
  · have hge : stop.val ≤ i.val := by scalar_tac
    have hd : (text.val.take stop.val).drop i.val = [] :=
      List.drop_eq_nil_of_le (by rw [List.length_take_of_le hstop]; exact hge)
    simp [hd, String.ofList_toList]
termination_by stop.val - i.val
decreasing_by omega

/-- Materialize the characters in a range as a string. An empty range yields `""`. -/
theorem word_text_eq (text : Slice Char) (start stop : Usize)
    (hstop : stop.val ≤ text.val.length) :
    sudo_rs.sudoers.tokens.word_text text start stop =
      ok (String.ofList ((text.val.drop start.val).take (stop.val - start.val))) := by
  simp only [sudo_rs.sudoers.tokens.word_text, alloc.string.String.new, bind_ok,
    word_text_loop_eq text stop hstop, String.toList_empty, List.nil_append, List.drop_take]

end SudoRsProofs.Parser
