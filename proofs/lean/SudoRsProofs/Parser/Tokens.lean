import SudoRsProofs.Parser.Abs

/-!
# Parser refinement: the core tokens (`src/sudoers/tokens.rs`)

The extracted `Hostname`, `AliasName` and `Meta<T>` against `SudoersSpec/Syntax/Tokens.lean`.

* **Character classes.** `aliasName_accept_1st_eq`, `aliasName_accept_eq`, `hostname_accept_eq`:
  the ASCII models of `SudoRs/FunsExternal.lean` are the reference classes.
* **Helpers of `Meta::construct`.** `trimmed_len` is the length of `trimEnd`, `is_all`,
  `is_alias_name` and `string_of` decide resp. build the trimmed prefix
  (`trimmed_len_eq`, `is_all_eq`, `is_alias_name_eq`, `string_of_eq`).
* **`resembles_ipv4`.** The Rust loop scans left to right; the reference splits the reversed text
  (`rsplitn 5 '.'`). Both are proved equal to `IPv4Shape`: the text split at `'.'`
  (`List.splitOn`) has at most four pieces, each one non-empty, at most 3 bytes long and numeric.
  The loop is first proved equal to the pure scanner `scan`, `scan` to the shape
  (`scan_iff`); `rsplitn` is related to `splitOn` by `splitn_eq`, `splitn_length` and
  `splitOn_reverse` (`looksLikeIPv4_iff`).
* **Instances.** `hostname_token_refines`, `meta_token_refines`: `TokenRefines` for `Hostname`
  and for `Meta<T>` given `TokenRefines` for `T`.
-/

open Aeneas Aeneas.Std Result

namespace SudoRsProofs.Parser

open SudoersSpec.Syntax (CharOracle trimEnd startsWithPred utf8Len)

/-! ## Generic helpers -/

private theorem charBeq (c d : Char) : (c == d) = decide (c = d) := rfl

private theorem index_eq {α : Type} (v : Slice α) (i : Usize) (h : i.val < v.val.length) :
    Slice.index_usize v i = ok v.val[i.val] :=
  eq_ok_of_spec (Slice.index_usize_spec v i h)

private theorem add_eq (x y : Usize) (h : x.val + y.val ≤ Usize.max) :
    ∃ z : Usize, x + y = ok z ∧ z.val = x.val + y.val :=
  exists_eq_ok_of_spec (UScalar.add_spec (by scalar_tac))

private theorem add_one_eq (x : Usize) (h : x.val < Usize.max) :
    ∃ z : Usize, x + 1#usize = ok z ∧ z.val = x.val + 1 := by
  obtain ⟨z, hz, hzv⟩ := add_eq x 1#usize (by simp; omega)
  exact ⟨z, hz, by simpa using hzv⟩

private theorem take_add_one_eq {α : Type} (l : List α) (i : Nat) (h : i < l.length) :
    l.take (i + 1) = l.take i ++ [l[i]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h]; rfl

/-! ## Character classes -/

theorem aliasName_accept_1st_eq (c : Char) :
    sudo_rs.sudoers.tokens.AliasName.Insts.Sudo_rsSudoersBasic_parserToken.accept_1st c =
      ok (SudoersSpec.Syntax.AliasName.accept1st c) := by
  simp [sudo_rs.sudoers.tokens.AliasName.Insts.Sudo_rsSudoersBasic_parserToken.accept_1st,
    core.char.methods.Char.is_ascii_uppercase, SudoersSpec.Syntax.AliasName.accept1st,
    SudoersSpec.Syntax.isAsciiUppercase, Char.isUpper, Char.le_def]

theorem aliasName_accept_eq (c : Char) :
    sudo_rs.sudoers.tokens.AliasName.Insts.Sudo_rsSudoersBasic_parserToken.accept c =
      ok (SudoersSpec.Syntax.AliasName.accept c) := by
  simp only [sudo_rs.sudoers.tokens.AliasName.Insts.Sudo_rsSudoersBasic_parserToken.accept,
    aliasName_accept_1st_eq, bind_ok, core.char.methods.Char.is_ascii_digit,
    SudoersSpec.Syntax.AliasName.accept, SudoersSpec.Syntax.AliasName.accept1st,
    SudoersSpec.Syntax.isAsciiUppercase, SudoersSpec.Syntax.isAsciiDigit, Char.isDigit,
    Char.le_def, charBeq, ge_iff_le, ← Bool.decide_and, ← Bool.decide_or, decide_eq_true_eq]
  split_ifs <;> congr 1 <;> simp only [decide_eq_decide, eq_comm (a := true), decide_eq_true_eq] <;>
    tauto

theorem hostname_accept_eq (c : Char) :
    sudo_rs.sudoers.tokens.Hostname.Insts.Sudo_rsSudoersBasic_parserToken.accept c =
      ok (SudoersSpec.Syntax.Hostname.accept c) := by
  simp only [sudo_rs.sudoers.tokens.Hostname.Insts.Sudo_rsSudoersBasic_parserToken.accept,
    core.char.methods.Char.is_ascii_alphanumeric, bind_ok, SudoersSpec.Syntax.Hostname.accept,
    SudoersSpec.Syntax.isAsciiAlphanumeric, SudoersSpec.Syntax.isAsciiDigit,
    SudoersSpec.Syntax.isAsciiUppercase, SudoersSpec.Syntax.isAsciiLowercase, Char.isAlphanum,
    Char.isAlpha, Char.isUpper, Char.isLower, Char.isDigit, Char.le_def, charBeq,
    ← Bool.decide_and, ← Bool.decide_or, decide_eq_true_eq]
  split_ifs <;> congr 1 <;> simp only [decide_eq_decide, eq_comm (a := true), decide_eq_true_eq] <;>
    tauto

private theorem utf8Size_le_four (c : Char) : c.utf8Size ≤ 4 := by
  simp only [Char.utf8Size]
  split_ifs <;> omega

theorem len_utf8_eq (c : Char) :
    ∃ n : Usize, core.char.methods.Char.len_utf8 c = ok n ∧ n.val = c.utf8Size := by
  refine ⟨_, rfl, ?_⟩
  simp only [Char.utf8Size, UInt32.lt_iff_toNat_lt, UInt32.le_iff_toNat_le]
  split_ifs <;> simp_all <;> omega

/-! ## `string_of` -/

theorem string_of_loop_eq (text : Slice Char) (len : Usize) (h : len.val ≤ text.val.length)
    (s : String) (i : Usize) (hi : i.val ≤ len.val) :
    sudo_rs.sudoers.tokens.string_of_loop text len s i =
      ok (String.ofList (s.toList ++ (text.val.take len.val).drop i.val)) := by
  unfold sudo_rs.sudoers.tokens.string_of_loop
  split
  · rename_i hlt
    have hi' : i.val < text.val.length := by scalar_tac
    obtain ⟨i1, hi1, hi1v⟩ := add_one_eq i (by scalar_tac)
    rw [index_eq text i hi']
    simp only [bind_ok, alloc.string.String.push, hi1]
    rw [string_of_loop_eq text len h _ i1 (by scalar_tac)]
    have hd : (text.val.take len.val).drop i.val =
        text.val[i.val] :: (text.val.take len.val).drop (i.val + 1) := by
      rw [List.drop_eq_getElem_cons (by simp; scalar_tac)]
      simp
    simp [hd, hi1v, String.toList_push]
  · have : len.val ≤ i.val := by scalar_tac
    simp [List.drop_eq_nil_of_le (by simp; omega : (text.val.take len.val).length ≤ i.val),
      String.ofList_toList]
termination_by len.val - i.val
decreasing_by all_goals scalar_tac

theorem string_of_eq (text : Slice Char) (len : Usize) (h : len.val ≤ text.val.length) :
    sudo_rs.sudoers.tokens.string_of text len = ok (String.ofList (text.val.take len.val)) := by
  simp [sudo_rs.sudoers.tokens.string_of, alloc.string.String.new,
    string_of_loop_eq text len h _ 0#usize (by simp)]

/-! ## `is_all` -/

theorem is_all_eq (text : Slice Char) (len : Usize) (h : len.val ≤ text.val.length) :
    sudo_rs.sudoers.tokens.is_all text len = ok (text.val.take len.val == "ALL".toList) := by
  have hALL : "ALL".toList = ['A', 'L', 'L'] := rfl
  unfold sudo_rs.sudoers.tokens.is_all
  split
  · rename_i h3
    have h3' : len.val = 3 := by scalar_tac
    obtain ⟨a, b, c, rest, hv⟩ : ∃ a b c rest, text.val = a :: b :: c :: rest := by
      match hv : text.val with
      | a :: b :: c :: rest => exact ⟨a, b, c, rest, rfl⟩
      | [] | [_] | [_, _] => simp_all
    simp [Slice.index_usize, hv, h3', hALL]
    split_ifs <;> simp_all [charBeq]
  · rename_i h3
    have h3' : len.val ≠ 3 := by scalar_tac
    have : (text.val.take len.val).length ≠ ("ALL".toList).length := by simp [hALL]; omega
    simp only [ok.injEq]
    symm
    simpa using fun e => this (congrArg List.length e)

/-! ## `is_alias_name` -/

theorem is_alias_name_loop_eq (text : Slice Char) (len : Usize) (h : len.val ≤ text.val.length)
    (b : Bool) (i : Usize) :
    sudo_rs.sudoers.tokens.is_alias_name_loop text len b i =
      ok (b && ((text.val.take len.val).drop i.val).all SudoersSpec.Syntax.AliasName.accept) := by
  unfold sudo_rs.sudoers.tokens.is_alias_name_loop
  split
  · rename_i hb
    split
    · rename_i hlt
      have hi' : i.val < text.val.length := by scalar_tac
      obtain ⟨i1, hi1, hi1v⟩ := add_one_eq i (by scalar_tac)
      rw [index_eq text i hi']
      simp only [bind_ok, aliasName_accept_eq, hi1]
      rw [is_alias_name_loop_eq text len h _ i1]
      have hd : (text.val.take len.val).drop i.val =
          text.val[i.val] :: (text.val.take len.val).drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons (by simp; scalar_tac)]
        simp
      simp [hd, hi1v, hb]
    · have : len.val ≤ i.val := by scalar_tac
      simp [List.drop_eq_nil_of_le (by simp; omega : (text.val.take len.val).length ≤ i.val)]
  · simp_all
termination_by len.val - i.val
decreasing_by all_goals scalar_tac

theorem startsWithPred_take (l : List Char) (n : Nat) (f : Char → Bool) (hn : 0 < n)
    (hl : 0 < l.length) : startsWithPred (l.take n) f = f l[0] := by
  cases l with
  | nil => simp at hl
  | cons a t =>
    cases n with
    | zero => omega
    | succ n => simp [startsWithPred]

theorem is_alias_name_eq (text : Slice Char) (len : Usize) (h : len.val ≤ text.val.length) :
    sudo_rs.sudoers.tokens.is_alias_name text len =
      ok (startsWithPred (text.val.take len.val) SudoersSpec.Syntax.AliasName.accept1st &&
        ((text.val.take len.val).drop 1).all SudoersSpec.Syntax.AliasName.accept) := by
  unfold sudo_rs.sudoers.tokens.is_alias_name
  split
  · rename_i hpos
    have h0 : 0 < len.val := by scalar_tac
    rw [index_eq text 0#usize (by simp; omega)]
    simp only [bind_ok, aliasName_accept_1st_eq, is_alias_name_loop_eq text len h]
    rw [startsWithPred_take _ _ _ h0 (by omega)]
    simp
  · have h0 : len.val = 0 := by scalar_tac
    simp [is_alias_name_loop_eq text len h, h0, startsWithPred]

/-! ## `trimmed_len` -/

theorem trimEnd_append_singleton (O : CharOracle) (l : List Char) (c : Char) :
    trimEnd O (l ++ [c]) = if O.isWhitespace c then trimEnd O l else l ++ [c] := by
  unfold trimEnd
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, List.dropWhile_cons]
  split <;> simp

theorem trimmed_len_loop_eq {O : CharOracle} (hO : UnicodeOracle O) (text : Slice Char)
    (len i : Usize) (hli : len.val ≤ i.val) (hi : i.val ≤ text.val.length)
    (hinv : text.val.take len.val = trimEnd O (text.val.take i.val)) :
    ∃ n : Usize, sudo_rs.sudoers.tokens.trimmed_len_loop text len i = ok n ∧
      n.val ≤ text.val.length ∧ text.val.take n.val = trimEnd O text.val := by
  unfold sudo_rs.sudoers.tokens.trimmed_len_loop
  dsimp only
  split
  · rename_i hlt
    have hi' : i.val < text.val.length := by scalar_tac
    obtain ⟨i2, hi2, hi2v⟩ := add_one_eq i (by scalar_tac)
    have htake : text.val.take i2.val = text.val.take i.val ++ [text.val[i.val]] := by
      rw [hi2v]; exact take_add_one_eq _ _ hi'
    rw [index_eq text i hi']
    simp only [bind_ok, hO.is_whitespace]
    by_cases hw : O.isWhitespace text.val[i.val] = true
    · simp only [hw, ↓reduceIte, bind_ok, hi2]
      exact trimmed_len_loop_eq hO text len i2 (by omega) (by omega)
        (by rw [htake, trimEnd_append_singleton]; simp only [hw, ↓reduceIte]; exact hinv)
    · simp only [hw, Bool.false_eq_true, ↓reduceIte, bind_ok, hi2]
      exact trimmed_len_loop_eq hO text i2 i2 (Nat.le_refl _) (by omega)
        (by rw [htake, trimEnd_append_singleton]; simp only [hw, Bool.false_eq_true, ↓reduceIte])
  · have hge : text.val.length ≤ i.val := by scalar_tac
    refine ⟨len, rfl, by omega, ?_⟩
    rw [hinv, List.take_of_length_le hge]
termination_by text.val.length - i.val
decreasing_by all_goals scalar_tac

theorem trimmed_len_eq {O : CharOracle} (hO : UnicodeOracle O) (text : Slice Char) :
    ∃ n : Usize, sudo_rs.sudoers.tokens.trimmed_len text = ok n ∧ n.val ≤ text.val.length ∧
      text.val.take n.val = SudoersSpec.Syntax.trimEnd O text.val :=
  trimmed_len_loop_eq hO text 0#usize 0#usize (by simp) (by simp) (by simp [trimEnd])

/-! ## `resembles_ipv4`: the common characterisation -/

theorem utf8Len_nil : utf8Len [] = 0 := rfl

theorem utf8Len_cons (c : Char) (l : List Char) : utf8Len (c :: l) = c.utf8Size + utf8Len l := by
  simp [utf8Len]

theorem utf8Len_append (a b : List Char) : utf8Len (a ++ b) = utf8Len a + utf8Len b := by
  simp [utf8Len]

theorem utf8Len_eq_zero {l : List Char} : utf8Len l = 0 ↔ l = [] := by
  cases l with
  | nil => simp [utf8Len_nil]
  | cons c t => simp only [utf8Len_cons, reduceCtorEq, iff_false]; have := c.utf8Size_pos; omega

/-- A piece of a text that resembles an IPv4 address: non-empty, at most 3 bytes, numeric. -/
def IPv4Piece (O : CharOracle) (p : List Char) : Prop :=
  p ≠ [] ∧ utf8Len p ≤ 3 ∧ ∀ x ∈ p, O.isNumeric x = true

/-- The text split at `'.'` has at most four pieces, each an `IPv4Piece`. -/
def IPv4Shape (O : CharOracle) (text : List Char) : Prop :=
  (text.splitOn '.').length ≤ 4 ∧ ∀ p ∈ text.splitOn '.', IPv4Piece O p

/-- The loop of `resembles_ipv4` on lists: `parts` is the number of the current piece, `pl` the
number of its bytes read so far; the result is the final test `ok && part_len != 0`. -/
def scan (O : CharOracle) : Nat → Nat → List Char → Bool
  | _, pl, [] => decide (pl ≠ 0)
  | parts, pl, c :: cs =>
    if c = '.' then
      if pl ≠ 0 ∧ parts < 4 then scan O (parts + 1) 0 cs else false
    else if pl + c.utf8Size ≤ 3 ∧ O.isNumeric c = true then scan O parts (pl + c.utf8Size) cs
    else false

theorem scan_iff (O : CharOracle) (cs : List Char) : ∀ (cur : List Char) (parts : Nat),
    parts ≤ 4 → utf8Len cur ≤ 3 → (∀ x ∈ cur, O.isNumeric x = true) →
    (scan O parts (utf8Len cur) cs = true ↔
      parts + (cs.splitOn '.').length ≤ 5 ∧
        ∀ p ∈ (cs.splitOn '.').modifyHead (cur ++ ·), IPv4Piece O p) := by
  induction cs with
  | nil =>
    intro cur parts hp hl hn
    simp only [scan, List.splitOn_nil, List.modifyHead_cons, List.append_nil,
      List.length_singleton, List.mem_singleton, forall_eq, IPv4Piece, decide_eq_true_eq, ne_eq,
      utf8Len_eq_zero]
    exact ⟨fun h => ⟨by omega, h, hl, hn⟩, fun h => h.2.1⟩
  | cons c cs ih =>
    intro cur parts hp hl hn
    obtain ⟨p0, rest, hps⟩ := List.exists_cons_of_ne_nil (List.splitOn_ne_nil '.' cs)
    rw [List.splitOn_cons_eq_ite_modifyHead, hps]
    by_cases hc : c = '.'
    · subst hc
      simp only [scan, ↓reduceIte, beq_self_eq_true, List.modifyHead_cons, List.append_nil,
        List.length_cons, List.forall_mem_cons]
      by_cases hz : utf8Len cur = 0
      · have : cur = [] := utf8Len_eq_zero.1 hz
        subst this
        simp [IPv4Piece, utf8Len_nil]
      · by_cases hq : parts < 4
        · have := ih [] (parts + 1) (by omega) (by simp [utf8Len_nil]) (by simp)
          rw [hps] at this
          simp only [utf8Len_nil, List.modifyHead_cons, List.nil_append, List.length_cons,
            List.forall_mem_cons] at this
          simp only [hz, hq, ne_eq, not_false_eq_true, and_self, ↓reduceIte, this]
          have hcur : IPv4Piece O cur := ⟨fun e => hz (by simp [e, utf8Len_nil]), hl, hn⟩
          constructor
          · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, hcur, h2, h3⟩
          · rintro ⟨h1, _, h2, h3⟩; exact ⟨by omega, h2, h3⟩
        · simp only [hq, and_false, ↓reduceIte, Bool.false_eq_true, false_iff, not_and]
          intro h; omega
    · have hc' : (c == '.') = false := by simpa using hc
      have hlc : utf8Len (cur ++ [c]) = utf8Len cur + c.utf8Size := by
        simp [utf8Len_append, utf8Len_cons, utf8Len_nil]
      simp only [scan, hc, ↓reduceIte, hc', Bool.false_eq_true, List.modifyHead_cons,
        List.length_cons]
      by_cases hcond : utf8Len cur + c.utf8Size ≤ 3 ∧ O.isNumeric c = true
      · have := ih (cur ++ [c]) parts hp (by omega)
          (by intro x hx; simp only [List.mem_append, List.mem_singleton] at hx
              rcases hx with hx | rfl
              · exact hn x hx
              · exact hcond.2)
        rw [hps, hlc] at this
        simp only [List.modifyHead_cons, List.append_assoc, List.singleton_append,
          List.length_cons] at this
        simp only [hcond, and_self, ↓reduceIte, this]
      · simp only [hcond, ↓reduceIte, Bool.false_eq_true, false_iff, not_and,
          List.forall_mem_cons]
        intro _ hpiece _
        apply hcond
        refine ⟨?_, hpiece.2.2 c (by simp)⟩
        have := hpiece.2.1
        simp only [utf8Len_append, utf8Len_cons] at this
        omega

theorem scan_shape (O : CharOracle) (text : List Char) :
    scan O 1 0 text = true ↔ IPv4Shape O text := by
  have h := scan_iff O text [] 1 (by omega) (by simp [utf8Len_nil]) (by simp)
  have hid : (text.splitOn '.').modifyHead ([] ++ ·) = text.splitOn '.' := by
    cases text.splitOn '.' <;> simp
  rw [utf8Len_nil, hid] at h
  rw [h, IPv4Shape]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩

/-! ## `rsplitn` against `splitOn` -/

theorem splitOn_of_span_nil {sep : Char} {s a : List Char}
    (h : s.span (· != sep) = (a, [])) : a = s ∧ s.splitOn sep = [s] := by
  rw [List.span_eq_takeWhile_dropWhile, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hs : s = a := by
    rw [← List.takeWhile_append_dropWhile (p := (· != sep)) (l := s), h1, h2, List.append_nil]
  refine ⟨hs.symm, List.splitOn_eq_singleton_of_beq_eq_false ?_⟩
  intro x hx
  have := List.all_takeWhile (p := (· != sep)) (l := s)
  rw [h1, ← hs, List.all_eq_true] at this
  simpa using this x hx

theorem splitOn_of_span_cons {sep : Char} {s a rest : List Char} {x : Char}
    (h : s.span (· != sep) = (a, x :: rest)) : s.splitOn sep = a :: rest.splitOn sep := by
  rw [List.span_eq_takeWhile_dropWhile, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hs : s = a ++ x :: rest := by
    rw [← List.takeWhile_append_dropWhile (p := (· != sep)) (l := s), h1, h2]
  have hw : s.dropWhile (· != sep) ≠ [] := by simp [h2]
  have hx := List.head_dropWhile_not (fun y => y != sep) hw
  simp only [h2, List.head_cons, bne_eq_false_iff_eq] at hx
  have ha : ∀ y ∈ a, (y == sep) = false := by
    intro y hy
    have := List.all_takeWhile (p := (· != sep)) (l := s)
    rw [h1, List.all_eq_true] at this
    simpa using this y hy
  rw [hs]
  exact List.splitOn_append_cons_of_forall_mem_beq_eq_false ha x (by simp [hx]) rest

theorem splitn_eq (sep : Char) : ∀ (n : Nat) (s : List Char),
    (s.splitOn sep).length ≤ n + 1 → SudoersSpec.Syntax.splitn (n + 1) sep s = s.splitOn sep
  | 0, s, h => by
    obtain ⟨p, hp⟩ : ∃ p, s.splitOn sep = [p] := by
      match hs : s.splitOn sep, List.splitOn_ne_nil sep s with
      | [p], _ => exact ⟨p, rfl⟩
      | [], hne => exact absurd rfl hne
      | _ :: _ :: _, _ => simp [hs] at h
    have hsp : s = p := by
      have := List.intercalate_splitOn (xs := s) sep
      rwa [hp, List.intercalate_singleton, eq_comm] at this
    rw [hsp] at hp ⊢
    simp [SudoersSpec.Syntax.splitn, hp]
  | n + 1, s, h => by
    rw [SudoersSpec.Syntax.splitn]
    split
    · rename_i heq
      obtain ⟨rfl, hs⟩ := splitOn_of_span_nil heq
      rw [hs]
    · rename_i heq
      rw [splitOn_of_span_cons heq] at h ⊢
      rw [splitn_eq sep n _ (by simp at h; omega)]

theorem splitn_length (sep : Char) : ∀ (n : Nat) (s : List Char),
    (SudoersSpec.Syntax.splitn (n + 1) sep s).length = min (n + 1) (s.splitOn sep).length
  | 0, s => by
    have := List.length_pos_iff.2 (List.splitOn_ne_nil sep s)
    simp [SudoersSpec.Syntax.splitn]
    omega
  | n + 1, s => by
    rw [SudoersSpec.Syntax.splitn]
    split
    · rename_i heq
      obtain ⟨rfl, hs⟩ := splitOn_of_span_nil heq
      simp [hs]
    · rename_i heq
      rw [splitOn_of_span_cons heq]
      simp only [List.length_cons, splitn_length sep n]
      omega

theorem not_mem_of_mem_splitOn (sep : Char) (s : List Char) : ∀ l ∈ s.splitOn sep, sep ∉ l := by
  induction s with
  | nil => simp
  | cons c cs ih =>
    obtain ⟨p0, rest, hps⟩ := List.exists_cons_of_ne_nil (List.splitOn_ne_nil sep cs)
    rw [List.splitOn_cons_eq_ite_modifyHead]
    rw [hps] at ih ⊢
    split
    · intro l hl
      simp only [List.mem_cons] at hl
      rcases hl with rfl | hl
      · simp
      · exact ih l (by simp [hl])
    · rename_i hc
      intro l hl
      simp only [List.modifyHead_cons, List.mem_cons] at hl
      rcases hl with rfl | hl
      · simp only [List.mem_cons, not_or]
        exact ⟨fun e => hc (by simp [e]), ih p0 (by simp)⟩
      · exact ih l (by simp [hl])

theorem intercalate_append_singleton (x : Char) (z : List Char) : ∀ L : List (List Char),
    L ≠ [] → [x].intercalate (L ++ [z]) = [x].intercalate L ++ x :: z
  | [], h => absurd rfl h
  | [a], _ => by simp [List.intercalate_cons_cons]
  | a :: b :: t, _ => by
    rw [List.cons_append, List.cons_append, List.intercalate_cons_cons, ← List.cons_append,
      intercalate_append_singleton x z (b :: t) (by simp), List.intercalate_cons_cons]
    simp

theorem reverse_intercalate (x : Char) : ∀ ls : List (List Char),
    ([x].intercalate ls).reverse = [x].intercalate (ls.map List.reverse).reverse
  | [] => rfl
  | [a] => by simp
  | a :: b :: t => by
    have hL : ((b :: t).map List.reverse).reverse ≠ [] := by simp
    have hr : ((a :: b :: t).map List.reverse).reverse =
        ((b :: t).map List.reverse).reverse ++ [a.reverse] := by
      rw [List.map_cons (l := b :: t), List.reverse_cons]
    rw [hr, intercalate_append_singleton x _ _ hL, ← reverse_intercalate x (b :: t),
      List.intercalate_cons_cons]
    simp

theorem splitOn_reverse (sep : Char) (s : List Char) :
    s.reverse.splitOn sep = ((s.splitOn sep).map List.reverse).reverse := by
  conv => lhs; rw [← List.intercalate_splitOn (xs := s) sep]
  rw [reverse_intercalate]
  apply List.splitOn_intercalate
  · intro l hl
    simp only [List.mem_reverse, List.mem_map] at hl
    obtain ⟨l', hl', rfl⟩ := hl
    simpa using not_mem_of_mem_splitOn sep s l' hl'
  · simp

theorem piece_bool_iff (O : CharOracle) (p : List Char) :
    (!p.isEmpty && decide (utf8Len p ≤ 3) && p.all O.isNumeric) = true ↔ IPv4Piece O p := by
  simp [IPv4Piece, and_assoc]

theorem looksLikeIPv4_iff (O : CharOracle) (text : List Char) :
    SudoersSpec.Syntax.Hostname.looksLikeIPv4 O text = true ↔ IPv4Shape O text := by
  have hrev := splitOn_reverse '.' text
  have hlen := splitn_length '.' 4 text.reverse
  simp only [Nat.reduceAdd] at hlen
  rw [hrev] at hlen
  simp only [List.length_reverse, List.length_map] at hlen
  unfold SudoersSpec.Syntax.Hostname.looksLikeIPv4 SudoersSpec.Syntax.rsplitn IPv4Shape
  by_cases h4 : (text.splitOn '.').length ≤ 4
  · have heq := splitn_eq '.' 4 text.reverse (by rw [hrev]; simp; omega)
    simp only [Nat.reduceAdd] at heq
    rw [heq, hrev, List.map_reverse, List.map_map]
    simp only [Function.comp_def, List.reverse_reverse, List.map_id']
    rw [List.take_of_length_le (by simp; omega), List.drop_eq_nil_of_le (by simp; omega)]
    simp only [List.isEmpty_nil, Bool.and_true, List.all_eq_true, List.mem_reverse,
      piece_bool_iff, h4, true_and]
  · have hne : ((SudoersSpec.Syntax.splitn 5 '.' text.reverse).map List.reverse).drop 4 ≠ [] := by
      intro h
      have := congrArg List.length h
      simp only [List.length_drop, List.length_map, List.length_nil] at this
      omega
    simp only [h4, false_and, iff_false, Bool.and_eq_true, not_and, List.isEmpty_iff]
    exact fun _ => hne

/-! ## `resembles_ipv4`: the loop -/

private theorem bne_zero (x : Usize) : (x != 0#usize) = decide (x.val ≠ 0) := by
  by_cases h : x.val = 0
  · have : x = 0#usize := by scalar_tac
    simp [this]
  · have : x ≠ 0#usize := by intro e; apply h; simp [e]
    simp [this, h]

theorem resembles_ipv4_loop_false (text : Slice Char) (parts part_len i : Usize) :
    sudo_rs.sudoers.tokens.resembles_ipv4_loop text parts part_len false i =
      ok (part_len, false) := by
  unfold sudo_rs.sudoers.tokens.resembles_ipv4_loop
  simp

theorem resembles_ipv4_loop_eq {O : CharOracle} (hO : UnicodeOracle O) (text : Slice Char)
    (parts part_len i : Usize) (hp : parts.val ≤ 4) (hl : part_len.val ≤ 3) :
    ∃ r : Usize × Bool,
      sudo_rs.sudoers.tokens.resembles_ipv4_loop text parts part_len true i = ok r ∧
      (if r.2 then r.1 != 0#usize else false) =
        scan O parts.val part_len.val (text.val.drop i.val) := by
  unfold sudo_rs.sudoers.tokens.resembles_ipv4_loop
  simp only [↓reduceIte]
  split
  · rename_i hlt
    have hi' : i.val < text.val.length := by scalar_tac
    obtain ⟨i2, hi2, hi2v⟩ := add_one_eq i (by scalar_tac)
    have hd : text.val.drop i.val = text.val[i.val] :: text.val.drop i2.val := by
      rw [hi2v]; exact List.drop_eq_getElem_cons hi'
    rw [index_eq text i hi', hd]
    simp only [bind_ok]
    by_cases hc : text.val[i.val] = '.'
    · obtain ⟨p2, hp2, hp2v⟩ := add_one_eq parts (by scalar_tac)
      have hok3 : (if (part_len != 0#usize) = true then ok (decide (parts < 4#usize))
          else ok false : Result Bool) = ok (decide (part_len.val ≠ 0 ∧ parts.val < 4)) := by
        rw [bne_zero]
        by_cases hz : part_len.val = 0
        · simp [hz]
        · have hlt4 : (parts < 4#usize) ↔ parts.val < 4 := by
            constructor <;> intro h <;> scalar_tac
          simp [hz, hlt4]
      simp only [hc, ↓reduceIte, hok3, bind_ok, hp2, hi2, scan]
      by_cases hb : part_len.val ≠ 0 ∧ parts.val < 4
      · obtain ⟨r, hr, hrv⟩ :=
          resembles_ipv4_loop_eq hO text p2 0#usize i2 (by omega) (by simp)
        refine ⟨r, by rw [decide_eq_true hb]; exact hr, ?_⟩
        rw [hrv, hp2v, ite_eq_left_of_eq_true _ _ (eq_true hb)]
        rfl
      · refine ⟨(0#usize, false), ?_, ?_⟩
        · rw [decide_eq_false hb]; exact resembles_ipv4_loop_false _ _ _ _
        · rw [ite_eq_right_of_eq_false _ _ (eq_false hb)]
          rfl
    · obtain ⟨n, hn, hnv⟩ := len_utf8_eq text.val[i.val]
      have hn4 : n.val ≤ 4 := by rw [hnv]; exact utf8Size_le_four _
      obtain ⟨pl2, hpl2, hpl2v⟩ := add_eq part_len n (by scalar_tac)
      have hcond_eq : (if pl2 ≤ 3#usize then core.char.methods.Char.is_numeric text.val[i.val]
          else ok false : Result Bool) = ok (decide (part_len.val + text.val[i.val].utf8Size ≤ 3 ∧
            O.isNumeric text.val[i.val] = true)) := by
        by_cases hle : part_len.val + text.val[i.val].utf8Size ≤ 3
        · have : pl2 ≤ 3#usize := by scalar_tac
          simp [this, hO.is_numeric, hle]
        · have : ¬ pl2 ≤ 3#usize := by scalar_tac
          simp [this, hle]
      simp only [hc, ↓reduceIte, hn, bind_ok, hpl2, hcond_eq, hi2, scan]
      by_cases hb : part_len.val + text.val[i.val].utf8Size ≤ 3 ∧ O.isNumeric text.val[i.val] = true
      · obtain ⟨r, hr, hrv⟩ :=
          resembles_ipv4_loop_eq hO text parts pl2 i2 hp (by omega)
        refine ⟨r, by rw [decide_eq_true hb]; exact hr, ?_⟩
        rw [hrv, hpl2v, hnv, ite_eq_left_of_eq_true _ _ (eq_true hb)]
      · refine ⟨(pl2, false), ?_, ?_⟩
        · rw [decide_eq_false hb]; exact resembles_ipv4_loop_false _ _ _ _
        · rw [ite_eq_right_of_eq_false _ _ (eq_false hb)]
          rfl
  · have hge : text.val.length ≤ i.val := by scalar_tac
    refine ⟨(part_len, true), rfl, ?_⟩
    simp [List.drop_eq_nil_of_le hge, scan, bne_zero]
termination_by text.val.length - i.val
decreasing_by all_goals scalar_tac

theorem resembles_ipv4_eq {O : CharOracle} (hO : UnicodeOracle O) (text : Slice Char) :
    sudo_rs.sudoers.tokens.resembles_ipv4 text =
      ok (SudoersSpec.Syntax.Hostname.looksLikeIPv4 O text.val) := by
  obtain ⟨⟨pl, b⟩, hr, hrv⟩ :=
    resembles_ipv4_loop_eq hO text 1#usize 0#usize 0#usize (by simp) (by simp)
  have hs : scan O 1 0 text.val = SudoersSpec.Syntax.Hostname.looksLikeIPv4 O text.val :=
    Bool.eq_iff_iff.2 ((scan_shape O text.val).trans (looksLikeIPv4_iff O text.val).symm)
  have h1 : scan O (1#usize : Usize).val (0#usize : Usize).val (text.val.drop (0#usize : Usize).val) =
      scan O 1 0 text.val := by simp
  rw [h1, hs] at hrv
  unfold sudo_rs.sudoers.tokens.resembles_ipv4
  rw [hr, bind_ok, ← hrv]
  cases b <;> rfl

/-! ## Token instances -/

theorem length_le_utf8ByteSize (s : String) : s.toList.length ≤ s.utf8ByteSize := by
  have key : ∀ l : List Char, l.length ≤ (String.ofList l).utf8ByteSize := by
    intro l
    induction l with
    | nil => simp
    | cons c l ih =>
      rw [String.ofList_cons, String.utf8ByteSize_append, String.utf8ByteSize_singleton]
      have := c.utf8Size_pos
      simp only [List.length_cons]
      omega
  simpa [String.ofList_toList] using key s.toList

theorem chars_of_eq (s : String) (h : s.utf8ByteSize ≤ Usize.max) :
    ∃ v : alloc.vec.Vec Char, sudoers.char_stream.chars_of s = ok v ∧
      (alloc.vec.Vec.deref v).val = s.toList := by
  have h' : s.toList.length ≤ Usize.max := le_trans (length_le_utf8ByteSize s) h
  refine ⟨⟨Slice.from s.toList h'⟩, ?_, ?_⟩
  · simp [sudoers.char_stream.chars_of, h']
  · rw [SudoRsProofs.Vec.deref_val]
    exact Slice.from_val _ _

/-- `Hostname::construct` is total: refined on every text (`Pre := fun _ => True`). -/
theorem hostname_token_refines {O : CharOracle} (hO : UnicodeOracle O) :
    TokenRefines sudo_rs.sudoers.tokens.Hostname.Insts.Sudo_rsSudoersBasic_parserToken id
      (SudoersSpec.Syntax.hostnameToken O) (fun _ => True) where
  max_len := ⟨_, rfl, by
    simp [sudo_rs.sudoers.basic_parser.Token.MAX_LEN.default, SudoersSpec.Syntax.hostnameToken]⟩
  max_len_le := by
    simp only [SudoersSpec.Syntax.hostnameToken]
    scalar_tac
  allow_escape := by
    simp [sudo_rs.sudoers.basic_parser.Token.ALLOW_ESCAPE.default, SudoersSpec.Syntax.hostnameToken]
  accept c := hostname_accept_eq c
  accept_1st c := hostname_accept_eq c
  escaped _ := rfl
  construct s hs _ := by
    obtain ⟨v, hv, hd⟩ := chars_of_eq s hs
    show ∃ r, sudo_rs.sudoers.tokens.Hostname.Insts.Sudo_rsSudoersBasic_parserToken.construct s =
      ok r ∧ ConstructRel id r (SudoersSpec.Syntax.Hostname.construct O s.toList)
    simp only [sudo_rs.sudoers.tokens.Hostname.Insts.Sudo_rsSudoersBasic_parserToken.construct, hv,
      bind_ok, resembles_ipv4_eq hO, hd, SudoersSpec.Syntax.Hostname.construct]
    cases SudoersSpec.Syntax.Hostname.looksLikeIPv4 O s.toList
    · exact ⟨_, rfl, (String.ofList_toList (s := s)).symm⟩
    · exact ⟨_, rfl, KindRel.hostIpv4⟩

/-- `Meta<T>` refines `metaToken` with the precondition of `T` on `construct`
(`Meta::construct` passes the raw text to `T::construct` or does not call it). -/
theorem meta_token_refines {O : CharOracle} {T α : Type}
    {Tk : sudo_rs.sudoers.basic_parser.Token T} {f : T → α}
    {T' : SudoersSpec.Syntax.TokenSpec α} {Pre : List Char → Prop} (hO : UnicodeOracle O)
    (h : TokenRefines Tk f T' Pre) :
    TokenRefines (sudo_rs.sudoers.tokens.Meta.Insts.Sudo_rsSudoersBasic_parserToken Tk)
      (SudoRsProofs.absMeta f) (SudoersSpec.Syntax.metaToken O T') Pre where
  max_len := by
    obtain ⟨n, hn, hnv⟩ := h.max_len
    refine ⟨n, ?_, hnv⟩
    show sudo_rs.sudoers.tokens.Meta.Insts.Sudo_rsSudoersBasic_parserToken.MAX_LEN Tk = ok n
    unfold sudo_rs.sudoers.tokens.Meta.Insts.Sudo_rsSudoersBasic_parserToken.MAX_LEN
    exact hn
  max_len_le := h.max_len_le
  allow_escape := by
    show sudo_rs.sudoers.tokens.Meta.Insts.Sudo_rsSudoersBasic_parserToken.ALLOW_ESCAPE Tk = _
    unfold sudo_rs.sudoers.tokens.Meta.Insts.Sudo_rsSudoersBasic_parserToken.ALLOW_ESCAPE
    exact h.allow_escape
  accept c := by
    show sudo_rs.sudoers.tokens.Meta.Insts.Sudo_rsSudoersBasic_parserToken.accept Tk c =
      ok (T'.accept c || O.isUppercase c)
    simp only [sudo_rs.sudoers.tokens.Meta.Insts.Sudo_rsSudoersBasic_parserToken.accept,
      h.accept c, bind_ok]
    cases T'.accept c <;> simp [hO.is_uppercase]
  accept_1st c := by
    show sudo_rs.sudoers.tokens.Meta.Insts.Sudo_rsSudoersBasic_parserToken.accept_1st Tk c =
      ok (T'.accept1st c || O.isUppercase c)
    simp only [sudo_rs.sudoers.tokens.Meta.Insts.Sudo_rsSudoersBasic_parserToken.accept_1st,
      h.accept_1st c, bind_ok]
    cases T'.accept1st c <;> simp [hO.is_uppercase]
  escaped c := h.escaped c
  construct s hs hpre := by
    obtain ⟨v, hv, hd⟩ := chars_of_eq s hs
    obtain ⟨n, hn, hnle, htake⟩ := trimmed_len_eq hO (alloc.vec.Vec.deref v)
    have hle : n.val ≤ (alloc.vec.Vec.deref v).val.length := hnle
    rw [hd] at htake
    show ∃ r, sudo_rs.sudoers.tokens.Meta.Insts.Sudo_rsSudoersBasic_parserToken.construct Tk s =
      ok r ∧ ConstructRel (SudoRsProofs.absMeta f) r (SudoersSpec.Syntax.Meta.construct O T' s.toList)
    simp only [sudo_rs.sudoers.tokens.Meta.Insts.Sudo_rsSudoersBasic_parserToken.construct, hv,
      bind_ok, hn, is_all_eq _ _ hle, is_alias_name_eq _ _ hle, string_of_eq _ _ hle, hd, htake,
      SudoersSpec.Syntax.Meta.construct]
    by_cases h1 : (trimEnd O s.toList == "ALL".toList) = true
    · simp only [h1, ↓reduceIte]
      exact ⟨_, rfl, rfl⟩
    · simp only [h1, Bool.false_eq_true, ↓reduceIte]
      by_cases h2 : (startsWithPred (trimEnd O s.toList) SudoersSpec.Syntax.AliasName.accept1st &&
          ((trimEnd O s.toList).drop 1).all SudoersSpec.Syntax.AliasName.accept) = true
      · simp only [h2, ↓reduceIte]
        exact ⟨_, rfl, rfl⟩
      · simp only [h2, Bool.false_eq_true, ↓reduceIte]
        obtain ⟨r, hr, hrel⟩ := h.construct s hs hpre
        rw [hr, bind_ok]
        cases r with
        | Ok item =>
          cases hc : T'.construct s.toList with
          | ok a =>
            rw [hc] at hrel
            exact ⟨_, rfl, show SudoersSpec.Meta.only (f item) = .only a from by
              rw [show f item = a from hrel]⟩
          | error e => rw [hc] at hrel; exact absurd hrel id
        | Err k =>
          cases hc : T'.construct s.toList with
          | ok a => rw [hc] at hrel; exact absurd hrel id
          | error e =>
            rw [hc] at hrel
            exact ⟨_, rfl, hrel⟩

end SudoRsProofs.Parser
