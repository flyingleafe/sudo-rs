import SudoersSpec.Authorization

/-!
# Environment policy of sudo-rs (`src/sudo/env/filter.rs`)

Which variable of the invoking user's environment sudo-rs passes to the command
(`keep_inherited`), and which `VAR=value` of the command line it accepts (`should_keep`). The
definitions transcribe the code, on bytes (`Bytes`, lists of `Nat`):

* `wildcard s t p`: the pattern `p` matches `t`, where `s` (`*`) matches any byte string and
  every other byte itself. `wildcard_match` in `src/sudo/env/wildcard_match.rs` is a greedy loop
  that backtracks to the most recent `*` only; `greedy` is that loop on list indices and
  `greedy_correct` proves it equal to `wildcard` for every input.
* `entryMatches`: an `env_keep`/`env_check` entry `NAME=VALUE` (split at the first `=`) matches
  name and value, an entry without `=` the name only; `inTable`: some entry matches. The result
  does not depend on the order of the table (`inTable_perm`): `HashSet` iteration order is
  unspecified.
* `tzSafe`: the TZ check. `TzEnv` holds the two values the code reads from the system: the
  zoneinfo directory `zoneinfo_path()` found, if any, and `PATH_MAX`.
* `shouldKeep`, `keepInherited`: the decision. `configOf` reads the policy part from the
  `Restrictions` of an authorization (`SudoersSpec.Authorization`).

Boundary. The environment itself is assembled by `get_target_environment`
(`src/sudo/env/environment.rs`), outside this file: start from the PAM environment, add the
inherited variables that `keepInherited` keeps (they override PAM), add the sudo variables
(`SUDO_*`, `HOME`, `SHELL`, `LOGNAME`/`USER`, `PATH` from `secure_path` or a default, `TERM`,
`PS1` from `SUDO_PS1`), then the command-line variables that `shouldKeep` accepts (any rejected
one makes sudo fail); with `setenv`/`SETENV` (`trust_environment`) the command-line variables are
added without this check (`dangerous_extend`). Those map operations are not specified here.

The precedence the code has, stated as theorems below: a value starting with `()` is never
kept; `PATH` is never kept when `secure_path` is set; for `TZ` an `env_keep` match suffices and
an `env_check` match needs `tzSafe`; for every other name an `env_check` match decides alone
(`%` or `/` in the value drops it, whatever `env_keep` says); otherwise `env_keep` decides.

`SudoRsProofs/EnvFilter.lean` proves the Aeneas extraction of `should_keep`, `keep_inherited`
and `wildcard_match` equal to these definitions.
-/

namespace SudoersSpec.EnvFilter

/-! ## Wildcard patterns -/

section Wildcard

variable {α : Type} [DecidableEq α]

/-- The suffixes of a list, longest first (`List.tails` of Batteries, which core lacks). -/
def suffixes {β : Type} : List β → List (List β)
  | [] => [[]]
  | a :: l => (a :: l) :: suffixes l

/-- `p` matches `t`; `s` in `p` matches any (possibly empty) part of `t`, every other element
itself. A `s` in `t` is an ordinary element. -/
def wildcard (s : α) : List α → List α → Bool
  | t, [] => t.isEmpty
  | t, d :: p =>
    if d = s then (suffixes t).any (fun u => wildcard s u p)
    else
      match t with
      | [] => false
      | c :: t' => decide (c = d) && wildcard s t' p

@[simp] theorem wildcard_nil (s : α) (t : List α) : wildcard s t [] = t.isEmpty := by
  simp [wildcard]

theorem wildcard_star (s : α) (t p : List α) :
    wildcard s t (s :: p) = (suffixes t).any (fun u => wildcard s u p) := by
  simp [wildcard]

theorem wildcard_lit_nil {s d : α} (h : d ≠ s) (p : List α) : wildcard s [] (d :: p) = false := by
  simp [wildcard, h]

theorem wildcard_lit_cons {s d : α} (h : d ≠ s) (c : α) (t p : List α) :
    wildcard s (c :: t) (d :: p) = (decide (c = d) && wildcard s t p) := by
  simp [wildcard, h]

/-- The suffixes of `u` are its `drop`s. -/
theorem any_tails (f : List α → Bool) :
    ∀ u : List α, (suffixes u).any f = true ↔ ∃ k, k ≤ u.length ∧ f (u.drop k) = true
  | [] => by
    simp only [suffixes, List.any_cons, List.any_nil, Bool.or_false, List.length_nil]
    constructor
    · intro h
      exact ⟨0, Nat.le_refl 0, by simpa using h⟩
    · rintro ⟨k, _, h⟩
      simpa using h
  | a :: u => by
    simp only [suffixes, List.any_cons, Bool.or_eq_true]
    rw [any_tails f u]
    constructor
    · rintro (h | ⟨k, hk, h⟩)
      · exact ⟨0, Nat.zero_le _, by simpa using h⟩
      · exact ⟨k + 1, by simp only [List.length_cons]; omega, by simpa using h⟩
    · rintro ⟨k, hk, h⟩
      cases k with
      | zero => exact Or.inl (by simpa using h)
      | succ k => exact Or.inr ⟨k, by simp only [List.length_cons] at hk; omega, by simpa using h⟩

theorem drop_drop' : ∀ (T : List α) (i k : Nat), (T.drop i).drop k = T.drop (i + k)
  | [], i, k => by simp
  | a :: T, 0, k => by simp
  | a :: T, i + 1, k => by
    rw [Nat.add_right_comm, List.drop_succ_cons, List.drop_succ_cons]
    exact drop_drop' T i k

/-- A pattern without `s` matches exactly itself. -/
theorem wildcard_noStar (s : α) :
    ∀ (t p : List α), (∀ c ∈ p, c ≠ s) → wildcard s t p = (t == p)
  | t, [], _ => by cases t <;> rfl
  | [], d :: p, hp => by
    rw [wildcard_lit_nil (hp d (by simp))]
    rfl
  | c :: t, d :: p, hp => by
    rw [wildcard_lit_cons (hp d (by simp)), wildcard_noStar s t p (fun x hx => hp x (by simp [hx]))]
    by_cases h : c = d
    · subst h; simp
    · simp [h]

/-- A pattern that is only `s` matches everything. -/
theorem wildcard_star_alone (s : α) (t : List α) : wildcard s t [s] = true := by
  rw [wildcard_star, any_tails]
  exact ⟨t.length, Nat.le_refl _, by simp⟩

/-- A star-free prefix of the pattern must be a prefix of the input. -/
theorem wildcard_lits {s : α} : ∀ (lits u q : List α), (∀ c ∈ lits, c ≠ s) →
    wildcard s u (lits ++ q) = true → ∃ v, u = lits ++ v ∧ wildcard s v q = true
  | [], u, q, _, h => ⟨u, rfl, by simpa using h⟩
  | c :: lits, [], q, hl, h => by
    rw [List.cons_append, wildcard_lit_nil (hl c (by simp))] at h
    exact absurd h (by simp)
  | c :: lits, d :: u, q, hl, h => by
    rw [List.cons_append, wildcard_lit_cons (hl c (by simp))] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hdc, h⟩ := h
    obtain ⟨v, hv, hw⟩ := wildcard_lits lits u q (fun x hx => hl x (by simp [hx])) h
    exact ⟨v, by rw [hdc, hv, List.cons_append], hw⟩

theorem wildcard_drop_star {s : α} {T P : List α} {t p : Nat} (ht : t ≤ T.length)
    (hp : p < P.length) (hs : P[p] = s) :
    wildcard s (T.drop t) (P.drop p) = true ↔
      ∃ k, t ≤ k ∧ k ≤ T.length ∧ wildcard s (T.drop k) (P.drop (p + 1)) = true := by
  rw [List.drop_eq_getElem_cons hp, hs, wildcard_star, any_tails]
  constructor
  · rintro ⟨j, hj, hw⟩
    try dsimp only at hw
    rw [List.length_drop] at hj
    rw [drop_drop'] at hw
    exact ⟨t + j, by omega, by omega, hw⟩
  · rintro ⟨k, hk1, hk2, hw⟩
    refine ⟨k - t, by rw [List.length_drop]; omega, ?_⟩
    try dsimp only
    have e : t + (k - t) = k := by omega
    rw [drop_drop', e]
    exact hw

/-! ### The greedy loop of `wildcard_match` -/

/-- The lexicographic order of the termination measures below. -/
theorem lex_lt {a a' b b' : Nat} (h : a' < a ∨ (a' = a ∧ b' < b)) :
    Prod.Lex (· < ·) (· < ·) (a', b') (a, b) := by
  rcases h with h | ⟨rfl, h⟩
  · exact Prod.Lex.left _ _ h
  · exact Prod.Lex.right _ h

/-- `wildcard_match` on list indices. `t`, `p`: the positions in input and pattern; `star`:
a `s` has been seen; `st`, `sp`: the input and pattern positions at which the current attempt
after the most recent `s` started. The hypotheses carry the termination argument. -/
def greedy (s : α) (T P : List α) (t p : Nat) (star : Bool) (st sp : Nat)
    (hst : st ≤ t) (ht : t ≤ T.length) : Bool :=
  if h : p < P.length ∧ t < T.length then
    if P[p]'h.1 = s then greedy s T P t (p + 1) true t (p + 1) (Nat.le_refl t) ht
    else if P[p]'h.1 = T[t]'h.2 then
      greedy s T P (t + 1) (p + 1) star st sp (by omega) (by omega)
    else if star then greedy s T P (st + 1) sp true (st + 1) sp (Nat.le_refl _) (by omega)
    else false
  else if h2 : t < T.length then
    if star then greedy s T P (st + 1) sp true (st + 1) sp (Nat.le_refl _) (by omega)
    else false
  else if h3 : p < P.length then
    if P[p]'h3 = s then greedy s T P t (p + 1) star st sp hst ht else false
  else true
termination_by (T.length + 1 - st, T.length - t + (P.length - p))
decreasing_by
  all_goals
    first
    | (apply lex_lt; omega)
    | (simp_wf; apply lex_lt; omega)
    | (simp only [Prod.lex_def]; omega)
    | (simp_wf; simp only [Prod.lex_def]; omega)

/-- The alternatives still open after the most recent `s`: the attempt may restart at any
later input position. -/
abbrev Alt (s : α) (T P : List α) (st sp : Nat) : Prop :=
  ∃ k, st < k ∧ k ≤ T.length ∧ wildcard s (T.drop k) (P.drop sp) = true

/-- Since the most recent `s`, the input from `st` to `t` matched the star-free pattern from
`sp` to `p`. -/
abbrev Seg (s : α) (T P : List α) (t p st sp : Nat) : Prop :=
  ∃ lits : List α, (∀ c ∈ lits, c ≠ s) ∧ P.drop sp = lits ++ P.drop p ∧
    T.drop st = lits ++ T.drop t

theorem seg_refl (s : α) (T P : List α) (t p : Nat) : Seg s T P t p t p :=
  ⟨[], by simp, by simp, by simp⟩

theorem alt_step {s : α} {T P : List α} {st sp : Nat} (h : st + 1 ≤ T.length) :
    Alt s T P st sp ↔
      (wildcard s (T.drop (st + 1)) (P.drop sp) = true ∨ Alt s T P (st + 1) sp) := by
  constructor
  · rintro ⟨k, hk1, hk2, hw⟩
    by_cases hk : k = st + 1
    · subst hk
      exact Or.inl hw
    · exact Or.inr ⟨k, by omega, hk2, hw⟩
  · rintro (hw | ⟨k, hk1, hk2, hw⟩)
    · exact ⟨st + 1, by omega, h, hw⟩
    · exact ⟨k, by omega, hk2, hw⟩

/-- The length bookkeeping of `Seg`: the matched part has length `t - st`. -/
theorem seg_length {T : List α} {t st : Nat} {lits : List α}
    (ht : t ≤ T.length) (hst : st ≤ t) (hT : T.drop st = lits ++ T.drop t) :
    lits.length = t - st := by
  have h := congrArg List.length hT
  simp only [List.length_drop, List.length_append] at h
  omega

/-- An earlier alternative that succeeds also succeeds from the current position. -/
theorem seg_shift {s : α} {T P : List α} {t p st sp : Nat} (ht : t ≤ T.length)
    (hst : st ≤ t) (hseg : Seg s T P t p st sp) (k : Nat) (hkn : k ≤ T.length)
    (hw : wildcard s (T.drop k) (P.drop sp) = true) :
    t - st + k ≤ T.length ∧ wildcard s (T.drop (t - st + k)) (P.drop p) = true := by
  obtain ⟨lits, hl, hP, hT⟩ := hseg
  have hL := seg_length ht hst hT
  rw [hP] at hw
  obtain ⟨v, hv, hw'⟩ := wildcard_lits lits _ _ hl hw
  have hlen := congrArg List.length hv
  simp only [List.length_drop, List.length_append] at hlen
  have hdrop : (T.drop k).drop lits.length = v := by
    rw [hv]
    simp
  rw [drop_drop'] at hdrop
  refine ⟨by omega, ?_⟩
  have e : t - st + k = k + lits.length := by omega
  rw [e, hdrop]
  exact hw'

/-- At the end of the input, no earlier alternative is left. -/
theorem no_alt_at_end {s : α} {T P : List α} {t p st sp : Nat} (ht : t = T.length)
    (hst : st ≤ t) (hseg : Seg s T P t p st sp) : ¬ Alt s T P st sp := by
  rintro ⟨k, hk1, hk2, hw⟩
  obtain ⟨lits, hl, hP, hT⟩ := hseg
  have hL := seg_length (Nat.le_of_eq ht) hst hT
  rw [hP] at hw
  obtain ⟨v, hv, _⟩ := wildcard_lits lits _ _ hl hw
  have hlen := congrArg List.length hv
  simp only [List.length_drop, List.length_append] at hlen
  omega

/-- The loop invariant: from any state satisfying it, `greedy` answers whether the rest of the
input matches the rest of the pattern, or (after a `s`) some later restart does. -/
theorem greedy_iff (s : α) (T P : List α) (t p : Nat) (star : Bool) (st sp : Nat)
    (hst : st ≤ t) (ht : t ≤ T.length)
    (hinv : star = true → Seg s T P t p st sp ∨ ¬ Alt s T P st sp) :
    greedy s T P t p star st sp hst ht = true ↔
      (wildcard s (T.drop t) (P.drop p) = true ∨ (star = true ∧ Alt s T P st sp)) := by
  unfold greedy
  by_cases h : p < P.length ∧ t < T.length
  · rw [dif_pos h]
    have hp := h.1
    have htn := h.2
    by_cases hs : P[p] = s
    · -- a new `s`: it supersedes the earlier alternatives
      rw [if_pos hs, greedy_iff s T P t (p + 1) true t (p + 1) (Nat.le_refl t) ht
        (fun _ => Or.inl (seg_refl s T P t (p + 1)))]
      rw [wildcard_drop_star ht hp hs]
      constructor
      · rintro (hw | ⟨_, k, hk1, hk2, hw⟩)
        · exact Or.inl ⟨t, Nat.le_refl t, ht, hw⟩
        · exact Or.inl ⟨k, by omega, hk2, hw⟩
      · rintro (⟨k, hk1, hk2, hw⟩ | ⟨hstar, halt⟩)
        · by_cases hkt : k = t
          · subst hkt
            exact Or.inl hw
          · exact Or.inr ⟨rfl, k, by omega, hk2, hw⟩
        · rcases hinv hstar with hseg | hnalt
          · obtain ⟨k, hk1, hk2, hw⟩ := halt
            obtain ⟨hlen, hw'⟩ := seg_shift ht hst hseg k hk2 hw
            rw [wildcard_drop_star hlen hp hs] at hw'
            obtain ⟨k2, hk21, hk22, hw2⟩ := hw'
            exact Or.inr ⟨rfl, k2, by omega, hk22, hw2⟩
          · exact absurd halt hnalt
    · rw [if_neg hs]
      by_cases hc : P[p] = T[t]
      · -- a literal match: the star-free segment grows by one
        have hinv' : star = true → Seg s T P (t + 1) (p + 1) st sp ∨ ¬ Alt s T P st sp := by
          intro hstar
          rcases hinv hstar with ⟨lits, hl, hP, hT⟩ | hn
          · refine Or.inl ⟨lits ++ [P[p]], ?_, ?_, ?_⟩
            · intro c hc'
              rw [List.mem_append, List.mem_singleton] at hc'
              rcases hc' with hc' | hc'
              · exact hl c hc'
              · rw [hc']
                exact hs
            · rw [hP, List.drop_eq_getElem_cons hp]
              simp
            · rw [hT, List.drop_eq_getElem_cons htn, hc]
              simp
          · exact Or.inr hn
        rw [if_pos hc, greedy_iff s T P (t + 1) (p + 1) star st sp (by omega) (by omega) hinv']
        have hW : wildcard s (T.drop t) (P.drop p) =
            wildcard s (T.drop (t + 1)) (P.drop (p + 1)) := by
          rw [List.drop_eq_getElem_cons hp, List.drop_eq_getElem_cons htn, wildcard_lit_cons hs]
          simp [hc]
        rw [hW]
      · -- a mismatch: restart after the most recent `s`, or fail
        rw [if_neg hc]
        have hW : wildcard s (T.drop t) (P.drop p) = false := by
          rw [List.drop_eq_getElem_cons hp, List.drop_eq_getElem_cons htn, wildcard_lit_cons hs]
          have hc' : ¬ T[t] = P[p] := fun e => hc e.symm
          simp [hc']
        cases star with
        | false => simp [hW]
        | true =>
          rw [if_pos rfl, greedy_iff s T P (st + 1) sp true (st + 1) sp (Nat.le_refl _)
            (by omega) (fun _ => Or.inl (seg_refl s T P (st + 1) sp)), hW]
          simp only [eq_self_iff_true, true_and, Bool.false_eq_true, false_or]
          exact (alt_step (by omega)).symm
  · rw [dif_neg h]
    by_cases htn : t < T.length
    · -- the pattern is exhausted, the input is not
      rw [dif_pos htn]
      have hp : P.length ≤ p := by omega
      have hW : wildcard s (T.drop t) (P.drop p) = false := by
        rw [List.drop_eq_nil_of_le hp, wildcard_nil, List.drop_eq_getElem_cons htn,
          List.isEmpty_cons]
      cases star with
      | false => simp [hW]
      | true =>
        rw [if_pos rfl, greedy_iff s T P (st + 1) sp true (st + 1) sp (Nat.le_refl _)
          (by omega) (fun _ => Or.inl (seg_refl s T P (st + 1) sp)), hW]
        simp only [eq_self_iff_true, true_and, Bool.false_eq_true, false_or]
        exact (alt_step (by omega)).symm
    · -- the input is exhausted
      rw [dif_neg htn]
      have htn' : t = T.length := by omega
      have hT0 : T.drop t = [] := List.drop_eq_nil_of_le (by omega)
      have hend : star = true → ¬ Alt s T P st sp := by
        intro hstar
        rcases hinv hstar with hseg | hn
        · exact no_alt_at_end htn' hst hseg
        · exact hn
      by_cases hp : p < P.length
      · rw [dif_pos hp]
        by_cases hs : P[p] = s
        · rw [if_pos hs, greedy_iff s T P t (p + 1) star st sp hst ht
            (fun hstar => Or.inr (hend hstar))]
          have hW : wildcard s (T.drop t) (P.drop p) =
              wildcard s (T.drop t) (P.drop (p + 1)) := by
            rw [hT0, List.drop_eq_getElem_cons hp, hs, wildcard_star]
            simp [suffixes]
          rw [hW]
        · rw [if_neg hs]
          have hW : wildcard s (T.drop t) (P.drop p) = false := by
            rw [hT0, List.drop_eq_getElem_cons hp, wildcard_lit_nil hs]
          constructor
          · intro hf
            exact absurd hf (by simp)
          · rintro (hw | ⟨hstar, halt⟩)
            · rw [hW] at hw
              exact absurd hw (by simp)
            · exact absurd halt (hend hstar)
      · rw [dif_neg hp]
        refine iff_of_true rfl (Or.inl ?_)
        simp only [hT0, List.drop_eq_nil_of_le (by omega : P.length ≤ p), wildcard_nil,
          List.isEmpty_nil]
termination_by (T.length + 1 - st, T.length - t + (P.length - p))
decreasing_by
  all_goals
    first
    | (apply lex_lt; omega)
    | (simp_wf; apply lex_lt; omega)
    | (simp only [Prod.lex_def]; omega)
    | (simp_wf; simp only [Prod.lex_def]; omega)

/-- **The greedy loop is correct**: from the initial state it computes `wildcard`. -/
theorem greedy_correct (s : α) (T P : List α) :
    greedy s T P 0 0 false 0 0 (Nat.le_refl 0) (Nat.zero_le _) = wildcard s T P := by
  have h := greedy_iff s T P 0 0 false 0 0 (Nat.le_refl 0) (Nat.zero_le _) (by simp)
  simp only [List.drop_zero, Bool.false_eq_true, false_and, or_false] at h
  exact Bool.eq_iff_iff.mpr h

/-- `wildcard` is preserved by an injective renaming of the alphabet. -/
theorem wildcard_map {β : Type} [DecidableEq β] (f : α → β) (hf : Function.Injective f)
    (s : α) : ∀ (t p : List α), wildcard (f s) (t.map f) (p.map f) = wildcard s t p
  | t, [] => by cases t <;> rfl
  | t, d :: p => by
    by_cases hd : d = s
    · subst hd
      rw [List.map_cons, wildcard_star, wildcard_star]
      apply Bool.eq_iff_iff.mpr
      rw [any_tails, any_tails]
      constructor
      · rintro ⟨k, hk, hw⟩
        rw [List.length_map] at hk
        rw [← List.map_drop, wildcard_map f hf d _ p] at hw
        exact ⟨k, hk, hw⟩
      · rintro ⟨k, hk, hw⟩
        refine ⟨k, by rw [List.length_map]; exact hk, ?_⟩
        try dsimp only
        rw [← List.map_drop, wildcard_map f hf d _ p]
        exact hw
    · have hfd : f d ≠ f s := fun e => hd (hf e)
      cases t with
      | nil => rw [List.map_cons, List.map_nil, wildcard_lit_nil hfd, wildcard_lit_nil hd]
      | cons c t =>
        rw [List.map_cons, List.map_cons, wildcard_lit_cons hfd, wildcard_lit_cons hd,
          wildcard_map f hf s t p]
        have : decide (f c = f d) = decide (c = d) := by
          by_cases h : c = d
          · simp [h]
          · have hfn : ¬ f c = f d := fun e => h (hf e)
            simp [h, hfn]
        rw [this]

end Wildcard

/-! ## Bytes

A byte is a `Nat` below 256 (the extraction's `u8` read through `.val`). -/

/-- Byte strings: names, values, table entries. -/
abbrev Bytes := List Nat

/-- `b'*'`. -/
def starByte : Nat := 42

/-- The UTF-8 bytes of a string (the bytes of a Rust `String`). -/
def utf8 (s : String) : Bytes := s.toByteArray.data.toList.map UInt8.toNat

/-- The position of the first `=` (`find_equals`), or the length if there is none. -/
def firstEq : Bytes → Nat
  | [] => 0
  | c :: r => if c = 61 then 0 else firstEq r + 1

/-- One `env_keep`/`env_check` entry (`entry_matches`): `NAME=VALUE`, split at the first `=`,
matches name and value; an entry without `=` matches the name only. -/
def entryMatches (key value entry : Bytes) : Bool :=
  if firstEq entry < entry.length then
    wildcard starByte key (entry.take (firstEq entry)) &&
      wildcard starByte value (entry.drop (firstEq entry + 1))
  else wildcard starByte key entry

/-- Some entry of the table matches (`in_table`). -/
def inTable (key value : Bytes) (table : List Bytes) : Bool :=
  table.any (entryMatches key value)

/-- Not a printable non-space ASCII character (`!` to `~`). -/
def notPrintable (c : Nat) : Bool := !(decide (33 ≤ c) && decide (c ≤ 126))

/-- `%` or `/`. -/
def percentOrSlash (c : Nat) : Bool := c == 37 || c == 47

/-- Two consecutive dots. -/
def hasDotDot : Bytes → Bool
  | a :: b :: r => (a == 46 && b == 46) || hasDotDot (b :: r)
  | _ => false

/-- What the TZ check reads from the system. -/
structure TzEnv where
  /-- The zoneinfo directory `zoneinfo_path()` found, as bytes, if any. -/
  zoneinfo : Option Bytes
  /-- `PATH_MAX`. -/
  pathMax : Nat

/-- The value without one leading `:`. -/
def stripColon (v : Bytes) : Bytes :=
  if v.head? = some 58 then v.tail else v

/-- A fully-qualified value lies inside the zoneinfo directory: it starts with the directory
followed by `/`. -/
def underZoneinfo (zoneinfo : Option Bytes) (c : Bytes) : Bool :=
  match zoneinfo with
  | none => false
  | some z => z.isPrefixOf c && (c.drop z.length).head? == some 47

/-- `is_safe_tz`. -/
def tzSafe (env : TzEnv) (value : Bytes) : Bool :=
  let c := stripColon value
  (c.head? != some 47 || underZoneinfo env.zoneinfo c) && !hasDotDot c &&
    !(c.any notPrintable) && decide (c.length < env.pathMax)

/-- The policy inputs of the decision. -/
structure Config where
  /-- `env_keep`, as bytes. -/
  keep : List Bytes
  /-- `env_check`, as bytes. -/
  check : List Bytes
  /-- `secure_path` is set. -/
  securePath : Bool
  /-- What the TZ check reads from the system. -/
  tz : TzEnv

/-- `PATH`. -/
def pathName : Bytes := [80, 65, 84, 72]
/-- `TZ`. -/
def tzName : Bytes := [84, 90]
/-- `()`. -/
def functionPrefix : Bytes := [40, 41]
/-- `HOME`, `SHELL`, `USER`, `LOGNAME`. -/
def loginNames : List Bytes :=
  [[72, 79, 77, 69], [83, 72, 69, 76, 76], [85, 83, 69, 82], [76, 79, 71, 78, 65, 77, 69]]

/-- `should_keep`: whether the variable `key=value` is passed on. -/
def shouldKeep (cfg : Config) (key value : Bytes) : Bool :=
  if functionPrefix.isPrefixOf value then false
  else if cfg.securePath && key == pathName then false
  else if key == tzName then
    inTable key value cfg.keep || (inTable key value cfg.check && tzSafe cfg.tz value)
  else if inTable key value cfg.check then !(value.any percentOrSlash)
  else inTable key value cfg.keep

/-- `keep_inherited`: whether a variable of the invoking user's environment is passed on; for a
login shell (`login`) never `HOME`, `SHELL`, `USER` or `LOGNAME`. -/
def keepInherited (cfg : Config) (login : Bool) (key value : Bytes) : Bool :=
  !(login && loginNames.contains key) && shouldKeep cfg key value

/-- The decision inputs taken from the `Restrictions` of an authorization. -/
def configOf (r : Restrictions (List String)) (tz : TzEnv) : Config where
  keep := r.envKeep.map utf8
  check := r.envCheck.map utf8
  securePath := r.path.isSome
  tz := tz

/-! ## Properties of the decision -/

/-- The table is a set: its order does not matter. -/
theorem inTable_perm {key value : Bytes} {t₁ t₂ : List Bytes} (h : t₁.Perm t₂) :
    inTable key value t₁ = inTable key value t₂ := by
  apply Bool.eq_iff_iff.mpr
  simp only [inTable, List.any_eq_true]
  constructor
  · rintro ⟨e, he, hm⟩
    exact ⟨e, h.mem_iff.mp he, hm⟩
  · rintro ⟨e, he, hm⟩
    exact ⟨e, h.mem_iff.mpr he, hm⟩

/-- A value starting with `()` is never kept. -/
theorem shouldKeep_function (cfg : Config) (key value : Bytes)
    (h : functionPrefix.isPrefixOf value = true) : shouldKeep cfg key value = false := by
  simp [shouldKeep, h]

/-- With `secure_path`, `PATH` is never kept. -/
theorem shouldKeep_securePath (cfg : Config) (value : Bytes) (h : cfg.securePath = true) :
    shouldKeep cfg pathName value = false := by
  simp [shouldKeep, h]

/-- For a name other than `TZ`, an `env_check` match decides alone: the value is kept iff it
has no `%` and no `/`, whatever `env_keep` says. -/
theorem shouldKeep_check (cfg : Config) (key value : Bytes) (htz : key ≠ tzName)
    (hf : functionPrefix.isPrefixOf value = false)
    (hpath : ¬ (cfg.securePath = true ∧ key = pathName))
    (hc : inTable key value cfg.check = true) :
    shouldKeep cfg key value = !(value.any percentOrSlash) := by
  unfold shouldKeep
  have h1 : (cfg.securePath && key == pathName) = false := by
    cases hs : cfg.securePath
    · rfl
    · simp only [Bool.true_and, beq_eq_false_iff_ne]
      exact fun e => hpath ⟨hs, e⟩
  have h2 : (key == tzName) = false := by simpa using htz
  simp [hf, h1, h2, hc]

/-- `TZ`: an `env_keep` match keeps it, an `env_check` match keeps it if `tzSafe`. -/
theorem shouldKeep_tz (cfg : Config) (value : Bytes)
    (hf : functionPrefix.isPrefixOf value = false) :
    shouldKeep cfg tzName value =
      (inTable tzName value cfg.keep || (inTable tzName value cfg.check && tzSafe cfg.tz value)) := by
  have h1 : (cfg.securePath && tzName == pathName) = false := by
    cases cfg.securePath <;> decide
  simp [shouldKeep, hf, h1]

/-- A variable that matches no entry of either table is dropped. -/
theorem shouldKeep_unlisted (cfg : Config) (key value : Bytes)
    (hk : inTable key value cfg.keep = false) (hc : inTable key value cfg.check = false) :
    shouldKeep cfg key value = false := by
  simp [shouldKeep, hk, hc]

/-- What a kept variable satisfies: no function value, not `PATH` under `secure_path`, and it
matches `env_keep`, or `env_check` with the value check (`tzSafe` for `TZ`, no `%`/`/` else). -/
theorem shouldKeep_sound (cfg : Config) (key value : Bytes)
    (h : shouldKeep cfg key value = true) :
    functionPrefix.isPrefixOf value = false ∧ ¬ (cfg.securePath = true ∧ key = pathName) ∧
      (inTable key value cfg.keep = true ∨
        (inTable key value cfg.check = true ∧ (key = tzName → tzSafe cfg.tz value = true) ∧
          (key ≠ tzName → value.any percentOrSlash = false))) := by
  have hf : functionPrefix.isPrefixOf value = false := by
    cases hfp : functionPrefix.isPrefixOf value
    · rfl
    · rw [shouldKeep_function cfg key value hfp] at h
      exact absurd h (by simp)
  have hp : ¬ (cfg.securePath = true ∧ key = pathName) := by
    rintro ⟨hs, rfl⟩
    rw [shouldKeep_securePath cfg value hs] at h
    exact absurd h (by simp)
  refine ⟨hf, hp, ?_⟩
  by_cases ht : key = tzName
  · subst ht
    rw [shouldKeep_tz cfg value hf] at h
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨hc, hz⟩
    · exact Or.inl h
    · exact Or.inr ⟨hc, fun _ => hz, fun hne => absurd rfl hne⟩
  · by_cases hc : inTable key value cfg.check = true
    · rw [shouldKeep_check cfg key value ht hf hp hc] at h
      exact Or.inr ⟨hc, fun e => absurd e ht, fun _ => by simpa using h⟩
    · have hc' : inTable key value cfg.check = false := by simpa using hc
      by_cases hk : inTable key value cfg.keep = true
      · exact Or.inl hk
      · have hk' : inTable key value cfg.keep = false := by simpa using hk
        rw [shouldKeep_unlisted cfg key value hk' hc'] at h
        exact absurd h (by simp)

/-- What a safe TZ value satisfies. -/
theorem tzSafe_sound (env : TzEnv) (value : Bytes) (h : tzSafe env value = true) :
    hasDotDot (stripColon value) = false ∧ (stripColon value).any notPrintable = false ∧
      (stripColon value).length < env.pathMax ∧
      ((stripColon value).head? = some 47 →
        underZoneinfo env.zoneinfo (stripColon value) = true) := by
  simp only [tzSafe, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true',
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨hz, hd⟩, hp⟩, hl⟩ := h
  refine ⟨hd, hp, hl, fun habs => ?_⟩
  rcases hz with hz | hz
  · exact absurd habs hz
  · exact hz

/-! ## Examples (kernel-checked by `decide`) -/

/-- `LC_*` matches `LC_ALL`. -/
example : wildcard starByte [76, 67, 95, 65, 76, 76] [76, 67, 95, 42] = true := by decide
/-- `*b` does not match `ba`; `*a*` does. -/
example : wildcard starByte [98, 97] [42, 98] = false := by decide
example : wildcard starByte [98, 97] [42, 97, 42] = true := by decide
/-- `A=a*` matches `A` with value `ab`, not `B` with value `ab` nor `A` with value `ba`. -/
example : entryMatches [65] [97, 98] [65, 61, 97, 42] = true := by decide
example : entryMatches [66] [97, 98] [65, 61, 97, 42] = false := by decide
example : entryMatches [65] [98, 97] [65, 61, 97, 42] = false := by decide

end SudoersSpec.EnvFilter
