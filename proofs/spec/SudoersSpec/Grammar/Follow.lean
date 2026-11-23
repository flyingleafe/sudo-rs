import SudoersSpec.Grammar.RoundTrip

/-!
# What may follow a host list

The follow condition of PT4 is the right context of the derivation. Here it is made explicit
for `SpecList<Hostname>` (`hostList_follow_iff`): the right context is admissible iff it is
empty, or its first character `d` is

* not `,` (the list would go on),
* not a blank and not `\` (the whitespace after the last item is maximal; a `\` not followed
  by a newline is a fatal error),
* not a host-name character when the list text ends with a host-name character (maximal munch
  of the last item, which then has no whitespace after it).

Nothing beyond the first character matters (`HeadOnly`). This uses `HostOracle` (that blanks,
`\` and newline are not host-name characters).
-/

namespace SudoersSpec.Grammar

open SudoersSpec.Syntax

variable {α : Type}

/-! ## Relations that look only at the next character -/

/-- `G` depends on its right context only through the first character. -/
def HeadOnly (G : Gram α) : Prop :=
  ∀ c a r r', r.head? = r'.head? → G c a r → G c a r'

theorem NextNot.of_head {P : Char → Prop} {r r' : List Char} (he : r.head? = r'.head?)
    (h : NextNot P r) : NextNot P r' :=
  fun d e => h d (he.trans e)

theorem head_append_eq {x r r' : List Char} (h : x ≠ [] ∨ r.head? = r'.head?) :
    (x ++ r).head? = (x ++ r').head? := by
  cases x with
  | nil => rcases h with h | h; exact absurd rfl h; simpa using h
  | cons a x => rfl

/-- Whitespace with another right context that does not continue it. -/
theorem Ws.replace {w r r' : List Char} (h : Ws w r)
    (hr : NextNot (fun d => blank d = true ∨ d = '\\') r') : Ws w r' := by
  induction h with
  | stop hb _ => exact .stop hb hr
  | cont hb _ ih => exact .cont hb ih

theorem Ws.of_head {w r r' : List Char} (h : Ws w r) (he : r.head? = r'.head?) : Ws w r' :=
  h.replace (h.stopAt.of_head he)

theorem WsG.headOnly : HeadOnly WsG := fun _ _ _ _ he h => Ws.of_head h he

theorem Bangs.of_head {n : Nat} {b X Y : List Char} (h : Bangs n b X) (he : X.head? = Y.head?) :
    Bangs n b Y := by
  induction h with
  | nil => exact .nil
  | cons hw _ ih => exact .cons (hw.of_head (head_append_eq (.inr he))) (ih he)

theorem NontermG.headOnly {G : Gram α} (hG : HeadOnly G) : HeadOnly (NontermG G) := by
  rintro c a r r' he ⟨c₁, w, rfl, hd, hw⟩
  exact ⟨c₁, w, rfl, hG _ _ _ _ (head_append_eq (.inr he)) hd, hw.of_head he⟩

theorem QualG.headOnly {G : Gram α} (hG : HeadOnly G) : HeadOnly (QualG G) := by
  intro c q r r' he h
  cases h with
  | @mk n b c₂ a _ hb hn hd =>
    have he' := head_append_eq (x := c₂) (.inr he)
    exact .mk (hb.of_head he') (hn.of_head he') (NontermG.headOnly hG _ _ _ _ he hd)

theorem HostItemG.headOnly (O : CharOracle) : HeadOnly (HostItemG O) := by
  rintro c a r r' he ⟨h1, h2, h3, h4, h5⟩
  exact ⟨h1, h2, h3, h4.of_head he, h5⟩

/-- `HostItemG` with another right context that does not continue the item. -/
theorem HostItemG.replace {O : CharOracle} {t : List Char} {a : Meta Hostname} {r r' : List Char}
    (h : HostItemG O t a r) (hr : NextNot (fun d => hostChar O d = true) r') :
    HostItemG O t a r' :=
  ⟨h.ne, h.chars, h.len, hr, h.val⟩

/-- The grammar of one item of a host list, with its whitespace. -/
abbrev HostElemG (O : CharOracle) : Gram (Spec Hostname) := NontermG (QualG (HostItemG O))

theorem HostElemG.headOnly (O : CharOracle) : HeadOnly (HostElemG O) :=
  NontermG.headOnly (QualG.headOnly (HostItemG.headOnly O))

theorem HostElemG.trunc (O : CharOracle) : Trunc (HostElemG O) :=
  NontermG.trunc (QualG.trunc (HostItemG.trunc O))

theorem HostElemG.ne_nil {O : CharOracle} {c : List Char} {q : Spec Hostname} {r : List Char}
    (h : HostElemG O c q r) : c ≠ [] := by
  obtain ⟨c₁, w, rfl, hq, -⟩ := h
  cases hq with
  | mk _ _ hd =>
    obtain ⟨t, w', rfl, hi, -⟩ := hd
    intro e
    simp only [List.append_eq_nil_iff] at e
    exact hi.ne e.1.2.1

/-! ## The last character of a text -/

/-- The text `c` ends with a host-name character. -/
def EndsHost (O : CharOracle) (c : List Char) : Prop :=
  ∃ x, c.getLast? = some x ∧ hostChar O x = true

theorem endsHost_append {O : CharOracle} {x y : List Char} (hy : y ≠ []) :
    EndsHost O (x ++ y) ↔ EndsHost O y := by
  obtain ⟨z, hz⟩ : ∃ z, y.getLast? = some z := by
    cases h : y.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp h) hy
    | some z => exact ⟨z, rfl⟩
  simp only [EndsHost, List.getLast?_append, hz, Option.some_or]

theorem HostOracle.hostChar_newline {O : CharOracle} (hO : HostOracle O) :
    hostChar O '\n' = false := by
  simp only [hostChar, hO.upper_ascii '\n' (by decide)]; decide

/-- Whitespace ends with a blank or a newline, so not with a host-name character. -/
theorem Ws.last_not_hostChar {O : CharOracle} (hO : HostOracle O) {w r : List Char}
    (h : Ws w r) : ∀ x, w.getLast? = some x → hostChar O x = false := by
  induction h with
  | @stop bs _ hb _ =>
    intro x hx
    have := hb x (List.mem_of_getLast? hx)
    cases hc : hostChar O x
    · rfl
    · rw [(hO.hostChar_ne hc).1] at this; cases this
  | @cont bs w' _ hb hw ih =>
    intro x hx
    rw [show bs ++ '\\' :: '\n' :: w' = (bs ++ ['\\', '\n']) ++ w' by simp,
      List.getLast?_append] at hx
    cases hy : w'.getLast? with
    | none =>
      rw [hy] at hx
      have : x = '\n' := by simpa using hx.symm
      subst this; exact hO.hostChar_newline
    | some y =>
      rw [hy] at hx
      have : x = y := by simpa using hx.symm
      subst this; exact ih x hy

theorem Ws.not_endsHost {O : CharOracle} (hO : HostOracle O) {w r : List Char} (h : Ws w r) :
    ¬ EndsHost O w := by
  rintro ⟨x, hx, hc⟩
  rw [h.last_not_hostChar hO x hx] at hc; cases hc

/-- Non-empty whitespace starts with a blank or `\`, so not with a host-name character. -/
theorem Ws.head_not_hostChar {O : CharOracle} (hO : HostOracle O) {w r : List Char}
    (h : Ws w r) : NextNot (fun d => hostChar O d = true) w := by
  intro d e hd
  obtain ⟨h1, h2, -⟩ := hO.hostChar_ne hd
  cases h with
  | stop hb _ =>
    cases w with
    | nil => cases e
    | cons b bs =>
      simp only [List.head?_cons, Option.some.injEq] at e
      subst e; rw [hb b (by simp)] at h1; cases h1
  | @cont bs w' _ hb _ =>
    cases bs with
    | nil => simp only [List.nil_append, List.head?_cons, Option.some.injEq] at e; exact h2 e.symm
    | cons b bs =>
      simp only [List.cons_append, List.head?_cons, Option.some.injEq] at e
      subst e; rw [hb b (by simp)] at h1; cases h1

/-! ## One item -/

/-- The condition on the next character `d` after an item `c`. -/
def ElemFollowChar (O : CharOracle) (c : List Char) (d : Char) : Prop :=
  ¬ (blank d = true ∨ d = '\\') ∧ (EndsHost O c → hostChar O d = false)

theorem hostElem_cons_iff {O : CharOracle} (hO : HostOracle O) {c : List Char}
    {q : Spec Hostname} {d : Char} {r : List Char} :
    HostElemG O c q (d :: r) ↔ HostElemG O c q [] ∧ ElemFollowChar O c d := by
  constructor
  · intro h
    refine ⟨HostElemG.trunc O c q [] (d :: r) h, ?_⟩
    obtain ⟨c₁, w', rfl, hq, hw'⟩ := h
    refine ⟨hw'.stopAt d rfl, ?_⟩
    intro hend
    cases hq with
    | @mk n b c₂ a _ hb hn hd =>
      obtain ⟨t, w, rfl, hi, hw⟩ := hd
      by_cases hww : w ++ w' = []
      · simp only [List.append_eq_nil_iff] at hww
        obtain ⟨rfl, rfl⟩ := hww
        cases hdc : hostChar O d
        · rfl
        · exact absurd hdc (hi.stop d rfl)
      · exfalso
        rw [show b ++ (t ++ w) ++ w' = (b ++ t) ++ (w ++ w') by simp,
          endsHost_append hww] at hend
        by_cases hw'n : w' = []
        · subst hw'n
          simp only [List.append_nil] at hend
          exact hw.not_endsHost hO hend
        · rw [endsHost_append hw'n] at hend
          exact hw'.not_endsHost hO hend
  · rintro ⟨h, hd1, hd2⟩
    obtain ⟨c₁, w', rfl, hq, hw'⟩ := h
    cases hq with
    | @mk n b c₂ a _ hb hn hd =>
      obtain ⟨t, w, rfl, hi, hw⟩ := hd
      have ht := hi.ne
      have he : ((t ++ w) ++ (w' ++ [])).head? = ((t ++ w) ++ (w' ++ d :: r)).head? :=
        head_append_eq (.inl (by simp [ht]))
      refine ⟨b ++ (t ++ w), w', rfl, .mk (hb.of_head he) (hn.of_head he) ⟨t, w, rfl, ?_, ?_⟩,
        hw'.replace (NextNot.cons_iff.mpr hd1)⟩
      · refine hi.replace ?_
        by_cases hww : w ++ w' = []
        · simp only [List.append_eq_nil_iff] at hww
          obtain ⟨rfl, rfl⟩ := hww
          have hend : EndsHost O (b ++ (t ++ []) ++ []) := by
            simp only [List.append_nil]
            rw [endsHost_append ht]
            obtain ⟨x, hx⟩ : ∃ x, t.getLast? = some x := by
              cases h : t.getLast? with
              | none => exact absurd (List.getLast?_eq_none_iff.mp h) ht
              | some x => exact ⟨x, rfl⟩
            exact ⟨x, hx, hi.chars x (List.mem_of_getLast? hx)⟩
          simp only [List.nil_append]
          exact NextNot.cons_iff.mpr (by rw [hd2 hend]; simp)
        · rw [← List.append_assoc]
          by_cases hwn : w = []
          · subst hwn
            simp only [List.nil_append] at hww ⊢
            exact NextNot.trunc (y := d :: r) (by
              have := hw'.head_not_hostChar hO
              intro x e; exact this x (by
                cases w' with
                | nil => exact absurd rfl hww
                | cons y ys => simpa using e))
          · intro x e
            exact hw.head_not_hostChar hO x (by
              cases w with
              | nil => exact absurd rfl hwn
              | cons y ys => simpa using e)
      · by_cases hw'n : w' = []
        · subst hw'n; exact hw.replace (NextNot.cons_iff.mpr hd1)
        · exact hw.of_head (head_append_eq (.inl hw'n))

/-! ## The list -/

/-- The condition on the next character `d` after a host list `c`. -/
def ListFollowChar (O : CharOracle) (c : List Char) (d : Char) : Prop :=
  d ≠ ',' ∧ ElemFollowChar O c d

theorem endsHost_of_tail {O : CharOracle} {x c₀ c'' : List Char} (hc₀ : c₀ ≠ []) :
    EndsHost O (x ++ c₀ ++ c'') ↔ (if c'' = [] then EndsHost O c₀ else EndsHost O c'') := by
  split
  · rename_i h; subst h; rw [List.append_nil, endsHost_append hc₀]
  · rename_i h; rw [endsHost_append h]

theorem hostTail_cons_iff {O : CharOracle} (hO : HostOracle O) {c : List Char}
    {qs : SpecList Hostname} {d : Char} {r : List Char} :
    ListTail (QualG (HostItemG O)) ',' c qs (d :: r) ↔
      ListTail (QualG (HostItemG O)) ',' c qs [] ∧ d ≠ ',' ∧
        (c ≠ [] → ElemFollowChar O c d) := by
  constructor
  · intro h
    generalize e : d :: r = R at h
    induction h with
    | nil hn =>
      subst e
      exact ⟨.nil (NextNot.nil _), (NextNot.cons_iff (P := (· = ','))).mp hn,
        fun h => absurd rfl h⟩
    | @cons w c₀ q c'' qs' rest hw he ht ih =>
      subst e
      obtain ⟨ht', hsep, hfol⟩ := ih rfl
      have hne := HostElemG.ne_nil he
      have hw' : Ws w (c₀ ++ c'' ++ []) :=
        hw.of_head (head_append_eq (.inl (by simp [hne])))
      refine ⟨?_, hsep, fun _ => ?_⟩
      · by_cases hc'' : c'' = []
        · subst hc''
          have he' := (hostElem_cons_iff hO).mp he
          exact .cons hw' he'.1 ht'
        · exact .cons hw' (HostElemG.headOnly O _ _ _ _ (head_append_eq (.inl hc'')) he) ht'
      · by_cases hc'' : c'' = []
        · subst hc''
          obtain ⟨-, hd1, hd2⟩ := (hostElem_cons_iff hO).mp he
          refine ⟨hd1, fun hend => hd2 ?_⟩
          have := (endsHost_of_tail (x := ',' :: w) (c'' := []) hne).mp hend
          simpa using this
        · obtain ⟨hd1, hd2⟩ := hfol hc''
          refine ⟨hd1, fun hend => hd2 ?_⟩
          have := (endsHost_of_tail (x := ',' :: w) (c'' := c'') hne).mp hend
          simpa [hc''] using this
  · rintro ⟨h, hsep, hfol⟩
    generalize e : ([] : List Char) = R at h
    induction h with
    | nil _ => exact .nil (NextNot.cons_iff.mpr hsep)
    | @cons w c₀ q c'' qs' rest hw he ht ih =>
      subst e
      have hne := HostElemG.ne_nil he
      have hall : ',' :: w ++ c₀ ++ c'' ≠ [] := by simp
      obtain ⟨hd1, hd2⟩ := hfol hall
      have hw' : Ws w (c₀ ++ c'' ++ d :: r) :=
        hw.of_head (head_append_eq (.inl (by simp [hne])))
      by_cases hc'' : c'' = []
      · subst hc''
        have he' : HostElemG O c₀ q (d :: r) := by
          refine (hostElem_cons_iff hO).mpr ⟨he, hd1, fun hend => hd2 ?_⟩
          exact (endsHost_of_tail (x := ',' :: w) (c'' := []) hne).mpr (by simpa using hend)
        have ht' : ListTail (QualG (HostItemG O)) ',' [] qs' (d :: r) :=
          ih (fun h => absurd rfl h) rfl
        exact .cons hw' he' ht'
      · have he' : HostElemG O c₀ q (c'' ++ d :: r) :=
          HostElemG.headOnly O _ _ _ _ (head_append_eq (.inl hc'')) he
        have ht' : ListTail (QualG (HostItemG O)) ',' c'' qs' (d :: r) := by
          refine ih (fun _ => ⟨hd1, fun hend => hd2 ?_⟩) rfl
          exact (endsHost_of_tail (x := ',' :: w) (c'' := c'') hne).mpr (by simpa [hc''] using hend)
        exact .cons hw' he' ht'

/-- The follow condition of a host list on its next character. -/
theorem hostList_cons_iff {O : CharOracle} (hO : HostOracle O) {c : List Char}
    {a : SpecList Hostname} {d : Char} {r : List Char} :
    HostListG O c a (d :: r) ↔ HostListG O c a [] ∧ ListFollowChar O c d := by
  rw [HostListG_eq]
  constructor
  · intro h
    cases h with
    | @mk c₀ q c' qs _ he ht hcount =>
      obtain ⟨ht', hsep, hfol⟩ := (hostTail_cons_iff hO).mp ht
      have hne := HostElemG.ne_nil he
      by_cases hc' : c' = []
      · subst hc'
        obtain ⟨he', hd⟩ := (hostElem_cons_iff hO).mp he
        refine ⟨.mk he' ht' hcount, hsep, ?_⟩
        simpa using hd
      · refine ⟨.mk (HostElemG.headOnly O _ _ _ _ (head_append_eq (.inl hc')) he) ht' hcount,
          hsep, ?_⟩
        obtain ⟨hd1, hd2⟩ := hfol hc'
        exact ⟨hd1, fun hend => hd2 ((endsHost_append hc').mp hend)⟩
  · rintro ⟨h, hsep, hd1, hd2⟩
    cases h with
    | @mk c₀ q c' qs _ he ht hcount =>
      have hne := HostElemG.ne_nil he
      by_cases hc' : c' = []
      · subst hc'
        have ht' := (hostTail_cons_iff hO (r := r)).mpr ⟨ht, hsep, fun h => absurd rfl h⟩
        have he' : HostElemG O c₀ q (d :: r) :=
          (hostElem_cons_iff hO).mpr ⟨he, hd1, fun hend => hd2 (by simpa using hend)⟩
        exact .mk he' ht' hcount
      · have ht' := (hostTail_cons_iff hO (r := r)).mpr
          ⟨ht, hsep, fun _ => ⟨hd1, fun hend => hd2 ((endsHost_append hc').mpr hend)⟩⟩
        exact .mk (HostElemG.headOnly O _ _ _ _ (head_append_eq (.inl hc')) he) ht' hcount

/-- **What may follow a host list** (exact, under `HostOracle`): the derivation of `a` from
`c` admits the right context `rest` iff it admits the end of the input and the next character,
if any, is not `,`, not a blank, not `\`, and not a host-name character when `c` ends with
one. -/
theorem hostList_follow_iff {O : CharOracle} (hO : HostOracle O) {c : List Char}
    {a : SpecList Hostname} {rest : List Char} :
    HostListG O c a rest ↔
      HostListG O c a [] ∧ ∀ d, rest.head? = some d → ListFollowChar O c d := by
  cases rest with
  | nil => simp
  | cons d r =>
    rw [hostList_cons_iff hO]
    simp

end SudoersSpec.Grammar
