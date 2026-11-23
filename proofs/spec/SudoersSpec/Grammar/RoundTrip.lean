import SudoersSpec.Grammar.Hostname

/-!
# PT5: printing and re-parsing `SpecList<Hostname>`

`printHostList` prints a host list with canonical spacing: items separated by `", "`, a single
`!` in front of a forbidden item, no whitespace at the ends. `Printable O a` characterises the
values it can print faithfully; `specListHostname_roundTrip` is PT5, derived from PT4 by building
the derivation of the printed text. `printable_iff_derivable` shows that `Printable` is exactly
the set of values the grammar (hence the parser) can produce.

PT5 needs three facts about the Unicode tables (`HostOracle`): the oracle agrees with ASCII on
ASCII characters for `is_uppercase` and `is_whitespace`, and no uppercase character is white
space. The parser itself is defined for every oracle; PT2 to PT4 hold for every oracle.
-/

namespace SudoersSpec.Grammar

open SudoersSpec.Syntax

/-! ## The hypothesis on the character oracle -/

theorem char_le_iff {a b : Char} : a ≤ b ↔ a.toNat ≤ b.toNat := by
  rw [Char.le_def, UInt32.le_iff_toNat_le]; rfl

/-- `char::is_whitespace` on ASCII: U+0009 to U+000D and U+0020 (Unicode `White_Space`). -/
def asciiWhiteSpace (c : Char) : Bool :=
  decide ((9 ≤ c.toNat ∧ c.toNat ≤ 13) ∨ c.toNat = 32)

/-- Facts about the Rust Unicode tables used by PT5, each true of `rustc`'s tables:
`char::is_uppercase` is `char::is_ascii_uppercase` on ASCII, `char::is_whitespace` is
`asciiWhiteSpace` on ASCII (the Rust documentation states both), and no character has both the
Unicode properties `Uppercase` and `White_Space`. -/
structure HostOracle (O : CharOracle) : Prop where
  upper_ascii : ∀ c : Char, c.toNat < 128 → O.isUppercase c = isAsciiUppercase c
  ws_ascii : ∀ c : Char, c.toNat < 128 → O.isWhitespace c = asciiWhiteSpace c
  upper_not_ws : ∀ c : Char, O.isUppercase c = true → O.isWhitespace c = false

theorem hostnameAccept_ascii {c : Char} (h : Hostname.accept c = true) :
    c.toNat < 128 ∧ asciiWhiteSpace c = false := by
  simp only [Hostname.accept, isAsciiAlphanumeric, isAsciiDigit, isAsciiUppercase,
    isAsciiLowercase, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    char_le_iff] at h
  simp only [asciiWhiteSpace, decide_eq_false_iff_not, not_or, not_and, Nat.not_le]
  rcases h with ((((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | rfl) | rfl) | rfl
  all_goals (first | decide | (simp at h1 h2; omega))

theorem HostOracle.hostChar_not_ws {O : CharOracle} (hO : HostOracle O) {c : Char}
    (h : hostChar O c = true) : O.isWhitespace c = false := by
  simp only [hostChar, Bool.or_eq_true] at h
  rcases h with h | h
  · obtain ⟨h1, h2⟩ := hostnameAccept_ascii h
    rw [hO.ws_ascii c h1, h2]
  · exact hO.upper_not_ws c h

/-- The syntax characters are not host-name characters. -/
theorem HostOracle.not_hostChar {O : CharOracle} (hO : HostOracle O) {c : Char}
    (hc : c = ' ' ∨ c = '\t' ∨ c = '\\' ∨ c = ',' ∨ c = '!') : hostChar O c = false := by
  have h128 : c.toNat < 128 := by rcases hc with rfl | rfl | rfl | rfl | rfl <;> decide
  simp only [hostChar, hO.upper_ascii c h128]
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> decide

theorem HostOracle.hostChar_ne {O : CharOracle} (hO : HostOracle O) {c : Char}
    (h : hostChar O c = true) : blank c = false ∧ c ≠ '\\' ∧ c ≠ ',' ∧ c ≠ '!' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases hb : blank c
    · rfl
    · have : c = '\t' ∨ c = ' ' := by simpa [blank] using hb
      rcases this with rfl | rfl
      · rw [hO.not_hostChar (.inr (.inl rfl))] at h; cases h
      · rw [hO.not_hostChar (.inl rfl)] at h; cases h
  · rintro rfl; rw [hO.not_hostChar (by simp)] at h; cases h
  · rintro rfl; rw [hO.not_hostChar (by simp)] at h; cases h
  · rintro rfl; rw [hO.not_hostChar (by simp)] at h; cases h

theorem dropWhile_eq_self {f : Char → Bool} {l : List Char} (h : ∀ x ∈ l, f x = false) :
    l.dropWhile f = l := by
  cases l with
  | nil => rfl
  | cons x l => simp [h x (by simp)]

/-- Under `HostOracle`, `trimEnd` does nothing to a text of host-name characters. -/
theorem HostOracle.trimEnd_eq {O : CharOracle} (hO : HostOracle O) {raw : List Char}
    (h : ∀ x ∈ raw, hostChar O x = true) : trimEnd O raw = raw := by
  unfold trimEnd
  rw [dropWhile_eq_self (fun x hx => hO.hostChar_not_ws (h x (List.mem_reverse.mp hx))),
    List.reverse_reverse]

/-- The classification of `Meta<Hostname>` without `trimEnd`, under `HostOracle`: `ALL`, an
alias name other than `ALL`, or a host name that is neither alias-shaped nor IPv4-like. -/
theorem HostOracle.metaHostVal_iff {O : CharOracle} (hO : HostOracle O) {raw : List Char}
    (h : ∀ x ∈ raw, hostChar O x = true) {a : Meta Hostname} :
    MetaHostVal O raw a ↔
      (raw = "ALL".toList ∧ a = .all) ∨
      (raw ≠ "ALL".toList ∧ AliasShape raw ∧ a = .alias (String.ofList raw)) ∨
      (¬ AliasShape raw ∧ ¬ IPv4Like O raw ∧ a = .only (String.ofList raw)) := by
  have ht := hO.trimEnd_eq h
  constructor
  · intro hv
    cases hv with
    | all h1 => exact .inl ⟨ht ▸ h1, rfl⟩
    | alias h1 h2 => rw [ht] at h1 h2 ⊢; exact .inr (.inl ⟨h1, h2, rfl⟩)
    | host h1 h2 => rw [ht] at h1; exact .inr (.inr ⟨h1, h2, rfl⟩)
  · rintro (⟨h1, rfl⟩ | ⟨h1, h2, rfl⟩ | ⟨h1, h2, rfl⟩)
    · exact .all (ht.trans h1)
    · have := MetaHostVal.alias (O := O) (raw := raw) (by rw [ht]; exact h1) (by rw [ht]; exact h2)
      rw [ht] at this; exact this
    · exact .host (by rw [ht]; exact h1) h2

/-! ## The printer -/

/-- A `Meta<Hostname>` as text. -/
def printMeta : Meta Hostname → List Char
  | .all => "ALL".toList
  | .alias n => n.toList
  | .only h => h.toList

/-- A `Spec<Hostname>` as text: `!` in front of a forbidden item. -/
def printSpec : Spec Hostname → List Char
  | .allow m => printMeta m
  | .forbid m => '!' :: printMeta m

/-- The items after the first, each preceded by `", "`. -/
def printTail : SpecList Hostname → List Char
  | [] => []
  | q :: qs => ',' :: ' ' :: printSpec q ++ printTail qs

/-- A host list as text, with canonical spacing: `a, !b, ALL`. -/
def printHostList : SpecList Hostname → List Char
  | [] => []
  | q :: qs => printSpec q ++ printTail qs

/-- The items the printer can print faithfully: `ALL`; an alias name other than `ALL`; a
non-empty host name of host-name characters that is neither alias-shaped (this includes `ALL`)
nor IPv4-like. Alias and host names take fewer than 255 bytes before their last character. -/
def PrintableMeta (O : CharOracle) : Meta Hostname → Prop
  | .all => True
  | .alias n => AliasShape n.toList ∧ n.toList ≠ "ALL".toList ∧ utf8Len n.toList.dropLast < 255
  | .only h => h.toList ≠ [] ∧ (∀ x ∈ h.toList, hostChar O x = true) ∧
      utf8Len h.toList.dropLast < 255 ∧ ¬ AliasShape h.toList ∧ ¬ IPv4Like O h.toList

/-- A printable host list: non-empty, at most 127 items (`Many::LIMIT`), every item printable. -/
def Printable (O : CharOracle) (a : SpecList Hostname) : Prop :=
  a ≠ [] ∧ a.length ≤ 127 ∧ ∀ q ∈ a, PrintableMeta O q.who

/-- The follow condition of a printed host list: the next character neither continues the last
item, nor is whitespace or `\`, nor a `,`. -/
def PrintFollow (O : CharOracle) (rest : List Char) : Prop :=
  NextNot (fun d => hostChar O d = true ∨ blank d = true ∨ d = '\\' ∨ d = ',') rest

/-! ## The derivation of a printed list -/

theorem aliasShape_hostChar (O : CharOracle) {n : List Char} (h : AliasShape n) :
    ∀ x ∈ n, hostChar O x = true := by
  obtain ⟨x, xs, rfl, h1, h2⟩ := h
  intro y hy
  simp only [List.mem_cons] at hy
  have hacc : AliasName.accept y = true := by
    rcases hy with rfl | hy
    · simp [AliasName.accept, AliasName.accept1st, h1]
    · exact h2 y hy
  simp only [AliasName.accept, AliasName.accept1st, Bool.or_eq_true, beq_iff_eq] at hacc
  simp only [hostChar, Hostname.accept, isAsciiAlphanumeric, Bool.or_eq_true, beq_iff_eq]
  rcases hacc with (h | h) | rfl
  · exact .inl (.inl (.inl (.inl (.inl (.inr h)))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl h)))))
  · exact .inl (.inr rfl)

theorem printMeta_chars (O : CharOracle) {m : Meta Hostname} (hm : PrintableMeta O m) :
    ∀ x ∈ printMeta m, hostChar O x = true := by
  cases m with
  | all =>
    have hA : Hostname.accept 'A' = true := by decide
    have hL : Hostname.accept 'L' = true := by decide
    intro x hx; simp [printMeta] at hx
    rcases hx with rfl | rfl <;> simp [hostChar, hA, hL]
  | alias n => exact aliasShape_hostChar O hm.1
  | only h => exact hm.2.1

theorem printMeta_ne (O : CharOracle) {m : Meta Hostname} (hm : PrintableMeta O m) :
    printMeta m ≠ [] := by
  cases m with
  | all => simp [printMeta]
  | alias n => obtain ⟨x, xs, h, -⟩ := hm.1; simp [printMeta, h]
  | only h => exact hm.1

theorem printMeta_item {O : CharOracle} (hO : HostOracle O) {m : Meta Hostname}
    (hm : PrintableMeta O m) {r : List Char} (hr : NextNot (fun d => hostChar O d = true) r) :
    HostItemG O (printMeta m) m r := by
  have hchars := printMeta_chars O hm
  refine ⟨printMeta_ne O hm, hchars, ?_, hr, ?_⟩
  · cases m with
    | all => decide
    | alias n => exact hm.2.2
    | only h => exact hm.2.2.1
  · apply (hO.metaHostVal_iff hchars).mpr
    cases m with
    | all => exact .inl ⟨rfl, rfl⟩
    | alias n => exact .inr (.inl ⟨hm.2.1, hm.1, by simp [printMeta]⟩)
    | only h => exact .inr (.inr ⟨hm.2.2.2.1, hm.2.2.2.2, by simp [printMeta]⟩)

/-- The follow condition of one item: it is neither continued nor followed by whitespace. -/
def ElemFollow (O : CharOracle) (r : List Char) : Prop :=
  NextNot (fun d => hostChar O d = true ∨ blank d = true ∨ d = '\\') r

theorem printSpec_head {O : CharOracle} (hO : HostOracle O) {q : Spec Hostname}
    (hq : PrintableMeta O q.who) (r : List Char) :
    NextNot (fun d => blank d = true ∨ d = '\\') (printSpec q ++ r) ∧
      NextNot (· = ',') (printSpec q ++ r) := by
  have key : ∀ m, PrintableMeta O m → ∀ r,
      NextNot (fun d => blank d = true ∨ d = '\\' ∨ d = ',' ∨ d = '!') (printMeta m ++ r) := by
    intro m hm r
    obtain ⟨x, xs, hx⟩ : ∃ x xs, printMeta m = x :: xs := by
      cases h : printMeta m with
      | nil => exact absurd h (printMeta_ne O hm)
      | cons x xs => exact ⟨x, xs, rfl⟩
    have hc := printMeta_chars O hm x (by rw [hx]; simp)
    obtain ⟨h1, h2, h3, h4⟩ := hO.hostChar_ne hc
    rw [hx]
    apply NextNot.cons_iff.mpr
    rintro (h | h | h | h)
    · rw [h1] at h; cases h
    · exact h2 h
    · exact h3 h
    · exact h4 h
  cases q with
  | allow m =>
    have := key m hq r
    exact ⟨this.mono fun d h => by rcases h with h | h; exact .inl h; exact .inr (.inl h),
      this.mono fun d h => .inr (.inr (.inl h))⟩
  | forbid m =>
    refine ⟨NextNot.cons_iff.mpr ?_, NextNot.cons_iff.mpr ?_⟩
    · rintro (h | h)
      · simp [blank] at h
      · cases h
    · intro h; cases h

theorem printMeta_cons {O : CharOracle} {m : Meta Hostname} (hm : PrintableMeta O m) :
    ∃ x xs, printMeta m = x :: xs ∧ hostChar O x = true := by
  cases h : printMeta m with
  | nil => exact absurd h (printMeta_ne O hm)
  | cons x xs => exact ⟨x, xs, rfl, printMeta_chars O hm x (by rw [h]; simp)⟩

theorem printMeta_notBang {O : CharOracle} (hO : HostOracle O) {m : Meta Hostname}
    (hm : PrintableMeta O m) (r : List Char) : NextNot (· = '!') (printMeta m ++ r) := by
  obtain ⟨x, xs, hx, hc⟩ := printMeta_cons hm
  rw [hx]
  exact NextNot.cons_iff.mpr (hO.hostChar_ne hc).2.2.2

theorem printSpec_elem {O : CharOracle} (hO : HostOracle O) {q : Spec Hostname}
    (hq : PrintableMeta O q.who) {r : List Char} (hr : ElemFollow O r) :
    NontermG (QualG (HostItemG O)) (printSpec q) q r := by
  have hws : Ws [] r := Ws.nil_iff.mpr (hr.mono fun d h => .inr h)
  have hstop : NextNot (fun d => hostChar O d = true) r := hr.mono fun d h => .inl h
  have hitem : ∀ m, PrintableMeta O m →
      NontermG (HostItemG O) (printMeta m) m r :=
    fun m hm => ⟨printMeta m, [], by simp, printMeta_item hO hm hstop, hws⟩
  refine ⟨printSpec q, [], by simp, ?_, hws⟩
  rw [List.nil_append]
  cases q with
  | allow m =>
    have hq' : PrintableMeta O m := hq
    exact QualG.mk (G := HostItemG O) (n := 0) (b := []) (c := printMeta m) Bangs.nil
      (printMeta_notBang hO hq' r) (hitem m hq')
  | forbid m =>
    have hq' : PrintableMeta O m := hq
    have hb : Bangs 1 ['!'] (printMeta m ++ r) :=
      Bangs.cons (w := []) (b := []) (n := 0) (rest := printMeta m ++ r)
        (Ws.nil_iff.mpr (printSpec_head hO (q := .allow m) hq' r).1) Bangs.nil
    exact QualG.mk (G := HostItemG O) (n := 1) hb (printMeta_notBang hO hq' r) (hitem m hq')

theorem PrintFollow.elemFollow {O : CharOracle} {r : List Char} (hr : PrintFollow O r) :
    ElemFollow O r :=
  hr.mono fun _ h => h.elim .inl fun h => .inr (h.elim .inl fun h => .inr (.inl h))

theorem elemFollow_printTail {O : CharOracle} (hO : HostOracle O) {rest : List Char}
    (hr : PrintFollow O rest) : ∀ qs : SpecList Hostname, ElemFollow O (printTail qs ++ rest)
  | [] => hr.elemFollow
  | q :: qs => by
    simp only [printTail, List.cons_append]
    apply NextNot.cons_iff.mpr
    rintro (h | h | h)
    · rw [hO.not_hostChar (by simp)] at h; cases h
    · simp [blank] at h
    · cases h

theorem printTail_listTail {O : CharOracle} (hO : HostOracle O) {rest : List Char}
    (hr : PrintFollow O rest) :
    ∀ qs : SpecList Hostname, (∀ q ∈ qs, PrintableMeta O q.who) →
      ListTail (QualG (HostItemG O)) ',' (printTail qs) qs rest
  | [], _ => .nil (hr.mono fun d h => .inr (.inr (.inr h)))
  | q :: qs, h => by
    have hq := h q (by simp)
    have ih := printTail_listTail hO hr qs (fun q' h' => h q' (List.mem_cons_of_mem _ h'))
    have hws : Ws [' '] (printSpec q ++ printTail qs ++ rest) := by
      refine .stop (by simp [blank]) ?_
      rw [List.append_assoc]; exact (printSpec_head hO hq _).1
    have := ListTail.cons (sep := ',') hws
      (printSpec_elem hO hq (elemFollow_printTail hO hr qs)) ih
    simp only [printTail]
    simpa using this

/-- The printed text of a printable list derives that list, for every right context that
satisfies the follow condition. -/
theorem print_derives {O : CharOracle} (hO : HostOracle O) {a : SpecList Hostname}
    (ha : Printable O a) {rest : List Char} (hr : PrintFollow O rest) :
    HostListG O (printHostList a) a rest := by
  obtain ⟨hne, hlen, hall⟩ := ha
  cases a with
  | nil => exact absurd rfl hne
  | cons q qs =>
    have hq := hall q (by simp)
    have ht := printTail_listTail hO hr qs (fun q' h' => hall q' (List.mem_cons_of_mem _ h'))
    have hfollow := elemFollow_printTail hO hr qs
    rw [HostListG_eq]
    refine ListG.mk (printSpec_elem hO hq hfollow) ht ?_
    cases qs with
    | nil => exact .inl rfl
    | cons _ _ => right; simp at hlen ⊢; omega

/-- **PT5**: a printable host list, printed and followed by any text that does not continue
it, parses back to itself and leaves exactly that text. -/
theorem specListHostname_roundTrip (O : CharOracle) (hO : HostOracle O) (D : Descriptions)
    {a : SpecList Hostname} (ha : Printable O a) {rest : List Char} (hr : PrintFollow O rest)
    (line col : Nat) :
    (specListHostname O D).run ⟨printHostList a ++ rest, line, col⟩ =
      (.ok a, ⟨rest, (posAfter (printHostList a) (line, col)).1,
        (posAfter (printHostList a) (line, col)).2⟩) :=
  specListHostname_complete O D (print_derives hO ha hr) line col

/-! ## `Printable` is exactly what the grammar produces -/

theorem ofBangs_who (n : Nat) (a : α) : (Qualified.ofBangs n a).who = a := by
  unfold Qualified.ofBangs; split <;> rfl

theorem HostItemG.printable {O : CharOracle} (hO : HostOracle O) {c : List Char}
    {m : Meta Hostname} {r : List Char} (h : HostItemG O c m r) : PrintableMeta O m := by
  obtain ⟨hne, hchars, hlen, -, hv⟩ := h
  rcases (hO.metaHostVal_iff hchars).mp hv with ⟨-, rfl⟩ | ⟨h1, h2, rfl⟩ | ⟨h1, h2, rfl⟩
  · trivial
  · simp only [PrintableMeta, String.toList_ofList]; exact ⟨h2, h1, hlen⟩
  · simp only [PrintableMeta, String.toList_ofList]; exact ⟨hne, hchars, hlen, h1, h2⟩

theorem QualG.printable {O : CharOracle} (hO : HostOracle O) {c : List Char}
    {q : Spec Hostname} {r : List Char} (h : QualG (HostItemG O) c q r) :
    PrintableMeta O q.who := by
  cases h with
  | mk _ _ hd =>
    obtain ⟨_, _, _, hi, _⟩ := hd
    rw [ofBangs_who]; exact hi.printable hO

theorem ListTail.printable {O : CharOracle} (hO : HostOracle O) {c : List Char}
    {qs : SpecList Hostname} {r : List Char} (h : ListTail (QualG (HostItemG O)) ',' c qs r) :
    ∀ q ∈ qs, PrintableMeta O q.who := by
  induction h with
  | nil _ => simp
  | cons _ hd _ ih =>
    obtain ⟨_, _, _, hq, _⟩ := hd
    intro q' hq'
    simp only [List.mem_cons] at hq'
    rcases hq' with rfl | hq'
    · exact hq.printable hO
    · exact ih q' hq'

/-- The values of the grammar are exactly the printable lists (under `HostOracle`). -/
theorem printable_iff_derivable {O : CharOracle} (hO : HostOracle O) (a : SpecList Hostname) :
    Printable O a ↔ ∃ c rest, HostListG O c a rest := by
  constructor
  · intro ha; exact ⟨printHostList a, [], print_derives hO ha (NextNot.nil _)⟩
  · rintro ⟨c, rest, h⟩
    rw [HostListG_eq] at h
    cases h with
    | @mk c₀ q c' qs _ hd ht hcount =>
      obtain ⟨_, _, _, hq, _⟩ := hd
      refine ⟨by simp, ?_, ?_⟩
      · rcases hcount with rfl | h
        · simp
        · simp; omega
      · intro q' hq'
        simp only [List.mem_cons] at hq'
        rcases hq' with rfl | hq'
        · exact hq.printable hO
        · exact ht.printable hO q' hq'

end SudoersSpec.Grammar
