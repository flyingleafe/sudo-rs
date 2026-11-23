import SudoersSpec.Grammar.RoundTrip

/-!
# Non-vacuity of the grammar theorems

Kernel-checked: derivations built from the constructors, each theorem applied to a concrete
input, the hypothesis `HostOracle` satisfied by the test oracle `CharOracle.latin1`, a token on
which PT2 fails, and texts without a derivation (negative controls).
-/

namespace SudoersSpec.Grammar.Examples

open SudoersSpec.Syntax
open SudoersSpec.Grammar

/-- The oracle of the examples. -/
abbrev O : CharOracle := CharOracle.latin1

theorem u32_le (a b : UInt32) : a ≤ b ↔ a.toNat ≤ b.toNat := UInt32.le_iff_toNat_le

theorem u32_beq (a b : UInt32) : (a == b) = decide (a.toNat = b.toNat) := by
  by_cases h : a = b
  · subst h; simp
  · have : a.toNat ≠ b.toNat := fun e => h (UInt32.toNat_inj.mp e)
    simp [h, this]

/-- The hypothesis of PT5 holds for the test oracle (the Rust tables on Latin-1). -/
theorem hostOracle_latin1 : HostOracle CharOracle.latin1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro c h
    simp only [CharOracle.latin1, isAsciiUppercase, char_le_iff, u32_le, Bool.or_eq_left_iff_imp,
      Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
    intro h2; simp at h h2; omega
  · intro c h
    simp only [CharOracle.latin1, asciiWhiteSpace, u32_le, u32_beq]
    simp at h ⊢
    have h1 : c.toNat ≠ 133 := by omega
    have h2 : c.toNat ≠ 160 := by omega
    simp [h1, h2]
  · intro c h
    simp only [CharOracle.latin1, isAsciiUppercase, char_le_iff, u32_le, u32_beq] at h ⊢
    simp at h ⊢
    omega

/-! ## Derivations built from the constructors -/

/-- Whitespace: a blank, a line continuation, a tab, then `=`. -/
example : Ws [' ', '\\', '\n', '\t'] ['='] :=
  Ws.cont (bs := [' ']) (by decide) (Ws.stop (by decide) (by decide))

/-- No whitespace derivation stops in front of a blank or a backslash. -/
example : ¬ Ws [' '] [' '] := fun h => h.stopAt ' ' rfl (.inl rfl)

/-- `web1` is a host item before `,`. -/
example : HostItemG O "web1".toList (.only "web1") [','] where
  ne := by decide
  chars := by decide
  len := by decide
  stop := by decide
  val := by
    have h := MetaHostVal.host (O := O) (raw := "web1".toList) (by decide) (by decide)
    exact h

/-- `SERVERS` is an alias reference. -/
example : HostItemG O "SERVERS".toList (.alias "SERVERS") [] where
  ne := by decide
  chars := by decide
  len := by decide
  stop := NextNot.nil _
  val := by
    have h := MetaHostVal.alias (O := O) (raw := "SERVERS".toList) (by decide) (by decide)
    exact h

/-- `!!ALL`: two negations give `allow`. -/
example : QualG (HostItemG O) "!!ALL".toList (.allow .all) [] := by
  have hitem : HostItemG O "ALL".toList .all [] :=
    ⟨by decide, by decide, by decide, NextNot.nil _, .all (by decide)⟩
  have := QualG.mk (G := HostItemG O) (n := 2) (b := ['!', '!']) (c := "ALL".toList) (a := .all)
    (rest := []) (.cons (w := []) (b := ['!']) (Ws.nil_iff.mpr (by decide))
      (.cons (w := []) (b := []) (Ws.nil_iff.mpr (by decide)) .nil)) (by decide)
    ⟨"ALL".toList, [], by decide, hitem, Ws.nil_iff.mpr (by decide)⟩
  exact this

/-! ## The theorems on concrete inputs -/

/-- A list with every kind of item, its text and its derivation. -/
def sample : SpecList Hostname := [.allow (.only "web1"), .forbid (.alias "DB"), .allow .all]

example : printHostList sample = "web1, !DB, ALL".toList := by decide

theorem sample_printable : Printable O sample := by
  refine ⟨by decide, by decide, ?_⟩
  intro q hq
  simp only [sample, List.mem_cons, List.mem_nil_iff, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨by decide, by decide, by decide, by decide, by decide⟩
  · exact ⟨by decide, by decide, by decide⟩
  · trivial

theorem sample_follow : PrintFollow O "= ALL\n".toList :=
  NextNot.cons_iff.mpr (by decide)

theorem sample_derives : HostListG O "web1, !DB, ALL".toList sample "= ALL\n".toList := by
  have h := print_derives hostOracle_latin1 sample_printable sample_follow
  rwa [show printHostList sample = "web1, !DB, ALL".toList by decide] at h

/-- PT4 on the sample: the parser returns the list, leaves `= ALL⏎`, at column 15. -/
example : (specListHostname O Descriptions.release).run
    ⟨"web1, !DB, ALL".toList ++ "= ALL\n".toList, 1, 1⟩ =
      (.ok sample, ⟨"= ALL\n".toList, 1, 15⟩) := by
  rw [specListHostname_complete O _ sample_derives 1 1]; rfl

/-- The same run, evaluated by the kernel without the theorem. -/
example : (specListHostname O Descriptions.release).run (Stream.ofString "web1, !DB, ALL= ALL\n") =
    (.ok sample, ⟨"= ALL\n".toList, 1, 15⟩) := by decide

/-- PT5 on the sample. -/
example : (specListHostname O Descriptions.test).run
    ⟨printHostList sample ++ "= ALL\n".toList, 3, 7⟩ =
      (.ok sample, ⟨"= ALL\n".toList, (posAfter (printHostList sample) (3, 7)).1,
        (posAfter (printHostList sample) (3, 7)).2⟩) :=
  specListHostname_roundTrip O hostOracle_latin1 _ sample_printable sample_follow 3 7

/-- PT4 corollary on the sample: no other value is derivable from its text. -/
example (a : SpecList Hostname) (h : Derives (HostListG O) "web1, !DB, ALL".toList a) :
    a = sample :=
  hostList_derives_unique O h ⟨_, sample_derives⟩

/-- A run with blanks, a line continuation, `!!` and an uppercase non-ASCII letter (accepted
by `Meta<Hostname>`, not by `Hostname`). -/
theorem run_cont : (specListHostname O Descriptions.release).run
    (Stream.ofString "a ,\\\n !! Éb\t=") =
      (.ok [.allow (.only "a"), .allow (.only "Éb")], ⟨"=".toList, 2, 8⟩) := by decide

/-- PT3 on that run: the consumed characters derive the list. -/
example : HostListG O "a ,\\\n !! Éb\t".toList [.allow (.only "a"), .allow (.only "Éb")]
    "=".toList := by
  obtain ⟨c, hc, hd, -⟩ := specListHostname_sound O _ run_cont
  have hc0 : "a ,\\\n !! Éb\t=".toList = c ++ "=".toList := hc
  have e : "a ,\\\n !! Éb\t=".toList = "a ,\\\n !! Éb\t".toList ++ "=".toList := by decide
  rw [e] at hc0
  have := List.append_cancel_right hc0
  subst this; exact hd

/-- PT2 on a rejected input: `=` cannot start a host list, and nothing is consumed. -/
example : (specListHostname O Descriptions.release).run (Stream.ofString "=x") =
    (.error .reject, Stream.ofString "=x") := by decide

example (s' : Stream)
    (h : (specListHostname O Descriptions.release).run (Stream.ofString "=x") = (.error .reject, s')) :
    s' = Stream.ofString "=x" :=
  specListHostname_rejectPure O _ _ _ h

/-! ## PT2 fails for tokens with escapes -/

/-- A token class with escapes in which `\` newline rejects after consuming: newline is not
escaped, and `\` and `' '` are not in the class (as the first character of `Username`). -/
def escTok : TokenSpec String where
  construct s := .ok (String.ofList s)
  accept := isAsciiAlphanumeric
  allowEscape := true
  escaped c := c == '\\' || c == ' '

theorem escTok_rejects : EscRejects escTok escTok.accept1st := by
  unfold EscRejects; decide

/-- The counterexample: `\` newline is consumed and the token rejects. -/
example : (token escTok).run (Stream.ofString "\\\nab") = (.error .reject, ⟨"ab".toList, 2, 1⟩) := by
  decide

theorem escTok_not_rejectPure : ¬ RejectPure (token escTok) :=
  fun h => (token_rejectPure_iff escTok).mp h escTok_rejects

/-- The failure reaches every production that starts with such a token. -/
example : (parseList ',' 127 "elem" (qualified "elem" (token escTok))).run
    (Stream.ofString "\\\nab") = (.error .reject, ⟨"ab".toList, 2, 1⟩) := by decide

/-! ## Negative controls: texts without a derivation -/

theorem no_derivation {c : List Char}
    (hc : ((specListHostname O Descriptions.release).run ⟨c, 1, 1⟩).1.isOk = false)
    (a : SpecList Hostname) (rest : List Char) : ¬ HostListG O c a rest := by
  intro h
  have h0 : HostListG O c a [] := HostListG.trunc O c a [] rest h
  have := specListHostname_complete O Descriptions.release h0 1 1
  rw [List.append_nil] at this
  rw [this] at hc
  cases hc

/-- An IPv4-like name is not a host name. -/
example (a : SpecList Hostname) (rest : List Char) : ¬ HostListG O "1.2.3.4".toList a rest :=
  no_derivation (by decide) a rest

/-- Neither is `123` (one numeric part). -/
example (a : SpecList Hostname) (rest : List Char) : ¬ HostListG O "123".toList a rest :=
  no_derivation (by decide) a rest

/-- A list does not end with a separator. -/
example (a : SpecList Hostname) (rest : List Char) : ¬ HostListG O "a, ".toList a rest :=
  no_derivation (by decide) a rest

/-- The empty text derives nothing. -/
example (a : SpecList Hostname) (rest : List Char) : ¬ HostListG O [] a rest :=
  no_derivation (by decide) a rest

/-- A `\` not followed by a newline ends no whitespace. -/
example (a : SpecList Hostname) (rest : List Char) : ¬ HostListG O "a \\x".toList a rest :=
  no_derivation (by decide) a rest

end SudoersSpec.Grammar.Examples
