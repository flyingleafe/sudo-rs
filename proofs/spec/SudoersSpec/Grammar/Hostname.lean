import SudoersSpec.Grammar.IPv4

/-!
# `SpecList<Hostname>` (`Host_List`): grammar and PT2 to PT4

The instance of the generic layer for host lists:

```
Host_List ::= Host (',' W Host)*                      -- ListG, at most 127 items, ends before a non-','
Host      ::= ('!' W)* Item W                         -- QualG: odd number of '!' = forbid
Item      ::= hostChar+                               -- HostItemG, maximal, length limit
              classified: ALL | alias name | host name (MetaHostVal)
```

with `W` the trailing whitespace of `Lexical.lean` (each `Host` is followed by its `W`, and
`parse_list` adds a second, always empty, `W`).
-/

namespace SudoersSpec.Grammar

open SudoersSpec.Syntax
open SudoersSpec.Syntax.Parser

/-- The token `Meta<Hostname>`. -/
abbrev metaHostToken (O : CharOracle) : TokenSpec (Meta Hostname) :=
  metaToken O (hostnameToken O)

/-- The characters of a `Meta<Hostname>` token, first and later ones alike: ASCII letters and
digits, `.`, `-`, `_` (`Hostname::accept`), and every character with `char::is_uppercase`
(added by `Meta<T>`). -/
def hostChar (O : CharOracle) (c : Char) : Bool :=
  Hostname.accept c || O.isUppercase c

/-- An alias name (`NAME ::= [A-Z][A-Z0-9_]*`, the test in `Meta::construct`). -/
def AliasShape (n : List Char) : Prop :=
  ∃ x xs, n = x :: xs ∧ isAsciiUppercase x = true ∧ ∀ y ∈ xs, AliasName.accept y = true

theorem aliasShape_iff (n : List Char) :
    AliasShape n ↔ (startsWithPred n AliasName.accept1st && (n.drop 1).all AliasName.accept) = true := by
  cases n with
  | nil => simp [AliasShape, startsWithPred]
  | cons x xs =>
    simp only [AliasShape, startsWithPred, AliasName.accept1st, List.drop_one, List.tail_cons,
      Bool.and_eq_true, List.all_eq_true, List.cons.injEq]
    constructor
    · rintro ⟨_, _, ⟨rfl, rfl⟩, h1, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨x, xs, ⟨rfl, rfl⟩, h1, h2⟩

instance (n : List Char) : Decidable (AliasShape n) := decidable_of_iff _ (aliasShape_iff n).symm

theorem aliasShape_ALL : AliasShape "ALL".toList := by decide

/-! ## Standalone `AliasName` and `Hostname` tokens -/

/-- The `NAME` token used in a declaration. Reservation of `ALL` is a check of the
enclosing declaration; the standalone token itself can produce `"ALL"`. -/
structure AliasNameG (c : List Char) (a : String) (rest : List Char) : Prop where
  shape : AliasShape c
  len : utf8Len c.dropLast < 255
  stop : NextNot (fun d => AliasName.accept d = true) rest
  value : a = String.ofList c

/-- The standalone `Hostname` token, without the wider `Meta<Hostname>` character class
or its `ALL` and alias classification. -/
structure HostnameG (O : CharOracle) (c : List Char) (a : Hostname) (rest : List Char) :
    Prop where
  ne : c ≠ []
  chars : ∀ x ∈ c, Hostname.accept x = true
  len : utf8Len c.dropLast < 255
  stop : NextNot (fun d => Hostname.accept d = true) rest
  notIPv4 : ¬ IPv4Like O c
  value : a = String.ofList c

private theorem nameLength {x : Char} {xs : List Char}
    (h : xs = [] ∨ utf8Len (x :: xs).dropLast < 255) :
    utf8Len (x :: xs).dropLast < 255 := by
  rcases h with rfl | h
  · show 0 < 255; decide
  · exact h

theorem tokenG_aliasName_iff {c : List Char} {a : String} {rest : List Char} :
    TokenG aliasNameToken c a rest ↔ AliasNameG c a rest := by
  rw [tokenG_noEsc (rfl : aliasNameToken.allowEscape = false)]
  constructor
  · rintro ⟨x, xs, rfl, hx, hxs, hs, hl, hv⟩
    exact ⟨⟨x, xs, rfl, hx, hxs⟩, nameLength hl, hs, (Except.ok.inj hv).symm⟩
  · rintro ⟨⟨x, xs, rfl, hx, hxs⟩, hl, hs, rfl⟩
    exact ⟨x, xs, rfl, hx, hxs, hs, .inr hl, rfl⟩

theorem tokenG_hostname_iff (O : CharOracle) {c : List Char} {a : Hostname} {rest : List Char} :
    TokenG (hostnameToken O) c a rest ↔ HostnameG O c a rest := by
  rw [tokenG_noEsc (rfl : (hostnameToken O).allowEscape = false)]
  have construct {r : List Char} :
      Hostname.construct O r = .ok a ↔ ¬ IPv4Like O r ∧ a = String.ofList r := by
    unfold Hostname.construct
    cases hb : Hostname.looksLikeIPv4 O r
    · have hn := mt (looksLikeIPv4_iff O r).mpr (by simp [hb])
      simp [hn, eq_comm]
    · have hi := (looksLikeIPv4_iff O r).mp hb
      simp [hi]
  constructor
  · rintro ⟨x, xs, rfl, hx, hxs, hs, hl, hv⟩
    obtain ⟨hi, hv⟩ := construct.mp hv
    refine ⟨by simp, ?_, nameLength hl, hs, hi, hv⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hx
    · exact hxs y hy
  · rintro ⟨hne, hc, hl, hs, hi, hv⟩
    cases c with
    | nil => exact absurd rfl hne
    | cons x xs =>
      exact ⟨x, xs, rfl, hc x (by simp), fun y hy => hc y (List.mem_cons_of_mem _ hy),
        hs, .inr hl, construct.mpr ⟨hi, hv⟩⟩

theorem aliasName_rejectPure : RejectPure (token aliasNameToken) :=
  token_rejectPure _ (fun h => by have := h.1; cases this)

theorem aliasName_sound : Sound (token aliasNameToken) AliasNameG :=
  (token_sound _).mono fun _ _ _ h => tokenG_aliasName_iff.mp h

theorem aliasName_complete : Complete (token aliasNameToken) AliasNameG :=
  (token_complete _).mono fun _ _ _ h => tokenG_aliasName_iff.mpr h

theorem hostname_rejectPure (O : CharOracle) : RejectPure (token (hostnameToken O)) :=
  token_rejectPure _ (fun h => by have := h.1; cases this)

theorem hostname_sound (O : CharOracle) : Sound (token (hostnameToken O)) (HostnameG O) :=
  (token_sound _).mono fun _ _ _ h => (tokenG_hostname_iff O).mp h

theorem hostname_complete (O : CharOracle) : Complete (token (hostnameToken O)) (HostnameG O) :=
  (token_complete _).mono fun _ _ _ h => (tokenG_hostname_iff O).mpr h

/-! ## `Meta<Hostname>` -/

/-- The classification of a `Meta<Hostname>` token text `raw` (`Meta::construct`). The decision
between `ALL`, an alias and a host name is made on `trimEnd O raw` (the text without trailing
`char::is_whitespace` characters); a host name is the raw text, and must not be IPv4-like. -/
inductive MetaHostVal (O : CharOracle) : List Char → Meta Hostname → Prop
  | all {raw : List Char} : trimEnd O raw = "ALL".toList → MetaHostVal O raw .all
  | alias {raw : List Char} : trimEnd O raw ≠ "ALL".toList → AliasShape (trimEnd O raw) →
      MetaHostVal O raw (.alias (String.ofList (trimEnd O raw)))
  | host {raw : List Char} : ¬ AliasShape (trimEnd O raw) → ¬ IPv4Like O raw →
      MetaHostVal O raw (.only (String.ofList raw))

theorem metaConstruct_iff (O : CharOracle) (raw : List Char) (a : Meta Hostname) :
    Meta.construct O (hostnameToken O) raw = .ok a ↔ MetaHostVal O raw a := by
  have hall := aliasShape_ALL
  simp only [Meta.construct, hostnameToken, Hostname.construct]
  by_cases h1 : trimEnd O raw = "ALL".toList
  · simp only [h1, beq_self_eq_true, ite_true, Except.ok.injEq]
    constructor
    · rintro rfl; exact .all h1
    · intro h
      cases h with
      | all _ => rfl
      | alias h2 _ => exact absurd h1 h2
      | host h2 _ => rw [h1] at h2; exact absurd hall h2
  · have hb : (trimEnd O raw == "ALL".toList) = false := by simpa using h1
    simp only [hb, Bool.false_eq_true, ite_false]
    by_cases h2 : AliasShape (trimEnd O raw)
    · have h2' := (aliasShape_iff _).mp h2
      simp only [h2', ite_true, Except.ok.injEq]
      constructor
      · rintro rfl; exact .alias h1 h2
      · intro h
        cases h with
        | all h => exact absurd h h1
        | alias _ _ => rfl
        | host h3 _ => exact absurd h2 h3
    · have h2' : (startsWithPred (trimEnd O raw) AliasName.accept1st &&
          ((trimEnd O raw).drop 1).all AliasName.accept) = false := by
        simpa using (mt (aliasShape_iff _).mpr h2)
      simp only [h2', Bool.false_eq_true, ite_false]
      by_cases h3 : IPv4Like O raw
      · have h3' := (looksLikeIPv4_iff O raw).mpr h3
        simp only [h3', ite_true]
        constructor
        · intro h; cases h
        · intro h
          cases h with
          | all h => exact absurd h h1
          | alias _ h => exact absurd h h2
          | host _ h => exact absurd h3 h
      · have h3' : Hostname.looksLikeIPv4 O raw = false := by
          simpa using (mt (looksLikeIPv4_iff O raw).mp h3)
        simp only [h3', Bool.false_eq_true, ite_false, Except.ok.injEq]
        constructor
        · rintro rfl; exact .host h2 h3
        · intro h
          cases h with
          | all h => exact absurd h h1
          | alias _ h => exact absurd h h2
          | host _ _ => rfl

/-- A `Meta<Hostname>` item (`metaHostname`): host-name characters, maximal (the next character
is not one), at most 255 bytes before the last character (the check of the token loop), and
classified by `MetaHostVal`. -/
structure HostItemG (O : CharOracle) (c : List Char) (a : Meta Hostname) (rest : List Char) :
    Prop where
  ne : c ≠ []
  chars : ∀ x ∈ c, hostChar O x = true
  len : utf8Len c.dropLast < 255
  stop : NextNot (fun d => hostChar O d = true) rest
  val : MetaHostVal O c a

theorem tokenG_metaHost_iff (O : CharOracle) {c : List Char} {a : Meta Hostname}
    {rest : List Char} : TokenG (metaHostToken O) c a rest ↔ HostItemG O c a rest := by
  rw [tokenG_noEsc (rfl : (metaHostToken O).allowEscape = false)]
  constructor
  · rintro ⟨x, xs, rfl, h1, hall, hn, hl, hc⟩
    refine ⟨by simp, ?_, nameLength hl, hn, (metaConstruct_iff O _ a).mp hc⟩
    · intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact h1
      · exact hall y hy
  · rintro ⟨hne, hall, hl, hn, hv⟩
    obtain ⟨x, xs, rfl⟩ : ∃ x xs, c = x :: xs := by
      cases c with
      | nil => exact absurd rfl hne
      | cons x xs => exact ⟨x, xs, rfl⟩
    exact ⟨x, xs, rfl, hall x (by simp), fun y hy => hall y (List.mem_cons_of_mem _ hy), hn,
      .inr hl, (metaConstruct_iff O _ a).mpr hv⟩

theorem HostItemG.trunc (O : CharOracle) : Trunc (HostItemG O) := by
  rintro c a x y ⟨h1, h2, h3, h4, h5⟩
  exact ⟨h1, h2, h3, h4.trunc, h5⟩

/-! ## `Meta<Hostname>`: PT2 to PT4 -/

theorem metaHostname_eq (O : CharOracle) : metaHostname O = token (metaHostToken O) := rfl

/-- PT3 for `Meta<Hostname>`. -/
theorem metaHostname_sound (O : CharOracle) : Sound (metaHostname O) (HostItemG O) :=
  (token_sound (metaHostToken O)).mono fun _ _ _ h => (tokenG_metaHost_iff O).mp h

/-- PT4 for `Meta<Hostname>`. -/
theorem metaHostname_complete (O : CharOracle) : Complete (metaHostname O) (HostItemG O) :=
  (token_complete (metaHostToken O)).mono fun _ _ _ h => (tokenG_metaHost_iff O).mpr h

/-- PT2 for `Meta<Hostname>`: no escapes, so a `Reject` consumed nothing. -/
theorem metaHostname_rejectPure (O : CharOracle) : RejectPure (metaHostname O) :=
  token_rejectPure _ (fun h => by have := h.1; cases this)

/-! ## `SpecList<Hostname>`: PT2 to PT4 -/

/-- The grammar of `SpecList<Hostname>` (`Host_List`). -/
def HostListG (O : CharOracle) : Gram (SpecList Hostname) :=
  SpecListG (HostItemG O) hostnameMany

theorem HostListG_eq (O : CharOracle) : HostListG O = ListG (QualG (HostItemG O)) ',' 127 := rfl

theorem HostListG.trunc (O : CharOracle) : Trunc (HostListG O) :=
  SpecListG.trunc (HostItemG.trunc O) _

/-- **PT2** for `SpecList<Hostname>`: a `Reject` leaves the stream unchanged. -/
theorem specListHostname_rejectPure (O : CharOracle) (D : Descriptions) :
    RejectPure (specListHostname O D) :=
  fun s s' h => metaHostname_rejectPure O s s' (specList_reject h)

/-- **PT3** for `SpecList<Hostname>`: on success the consumed characters `c` derive the list,
the right context is the remaining input, and the position is the one after `c`. -/
theorem specListHostname_sound (O : CharOracle) (D : Descriptions) {s s' : Stream}
    {a : SpecList Hostname} (h : (specListHostname O D).run s = (.ok a, s')) :
    ∃ c, s.rest = c ++ s'.rest ∧ HostListG O c a s'.rest ∧ s'.getPos = posAfter c s.getPos :=
  (specList_sound (metaHostname_sound O) hostnameMany D.hostname).pos h

/-- **PT4** for `SpecList<Hostname>`: a derivation of `a` from `c` with right context `rest`
makes the parser return `a` on `c ++ rest` and leave `rest`, at the position after `c`. -/
theorem specListHostname_complete (O : CharOracle) (D : Descriptions) {c rest : List Char}
    {a : SpecList Hostname} (h : HostListG O c a rest) (line col : Nat) :
    (specListHostname O D).run ⟨c ++ rest, line, col⟩ =
      (.ok a, ⟨rest, (posAfter c (line, col)).1, (posAfter c (line, col)).2⟩) :=
  (specList_complete (metaHostname_complete O) hostnameMany D.hostname).run_eq h line col

/-- PT3 and PT4 together: the parser succeeds on `c ++ rest` leaving `rest` iff the grammar
derives the value from `c` with right context `rest`. -/
theorem specListHostname_run_ok_iff (O : CharOracle) (D : Descriptions) {c rest : List Char}
    {a : SpecList Hostname} {s : Stream} (hs : s.rest = c ++ rest) :
    (∃ s', (specListHostname O D).run s = (.ok a, s') ∧ s'.rest = rest) ↔ HostListG O c a rest :=
  run_ok_iff (specList_sound (metaHostname_sound O) hostnameMany D.hostname)
    (specList_complete (metaHostname_complete O) hostnameMany D.hostname) hs

/-- **PT4 corollary, unambiguity**: two derivations of the same input split it at the same
place and give the same list. -/
theorem hostList_unambiguous (O : CharOracle) {c c' r r' : List Char} {a a' : SpecList Hostname}
    (h1 : HostListG O c a r) (h2 : HostListG O c' a' r') (he : c ++ r = c' ++ r') :
    c = c' ∧ a = a' :=
  (specList_complete (metaHostname_complete O) hostnameMany Descriptions.release.hostname).unambiguous
    h1 h2 he

/-- **PT4 corollary, unambiguity of `Derives`**: a text derives at most one host list. -/
theorem hostList_derives_unique (O : CharOracle) {c : List Char} {a a' : SpecList Hostname}
    (h1 : Derives (HostListG O) c a) (h2 : Derives (HostListG O) c a') : a = a' :=
  (specList_complete (metaHostname_complete O) hostnameMany
    Descriptions.release.hostname).derives_unique (HostListG.trunc O) h1 h2

end SudoersSpec.Grammar
