import SudoersSpec.Grammar.PermissionSurface

namespace SudoersSpec.Grammar

open SudoersSpec.Syntax

/-- The name's first character is an ordinary name character, not a punctuation marker.
The remaining character/length/value tests belong to `LiteralValue`. -/
def NameStart (s : String) : Prop :=
  ∃ d, s.toList.head? = some d ∧ Hostname.accept d = true

abbrev IdLiteral (n : Nat) : Prop :=
  n < 2^32 ∧ LiteralValue digitsU32Token (toString n).toList n

/-- Bare names in group positions use the `Username` constructor, not meta classification. -/
def RawIdentifierValue (O : Oracles) : Identifier → Prop
  | .name n => NameStart n ∧ LiteralValue (usernameToken O) n.toList n
  | .id n => IdLiteral n

/-- User and group member values fit their literal classes, constructors and byte limits.
Plain names in `Meta` positions must not be classified as all/alias. -/
def UserValue (O : Oracles) : Meta UserSpecifier → Prop
  | .all => True
  | .alias n => AliasShape n.toList ∧ LiteralValue (MetaUsernameToken O) n.toList (.alias n)
  | .only (.user (.name n)) => NameStart n ∧ LiteralValue (MetaUsernameToken O) n.toList (.only n)
  | .only (.user (.id n)) => IdLiteral n
  | .only (.group i) | .only (.nonunixGroup i) => RawIdentifierValue O i

def IdentifierValue (O : Oracles) : Meta Identifier → Prop
  | .all => True
  | .alias n => AliasShape n.toList ∧ LiteralValue (MetaUsernameToken O) n.toList (.alias n)
  | .only (.name n) => NameStart n ∧ LiteralValue (MetaUsernameToken O) n.toList (.only n)
  | .only (.id n) => IdLiteral n

private theorem aliasStart {n : String} (h : AliasShape n.toList) : NameStart n := by
  obtain ⟨d, ds, hs, hd, _⟩ := h
  exact ⟨d, by rw [hs]; rfl, by simp [Hostname.accept, isAsciiAlphanumeric, hd]⟩

private theorem startChar {s : String} {d : Char} (h : s.toList.head? = some d)
    (hb : blank d = false) (hs : d ≠ '\\') (hc : d ≠ ',') (hco : d ≠ ':') : SurfaceStart s :=
  ⟨d, h, hb, hs, hc, hco⟩

private theorem hostname_not_separator {d : Char} (hd : Hostname.accept d = true) :
    blank d = false ∧ d ≠ '\\' ∧ d ≠ ',' ∧ d ≠ ':' ∧ d ≠ '!' := by
  have h (e : d = ' ' ∨ d = '\t' ∨ d = '\\' ∨ d = ',' ∨ d = ':' ∨ d = '!') : False := by
    rcases e with rfl | rfl | rfl | rfl | rfl | rfl <;> contradiction
  refine ⟨?_, fun e => h (by simp [e]), fun e => h (by simp [e]), fun e => h (by simp [e]),
    fun e => h (by simp [e])⟩
  cases e : blank d
  · rfl
  · have hh : d = '\t' ∨ d = ' ' := by simpa [blank] using e
    exact False.elim (h (hh.elim (fun h => .inr (.inl h)) Or.inl))

theorem NameStart.surface {s : String} (h : NameStart s) : SurfaceStart s := by
  obtain ⟨d, hd, hc⟩ := h
  obtain ⟨h₁, h₂, h₃, h₄, _⟩ := hostname_not_separator hc
  exact startChar hd h₁ h₂ h₃ h₄

theorem NameStart.notBang {s : String} (h : NameStart s) (r : List Char) :
    NextNot (· = '!') (s.toList ++ r) := by
  obtain ⟨d, hd, hc⟩ := h
  intro x hx he
  rw [List.head?_append, hd] at hx
  exact (hostname_not_separator hc).2.2.2.2 ((Option.some.inj hx).trans he)

/-- Add the single canonical `!` (if any); a meta item already includes its assigned gap. -/
theorem qualifyPrinted {G : Gram α} {f : α → String} {r : List Char} {b : Bool} {m : α}
    (hs : SurfaceStart (f m)) (hn : NextNot (· = '!') ((f m).toList ++ (gap b ++ r)))
    (h : NontermG G ((f m).toList ++ gap b) m r)
    (q : Qualified α) (hq : q.who = m) :
    QualG G ((PermissionPrint.qualified f q).toList ++ gap b) q r := by
  cases q with
  | allow a =>
    change a = m at hq; subst m
    exact QualG.mk (b := []) (.nil (rest := ((f a).toList ++ gap b) ++ r))
      (by rwa [List.append_assoc]) h
  | forbid a =>
    change a = m at hq; subst m
    have hw : Ws [] (((f a).toList ++ gap b) ++ r) := by
      rw [List.append_assoc]; exact (hs.append _).1.nil
    have hb : Bangs 1 ['!'] (((f a).toList ++ gap b) ++ r) := .cons (w := []) hw .nil
    have hh := QualG.mk hb (by rwa [List.append_assoc]) h
    simp only [PermissionPrint.qualified, String.toList_append, List.append_assoc]
    exact hh

private theorem boundary_noName {O : CharOracle} (hO : PermissionLexical O) {d : Char}
    (hd : d = ' ' ∨ endMark d) :
    Username.accept O d = false ∧ O.isUppercase d = false ∧ isAsciiDigit d = false ∧ d ≠ '\\' := by
  have hdAscii : d.toNat < 128 := by
    rcases hd with rfl | hd
    · decide
    · rcases hd with rfl | rfl | rfl | rfl | rfl <;> decide
  rw [Username.accept, hO.alnum_ascii d hdAscii, hO.host.upper_ascii d hdAscii]
  rcases hd with rfl | hd
  · decide
  · rcases hd with rfl | rfl | rfl | rfl | rfl <;> decide

private theorem metaNameStop {O : Oracles} (hO : PermissionLexical O.char) {b : Bool} {r : List Char}
    (hr : Boundary b r) : EscStop (MetaUsernameToken O) (MetaUsernameToken O).accept (gap b ++ r) := by
  intro d hd ha
  obtain ⟨h₁, h₂, _, h₃⟩ := boundary_noName hO (hr.gapHead hd)
  change (Username.accept O.char d || O.char.isUppercase d) = true ∨ (true = true ∧ d = '\\') at ha
  simp [h₁, h₂, h₃] at ha

private theorem nameStop {O : Oracles} (hO : PermissionLexical O.char) {b : Bool} {r : List Char}
    (hr : Boundary b r) : EscStop (usernameToken O) (usernameToken O).accept (gap b ++ r) := by
  intro d hd ha
  obtain ⟨h₁, _, _, h₃⟩ := boundary_noName hO (hr.gapHead hd)
  change Username.accept O.char d = true ∨ (true = true ∧ d = '\\') at ha
  simp [h₁, h₃] at ha

private theorem digitsStop {O : Oracles} (hO : PermissionLexical O.char) {b : Bool} {r : List Char}
    (hr : Boundary b r) : EscStop digitsU32Token digitsU32Token.accept (gap b ++ r) := by
  intro d hd ha
  obtain ⟨_, _, h₂, _⟩ := boundary_noName hO (hr.gapHead hd)
  change isAsciiDigit d = true ∨ (false = true ∧ d = '\\') at ha
  simp [h₂] at ha

private theorem boundary_notQuote {O : Oracles} (hO : PermissionLexical O.char) {r : List Char}
    {d : Char} (hd : d = '#' ∨ d = '%') :
    EscStop (MetaUsernameToken O) (MetaUsernameToken O).accept1st (d :: r) := by
  have h : d.toNat < 128 := by rcases hd with rfl | rfl <;> decide
  apply NextNot.cons_iff.mpr
  change ¬ ((Username.accept1st O.char d || O.char.isUppercase d) = true ∨ (true = true ∧ d = '\\'))
  rw [Username.accept1st, Username.accept, hO.alnum_ascii d h, hO.host.upper_ascii d h]
  rcases hd with rfl | rfl <;> decide

private theorem metaViaWord {O : Oracles} {G : Gram α} {f : String → α} {b : Bool}
    {txt r : List Char} {m : Meta String} (hO : PermissionLexical O.char) (hr : Boundary b r)
    (hv : LiteralValue (MetaUsernameToken O) txt m) :
    MetaG O G f (txt ++ gap b) (match m with
      | .all => .all | .alias a => .alias a | .only v => .only (f v)) r := by
  have ht := hv.derives (metaNameStop hO hr)
  have h : NontermG (OptG (TokenG (MetaUsernameToken O)) (TokenRejectG (MetaUsernameToken O)))
      (txt ++ gap b) (some m) r := takeGap (.some ht) hr
  cases m
  · exact ⟨txt ++ gap b, [], some .all, by simp, h, pureG (Meta.all : Meta α) r⟩
  · rename_i v; exact ⟨txt ++ gap b, [], some (.only v), by simp, h, pureG (Meta.only (f v)) r⟩
  · rename_i n; exact ⟨txt ++ gap b, [], some (.alias n), by simp, h, pureG (Meta.alias n : Meta α) r⟩

private theorem metaViaFallback {O : Oracles} {G : Gram α} {f : String → α}
    {d : Char} {c r : List Char} {a : α} (hO : PermissionLexical O.char)
    (hd : d = '#' ∨ d = '%') (hp : G (d :: c) a r) : MetaG O G f (d :: c) (.only a) r := by
  refine ⟨[], d :: c, none, rfl, ?_, mapG hp⟩
  have hw : WsStop (d :: (c ++ r)) := by
    rcases hd with rfl | rfl <;> exact NextNot.cons_iff.mpr (by decide)
  exact nonterm (.none (.stop (boundary_notQuote hO hd))) hw

theorem idText (n : Nat) : (PermissionPrint.identifier (.id n)).toList = '#' :: (toString n).toList := by
  change ("#" ++ toString n).toList = _
  rw [String.toList_append]; rfl

theorem rawIdG {O : Oracles} (hO : PermissionLexical O.char) {i : Identifier}
    (hi : RawIdentifierValue O i) {b : Bool} {r : List Char} (hr : Boundary b r) :
    IdentifierG O ((PermissionPrint.identifier i).toList ++ gap b) i r := by
  cases i with
  | id n =>
    rw [idText, List.cons_append]
    exact seqG (MarkG.present (ch := '#')) (mapG (takeGap (hi.2.derives (digitsStop hO hr)) hr))
  | name n =>
    obtain ⟨d, hd, hname⟩ := hi.1
    have he : d ≠ '#' := by rintro rfl; contradiction
    have hn : NextNot (· = '#') ((n.toList ++ gap b) ++ r) := by
      intro x hx h
      simp only [List.append_assoc, List.head?_append, hd, Option.some_or, Option.some.injEq] at hx
      exact he (hx.trans h)
    exact ⟨[], _, false, rfl, .absent hn, mapG (takeGap (hi.2.derives (nameStop hO hr)) hr)⟩

private theorem allLiteral {O : Oracles} (hO : PermissionLexical O.char) :
    LiteralValue (MetaUsernameToken O) "ALL".toList .all := by
  have huA := hO.host.upper_ascii 'A' (by decide)
  have huL := hO.host.upper_ascii 'L' (by decide)
  have hwL := hO.host.ws_ascii 'L' (by decide)
  refine ⟨⟨by decide, ?_, ?_, by decide, by show 2 < 255; decide⟩, ?_⟩
  · intro d hd
    have e : d = 'A' := by simpa using hd.symm
    subst d
    change (Username.accept1st O.char 'A' || O.char.isUppercase 'A') = true
    rw [huA]
    simp only [Bool.or_eq_true]; exact .inr (by decide)
  · intro d hd
    have e : d = 'L' := by simpa using hd
    subst d
    change (Username.accept O.char 'L' || O.char.isUppercase 'L') = true
    rw [huL]
    simp only [Bool.or_eq_true]; exact .inr (by decide)
  · change Meta.construct O.char (usernameToken O) "ALL".toList = .ok .all
    have e : trimEnd O.char "ALL".toList = "ALL".toList := by
      change (['L', 'L', 'A'].dropWhile O.char.isWhitespace).reverse = _
      have hz : O.char.isWhitespace 'L' = false := hwL.trans (by decide)
      rw [List.dropWhile_cons_of_neg (by simp [hz])]
      rfl
    unfold Meta.construct
    rw [e]
    rfl

private theorem rawUserIdG {O : Oracles} (hO : PermissionLexical O.char) {n : Nat}
    (h : IdLiteral n) {b : Bool} {r : List Char} (hr : Boundary b r) :
    UserSpecifierG O ((PermissionPrint.user (.user (.id n))).toList ++ gap b) (.user (.id n)) r := by
  have hi := rawIdG hO (i := .id n) h hr
  rw [idText] at hi
  change UserSpecifierG O ((PermissionPrint.identifier (.id n)).toList ++ gap b) (.user (.id n)) r
  rw [idText]
  have hn (ch : Char) (hc : '#' ≠ ch) : NextNot (· = ch) (('#' :: (toString n).toList) ++ gap b ++ r) :=
    NextNot.cons_iff.mpr hc
  have hw : WsStop r := hr.1
  exact ⟨[], _, false, rfl, .absent (hn '"' (by decide)),
    [], _, false, rfl, .absent (hn '%' (by decide)),
    [], _, false, rfl, .absent (hn '+' (by decide)), mapG (nonterm hi hw)⟩

private theorem rawGroupG {O : Oracles} (hO : PermissionLexical O.char) {i : Identifier}
    (h : RawIdentifierValue O i) {b : Bool} {r : List Char} (hr : Boundary b r) (nonunix : Bool) :
    UserSpecifierG O ((PermissionPrint.user (if nonunix then .nonunixGroup i else .group i)).toList ++ gap b)
      (if nonunix then .nonunixGroup i else .group i) r := by
  have hc := nonterm (rawIdG hO h hr) hr.1
  cases nonunix with
  | true =>
    simp only [ite_true, PermissionPrint.user, String.toList_append, List.append_assoc]
    change UserSpecifierG O ('%' :: ':' :: ((PermissionPrint.identifier i).toList ++ gap b))
      (.nonunixGroup i) r
    exact ⟨[], _, false, rfl, .absent (NextNot.cons_iff.mpr (by decide)),
      ['%'], _, true, rfl, .present, [':'], _, true, rfl, .present, mapG hc⟩
  | false =>
    have hn : NextNot (· = ':') (((PermissionPrint.identifier i).toList ++ gap b) ++ r) := by
      cases i with
      | id n => rw [idText]; exact NextNot.cons_iff.mpr (by decide)
      | name n =>
        have h' := (h.1.surface.append (gap b ++ r)).2.2
        rwa [List.append_assoc]
    simp only [Bool.false_eq_true, ite_false, PermissionPrint.user, String.toList_append, List.append_assoc]
    change UserSpecifierG O ('%' :: ((PermissionPrint.identifier i).toList ++ gap b)) (.group i) r
    exact ⟨[], _, false, rfl, .absent (NextNot.cons_iff.mpr (by decide)),
      ['%'], _, true, rfl, .present, [], _, false, rfl, .absent hn, mapG hc⟩

abbrev userText := PermissionPrint.metaItem PermissionPrint.user
abbrev identText := PermissionPrint.metaItem PermissionPrint.identifier

theorem userValue_grammar {O : Oracles} (hO : PermissionLexical O.char) {m : Meta UserSpecifier}
    (hm : UserValue O m) {b : Bool} {r : List Char} (hr : Boundary b r) :
    NontermG (MetaUserG O) ((userText m).toList ++ gap b) m r := by
  apply nonterm _ hr.1
  cases m with
  | all => exact metaViaWord hO hr (allLiteral hO)
  | alias n => exact metaViaWord hO hr hm.2
  | only u =>
    cases u with
    | user i => cases i with
      | name n => exact metaViaWord hO hr hm.2
      | id n =>
        change MetaUserG O ((PermissionPrint.identifier (.id n)).toList ++ gap b) (.only (.user (.id n))) r
        rw [idText, List.cons_append]
        have hi := rawUserIdG hO hm hr
        change UserSpecifierG O ((PermissionPrint.identifier (.id n)).toList ++ gap b) _ r at hi
        rw [idText, List.cons_append] at hi
        exact metaViaFallback hO (.inl rfl) hi
    | group i =>
      change MetaUserG O ((PermissionPrint.user (.group i)).toList ++ gap b) (.only (.group i)) r
      simp only [PermissionPrint.user, String.toList_append, List.append_assoc]
      change MetaUserG O ('%' :: ((PermissionPrint.identifier i).toList ++ gap b)) (.only (.group i)) r
      apply metaViaFallback hO (.inr rfl)
      have hp := rawGroupG hO hm hr false
      simp only [Bool.false_eq_true, ite_false, PermissionPrint.user, String.toList_append,
        List.append_assoc] at hp
      exact hp
    | nonunixGroup i =>
      change MetaUserG O ((PermissionPrint.user (.nonunixGroup i)).toList ++ gap b) (.only (.nonunixGroup i)) r
      simp only [PermissionPrint.user, String.toList_append, List.append_assoc]
      change MetaUserG O ('%' :: ':' :: ((PermissionPrint.identifier i).toList ++ gap b))
        (.only (.nonunixGroup i)) r
      apply metaViaFallback hO (.inr rfl)
      have hp := rawGroupG hO hm hr true
      simp only [ite_true, PermissionPrint.user, String.toList_append, List.append_assoc] at hp
      exact hp

theorem identValue_grammar {O : Oracles} (hO : PermissionLexical O.char) {m : Meta Identifier}
    (hm : IdentifierValue O m) {b : Bool} {r : List Char} (hr : Boundary b r) :
    NontermG (MetaIdentifierG O) ((identText m).toList ++ gap b) m r := by
  apply nonterm _ hr.1
  cases m with
  | all => exact metaViaWord hO hr (allLiteral hO)
  | alias n => exact metaViaWord hO hr hm.2
  | only i => cases i with
    | name n => exact metaViaWord hO hr hm.2
    | id n =>
      change MetaIdentifierG O ((PermissionPrint.identifier (.id n)).toList ++ gap b) (.only (.id n)) r
      rw [idText, List.cons_append]
      exact metaViaFallback hO (.inl rfl) (by simpa only [idText, List.cons_append] using rawIdG hO (i := .id n) hm hr)

/-- First-character information for member renderings, before their optional `!`. -/
structure MemberStart (s : String) : Prop where
  start : SurfaceStart s
  notBang : ∀ r, NextNot (· = '!') (s.toList ++ r)

theorem NameStart.member {s : String} (h : NameStart s) : MemberStart s := ⟨h.surface, h.notBang⟩

theorem literalMember {s : String} {d : Char} (hd : s.toList.head? = some d)
    (hw : blank d = false) (hb : d ≠ '\\') (hc : d ≠ ',') (hcol : d ≠ ':') (hn : d ≠ '!') : MemberStart s := by
  refine ⟨startChar hd hw hb hc hcol, ?_⟩
  intro r x e he
  rw [List.head?_append, hd] at e
  exact hn ((Option.some.inj e).trans he)

private theorem allStart : MemberStart "ALL" :=
  literalMember (d := 'A') rfl (by decide) (by decide) (by decide) (by decide) (by decide)

theorem userValue_start {O : Oracles} {m : Meta UserSpecifier} (hm : UserValue O m) :
    MemberStart (userText m) := by
  cases m with
  | all => exact allStart
  | alias n => exact (aliasStart hm.1).member
  | only u =>
    cases u with
    | group i | nonunixGroup i =>
      exact literalMember (d := '%') (by simp [userText, PermissionPrint.metaItem, PermissionPrint.user,
        String.toList_append]) (by decide) (by decide) (by decide) (by decide) (by decide)
    | user i => cases i with
      | id n =>
        have hh : (PermissionPrint.identifier (.id n)).toList.head? = some '#' := by rw [idText]; rfl
        exact literalMember hh (by decide) (by decide) (by decide) (by decide) (by decide)
      | name n => exact hm.1.member

theorem identValue_start {O : Oracles} {m : Meta Identifier} (hm : IdentifierValue O m) :
    MemberStart (identText m) := by
  cases m with
  | all => exact allStart
  | alias n => exact (aliasStart hm.1).member
  | only i => cases i with
    | id n =>
      have hh : (PermissionPrint.identifier (.id n)).toList.head? = some '#' := by rw [idText]; rfl
      exact literalMember hh (by decide) (by decide) (by decide) (by decide) (by decide)
    | name n => exact hm.1.member

theorem memberPrinted_start {f : α → String} {q : Spec α}
    (hm : MemberStart (PermissionPrint.metaItem f q.who)) : SurfaceStart (PermissionPrint.spec f q) := by
  cases q with
  | allow _ => exact hm.start
  | forbid _ =>
    refine ⟨'!', ?_, by decide, by decide, by decide, by decide⟩
    simp [PermissionPrint.spec, PermissionPrint.qualified, String.toList_append]

theorem memberPrinted_grammar {f : α → String} {q : Spec α} {G : Gram (Meta α)}
    {r : List Char} {b : Bool} (hm : MemberStart (PermissionPrint.metaItem f q.who))
    (hg : NontermG G ((PermissionPrint.metaItem f q.who).toList ++ gap b) q.who r)
    (hr : Boundary b r) : NontermG (QualG G) ((PermissionPrint.spec f q).toList ++ gap b) q r :=
  nonterm (qualifyPrinted hm.start (hm.notBang _) hg q rfl) hr.1

theorem userList_value {O : Oracles} (hO : PermissionLexical O.char) {xs : SpecList UserSpecifier}
    (h : BoundedItems (fun q => UserValue O q.who) xs) {b : Bool} {r : List Char}
    (hr : Boundary b r) (hsep : NextNot (· = ',') r) :
    UserListG O ((PermissionPrint.specList PermissionPrint.user xs).toList ++ gap b) xs r :=
  canonicalList _ .comma (fun r => Boundary.cons (.inl rfl) (' ' :: r) false)
    (fun _ hq _ _ hr => memberPrinted_grammar (userValue_start hq) (userValue_grammar hO hq hr) hr)
    (fun _ hq => memberPrinted_start (userValue_start hq)) h hr hsep

theorem identList_value {O : Oracles} (hO : PermissionLexical O.char) {xs : SpecList Identifier}
    (h : BoundedItems (fun q => IdentifierValue O q.who) xs) {b : Bool} {r : List Char}
    (hr : Boundary b r) (hsep : NextNot (· = ',') r) :
    IdentifierListG O ((PermissionPrint.specList PermissionPrint.identifier xs).toList ++ gap b) xs r :=
  canonicalList _ .comma (fun r => Boundary.cons (.inl rfl) (' ' :: r) false)
    (fun _ hq _ _ hr => memberPrinted_grammar (identValue_start hq) (identValue_grammar hO hq hr) hr)
    (fun _ hq => memberPrinted_start (identValue_start hq)) h hr hsep

end SudoersSpec.Grammar
