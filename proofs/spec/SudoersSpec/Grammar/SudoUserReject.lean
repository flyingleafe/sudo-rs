import SudoersSpec.Grammar.PermissionAtoms

namespace SudoersSpec.Grammar

open SudoersSpec.Syntax SudoersSpec.Syntax.Parser

private theorem reject_after_sound {p : Parser α} {q : α → Parser β}
    {G : Gram α} {R : α → Gram Unit} (hp : Sound p G)
    (hn : ∀ s t, p.run s = (.error .reject, t) → False)
    (hq : ∀ a, RejectSound (q a) (R a)) : RejectSound (p >>= q) (SeqG G R) := by
  intro s t h
  rcases run_bind_eq_error.mp h with h | ⟨a, u, hu, ht⟩
  · exact (hn _ _ h).elim
  · obtain ⟨x, hx, hg⟩ := hp _ _ _ hu
    obtain ⟨y, hy, hr⟩ := hq a _ _ ht
    exact ⟨x ++ y, by rw [hx, hy, List.append_assoc], x, y, a, rfl, hy ▸ hg, hr⟩

private theorem reject_after_complete {p : Parser α} {q : α → Parser β}
    {G : Gram α} {R : α → Gram Unit} (hp : Complete p G)
    (hq : ∀ a, RejectComplete (q a) (R a)) : RejectComplete (p >>= q) (SeqG G R) := by
  rintro c r s ⟨x, y, a, rfl, hx, hy⟩ hs
  obtain ⟨u, hu, hrest⟩ := hp x a (y ++ r) s hx (by rw [hs, List.append_assoc])
  obtain ⟨t, ht, hr⟩ := hq a y r u hy hrest
  exact ⟨t, by rw [run_bind_of_ok hu, ht], hr⟩

private theorem mark_reject_sound (ch : Char) {q : Bool → Parser α} {R : Bool → Gram Unit}
    (hq : ∀ b, RejectSound (q b) (R b)) :
    RejectSound (eatChar ch >>= q) (SeqG (MarkG ch) R) :=
  reject_after_sound (mark_sound ch) (by intro s t h; simp at h) hq

private theorem mapP_reject {p : Parser α} {f : α → β} {s t : Stream}
    (h : (MapP p f).run s = (.error .reject, t)) : p.run s = (.error .reject, t) := by
  rcases run_bind_eq_error.mp h with h | ⟨_, _, _, h⟩
  · exact h
  · simp at h

private theorem mapP_reject_complete {p : Parser α} {R : Gram Unit}
    (hp : RejectComplete p R) (f : α → β) : RejectComplete (MapP p f) R := by
  intro c r s hd hs
  obtain ⟨t, ht, hr⟩ := hp c r s hd hs
  exact ⟨t, run_bind_of_error ht _, hr⟩

private theorem tryNonterminal_reject_complete {p : Parser α} {R : Gram Unit}
    (hp : RejectComplete p R) : RejectComplete (tryNonterminal p) R := by
  intro c r s hd hs
  obtain ⟨t, ht, hr⟩ := hp c r s hd hs
  exact ⟨t, tryNonterminal_reject.mpr ht, hr⟩

private def IdentifierRejectG (O : Oracles) : Gram Unit :=
  SeqG (MarkG '#') fun numeric => if numeric then EmptyG else TokenRejectG (usernameToken O)

private theorem identifier_reject_sound (O : Oracles) (D : Descriptions) :
    RejectSound (identifier O D) (IdentifierRejectG O) := by
  unfold identifier IdentifierRejectG
  apply mark_reject_sound
  intro b
  cases b with
  | false =>
    intro s t h
    exact token_rejectSound (usernameToken O) s t
      (tryNonterminal_reject.mp (mapP_reject (f := Identifier.name) h))
  | true =>
    intro s t h
    exact (expectNonterminal_ne_reject D.digitsU32 (token digitsU32Token) s
      (congrArg Prod.fst (mapP_reject (f := Identifier.id) h))).elim

private theorem identifier_reject_complete (O : Oracles) (D : Descriptions) :
    RejectComplete (identifier O D) (IdentifierRejectG O) := by
  unfold identifier IdentifierRejectG
  apply reject_after_complete (mark_complete '#')
  intro b
  cases b with
  | false =>
    exact mapP_reject_complete (tryNonterminal_reject_complete (token_rejectComplete _)) _
  | true =>
    intro _ _ _ h _
    exact False.elim h

private def ParseUserRejectG (O : Oracles) : Gram Unit :=
  SeqG (MarkG '%') fun group => if group then EmptyG else
    SeqG (MarkG '+') fun plus => if plus then EmptyG else IdentifierRejectG O

private theorem parseUser_reject_sound (O : Oracles) (D : Descriptions) :
    RejectSound (parseUser O D) (ParseUserRejectG O) := by
  unfold parseUser ParseUserRejectG
  apply mark_reject_sound
  intro b
  cases b with
  | false =>
    apply mark_reject_sound
    intro plus
    cases plus with
    | false =>
      intro s t h
      exact identifier_reject_sound O D s t
        (tryNonterminal_reject.mp (mapP_reject (f := UserSpecifier.user) h))
    | true =>
      intro s t h
      simp at h
  | true =>
    intro s t h
    simp only [ite_true] at h
    rcases run_bind_eq_error.mp h with h | ⟨nonunix, u, _, h⟩
    · simp at h
    · exact (expectNonterminal_ne_reject D.identifier (identifier O D) u
        (congrArg Prod.fst (mapP_reject
          (f := fun i => if nonunix then UserSpecifier.nonunixGroup i else .group i) h))).elim

private theorem parseUser_reject_complete (O : Oracles) (D : Descriptions) :
    RejectComplete (parseUser O D) (ParseUserRejectG O) := by
  unfold parseUser ParseUserRejectG
  apply reject_after_complete (mark_complete '%')
  intro b
  cases b with
  | false =>
    apply reject_after_complete (mark_complete '+')
    intro plus
    cases plus with
    | false =>
      exact mapP_reject_complete (tryNonterminal_reject_complete (identifier_reject_complete O D)) _
    | true =>
      intro _ _ _ h _
      exact False.elim h
  | true =>
    intro _ _ _ h _
    exact False.elim h

/-- A nested rejection accounts for the inner token text, not any more of the outer input. -/
private def InnerUserRejectG (O : Oracles) (text : String) : Gram Unit :=
  fun c _ _ => c = [] ∧ ∃ x r, text.toList = x ++ r ∧ ParseUserRejectG O x () r

private def QuotedUserRejectG (O : Oracles) : Gram Unit :=
  SeqG (NontermG (TokenG (unquotedToken O.char (usernameToken O)))) (InnerUserRejectG O)

private theorem expectSyntax_ne_reject (ch : Char) (s : Stream) :
    ((expectSyntax ch).run s).1 ≠ .error .reject := by
  simp only [expectSyntax, run_bind, run_observe]
  split <;> simp [run_bind]

private theorem quotedTail_reject_sound (O : Oracles) (D : Descriptions) (start : Nat × Nat)
    (text : String) : RejectSound (do
      let result ← nested (parseUser O D) (Stream.newWithPos text.toList start)
      let a ← lift result
      expectSyntax '"'
      pure a) (InnerUserRejectG O text) := by
  intro s t h
  rw [run_bind_of_ok (run_nested _ _ _)] at h
  rcases run_bind_eq_error.mp h with h | ⟨a, u, _, h⟩
  · simp only [run_lift, Prod.mk.injEq] at h
    obtain ⟨hr, rfl⟩ := h
    obtain ⟨x, hx, hd⟩ := parseUser_reject_sound O D _ _ (Prod.ext hr rfl)
    exact ⟨[], rfl, rfl, x, _, hx, hd⟩
  · exact (expectSyntax_ne_reject '"' u (congrArg Prod.fst (mapP_reject (f := fun _ => a) h))).elim

private theorem quotedTail_reject_complete (O : Oracles) (D : Descriptions) (start : Nat × Nat)
    (text : String) : RejectComplete (do
      let result ← nested (parseUser O D) (Stream.newWithPos text.toList start)
      let a ← lift result
      expectSyntax '"'
      pure a) (InnerUserRejectG O text) := by
  rintro c r s ⟨rfl, x, innerRest, htext, hd⟩ hs
  obtain ⟨u, hu, _⟩ := parseUser_reject_complete O D x innerRest
    (Stream.newWithPos text.toList start) hd htext
  -- `nested` returns the inner rejection without moving the outer stream.
  exact ⟨s, by simp [run_bind, hu], hs⟩

private def UserSpecifierRejectG (O : Oracles) : Gram Unit :=
  SeqG (MarkG '"') fun quoted => if quoted then QuotedUserRejectG O else ParseUserRejectG O

private theorem userSpecifier_reject_sound (O : Oracles) (D : Descriptions) :
    RejectSound (userSpecifier O D) (UserSpecifierRejectG O) := by
  unfold userSpecifier UserSpecifierRejectG
  apply mark_reject_sound
  intro b
  cases b with
  | false => exact parseUser_reject_sound O D
  | true =>
    intro s t h
    simp only [ite_true, run_bind_of_ok (run_getPos s)] at h
    exact (reject_after_sound (expectNonterminal_sound (token_sound _) D.username)
      (fun u _ h => expectNonterminal_ne_reject D.username _ u (congrArg Prod.fst h))
      (quotedTail_reject_sound O D s.getPos)) s t h

private theorem userSpecifier_reject_complete (O : Oracles) (D : Descriptions) :
    RejectComplete (userSpecifier O D) (UserSpecifierRejectG O) := by
  unfold userSpecifier UserSpecifierRejectG
  apply reject_after_complete (mark_complete '"')
  intro b
  cases b with
  | false => exact parseUser_reject_complete O D
  | true =>
    intro c r s hd hs
    simp only [ite_true, run_bind_of_ok (run_getPos s)]
    exact (reject_after_complete (expectNonterminal_complete (token_complete _) D.username)
      (quotedTail_reject_complete O D s.getPos)) c r s hd hs

private def ParseMetaRejectG (O : Oracles) (R : Gram Unit) : Gram Unit :=
  SeqG (NontermG (OptG (TokenG (MetaUsernameToken O)) (TokenRejectG (MetaUsernameToken O)))) fun
    | none => R
    | some _ => EmptyG

private theorem parseMeta_reject_sound (O : Oracles) {p : Parser α} {R : Gram Unit}
    (hp : RejectSound p R) (embed : String → α) :
    RejectSound (parseMeta O p embed) (ParseMetaRejectG O R) := by
  unfold parseMeta ParseMetaRejectG
  apply reject_after_sound
    (tryNonterminal_sound (option_sound (token_sound _) (token_rejectSound _)))
  · intro s t h
    have h' := tryNonterminal_reject.mp h
    rw [parseOption, run_maybe] at h'
    rcases ht : (token (MetaUsernameToken O)).run s with ⟨r, u⟩
    rw [ht] at h'
    cases r with
    | ok _ => simp at h'
    | error e => cases e <;> simp at h'
  · intro a
    cases a with
    | none =>
      intro s t h
      exact hp s t (mapP_reject (f := Meta.only) h)
    | some m =>
      intro s t h
      cases m <;> simp at h

private theorem parseMeta_reject_complete (O : Oracles) {p : Parser α} {R : Gram Unit}
    (hp : RejectComplete p R) (embed : String → α) :
    RejectComplete (parseMeta O p embed) (ParseMetaRejectG O R) := by
  unfold parseMeta ParseMetaRejectG
  apply reject_after_complete
    (tryNonterminal_complete (option_complete (token_complete _) (token_rejectComplete _)))
  intro a
  cases a with
  | none => exact mapP_reject_complete hp _
  | some _ =>
    intro _ _ _ h _
    exact False.elim h

/-- The first user-list entry rejects before any qualification marker. Its consumed prefix
includes the failed meta-token probe and its trailing whitespace, and may include a quote and
its text if the user parser rejects on the separate quoted stream. -/
def UserListRejectG (O : Oracles) : Gram Unit :=
  fun c a r => NextNot (· = '!') (c ++ r) ∧ ParseMetaRejectG O (UserSpecifierRejectG O) c a r

theorem userList_reject_sound (O : Oracles) (D : Descriptions) :
    RejectSound (tryNonterminal (specListUserSpecifier O D)) (UserListRejectG O) := by
  intro s t h
  have h' := tryNonterminal_reject.mp h
  rw [specListUserSpecifier, specList_eq] at h'
  obtain ⟨hn, hr⟩ := qualified_reject_iff.mp (parseList_reject h')
  obtain ⟨c, hc, hd⟩ := parseMeta_reject_sound O (userSpecifier_reject_sound O D) _ s t hr
  exact ⟨c, hc, hc ▸ hn, hd⟩

theorem userList_reject_complete (O : Oracles) (D : Descriptions) :
    RejectComplete (tryNonterminal (specListUserSpecifier O D)) (UserListRejectG O) := by
  rintro c r s ⟨hn, hmeta⟩ hs
  obtain ⟨t, ht, hr⟩ := parseMeta_reject_complete O (userSpecifier_reject_complete O D)
    (fun name => .user (.name name)) c r s hmeta hs
  refine ⟨t, tryNonterminal_reject.mpr ?_, hr⟩
  unfold specListUserSpecifier
  exact specList_reject_iff.mpr ⟨hs.symm ▸ hn, ht⟩

/-- A group list rejects only on its first, unqualified entry. The consumed prefix
includes any input consumed by the failed meta-token probe and its trailing whitespace. -/
def IdentifierListRejectG (O : Oracles) : Gram Unit :=
  fun c a r => NextNot (· = '!') (c ++ r) ∧ ParseMetaRejectG O (IdentifierRejectG O) c a r

theorem identifierList_reject_sound (O : Oracles) (D : Descriptions) :
    RejectSound (tryNonterminal (specListIdentifier O D)) (IdentifierListRejectG O) := by
  intro s t h
  have h' := tryNonterminal_reject.mp h
  rw [specListIdentifier] at h'
  obtain ⟨hn, hr⟩ := specList_reject_iff.mp h'
  obtain ⟨c, hc, hd⟩ := parseMeta_reject_sound O (identifier_reject_sound O D) Identifier.name s t hr
  exact ⟨c, hc, hc ▸ hn, hd⟩

theorem identifierList_reject_complete (O : Oracles) (D : Descriptions) :
    RejectComplete (tryNonterminal (specListIdentifier O D)) (IdentifierListRejectG O) := by
  rintro c r s ⟨hn, hmeta⟩ hs
  obtain ⟨t, ht, hr⟩ := parseMeta_reject_complete O (identifier_reject_complete O D)
    Identifier.name c r s hmeta hs
  exact ⟨t, tryNonterminal_reject.mpr (specList_reject_iff.mpr ⟨hs.symm ▸ hn, ht⟩), hr⟩

end SudoersSpec.Grammar
