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

private theorem mark_reject_sound (ch : Char) {q : Bool → Parser α} {R : Bool → Gram Unit}
    (hq : ∀ b, RejectSound (q b) (R b)) :
    RejectSound (eatChar ch >>= q) (SeqG (MarkG ch) R) :=
  reject_after_sound (mark_sound ch) (by intro s t h; simp at h) hq

private theorem mapP_reject {p : Parser α} {f : α → β} {s t : Stream}
    (h : (MapP p f).run s = (.error .reject, t)) : p.run s = (.error .reject, t) := by
  rcases run_bind_eq_error.mp h with h | ⟨_, _, _, h⟩
  · exact h
  · simp at h

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

private def MetaUserRejectG (O : Oracles) : Gram Unit :=
  SeqG (NontermG (OptG (TokenG (MetaUsernameToken O)) (TokenRejectG (MetaUsernameToken O)))) fun
    | none => UserSpecifierRejectG O
    | some _ => EmptyG

private theorem metaUser_reject_sound (O : Oracles) (D : Descriptions) :
    RejectSound (metaUserSpecifier O D) (MetaUserRejectG O) := by
  unfold metaUserSpecifier parseMeta MetaUserRejectG
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
      exact userSpecifier_reject_sound O D s t (mapP_reject (f := Meta.only) h)
    | some m =>
      intro s t h
      cases m <;> simp at h

/-- The first user-list entry rejects before any qualification marker. Its consumed prefix
includes the failed meta-token probe and its trailing whitespace, and may include a quote and
its text if the user parser rejects on the separate quoted stream. -/
def UserListRejectG (O : Oracles) : Gram Unit :=
  fun c a r => NextNot (· = '!') (c ++ r) ∧ MetaUserRejectG O c a r

theorem userList_reject_sound (O : Oracles) (D : Descriptions) :
    RejectSound (tryNonterminal (specListUserSpecifier O D)) (UserListRejectG O) := by
  intro s t h
  have h' := tryNonterminal_reject.mp h
  rw [specListUserSpecifier, specList_eq] at h'
  obtain ⟨hn, hr⟩ := qualified_reject_iff.mp (parseList_reject h')
  obtain ⟨c, hc, hd⟩ := metaUser_reject_sound O D s t hr
  exact ⟨c, hc, hc ▸ hn, hd⟩

end SudoersSpec.Grammar
