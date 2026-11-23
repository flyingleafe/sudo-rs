import SudoersSpec.Grammar.SudoInclude

namespace SudoersSpec.Grammar

open SudoersSpec.Syntax SudoersSpec.Syntax.Parser

private theorem failure_after_complete {p : Parser α} {q : α → Parser β}
    {G : Gram α} {F : α → Gram Unit} (hp : Complete p G)
    (hq : ∀ a, FailureComplete (q a) (F a)) : FailureComplete (p >>= q) (SeqG G F) := by
  rintro c r s ⟨x, y, a, rfl, hx, hy⟩ hs
  obtain ⟨u, hu, hr⟩ := hp x a (y ++ r) s hx (by rw [hs, List.append_assoc])
  obtain ⟨e, t, ht, hrest⟩ := hq a y r u hy hr
  exact ⟨e, t, by rw [run_bind_of_ok hu, ht], hrest⟩

private theorem user_bind_failure_complete {p : Parser α} {q : α → Parser β}
    {G : Gram α} {F : Gram Unit} {H : α → Gram Unit}
    (hp : Complete p G) (hf : FailureComplete p F)
    (hq : ∀ a, FailureComplete (q a) (H a)) :
    FailureComplete (p >>= q) (fun c a r => F c a r ∨ SeqG G H c a r) := by
  intro c r s h hs
  rcases h with hf' | hq'
  · obtain ⟨e, t, ht, hr⟩ := hf c r s hf' hs
    exact ⟨e, t, run_bind_of_error ht _, hr⟩
  · exact failure_after_complete hp hq c r s hq' hs

private theorem mark_failure_after_sound (ch : Char) {q : Bool → Parser α}
    {F : Bool → Gram Unit} (hq : ∀ b, FailureSound (q b) (F b)) :
    FailureSound (eatChar ch >>= q) (SeqG (MarkG ch) F) := by
  have hn : FailureSound (eatChar ch) EmptyG := by intro s e t h; simp at h
  exact (bind_failure_sound (mark_sound ch) hn hq).mono (fun _ _ _ h => h.elim False.elim id)

private theorem mapP_failure_sound {p : Parser α} {F : Gram Unit}
    (hp : FailureSound p F) (f : α → β) : FailureSound (MapP p f) F := by
  intro s e t h
  rcases run_bind_eq_error.mp h with h | ⟨_, _, _, h⟩
  · exact hp s e t h
  · cases h

private theorem mapP_failure_complete {p : Parser α} {F : Gram Unit}
    (hp : FailureComplete p F) (f : α → β) : FailureComplete (MapP p f) F := by
  intro c r s hg hs
  obtain ⟨e, t, ht, hr⟩ := hp c r s hg hs
  exact ⟨e, t, run_bind_of_error ht _, hr⟩

private def IdentifierFailureG (O : Oracles) : Gram Unit :=
  SeqG (MarkG '#') fun numeric =>
    if numeric then NontermFailureG DigitsG (TokenFailureG digitsU32Token)
    else NontermFailureG (UsernameG O) (TokenFailureG (usernameToken O))

private theorem identifier_failure_sound (O : Oracles) (D : Descriptions) :
    FailureSound (identifier O D) (IdentifierFailureG O) := by
  unfold identifier IdentifierFailureG
  apply mark_failure_after_sound
  intro b; cases b
  · exact mapP_failure_sound (tryNonterm_failure (token_sound _) (token_failure_sound _)) _
  · exact mapP_failure_sound (expectNonterm_failure (token_sound _) (token_failure_sound _) _) _

private theorem identifier_failure_complete (O : Oracles) (D : Descriptions) :
    FailureComplete (identifier O D) (IdentifierFailureG O) := by
  unfold identifier IdentifierFailureG
  apply failure_after_complete (mark_complete '#')
  intro b; cases b
  · exact mapP_failure_complete
      (tryNontermFailure_complete (token_complete _) (token_failure_complete _)) _
  · exact mapP_failure_complete
      (expectNontermFailure_complete (token_complete _) (token_failure_complete _) _) _

private def ParseUserFailureG (O : Oracles) : Gram Unit :=
  SeqG (MarkG '%') fun group =>
    if group then
      SeqG (MarkG ':') fun _ => NontermFailureG (IdentifierG O) (IdentifierFailureG O)
    else
      SeqG (MarkG '+') fun plus =>
        if plus then PureG () else NontermFailureG (IdentifierG O) (IdentifierFailureG O)

private theorem parseUser_failure_sound (O : Oracles) (D : Descriptions) :
    FailureSound (parseUser O D) (ParseUserFailureG O) := by
  unfold parseUser ParseUserFailureG
  apply mark_failure_after_sound
  intro group; cases group
  · apply mark_failure_after_sound
    intro plus; cases plus
    · exact mapP_failure_sound (tryNonterm_failure (identifier_sound O D)
        (identifier_failure_sound O D)) _
    · intro s e t h
      simp only [ite_true, run_fatalHere] at h
      cases h
      exact ⟨[], rfl, rfl, rfl⟩
  · apply mark_failure_after_sound
    intro nonunix
    exact mapP_failure_sound (expectNonterm_failure (identifier_sound O D)
      (identifier_failure_sound O D) D.identifier) _

private theorem parseUser_failure_complete (O : Oracles) (D : Descriptions) :
    FailureComplete (parseUser O D) (ParseUserFailureG O) := by
  unfold parseUser ParseUserFailureG
  apply failure_after_complete (mark_complete '%')
  intro group; cases group
  · apply failure_after_complete (mark_complete '+')
    intro plus; cases plus
    · exact mapP_failure_complete (tryNontermFailure_complete (identifier_complete O D)
        (identifier_failure_complete O D)) _
    · rintro c r s ⟨rfl, _⟩ hs
      exact ⟨_, s, run_fatalHere _ _, hs⟩
  · apply failure_after_complete (mark_complete ':')
    intro nonunix
    exact mapP_failure_complete (expectNontermFailure_complete (identifier_complete O D)
      (identifier_failure_complete O D) D.identifier) _

/-- The nested parse consumes only its own re-escaped text. Its success is required to reach
the closing delimiter, but need not exhaust that text. -/
private def QuotedTailFailureG (O : Oracles) (text : String) : Gram Unit :=
  fun c _ r =>
    (c = [] ∧ ∃ x y, text.toList = x ++ y ∧ ParseUserFailureG O x () y) ∨
    ((∃ a, QuotedUserValue O text a) ∧ RequiredMarkFailureG '"' c () r)

private abbrev quotedTail (O : Oracles) (D : Descriptions) (start : Nat × Nat) (text : String) :
    Parser UserSpecifier := do
  let res ← nested (parseUser O D) (Stream.newWithPos text.toList start)
  let a ← lift res
  expectSyntax '"'
  pure a

private theorem quotedTail_failure_sound (O : Oracles) (D : Descriptions)
    (start : Nat × Nat) (text : String) :
    FailureSound (quotedTail O D start text) (QuotedTailFailureG O text) := by
  intro s e t h
  simp only [quotedTail, run_bind_of_ok (run_nested _ _ _)] at h
  rcases hu : (parseUser O D).run (Stream.newWithPos text.toList start) with ⟨res, u⟩
  rw [hu] at h
  cases res with
  | error e' =>
    simp only [run_bind_of_error (run_lift (.error e') s), Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    obtain ⟨x, hx, hd⟩ := parseUser_failure_sound O D _ _ _ hu
    exact ⟨[], rfl, .inl ⟨rfl, x, u.rest, hx, hd⟩⟩
  | ok a =>
    simp only [run_bind_of_ok (run_lift (.ok a) s)] at h
    obtain ⟨x, hx, hg⟩ := parseUser_sound O D _ _ _ hu
    obtain ⟨c, hc, hf⟩ := mapP_failure_sound (requiredMark_failure '"') (fun _ => a) _ _ _ h
    exact ⟨c, hc, .inr ⟨⟨a, x, u.rest, hx, hg⟩, hf⟩⟩

private theorem quotedTail_failure_complete (O : Oracles) (D : Descriptions)
    (start : Nat × Nat) (text : String) :
    FailureComplete (quotedTail O D start text) (QuotedTailFailureG O text) := by
  intro c r s hg hs
  rcases hg with ⟨rfl, x, y, htext, hf⟩ | ⟨⟨a, x, y, htext, hg⟩, hf⟩
  · obtain ⟨e, u, hu, _⟩ := parseUser_failure_complete O D x y
      (Stream.newWithPos text.toList start) hf htext
    exact ⟨e, s, by simp [quotedTail, run_bind, hu], hs⟩
  · obtain ⟨u, hu, _⟩ := parseUser_complete O D x a y
      (Stream.newWithPos text.toList start) hg htext
    obtain ⟨e, t, ht, hr⟩ := requiredMarkFailure_complete '"' c r s hf hs
    exact ⟨e, t, by simp [quotedTail, run_bind, hu, ht], hr⟩

private abbrev quotedNameToken (O : Oracles) := unquotedToken O.char (usernameToken O)

private def UserSpecifierFailureG (O : Oracles) : Gram Unit :=
  SeqG (MarkG '"') fun quoted =>
    if quoted then fun c a r =>
      NontermFailureG (TokenG (quotedNameToken O)) (TokenFailureG (quotedNameToken O)) c a r ∨
      SeqG (NontermG (TokenG (quotedNameToken O))) (QuotedTailFailureG O) c a r
    else ParseUserFailureG O

private theorem userSpecifier_failure_sound (O : Oracles) (D : Descriptions) :
    FailureSound (userSpecifier O D) (UserSpecifierFailureG O) := by
  unfold userSpecifier UserSpecifierFailureG
  apply mark_failure_after_sound
  intro quoted; cases quoted
  · exact parseUser_failure_sound O D
  · intro s e t h
    simp only [ite_true, run_bind_of_ok (run_getPos s)] at h
    exact bind_failure_sound (expectNonterminal_sound (token_sound _) D.username)
      (expectNonterm_failure (token_sound _) (token_failure_sound _) D.username)
      (quotedTail_failure_sound O D s.getPos) s e t h

private theorem userSpecifier_failure_complete (O : Oracles) (D : Descriptions) :
    FailureComplete (userSpecifier O D) (UserSpecifierFailureG O) := by
  unfold userSpecifier UserSpecifierFailureG
  apply failure_after_complete (mark_complete '"')
  intro quoted; cases quoted
  · exact parseUser_failure_complete O D
  · intro c r s hg hs
    simp only [ite_true, run_bind_of_ok (run_getPos s)]
    exact user_bind_failure_complete (expectNonterminal_complete (token_complete _) D.username)
      (expectNontermFailure_complete (token_complete _) (token_failure_complete _) D.username)
      (quotedTail_failure_complete O D s.getPos) c r s hg hs

private abbrev MetaUserProbeG (O : Oracles) :=
  OptG (TokenG (MetaUsernameToken O)) (TokenRejectG (MetaUsernameToken O))

/-- Failure in the optional meta-name probe or in the fallback user production. The second
branch includes the prefix consumed by a rejecting token and any subsequent whitespace. -/
def MetaUserFailureG (O : Oracles) : Gram Unit := fun c a r =>
  NontermFailureG (MetaUserProbeG O) (TokenFatalG (MetaUsernameToken O)) c a r ∨
  SeqG (NontermG (MetaUserProbeG O)) (fun
    | none => UserSpecifierFailureG O
    | some _ => EmptyG) c a r

theorem metaUser_failure_sound (O : Oracles) (D : Descriptions) :
    FailureSound (metaUserSpecifier O D) (MetaUserFailureG O) := by
  unfold metaUserSpecifier parseMeta MetaUserFailureG
  have hp := option_sound (token_sound (MetaUsernameToken O)) (token_rejectSound _)
  apply bind_failure_sound (tryNonterminal_sound hp) (tryNonterm_failure hp (optionalToken_failure _))
  intro a; cases a with
  | none => exact mapP_failure_sound (userSpecifier_failure_sound O D) _
  | some m => cases m <;> (intro s e t h; cases h)

theorem metaUser_failure_complete (O : Oracles) (D : Descriptions) :
    FailureComplete (metaUserSpecifier O D) (MetaUserFailureG O) := by
  unfold metaUserSpecifier parseMeta MetaUserFailureG
  have hp := option_complete (token_complete (MetaUsernameToken O)) (token_rejectComplete _)
  apply user_bind_failure_complete (tryNonterminal_complete hp)
    (tryNontermFailure_complete hp (optionalTokenFailure_complete _))
  intro a; cases a with
  | none => exact mapP_failure_complete (userSpecifier_failure_complete O D) _
  | some _ => intro _ _ _ h _; exact False.elim h

end SudoersSpec.Grammar
