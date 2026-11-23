import SudoersSpec.Grammar.Hostname

namespace SudoersSpec.Grammar

open SudoersSpec.Syntax SudoersSpec.Syntax.Parser

/-! ## Sequencing, guarded alternatives and rejection -/

abbrev MapG (G : Gram α) (f : α → β) : Gram β :=
  fun c b r => ∃ a, G c a r ∧ f a = b

abbrev EmptyG : Gram α := fun _ _ _ => False

abbrev MapP (p : Parser α) (f : α → β) : Parser β := p >>= fun a => pure (f a)

theorem mapP_sound {p : Parser α} {G : Gram α} (h : Sound p G) (f : α → β) :
    Sound (MapP p f) (MapG G f) := by
  intro s b s' hr
  obtain ⟨a, s₁, hp, hf⟩ := run_bind_eq_ok.mp hr
  simp only [run_pure, Prod.mk.injEq, Except.ok.injEq] at hf
  obtain ⟨eq, rfl⟩ := hf
  obtain ⟨c, hc, ha⟩ := h s a _ hp
  exact ⟨c, hc, a, ha, eq⟩

theorem mapP_complete {p : Parser α} {G : Gram α} (h : Complete p G) (f : α → β) :
    Complete (MapP p f) (MapG G f) := by
  rintro c b r s ⟨a, ha, rfl⟩ hs
  obtain ⟨s₁, hp, hr⟩ := h c a r s ha hs
  exact ⟨s₁, run_bind_of_ok hp _, hr⟩

theorem seq_sound {p : Parser α} {G : Gram α} {q : α → Parser β} {H : α → Gram β}
    (hp : Sound p G) (hq : ∀ a, Sound (q a) (H a)) : Sound (p >>= q) (SeqG G H) :=
  bind_sound hp hq

theorem seq_complete {p : Parser α} {G : Gram α} {q : α → Parser β} {H : α → Gram β}
    (hp : Complete p G) (hq : ∀ a, Complete (q a) (H a)) : Complete (p >>= q) (SeqG G H) :=
  bind_complete hp hq

/-- A bare punctuation check does not take `Ws`. The false branch consumes nothing. -/
inductive MarkG (ch : Char) : Gram Bool where
  | present : MarkG ch [ch] true r
  | absent : NextNot (· = ch) r → MarkG ch [] false r

theorem mark_sound (ch : Char) : Sound (eatChar ch) (MarkG ch) := by
  intro s b s' h
  rw [run_eatChar, Stream.eatChar_eq] at h
  split at h
  · rename_i hpk
    cases h
    exact ⟨[ch], Stream.rest_of_peek hpk, .present⟩
  · rename_i hpk
    cases h
    exact ⟨[], rfl, .absent (fun d hd he => hpk (he ▸ hd))⟩

theorem mark_complete (ch : Char) : Complete (eatChar ch) (MarkG ch) := by
  intro c b r s hd hs
  rw [run_eatChar, Stream.eatChar_eq, Stream.peek_eq_head, hs]
  cases hd with
  | present => exact ⟨s.pop, by simp, by rw [Stream.pop_rest, hs]; rfl⟩
  | absent hn =>
    have h : r.head? ≠ some ch := fun h => hn ch h rfl
    exact ⟨s, by simp [h], hs⟩

/-- Syntax punctuation as a lookahead which reports whether it was present. -/
inductive SyntaxMarkG (ch : Char) : Gram Bool where
  | present : SynG ch c () r → SyntaxMarkG ch c true r
  | absent : NextNot (· = ch) r → SyntaxMarkG ch [] false r

theorem syntaxMark_sound (ch : Char) : Sound (isSyntax ch) (SyntaxMarkG ch) := by
  intro s b s' h
  cases b with
  | false =>
    obtain ⟨rfl, hn⟩ := isSyntax_false_iff.mp h
    exact ⟨[], rfl, .absent hn⟩
  | true =>
    obtain ⟨c, hc, hd⟩ := trySyntax_sound ch s () s' (isSyntax_true_iff.mp h)
    exact ⟨c, hc, .present hd⟩

theorem syntaxMark_complete (ch : Char) : Complete (isSyntax ch) (SyntaxMarkG ch) := by
  intro c b r s hd hs
  cases hd with
  | present hd =>
    obtain ⟨s', hf, hr⟩ := trySyntax_complete ch _ () r s hd hs
    exact ⟨s', isSyntax_true_iff.mpr hf, hr⟩
  | absent hn => exact ⟨s, isSyntax_false_iff.mpr ⟨rfl, hs.symm ▸ hn⟩, hs⟩

/-- Rejection is a lexical judgment with a consumed prefix, not a success judgment. -/
def RejectSound (p : Parser α) (R : Gram Unit) : Prop :=
  ∀ s s', p.run s = (.error .reject, s') → ∃ c, s.rest = c ++ s'.rest ∧ R c () s'.rest

def RejectComplete (p : Parser α) (R : Gram Unit) : Prop :=
  ∀ c r s, R c () r → s.rest = c ++ r → ∃ s', p.run s = (.error .reject, s') ∧ s'.rest = r

inductive TokenRejectG (T : TokenSpec α) : Gram Unit where
  | stop : EscStop T T.accept1st r → TokenRejectG T [] () r
  | continuation : EscRejects T T.accept1st → TokenRejectG T ['\\', '\n'] () r

theorem token_rejectSound (T : TokenSpec α) : RejectSound (token T) (TokenRejectG T) := by
  intro s s' h
  rcases token_reject T h with ⟨rfl, hs⟩ | ⟨hs, he⟩
  · exact ⟨[], rfl, .stop hs⟩
  · exact ⟨_, he, .continuation hs⟩

theorem token_rejectComplete (T : TokenSpec α) : RejectComplete (token T) (TokenRejectG T) := by
  intro c r s h hs
  cases h with
  | stop ht =>
    have hr : EscStop T T.accept1st s.rest := by rw [hs]; exact ht
    exact ⟨s, by rw [token_run, acceptEscaped_stop T T.accept1st hr], hs⟩
  | continuation ht => exact token_reject_of_escRejects T ht hs

inductive OptG (G : Gram α) (R : Gram Unit) : Gram (Option α) where
  | some : G c a r → OptG G R c (some a) r
  | none : R c () r → OptG G R c none r

theorem option_sound {p : Parser α} {G : Gram α} {R : Gram Unit}
    (hg : Sound p G) (hr : RejectSound p R) : Sound (parseOption p) (OptG G R) := by
  intro s a s' h
  change (Parser.maybe p).run s = _ at h
  rw [run_maybe] at h
  revert h
  cases hp : p.run s with
  | mk rr t =>
    cases rr with
    | ok x =>
      simp only [maybe_ok, Prod.mk.injEq, Except.ok.injEq]
      rintro ⟨rfl, rfl⟩
      obtain ⟨c, hc, hd⟩ := hg _ _ _ hp
      exact ⟨c, hc, .some hd⟩
    | error e => cases e with
      | fatal span k => simp
      | reject =>
        simp only [maybe_reject, Prod.mk.injEq, Except.ok.injEq]
        rintro ⟨rfl, rfl⟩
        obtain ⟨c, hc, hd⟩ := hr _ _ hp
        exact ⟨c, hc, .none hd⟩

theorem option_complete {p : Parser α} {G : Gram α} {R : Gram Unit}
    (hg : Complete p G) (hr : RejectComplete p R) : Complete (parseOption p) (OptG G R) := by
  intro c a r s hd hs
  cases hd with
  | some h =>
    obtain ⟨t, ht, tr⟩ := hg _ _ _ _ h hs
    exact ⟨t, by simp [parseOption, ht], tr⟩
  | none h =>
    obtain ⟨t, ht, tr⟩ := hr _ _ _ h hs
    exact ⟨t, by simp [parseOption, ht], tr⟩

/-! ## Identifiers and user lists -/

abbrev UsernameG (O : Oracles) : Gram String := TokenG (usernameToken O)
abbrev DigitsG : Gram Nat := TokenG digitsU32Token

/-- `#` followed by a decimal `u32` (lexer length 10), or an unprefixed name. -/
def IdentifierG (O : Oracles) : Gram Identifier :=
  SeqG (MarkG '#') fun isId =>
    if isId then MapG (NontermG DigitsG) Identifier.id
    else MapG (NontermG (UsernameG O)) Identifier.name

theorem identifier_sound (O : Oracles) (D : Descriptions) :
    Sound (identifier O D) (IdentifierG O) := by
  unfold identifier IdentifierG
  apply seq_sound (mark_sound '#')
  intro b; cases b
  · exact mapP_sound (tryNonterminal_sound (token_sound _)) _
  · exact mapP_sound (expectNonterminal_sound (token_sound _) _) _

theorem identifier_complete (O : Oracles) (D : Descriptions) :
    Complete (identifier O D) (IdentifierG O) := by
  unfold identifier IdentifierG
  apply seq_complete (mark_complete '#')
  intro b; cases b
  · exact mapP_complete (tryNonterminal_complete (token_complete _)) _
  · exact mapP_complete (expectNonterminal_complete (token_complete _) _) _

/-- Direct users, Unix groups and non-Unix groups. `+` has no production. -/
def ParseUserG (O : Oracles) : Gram UserSpecifier :=
  SeqG (MarkG '%') fun group =>
    if group then
      SeqG (MarkG ':') fun nonunix => MapG (NontermG (IdentifierG O)) fun i =>
        if nonunix then .nonunixGroup i else .group i
    else
      SeqG (MarkG '+') fun plus =>
        if plus then EmptyG else MapG (NontermG (IdentifierG O)) UserSpecifier.user

theorem parseUser_sound (O : Oracles) (D : Descriptions) :
    Sound (parseUser O D) (ParseUserG O) := by
  unfold parseUser ParseUserG
  apply seq_sound (mark_sound '%')
  intro b; cases b
  · apply seq_sound (mark_sound '+')
    intro b; cases b
    · exact mapP_sound (tryNonterminal_sound (identifier_sound O D)) _
    · intro s a s' h; cases h
  · apply seq_sound (mark_sound ':')
    intro b
    exact mapP_sound (expectNonterminal_sound (identifier_sound O D) _) _

theorem parseUser_complete (O : Oracles) (D : Descriptions) :
    Complete (parseUser O D) (ParseUserG O) := by
  unfold parseUser ParseUserG
  apply seq_complete (mark_complete '%')
  intro b; cases b
  · apply seq_complete (mark_complete '+')
    intro b; cases b
    · exact mapP_complete (tryNonterminal_complete (identifier_complete O D)) _
    · intro c a r s h _; exact False.elim h
  · apply seq_complete (mark_complete ':')
    intro b
    exact mapP_complete (expectNonterminal_complete (identifier_complete O D) _) _

/-- In a quoted user the enclosed text is re-escaped by `Unquoted`. The inner user
judgment is on that separate character stream and need not consume the whole inner text. -/
def QuotedUserValue (O : Oracles) (text : String) (a : UserSpecifier) : Prop :=
  ∃ c r, text.toList = c ++ r ∧ ParseUserG O c a r

abbrev QuotedUserG (O : Oracles) : Gram UserSpecifier :=
  SeqG (NontermG (TokenG (unquotedToken O.char (usernameToken O)))) fun text =>
    fun c a r => QuotedUserValue O text a ∧ SynG '"' c () r

def UserSpecifierG (O : Oracles) : Gram UserSpecifier :=
  SeqG (MarkG '"') fun q => if q then QuotedUserG O else ParseUserG O

private abbrev quotedTail (O : Oracles) (D : Descriptions) (start : Nat × Nat) (text : String) :
    Parser UserSpecifier := do
  let result ← nested (parseUser O D) (Stream.newWithPos text.toList start)
  let a ← lift result
  expectSyntax '"'
  pure a

private theorem quotedTail_sound (O : Oracles) (D : Descriptions) (start : Nat × Nat) (text : String) :
    Sound (quotedTail O D start text) (fun c a r => QuotedUserValue O text a ∧ SynG '"' c () r) := by
  intro t a t' ht
  simp only [quotedTail, run_bind_of_ok (run_nested _ _ _)]
    at ht
  rcases hu : (parseUser O D).run (Stream.newWithPos text.toList start) with ⟨res, dst⟩
  rw [hu] at ht
  cases res with
  | error _ => cases ht
  | ok u =>
    obtain ⟨c, hc, _, hsyn, rfl⟩ := (mapP_sound (expectSyntax_sound '"') (fun _ => u)) t a t' ht
    obtain ⟨x, hx, hg⟩ := parseUser_sound O D _ _ _ hu
    exact ⟨c, hc, ⟨x, _, hx, hg⟩, hsyn⟩

private theorem quotedUser_sound (O : Oracles) (D : Descriptions) :
    Sound (do
      let start ← getPos
      let text ← expectNonterminal D.username (token (unquotedToken O.char (usernameToken O)))
      quotedTail O D start text) (QuotedUserG O) := by
  intro s a s' h
  rw [run_bind_of_ok (run_getPos s)] at h
  exact (seq_sound (expectNonterminal_sound (token_sound _) D.username)
    (quotedTail_sound O D s.getPos)) s a s' h

theorem userSpecifier_sound (O : Oracles) (D : Descriptions) :
    Sound (userSpecifier O D) (UserSpecifierG O) := by
  unfold userSpecifier UserSpecifierG
  apply seq_sound (mark_sound '"')
  intro b; cases b
  · exact parseUser_sound O D
  · exact quotedUser_sound O D

private theorem quotedTail_complete (O : Oracles) (D : Descriptions) (start : Nat × Nat)
    (text : String) : Complete (quotedTail O D start text)
      (fun c a r => QuotedUserValue O text a ∧ SynG '"' c () r) := by
  rintro c a r t ⟨⟨src, tail, hsrc, huser⟩, hsyn⟩ ht
  obtain ⟨u, hu, _⟩ := parseUser_complete O D _ _ _ (Stream.newWithPos text.toList start) huser hsrc
  obtain ⟨t', hp, hr⟩ := expectSyntax_complete '"' c () r t hsyn ht
  exact ⟨t', by simp [quotedTail, run_bind, hu, hp], hr⟩

private theorem quotedUser_complete (O : Oracles) (D : Descriptions) :
    Complete (do
      let start ← getPos
      let text ← expectNonterminal D.username (token (unquotedToken O.char (usernameToken O)))
      quotedTail O D start text) (QuotedUserG O) := by
  intro c a r s hd hs
  rw [run_bind_of_ok (run_getPos s)]
  exact (seq_complete (expectNonterminal_complete (token_complete _) D.username)
    (quotedTail_complete O D s.getPos)) c a r s hd hs

theorem userSpecifier_complete (O : Oracles) (D : Descriptions) :
    Complete (userSpecifier O D) (UserSpecifierG O) := by
  unfold userSpecifier UserSpecifierG
  apply seq_complete (mark_complete '"')
  intro b; cases b
  · exact parseUser_complete O D
  · exact quotedUser_complete O D

abbrev MetaUsernameToken (O : Oracles) := metaToken O.char (usernameToken O)

def MetaG (O : Oracles) (G : Gram α) (embed : String → α) : Gram (Meta α) :=
  SeqG (NontermG (OptG (TokenG (MetaUsernameToken O)) (TokenRejectG (MetaUsernameToken O)))) fun
    | none => MapG G Meta.only
    | some m => PureG (match m with
      | .all => .all
      | .alias a => .alias a
      | .only name => .only (embed name))

theorem parseMeta_sound (O : Oracles) {p : Parser α} {G : Gram α} (h : Sound p G)
    (embed : String → α) : Sound (parseMeta O p embed) (MetaG O G embed) := by
  unfold parseMeta MetaG
  apply seq_sound (tryNonterminal_sound (option_sound (token_sound _) (token_rejectSound _)))
  intro m; cases m with
  | none => exact mapP_sound h _
  | some m => cases m <;> exact pure_sound _

theorem parseMeta_complete (O : Oracles) {p : Parser α} {G : Gram α} (h : Complete p G)
    (embed : String → α) : Complete (parseMeta O p embed) (MetaG O G embed) := by
  unfold parseMeta MetaG
  apply seq_complete (tryNonterminal_complete (option_complete (token_complete _) (token_rejectComplete _)))
  intro m; cases m with
  | none => exact mapP_complete h _
  | some m => cases m <;> exact pure_complete _

abbrev MetaUserG (O : Oracles) := MetaG O (UserSpecifierG O) (fun n => .user (.name n))
abbrev MetaIdentifierG (O : Oracles) := MetaG O (IdentifierG O) Identifier.name
abbrev UserListG (O : Oracles) := SpecListG (MetaUserG O) userSpecifierMany
abbrev IdentifierListG (O : Oracles) := SpecListG (MetaIdentifierG O) identifierMany

theorem userList_sound (O : Oracles) (D : Descriptions) :
    Sound (specListUserSpecifier O D) (UserListG O) :=
  specList_sound (parseMeta_sound O (userSpecifier_sound O D) _) _ _

theorem userList_complete (O : Oracles) (D : Descriptions) :
    Complete (specListUserSpecifier O D) (UserListG O) :=
  specList_complete (parseMeta_complete O (userSpecifier_complete O D) _) _ _

theorem identifierList_sound (O : Oracles) (D : Descriptions) :
    Sound (specListIdentifier O D) (IdentifierListG O) :=
  specList_sound (parseMeta_sound O (identifier_sound O D) _) _ _

theorem identifierList_complete (O : Oracles) (D : Descriptions) :
    Complete (specListIdentifier O D) (IdentifierListG O) :=
  specList_complete (parseMeta_complete O (identifier_complete O D) _) _ _

end SudoersSpec.Grammar
