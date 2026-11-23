import SudoersSpec.Grammar.PermissionAtoms

namespace SudoersSpec.Grammar

open SudoersSpec.Syntax SudoersSpec.Syntax.Parser

/-- No successful derivation starts at this input, regardless of its split point. -/
def NoMatch (G : Gram α) (input : List Char) : Prop :=
  ∀ c a r, input = c ++ r → ¬ G c a r

theorem noMatch_of_error {p : Parser α} {G : Gram α} (hp : Complete p G)
    {s s' : Stream} {e : Status} (he : p.run s = (.error e, s')) : NoMatch G s.rest := by
  intro c a r hs hd
  obtain ⟨t, ht, _⟩ := hp _ _ _ _ hd hs
  rw [he] at ht
  cases ht

/-- An error swallowed by `RunAs` can advance the cursor. This rule records the skipped
prefix and the absence of *any* successful derivation on the original input. It is for PT3
only: it does not assert that the Skipped prefix is the parser's unique failure boundary. -/
def MissG (G : Gram α) : Gram Unit := fun c _ r => NoMatch G (c ++ r)

/-- Runas users: a successful list, or an observed error with its skipped prefix. -/
abbrev RunasUsersG (O : Oracles) : Gram (List (Spec UserSpecifier)) :=
  fun c a r => NontermG (UserListG O) c a r ∨ (a = [] ∧ MissG (NontermG (UserListG O)) c () r)

abbrev RunasGroupListG (O : Oracles) : Gram (List (Spec Identifier)) :=
  SeqG (SynG ':') fun _ => NontermG (IdentifierListG O)

/-- A `:` can be absent, or it can be read and followed by a rejecting group list. -/
inductive RunasGroupsG (O : Oracles) : Gram (List (Spec Identifier)) where
  | present : RunasGroupListG O c a r → RunasGroupsG O c a r
  | absent : NextNot (· = ':') r → RunasGroupsG O [] [] r
  | missing : SynG ':' d () (c ++ r) → MissG (NontermG (IdentifierListG O)) c () r →
      RunasGroupsG O (d ++ c) [] r

/-- The successful lexical rule shared between the general and canonical runas grammars. -/
def RunasForm (U : Gram (SpecList UserSpecifier)) (G : Gram (SpecList Identifier)) : Gram RunAs :=
  SeqG (SynG '(') fun _ =>
    SeqG U fun u => SeqG G fun g => MapG (SynG ')') fun _ => ⟨u, g⟩

abbrev RunAsG (O : Oracles) := RunasForm (RunasUsersG O) (RunasGroupsG O)

/-- A sufficient, position-free start test for an empty user list in canonical runas.
Neither the meta name token nor the direct user/name production starts here. In particular
this guard applies before `:` and `)` under the documented oracle assumptions. -/
def EmptyRunasUsers (O : Oracles) (r : List Char) : Prop :=
  NextNot (fun d => blank d = true ∨ d = '\\' ∨ d = '!' ∨ d = '"' ∨ d = '%' ∨
    d = '+' ∨ d = '#' ∨ Username.accept1st O.char d = true ∨ O.char.isUppercase d = true) r

abbrev CleanRunasUsersG (O : Oracles) : Gram (SpecList UserSpecifier) :=
  fun c a r => NontermG (UserListG O) c a r ∨ (c = [] ∧ a = [] ∧ EmptyRunasUsers O r)

inductive CleanRunasGroupsG (O : Oracles) : Gram (SpecList Identifier) where
  | present : RunasGroupListG O c a r → CleanRunasGroupsG O c a r
  | absent : NextNot (· = ':') r → CleanRunasGroupsG O [] [] r

abbrev CleanRunAsG (O : Oracles) := RunasForm (CleanRunasUsersG O) (CleanRunasGroupsG O)

/-- The clean trace uses a position-free guard, not an observed parser result. -/
theorem emptyRunasUsers_reject (O : Oracles) (D : Descriptions) {s : Stream}
    (h : EmptyRunasUsers O s.rest) : (specListUserSpecifier O D).run s = (.error .reject, s) := by
  have guard {P : Char → Prop} (hp : ∀ d, P d → blank d = true ∨ d = '\\' ∨ d = '!' ∨
      d = '"' ∨ d = '%' ∨ d = '+' ∨ d = '#' ∨ Username.accept1st O.char d = true ∨
      O.char.isUppercase d = true) := (NextNot.mono h hp : NextNot P s.rest)
  have hBang := guard (P := (· = '!')) (by intro d hd; exact .inr (.inr (.inl hd)))
  have symbol {ch : Char} (hn : NextNot (· = ch) s.rest) : (eatChar ch).run s = (.ok false, s) := by
    obtain ⟨t, ht, hr⟩ := mark_complete ch [] false s.rest s (.absent hn) rfl
    have e := (reaches_of_run ht).eq_of_length_eq (congrArg List.length hr)
    rwa [e] at ht
  have hq := symbol (guard (P := (· = '"')) (by intro d hd; exact .inr (.inr (.inr (.inl hd)))))
  have hg := symbol (guard (P := (· = '%')) (by intro d hd; exact .inr (.inr (.inr (.inr (.inl hd))))))
  have hp := symbol (guard (P := (· = '+')) (by intro d hd; exact .inr (.inr (.inr (.inr (.inr (.inl hd)))))))
  have hh := symbol (guard (P := (· = '#')) (by intro d hd; exact .inr (.inr (.inr (.inr (.inr (.inr (.inl hd))))))))
  have hm : EscStop (MetaUsernameToken O) (MetaUsernameToken O).accept1st s.rest := by
    intro d hd hit
    apply h d hd
    change ((Username.accept1st O.char d || O.char.isUppercase d) = true) ∨
      (true = true ∧ d = '\\') at hit
    rcases hit with ha | ⟨_, hd'⟩
    · simp only [Bool.or_eq_true] at ha
      exact .inr (.inr (.inr (.inr (.inr (.inr (.inr ha))))))
    · exact .inr (.inl hd')
  have hu : EscStop (usernameToken O) (usernameToken O).accept1st s.rest := by
    intro d hd hit
    apply h d hd
    change Username.accept1st O.char d = true ∨ (true = true ∧ d = '\\') at hit
    rcases hit with h' | ⟨_, h'⟩
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h')))))))
    · exact .inr (.inl h')
  have hw := guard (P := fun d => blank d = true ∨ d = '\\') (by
    intro d hd; exact hd.elim Or.inl (fun h' => .inr (.inl h')))
  obtain ⟨t, ht, hr⟩ := skipTrailingWhitespace_complete [] () s.rest s (Ws.nil_iff.mpr hw) rfl
  have he := (reaches_of_run ht).eq_of_length_eq (congrArg List.length hr)
  rw [he] at ht
  apply specList_reject_iff.mpr
  refine ⟨hBang, ?_⟩
  have hm' : (token (MetaUsernameToken O)).run s = (.error .reject, s) := by
    rw [token_run, acceptEscaped_stop _ _ hm]
  have hu' : (token (usernameToken O)).run s = (.error .reject, s) := by
    rw [token_run, acceptEscaped_stop _ _ hu]
  have hi : (identifier O D).run s = (.error .reject, s) := by
    simp only [identifier, run_bind, hh, Bool.false_eq_true, ite_false, tryNonterminal_run, hu']
  have hy : (parseUser O D).run s = (.error .reject, s) := by
    simp only [parseUser, run_bind, hg, hp, Bool.false_eq_true, ite_false, tryNonterminal_run, hi]
  have hz : (userSpecifier O D).run s = (.error .reject, s) := by
    simp only [userSpecifier, run_bind, hq, Bool.false_eq_true, ite_false, hy]
  simp only [metaUserSpecifier, parseMeta, parseOption, tryNonterminal_run, run_bind, run_maybe,
    hm', ht, hz, maybe_reject]

private abbrev parseRunasUsers (O : Oracles) (D : Descriptions) :=
  MapP (observe (tryNonterminal (specListUserSpecifier O D))) fun r =>
    match r with | .ok u => u | .error _ => []

private theorem runasUsers_sound (O : Oracles) (D : Descriptions) :
    Sound (parseRunasUsers O D) (RunasUsersG O) := by
  intro s a s' h
  simp only [run_bind, run_observe, run_pure, Prod.mk.injEq] at h
  revert h
  cases hu : (tryNonterminal (specListUserSpecifier O D)).run s with
  | mk r t => cases r with
    | ok u =>
      simp only [Except.ok.injEq]
      rintro ⟨rfl, rfl⟩
      obtain ⟨c, hc, hd⟩ := (tryNonterminal_sound (userList_sound O D)) _ _ _ hu
      exact ⟨c, hc, .inl hd⟩
    | error e =>
      simp only [Except.ok.injEq]
      rintro ⟨rfl, rfl⟩
      obtain ⟨c, hc⟩ := (reaches_of_run hu).suffix
      refine ⟨c, hc.symm, .inr ⟨rfl, ?_⟩⟩
      unfold MissG
      rw [hc]
      exact noMatch_of_error (tryNonterminal_complete (userList_complete O D)) hu

private theorem runasUsers_complete (O : Oracles) (D : Descriptions) :
    Complete (parseRunasUsers O D) (CleanRunasUsersG O) := by
  intro c a r s hd hs
  rcases hd with hd | ⟨rfl, rfl, hd⟩
  · obtain ⟨t, ht, hr⟩ := (tryNonterminal_complete (userList_complete O D)) _ _ _ _ hd hs
    exact ⟨t, by simp [parseRunasUsers, run_bind, ht], hr⟩
  · have h := tryNonterminal_reject.mpr (emptyRunasUsers_reject O D (by rw [hs]; exact hd))
    exact ⟨s, by simp [parseRunasUsers, run_bind, h], hs⟩

private abbrev parseRunasGroupList (O : Oracles) (D : Descriptions) : Parser (SpecList Identifier) :=
  do trySyntax ':'; tryNonterminal (specListIdentifier O D)

private theorem runasGroupList_sound (O : Oracles) (D : Descriptions) :
    Sound (parseRunasGroupList O D) (RunasGroupListG O) :=
  seq_sound (trySyntax_sound ':') (fun _ => tryNonterminal_sound (identifierList_sound O D))

private theorem runasGroupList_complete (O : Oracles) (D : Descriptions) :
    Complete (parseRunasGroupList O D) (RunasGroupListG O) :=
  seq_complete (trySyntax_complete ':') (fun _ => tryNonterminal_complete (identifierList_complete O D))

private abbrev parseRunasGroups (O : Oracles) (D : Descriptions) :=
  MapP (Parser.maybe (parseRunasGroupList O D)) (·.getD [])

private theorem runasGroupList_rejectSound (O : Oracles) (D : Descriptions) :
    RejectSound (parseRunasGroupList O D) (fun c _ r => RunasGroupsG O c [] r) := by
  intro s s' h
  rcases run_bind_eq_error.mp h with h | ⟨_, t, h₁, h₂⟩
  · obtain ⟨rfl, hn⟩ := trySyntax_reject_iff.mp h
    exact ⟨[], rfl, .absent hn⟩
  · obtain ⟨c, hc, hd⟩ := trySyntax_sound ':' _ _ _ h₁
    obtain ⟨d, he⟩ := (reaches_of_run h₂).suffix
    have hm := noMatch_of_error (tryNonterminal_complete (identifierList_complete O D)) h₂
    refine ⟨c ++ d, by rw [hc, ← he, List.append_assoc], .missing ?_ ?_⟩
    · rw [he]; exact hd
    · unfold MissG; rw [he]; exact hm

private theorem runasGroups_sound (O : Oracles) (D : Descriptions) :
    Sound (parseRunasGroups O D) (RunasGroupsG O) :=
  (mapP_sound (option_sound (runasGroupList_sound O D) (runasGroupList_rejectSound O D)) _).mono
    (by rintro c a r ⟨o, ho, rfl⟩; cases ho with
        | some h => exact .present h
        | none h => exact h)

private theorem runasGroups_complete (O : Oracles) (D : Descriptions) :
    Complete (parseRunasGroups O D) (CleanRunasGroupsG O) := by
  intro c a r s hd hs
  cases hd with
  | present h =>
    obtain ⟨t, ht, hr⟩ := runasGroupList_complete O D _ _ _ _ h hs
    have hm : (Parser.maybe (parseRunasGroupList O D)).run s = (.ok (some a), t) := by
      rw [run_maybe, ht]; rfl
    exact ⟨t, run_bind_of_ok hm _, hr⟩
  | absent h =>
    have ht : (trySyntax ':').run s = (.error .reject, s) :=
      trySyntax_reject_iff.mpr ⟨rfl, by rw [hs]; exact h⟩
    exact ⟨s, by simp [parseRunasGroups, run_bind, ht], hs⟩

private abbrev runAsModel (O : Oracles) (D : Descriptions) : Parser RunAs := do
  trySyntax '('
  let u ← parseRunasUsers O D
  let g ← parseRunasGroups O D
  expectSyntax ')'
  pure ⟨u, g⟩

private theorem runAs_run_eq (O : Oracles) (D : Descriptions) (s : Stream) :
    (runAs O D).run s = (runAsModel O D).run s := by
  simp only [runAs, runAsModel, run_bind]
  cases he : (trySyntax '(').run s with
  | mk e t => cases e with
    | error _ => rfl
    | ok _ =>
      simp only [run_observe, run_pure]
      cases hu : (tryNonterminal (specListUserSpecifier O D)).run t with
      | mk r u =>
        cases hg : (Parser.maybe (parseRunasGroupList O D)).run u with
        | mk g v => cases g <;> rfl

theorem runAs_sound (O : Oracles) (D : Descriptions) : Sound (runAs O D) (RunAsG O) := by
  intro s a t h
  rw [runAs_run_eq] at h
  exact (seq_sound (trySyntax_sound '(') (fun _ => seq_sound (runasUsers_sound O D)
    (fun _ => seq_sound (runasGroups_sound O D) (fun _ => mapP_sound (expectSyntax_sound ')') _)))) s a t h

theorem runAs_complete (O : Oracles) (D : Descriptions) : Complete (runAs O D) (CleanRunAsG O) := by
  intro c a r s hd hs
  rw [runAs_run_eq]
  exact (seq_complete (trySyntax_complete '(') (fun _ => seq_complete (runasUsers_complete O D)
    (fun _ => seq_complete (runasGroups_complete O D) (fun _ => mapP_complete (expectSyntax_complete ')') _)))) c a r s hd hs

abbrev AbsentSyntaxG (ch : Char) : Gram Unit := fun c _ r => c = [] ∧ NextNot (· = ch) r

theorem runAs_rejectSound (O : Oracles) (D : Descriptions) :
    RejectSound (runAs O D) (AbsentSyntaxG '(') := by
  intro s s' h
  rw [runAs_run_eq] at h
  rcases run_bind_eq_error.mp h with hit | ⟨_, t, _, hit⟩
  · obtain ⟨rfl, hn⟩ := trySyntax_reject_iff.mp hit
    exact ⟨[], rfl, rfl, hn⟩
  · exfalso
    rcases run_bind_eq_error.mp hit with h₁ | ⟨_, u, _, h₂⟩
    · simp only [parseRunasUsers, run_bind, run_observe, run_pure] at h₁
      cases h₁
    · rcases run_bind_eq_error.mp h₂ with h₁ | ⟨_, v, _, h₂⟩
      · unfold parseRunasGroups at h₁
        rcases run_bind_eq_error.mp h₁ with h₁ | ⟨_, _, _, h₁⟩
        · simp only [run_maybe, Prod.mk.injEq] at h₁
          have e := h₁.1
          cases eq : ((parseRunasGroupList O D).run u).1 with
          | ok _ => simp [eq] at e
          | error x => cases x <;> simp [eq] at e
        · cases h₁
      · rcases run_bind_eq_error.mp h₂ with h₁ | ⟨_, _, _, h₁⟩
        · simp only [expectSyntax, run_bind, run_observe] at h₁
          split at h₁ <;> simp [run_bind] at h₁
        · cases h₁

theorem runAs_rejectComplete (O : Oracles) (D : Descriptions) :
    RejectComplete (runAs O D) (AbsentSyntaxG '(') := by
  rintro c r s ⟨rfl, hn⟩ hs
  have h : (trySyntax '(').run s = (.error .reject, s) :=
    trySyntax_reject_iff.mpr ⟨rfl, by rw [hs]; exact hn⟩
  exact ⟨s, by rw [runAs_run_eq, run_bind_of_error h], hs⟩

end SudoersSpec.Grammar
