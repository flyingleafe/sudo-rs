import SudoersSpec.Grammar.Permission
import SudoersSpec.Syntax.Sudo

namespace SudoersSpec.Grammar

open SudoersSpec.Syntax SudoersSpec.Syntax.Parser

/-- The keys for which directive dispatch does not apply. This is a classification of the
first user value; it is not a predicate on the result of an attempted directive parse. -/
def OrdinaryKey : Spec UserSpecifier → Prop
  | .allow (.only (.user (.name keyword))) =>
    keyword ≠ "User_Alias" ∧ keyword ≠ "Host_Alias" ∧ keyword ≠ "Cmnd_Alias" ∧
    keyword ≠ "Cmd_Alias" ∧ keyword ≠ "Runas_Alias" ∧
    "Defaults".toList.isPrefixOf keyword.toList = false
  | _ => True

theorem aBind_not_reject {s0 s : Stream} {p : AParser s0 α} {q : α → AParser s0 β}
    (hp : (p.run s).1 ≠ .error .reject) (hq : ∀ a t, ((q a).run t).1 ≠ .error .reject) :
    (((p >>= q)).run s).1 ≠ .error .reject := by
  rw [AParser.run_bind]
  rcases h : p.run s with ⟨res, t⟩
  rw [h] at hp
  cases res with
  | ok a => exact hq a t
  | error e => intro he; exact hp (congrArg Except.error (Except.error.inj he))

private theorem aExpected_not_reject (p : Parser α) (d : String) (s0 s : Stream) :
    ((monadLift (expectNonterminal d p) : AParser s0 α).run s).1 ≠ .error .reject :=
  expectNonterminal_ne_reject d p s

private theorem defaultsScope_not_reject (O : Oracles) (D : Descriptions) (r : List Char)
    (s0 s : Stream) : ((defaultsScope O D r s0).run s).1 ≠ .error .reject := by
  unfold defaultsScope
  split
  · apply aBind_not_reject (by simp [AParser.run_restore]); intro _ _
    apply aBind_not_reject (by simp); intro _ _
    apply aBind_not_reject (skipTrailingWhitespace_ne_reject _); intro _ _
    exact aBind_not_reject (aExpected_not_reject _ _ _ _) (fun _ _ => by simp)
  · apply aBind_not_reject (isSyntax_ne_reject ':' s); intro b t
    cases b
    · apply aBind_not_reject (isSyntax_ne_reject '!' t); intro b t
      cases b
      · apply aBind_not_reject (isSyntax_ne_reject '>' t); intro b t
        cases b
        · simp
        · exact aBind_not_reject (aExpected_not_reject _ _ _ _) (fun _ _ => by simp)
      · exact aBind_not_reject (aExpected_not_reject _ _ _ _) (fun _ _ => by simp)
    · exact aBind_not_reject (aExpected_not_reject _ _ _ _) (fun _ _ => by simp)

private theorem directive_reject_iff (O : Oracles) (D : Descriptions) (key : Spec UserSpecifier)
    (s0 s t : Stream) :
    (getDirective O D key s0).run s = (.error .reject, t) ↔ t = s ∧ OrdinaryKey key := by
  unfold getDirective OrdinaryKey
  split
  · rename_i keyword
    have no : ∀ {p : AParser s0 Directive}, (p.run s).1 ≠ .error .reject →
        p.run s ≠ (.error .reject, t) := fun hp he => hp (congrArg Prod.fst he)
    split
    case h_1 | h_2 | h_3 | h_4 | h_5 =>
      exact iff_of_false (no (aBind_not_reject (aExpected_not_reject _ _ _ _) (fun _ _ => by simp)))
        (by simp)
    case h_6 =>
      rename_i _ h1 h2 h3 h4 h5
      by_cases hD : "Defaults".toList.isPrefixOf keyword.toList = true
      · simp only [hD, ite_true]
        refine iff_of_false (no ?_) (by simp)
        apply aBind_not_reject (by simp); intro _ t
        split
        · apply aBind_not_reject (defaultsScope_not_reject O D _ _ _); intro _ t
          exact aBind_not_reject (aExpected_not_reject _ _ _ _) (fun _ _ => by simp)
        · apply aBind_not_reject (by simp); intro _ t
          exact aBind_not_reject (aExpected_not_reject _ _ _ _) (fun _ _ => by simp)
      · have he : "Defaults".toList.isPrefixOf keyword.toList = false := by
          cases e : "Defaults".toList.isPrefixOf keyword.toList
          · rfl
          · exact False.elim (hD e)
        simp only [he, Bool.false_eq_true, ite_false]
        change (Except.error Status.reject, s) = (.error .reject, t) ↔ t = s ∧ _
        constructor
        · intro h; cases h
          exact ⟨rfl, h1, h2, h3, h4, h5, trivial⟩
        · rintro ⟨rfl, _⟩; rfl
  · change (Except.error Status.reject, s) = (.error .reject, t) ↔ t = s ∧ _
    split <;> simp_all [eq_comm]

/-- The leading-`#` branch reads one raw identifier, then the usual list after an optional comma.
The extra first item is separate from the tail's limit, just as in `sudoHash`. -/
def HashUsersG (O : Oracles) : Gram (SpecList UserSpecifier) :=
  SeqG (NontermG (IdentifierG O)) fun a =>
    SeqG (SyntaxMarkG ',') fun comma =>
      if comma then MapG (NontermG (UserListG O)) (fun users => .allow (.only (.user a)) :: users)
      else PureG [.allow (.only (.user a))]

private def hashUsers (O : Oracles) (D : Descriptions) : Parser (SpecList UserSpecifier) := do
  let a ← tryNonterminal (identifier O D)
  let comma ← isSyntax ','
  if comma then
    let u ← expectNonterminal D.userSpecifier (specListUserSpecifier O D)
    pure (.allow (.only (.user a)) :: u)
  else pure [.allow (.only (.user a))]

private theorem hashUsers_sound (O : Oracles) (D : Descriptions) :
    Sound (hashUsers O D) (HashUsersG O) := by
  unfold hashUsers HashUsersG
  apply seq_sound (tryNonterminal_sound (identifier_sound O D)); intro a
  apply seq_sound (syntaxMark_sound ','); intro b
  cases b
  · exact pure_sound _
  · exact mapP_sound (expectNonterminal_sound (userList_sound O D) _) _

private theorem hashUsers_complete (O : Oracles) (D : Descriptions) :
    Complete (hashUsers O D) (HashUsersG O) := by
  unfold hashUsers HashUsersG
  apply seq_complete (tryNonterminal_complete (identifier_complete O D)); intro a
  apply seq_complete (syntaxMark_complete ','); intro b
  cases b
  · exact pure_complete _
  · exact mapP_complete (expectNonterminal_complete (userList_complete O D) _) _

abbrev DispatchForm (O : Oracles) (U : Gram (SpecList UserSpecifier)) (E : Gram PermissionEntry) :
    Gram PermissionSpec :=
  SeqG U fun u => MapG (NontermG (PermissionsForm O E)) (fun p => ⟨u, p⟩)

private abbrev finishPermission (O : Oracles) (D : Descriptions) (u : SpecList UserSpecifier) :
    Parser Sudo := MapP (expectNonterminal D.hostsRunasCommands (permissions O D))
      (fun p => .spec ⟨u, p⟩)

private abbrev joinedPermission (O : Oracles) (D : Descriptions) (p : Parser (SpecList UserSpecifier)) :
    Parser Sudo := p >>= finishPermission O D

abbrev SudoDispatchG (G : Gram PermissionSpec) : Gram Sudo :=
  fun c a r => ∃ p, a = .spec p ∧ G c p r

private theorem dispatch_sound (O : Oracles) (D : Descriptions) {p : Parser (SpecList UserSpecifier)}
    {G : Gram (SpecList UserSpecifier)} (hp : Sound p G) :
    Sound (joinedPermission O D p) (SudoDispatchG (DispatchForm O G (EntryG O))) := by
  have hs := seq_sound hp (fun u => mapP_sound (expectNonterminal_sound (permissions_sound O D)
    D.hostsRunasCommands)
    (fun p => Sudo.spec ⟨u, p⟩))
  apply hs.mono
  rintro c a r ⟨x, y, u, rfl, hx, p, hy, rfl⟩
  exact ⟨_, rfl, x, y, u, rfl, hx, p, hy, rfl⟩

private theorem dispatch_complete (O : Oracles) (D : Descriptions) {p : Parser (SpecList UserSpecifier)}
    {G : Gram (SpecList UserSpecifier)} (hp : Complete p G) :
    Complete (joinedPermission O D p) (SudoDispatchG (DispatchForm O G (CleanEntryG O))) := by
  have hs := seq_complete hp (fun u => mapP_complete (expectNonterminal_complete (permissions_complete O D)
    D.hostsRunasCommands)
    (fun p => Sudo.spec ⟨u, p⟩))
  apply hs.mono
  rintro c a r ⟨_, rfl, x, y, u, rfl, hx, p, hy, eq⟩
  exact ⟨x, y, u, rfl, hx, p, hy, congrArg Sudo.spec eq⟩

private theorem parseInclude_not_spec (O : Oracles) (D : Descriptions) (s t : Stream)
    (p : PermissionSpec) : (parseInclude O D).run s ≠ (.ok (.spec p), t) := by
  intro h
  obtain ⟨start, u, _, hh⟩ := run_bind_eq_ok.mp h
  obtain ⟨key, v, _, hh⟩ := run_bind_eq_ok.mp hh
  split at hh
  · obtain ⟨⟨_, _⟩, _, _, he⟩ := run_bind_eq_ok.mp hh
    cases he
  · obtain ⟨⟨_, _⟩, _, _, he⟩ := run_bind_eq_ok.mp hh
    cases he
  · cases hh

private theorem sudoHash_ok_iff (O : Oracles) (D : Descriptions) (s t : Stream) (p : PermissionSpec) :
    (sudoHash O D).run s = (.ok (.spec p), t) ↔
      (joinedPermission O D (hashUsers O D)).run s = (.ok (.spec p), t) := by
  simp only [sudoHash, joinedPermission, hashUsers, run_bind, run_observe]
  cases h : (tryNonterminal (identifier O D)).run s with
  | mk res u =>
    cases res with
    | ok a =>
      simp only [run_bind]
      cases (isSyntax ',').run u with
      | mk e v =>
        cases e with
        | error _ => rfl
        | ok b =>
          cases b with
          | false => rfl
          | true =>
            simp only [ite_true, run_bind]
            cases (expectNonterminal D.userSpecifier (specListUserSpecifier O D)).run v with
            | mk e v => cases e <;> rfl
    | error e =>
      simp only [run_bind, run_observe]
      rcases hi : (parseInclude O D).run u with ⟨ri, v⟩
      cases ri with
      | ok a =>
        constructor
        · intro e
          simp only [run_pure, Prod.mk.injEq, Except.ok.injEq] at e
          exact False.elim (parseInclude_not_spec O D u t p (hi.trans (by rw [e.1, e.2])))
        · intro e; cases e
      | error st => simp [run_bind]

/-- The permission fragment of `Sudo`: a separate leading-`#` form; a quoted-first-user
form; and the ordinary form, in which the first parsed user cannot select a directive. -/
inductive SudoPermissionForm (O : Oracles) (E : Gram PermissionEntry) : Gram PermissionSpec
  | hash : (c ++ r).head? = some '#' → DispatchForm O (HashUsersG O) E c a r →
      SudoPermissionForm O E c a r
  | quoted : (c ++ r).head? = some '"' → PermissionForm O E c a r → SudoPermissionForm O E c a r
  | ordinary : NextNot (fun d => d = '@' ∨ d = '#' ∨ d = '"') (c ++ r) →
      OrdinaryKey (a.users.headD (.allow .all)) → PermissionForm O E c a r →
      SudoPermissionForm O E c a r

abbrev SudoPermissionG (O : Oracles) := SudoPermissionForm O (EntryG O)
abbrev PositiveSudoPermissionG (O : Oracles) := SudoPermissionForm O (CleanEntryG O)

/-- A successful permission from the ordinary branch agrees with the selected permission
production. Completeness needs a key for which the directive branch is absent. -/
private theorem sudoMain_spec_iff (O : Oracles) (D : Descriptions) (s t : Stream) (p : PermissionSpec)
    (hquote : s.peek ≠ some '"') :
    (sudoMain O D s).run s = (.ok (.spec p), t) ↔
      OrdinaryKey (p.users.headD (.allow .all)) ∧
      (permissionLine O D).run s = (.ok p, t) := by
  have hbeq : (s.peek == some '"') = false := by simpa using hquote
  simp only [sudoMain, permissionLine, AParser.run_bind, AParser.run_lift, run_peek,
    hbeq, Bool.false_eq_true, ite_false, run_maybe, run_bind]
  cases h : (tryNonterminal (specListUserSpecifier O D)).run s with
  | mk rr u =>
    cases rr with
    | error e => cases e <;> simp
    | ok users =>
      simp only [maybe_ok]
      have he := directive_reject_iff O D (users.headD (.allow .all)) s u
      cases hd : (getDirective O D (users.headD (.allow .all)) s).run u with
      | mk rd v =>
        cases rd with
        | ok d =>
          have hn : ¬ OrdinaryKey (users.headD (.allow .all)) := fun ho => by
            have := (he u).mpr ⟨rfl, ho⟩
            rw [hd] at this
            cases this
          constructor
          · intro h
            simp only [AParser.run_bind, AParser.run_maybe, hd, maybe_ok] at h
            split at h <;> simp at h
          · rintro ⟨hk, hp⟩
            revert hp
            cases (expectNonterminal D.hostsRunasCommands (permissions O D)).run u with
            | mk rp v =>
              cases rp with
              | error e => simp
              | ok pp =>
                simp only [run_pure, Prod.mk.injEq, Except.ok.injEq]
                rintro ⟨rfl, _⟩
                exact False.elim (hn hk)
        | error e =>
          cases e with
          | fatal span kind =>
            have hn : ¬ OrdinaryKey (users.headD (.allow .all)) := fun ho => by
              have := (he u).mpr ⟨rfl, ho⟩
              rw [hd] at this
              cases this
            constructor
            · intro h
              simp only [AParser.run_bind, AParser.run_maybe, hd, maybe_fatal] at h
              cases h
            · rintro ⟨hk, hp⟩
              revert hp
              cases (expectNonterminal D.hostsRunasCommands (permissions O D)).run u with
              | mk rp v =>
                cases rp with
                | error e => simp
                | ok pp =>
                  simp only [run_pure, Prod.mk.injEq, Except.ok.injEq]
                  rintro ⟨rfl, _⟩
                  exact False.elim (hn hk)
          | reject =>
            obtain ⟨hv, hk⟩ := (he v).mp hd
            subst v
            simp only [AParser.run_maybe, hd, maybe_reject, AParser.run_bind, AParser.run_lift]
            cases (expectNonterminal D.hostsRunasCommands (permissions O D)).run u with
            | mk rp v =>
              cases rp with
              | error e => simp
              | ok pp =>
                simp only [run_pure, AParser.run_pure, Prod.mk.injEq, Except.ok.injEq, Sudo.spec.injEq]
                exact ⟨fun e => ⟨by rw [← e.1]; exact hk, e⟩, And.right⟩

private theorem sudoMain_quote_eq (O : Oracles) (D : Descriptions) (s : Stream)
    (h : s.peek = some '"') : (sudoMain O D s).run s =
      (joinedPermission O D (expectNonterminal D.userSpecifier (specListUserSpecifier O D))).run s := by
  simp only [sudoMain, joinedPermission, finishPermission, AParser.run_bind, AParser.run_lift,
    run_peek, h, beq_self_eq_true, ite_true, run_bind]
  rcases (expectNonterminal D.userSpecifier (specListUserSpecifier O D)).run s with ⟨rr, u⟩
  cases rr with
  | error _ => rfl
  | ok a =>
    rcases (expectNonterminal D.hostsRunasCommands (permissions O D)).run u with ⟨rr, v⟩
    cases rr <;> rfl

private theorem sudo_not_at (O : Oracles) (D : Descriptions) (s : Stream)
    (hn : s.peek ≠ some '@') : (sudo O D).run s =
      if s.peek = some '#' then (sudoHash O D).run s else (sudoMain O D s).run s := by
  simp only [sudo, run_bind, run_eatChar, Stream.eatChar_eq, hn, ite_false, Bool.false_eq_true,
    run_peek]
  by_cases h : s.peek = some '#'
  · simp [h]
  · have he : (s.peek == some '#') = false := by simpa using h
    simp [he, h]

/-- PT3 for the actual `Syntax.sudo` permission-producing branches, including the leading-`#`
branch. The selected entry and position come from the real production, not a reparse. -/
theorem sudo_permission_sound (O : Oracles) (D : Descriptions) {s t : Stream} {a : PermissionSpec}
    (h : (sudo O D).run s = (.ok (.spec a), t)) :
    ∃ c, s.rest = c ++ t.rest ∧ SudoPermissionG O c a t.rest ∧ t.getPos = posAfter c s.getPos := by
  have hn : s.peek ≠ some '@' := by
    intro he
    have ha : (sudo O D).run s = (parseInclude O D).run s.pop := by
      simp only [sudo, run_bind, run_eatChar, Stream.eatChar_eq, he, ite_true]
    rw [ha] at h
    exact parseInclude_not_spec O D _ _ _ h
  have pos {c : List Char} (hs : s.rest = c ++ t.rest) : t.getPos = posAfter c s.getPos := by
    rw [(reaches_of_run h).getPos_eq.2, hs, take_sub_length_append]
  have hs := h
  rw [sudo_not_at O D s hn] at hs
  split at hs
  · rename_i hh
    obtain ⟨c, hc, b, he, hd⟩ := dispatch_sound O D (hashUsers_sound O D) _ _ _
      ((sudoHash_ok_iff O D s t a).mp hs)
    cases he
    exact ⟨c, hc, .hash (by rw [← hc]; exact hh) hd, pos hc⟩
  · rename_i hh
    by_cases hq : s.peek = some '"'
    · rw [sudoMain_quote_eq O D s hq] at hs
      obtain ⟨c, hc, b, he, hd⟩ := dispatch_sound O D (expectNonterminal_sound (userList_sound O D) _) _ _ _ hs
      cases he
      exact ⟨c, hc, .quoted (by rw [← hc]; exact hq) hd, pos hc⟩
    · obtain ⟨hk, he⟩ := (sudoMain_spec_iff O D s t a hq).mp hs
      obtain ⟨c, hc, hd⟩ := permissionLine_sound O D _ _ _ he
      have hguard : NextNot (fun d => d = '@' ∨ d = '#' ∨ d = '"') (c ++ t.rest) := by
        rw [← hc]
        intro d hd hch
        rcases hch with rfl | rfl | rfl
        · exact hn hd
        · exact hh hd
        · exact hq hd
      exact ⟨c, hc, .ordinary hguard hk hd, pos hc⟩

/-- PT4 for the actual permission branches, on the clean grammar. -/
theorem sudo_permission_complete (O : Oracles) (D : Descriptions) {c r : List Char}
    {a : PermissionSpec} {s : Stream} (h : PositiveSudoPermissionG O c a r)
    (hs : s.rest = c ++ r) : ∃ t, (sudo O D).run s = (.ok (.spec a), t) ∧ t.rest = r := by
  have hpk : s.peek = (c ++ r).head? := hs ▸ rfl
  cases h with
  | hash hh hd =>
    obtain ⟨t, ht, hr⟩ := dispatch_complete O D (hashUsers_complete O D) c (.spec a) r s ⟨a, rfl, hd⟩ hs
    have he : s.peek = some '#' := hpk.trans hh
    have hn : s.peek ≠ some '@' := by rw [he]; decide
    exact ⟨t, by rw [sudo_not_at O D s hn, ite_eq_left he]; exact (sudoHash_ok_iff O D s t a).mpr ht, hr⟩
  | quoted hq hd =>
    obtain ⟨t, ht, hr⟩ := dispatch_complete O D (expectNonterminal_complete (userList_complete O D) _)
      c (.spec a) r s ⟨a, rfl, hd⟩ hs
    have he : s.peek = some '"' := hpk.trans hq
    have hn : s.peek ≠ some '@' := by rw [he]; decide
    have hh : s.peek ≠ some '#' := by rw [he]; decide
    exact ⟨t, by rw [sudo_not_at O D s hn, ite_eq_right hh, sudoMain_quote_eq O D s he]; exact ht, hr⟩
  | ordinary hn hk hd =>
    have notAt : s.peek ≠ some '@' := fun h => hn '@' (hpk.symm.trans h) (.inl rfl)
    have notHash : s.peek ≠ some '#' := fun h => hn '#' (hpk.symm.trans h) (.inr (.inl rfl))
    have notQuote : s.peek ≠ some '"' := fun h => hn '"' (hpk.symm.trans h) (.inr (.inr rfl))
    obtain ⟨t, ht, hr⟩ := permissionLine_complete O D c a r s hd hs
    refine ⟨t, ?_, hr⟩
    rw [sudo_not_at O D s notAt, ite_eq_right notHash]
    exact (sudoMain_spec_iff O D s t a notQuote).mpr ⟨hk, ht⟩

/-- PT4 with the exact output position for the actual permission branches of `sudo`. -/
theorem sudo_permission_pt4 (O : Oracles) (D : Descriptions) {c r : List Char}
    {a : PermissionSpec} (h : PositiveSudoPermissionG O c a r) (line col : Nat) :
    (sudo O D).run ⟨c ++ r, line, col⟩ =
      (.ok (.spec a), ⟨r, (posAfter c (line, col)).1, (posAfter c (line, col)).2⟩) := by
  obtain ⟨t, ht, hr⟩ := sudo_permission_complete O D (s := ⟨c ++ r, line, col⟩) h rfl
  rw [ht, run_eq_of_rest ht hr]

/-- A clean permission derivation determines the consumed prefix and value on a fixed input. -/
theorem sudo_permission_unambiguous (O : Oracles) (D : Descriptions)
    {c c' r r' : List Char} {a a' : PermissionSpec}
    (h₁ : PositiveSudoPermissionG O c a r) (h₂ : PositiveSudoPermissionG O c' a' r')
    (he : c ++ r = c' ++ r') : c = c' ∧ a = a' := by
  have hc : Complete (sudo O D) (SudoDispatchG (PositiveSudoPermissionG O)) := by
    rintro x _ y s ⟨b, rfl, hg⟩ hs
    exact sudo_permission_complete O D hg hs
  obtain ⟨hc', ha⟩ := hc.unambiguous ⟨a, rfl, h₁⟩ ⟨a', rfl, h₂⟩ he
  exact ⟨hc', Sudo.spec.inj ha⟩

end SudoersSpec.Grammar
