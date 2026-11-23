import SudoersSpec.Grammar.SudoPermissionAt
import SudoersSpec.Grammar.SudoFile

/-! The stable permission dispatch uses the same independent user-list grammar as the
soundness proof, but the permission tail is now cursor-indexed all the way to the tags. -/

namespace SudoersSpec.Grammar

open SudoersSpec.Syntax SudoersSpec.Syntax.Parser

private abbrev UserPrefixG (O : Oracles) := NontermG (UserListG O)
private abbrev PermissionTailG (O : Oracles) := CursorNontermG (PermissionsAtG O)

/-- Exact successful permission alternatives of `Sudo`, with ambient locations and exact
runas fallback boundaries in their command lists. -/
inductive ExactSudoPermissionG (O : Oracles) : Stream → PermissionSpec → Stream → Prop where
  | hash : s.peek = some '#' → AtCursor (HashUsersG O) s p.users u →
      PermissionTailG O u p.permissions t → ExactSudoPermissionG O s p t
  | quoted : s.peek = some '"' → AtCursor (UserPrefixG O) s p.users u →
      PermissionTailG O u p.permissions t → ExactSudoPermissionG O s p t
  | ordinary : OrdinaryStart s → OrdinaryKey (p.users.headD (.allow .all)) →
      AtCursor (UserPrefixG O) s p.users u → PermissionTailG O u p.permissions t →
      ExactSudoPermissionG O s p t

private abbrev hashUsersRead (O : Oracles) (D : Descriptions) : Parser (SpecList UserSpecifier) := do
  let a ← tryNonterminal (identifier O D)
  let comma ← isSyntax ','
  if comma then
    let u ← expectNonterminal D.userSpecifier (specListUserSpecifier O D)
    pure (.allow (.only (.user a)) :: u)
  else pure [.allow (.only (.user a))]

private theorem hashUsersRead_complete (O : Oracles) (D : Descriptions) :
    Complete (hashUsersRead O D) (HashUsersG O) := by
  unfold hashUsersRead HashUsersG
  apply seq_complete (tryNonterminal_complete (identifier_complete O D))
  intro a
  apply seq_complete (syntaxMark_complete ',')
  intro b
  cases b
  · exact pure_complete _
  · exact mapP_complete (expectNonterminal_complete (userList_complete O D) _) _

private abbrev finishPermission (O : Oracles) (D : Descriptions) (users : SpecList UserSpecifier) : Parser Sudo := do
  let perms ← expectNonterminal D.hostsRunasCommands (permissions O D)
  pure (.spec ⟨users, perms⟩)

private theorem finishPermission_iff (O : Oracles) (D : Descriptions) {s t : Stream}
    {users : SpecList UserSpecifier} {p : PermissionSpec} :
    (finishPermission O D users).run s = (.ok (.spec p), t) ↔
      users = p.users ∧ PermissionTailG O s p.permissions t := by
  constructor
  · intro h
    obtain ⟨perms, u, hp, h⟩ := run_bind_eq_ok.mp h
    cases h
    exact ⟨rfl, (expectNonterminal_at_iff (permissions_at_iff O D) _).mp hp⟩
  · rintro ⟨rfl, hp⟩
    exact run_bind_eq_ok.mpr ⟨p.permissions, t, (expectNonterminal_at_iff (permissions_at_iff O D) _).mpr hp, rfl⟩

private theorem hash_after_users (O : Oracles) (D : Descriptions) {s u : Stream}
    {users : SpecList UserSpecifier} (h : (hashUsersRead O D).run s = (.ok users, u)) :
    (sudoHash O D).run s = (finishPermission O D users).run u := by
  obtain ⟨id, v, hi, h⟩ := run_bind_eq_ok.mp h
  obtain ⟨b, w, hc, h⟩ := run_bind_eq_ok.mp h
  simp only [sudoHash, run_bind, run_observe, hi, hc]
  cases b with
  | false =>
    cases h
    rfl
  | true =>
    obtain ⟨tail, z, ht, he⟩ := run_bind_eq_ok.mp h
    cases he
    simp [run_bind, ht]

private theorem quoted_after_users (O : Oracles) (D : Descriptions) {s u : Stream}
    {users : SpecList UserSpecifier} (hq : s.peek = some '"')
    (h : (expectNonterminal D.userSpecifier (specListUserSpecifier O D)).run s = (.ok users, u)) :
    (sudoMain O D s).run s = (finishPermission O D users).run u := by
  simp [sudoMain, AParser.run_bind, AParser.run_lift, hq, h, run_bind]

private theorem getDirective_reject_ordinary (O : Oracles) (D : Descriptions) (s u : Stream)
    (key : Spec UserSpecifier) (h : OrdinaryKey key) :
    (getDirective O D key s).run u = (.error .reject, u) := by
  unfold getDirective
  split
  · rename_i word
    simp only [OrdinaryKey] at h
    obtain ⟨hu, hh, hc, hcmd, hr, hd⟩ := h
    split
    · exact (hu rfl).elim
    · exact (hh rfl).elim
    · exact (hc rfl).elim
    · exact (hcmd rfl).elim
    · exact (hr rfl).elim
    · simp only [hd, Bool.false_eq_true, ite_false, AParser.run_lift, run_reject]
  · rfl

private theorem ordinary_after_users (O : Oracles) (D : Descriptions) {s u : Stream}
    {users : SpecList UserSpecifier} (hq : s.peek ≠ some '"')
    (h : (tryNonterminal (specListUserSpecifier O D)).run s = (.ok users, u))
    (hk : OrdinaryKey (users.headD (.allow .all))) :
    (sudoMain O D s).run s = (finishPermission O D users).run u := by
  have hr := getDirective_reject_ordinary O D s u _ hk
  simp only [List.headD_eq_head?_getD] at hr
  simp [sudoMain, AParser.run_bind, AParser.run_lift, hq, h, hr, run_bind]

private theorem sudo_hash_run (O : Oracles) (D : Descriptions) {s : Stream}
    (hh : s.peek = some '#') : (sudo O D).run s = (sudoHash O D).run s := by
  simp [sudo, run_bind, Stream.eatChar_eq, hh]

private theorem sudo_main_run (O : Oracles) (D : Descriptions) {s : Stream}
    (ha : s.peek ≠ some '@') (hh : s.peek ≠ some '#') :
    (sudo O D).run s = (sudoMain O D s).run s := by
  simp [sudo, run_bind, Stream.eatChar_eq, ha, hh]

/-- The broad soundness derivation already identifies the correct prefix grammar, before
any permission-tail behavior is needed. Use its user prefix but not its recovered runas or
tag-span evidence. -/
private theorem userPrefix_of_dispatch (O : Oracles) {G : Gram (SpecList UserSpecifier)}
    {q : Parser (SpecList UserSpecifier)} (hq : Complete q G) {s t : Stream}
    {c : List Char} {p : PermissionSpec} (h : DispatchForm O G (EntryG O) c p t.rest)
    (hs : s.rest = c ++ t.rest) :
    ∃ u, q.run s = (.ok p.users, u) ∧ AtCursor G s p.users u := by
  obtain ⟨x, y, users, rfl, hg, perms, _, rfl⟩ := h
  rw [List.append_assoc] at hs
  obtain ⟨u, hu, hr⟩ := hq _ _ _ _ hg hs
  exact ⟨u, hu, AtCursor.of_run hu (hr.symm ▸ hs) (hr.symm ▸ hg)⟩

/-- The exact cursor grammar is equivalent to producing a permission item, for every
stable permission success, not only for printable ASTs. -/
theorem sudo_permission_at_iff (O : Oracles) (D : Descriptions) {s t : Stream} {p : PermissionSpec} :
    (sudo O D).run s = (.ok (.spec p), t) ↔ ExactSudoPermissionG O s p t := by
  constructor
  · intro h
    obtain ⟨c, hc, hg, _⟩ := sudo_permission_sound O D h
    cases hg with
    | hash hh hp =>
      have hh' : s.peek = some '#' := by simpa only [Stream.peek_eq_head, hc] using hh
      obtain ⟨u, hu, husers⟩ := userPrefix_of_dispatch O (hashUsersRead_complete O D) hp hc
      rw [sudo_hash_run O D hh', hash_after_users O D hu] at h
      exact .hash hh' husers ((finishPermission_iff O D).mp h).2
    | quoted hq hp =>
      have hq' : s.peek = some '"' := by simpa only [Stream.peek_eq_head, hc] using hq
      have ha : s.peek ≠ some '@' := by rw [hq']; decide
      have hh : s.peek ≠ some '#' := by rw [hq']; decide
      obtain ⟨u, hu, husers⟩ := userPrefix_of_dispatch O
        (expectNonterminal_complete (userList_complete O D) D.userSpecifier) hp hc
      rw [sudo_main_run O D ha hh, quoted_after_users O D hq' hu] at h
      exact .quoted hq' husers ((finishPermission_iff O D).mp h).2
    | ordinary hguard hk hp =>
      have ho : OrdinaryStart s := by simpa only [OrdinaryStart, hc] using hguard
      have ha : s.peek ≠ some '@' := fun he => ho '@' he (.inl rfl)
      have hh : s.peek ≠ some '#' := fun he => ho '#' he (.inr (.inl rfl))
      have hq : s.peek ≠ some '"' := fun he => ho '"' he (.inr (.inr rfl))
      obtain ⟨u, hu, husers⟩ := userPrefix_of_dispatch O (tryNonterminal_complete (userList_complete O D)) hp hc
      rw [sudo_main_run O D ha hh, ordinary_after_users O D hq hu hk] at h
      exact .ordinary ho hk husers ((finishPermission_iff O D).mp h).2
  · intro h
    cases h with
    | hash hh hu hp =>
      rw [sudo_hash_run O D hh, hash_after_users O D (hu.complete (hashUsersRead_complete O D))]
      exact (finishPermission_iff O D).mpr ⟨rfl, hp⟩
    | quoted hq hu hp =>
      have ha : s.peek ≠ some '@' := by rw [hq]; decide
      have hh : s.peek ≠ some '#' := by rw [hq]; decide
      rw [sudo_main_run O D ha hh, quoted_after_users O D hq
        (hu.complete (expectNonterminal_complete (userList_complete O D) _))]
      exact (finishPermission_iff O D).mpr ⟨rfl, hp⟩
    | ordinary ho hk hu hp =>
      have ha : s.peek ≠ some '@' := fun he => ho '@' he (.inl rfl)
      have hh : s.peek ≠ some '#' := fun he => ho '#' he (.inr (.inl rfl))
      have hq : s.peek ≠ some '"' := fun he => ho '"' he (.inr (.inr rfl))
      rw [sudo_main_run O D ha hh, ordinary_after_users O D hq
        (hu.complete (tryNonterminal_complete (userList_complete O D))) hk]
      exact (finishPermission_iff O D).mpr ⟨rfl, hp⟩

end SudoersSpec.Grammar
