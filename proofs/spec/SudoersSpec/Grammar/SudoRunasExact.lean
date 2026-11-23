import SudoersSpec.Grammar.PermissionRunAs
import SudoersSpec.Grammar.SudoFailure
import SudoersSpec.Grammar.SudoUserReject

/-! The extra lexical evidence needed to replace the two uses of `MissG` in `RunAsG`.
Users recover at the exact failure cursor for *either* kind of error. Groups recover at the
exact cursor of a *rejection*; fatal group failures cannot produce a runas clause. -/

namespace SudoersSpec.Grammar

open SudoersSpec.Syntax SudoersSpec.Syntax.Parser

abbrev RunasUsersWithFailureG (O : Oracles) (U : Gram Unit) : Gram (SpecList UserSpecifier) :=
  fun c u r => NontermG (UserListG O) c u r ∨ (u = [] ∧ U c () r)

abbrev RunasGroupRejectG (R : Gram Unit) : Gram Unit :=
  fun c u r => AbsentSyntaxG ':' c u r ∨ SeqG (SynG ':') (fun _ => R) c u r

abbrev RunasGroupsWithRejectG (O : Oracles) (R : Gram Unit) : Gram (SpecList Identifier) :=
  MapG (OptG (RunasGroupListG O) (RunasGroupRejectG R)) (·.getD [])

abbrev RunasWithFailureG (O : Oracles) (U R : Gram Unit) : Gram RunAs :=
  RunasForm (RunasUsersWithFailureG O U) (RunasGroupsWithRejectG O R)

private abbrev usersResult (O : Oracles) (D : Descriptions) : Parser (SpecList UserSpecifier) :=
  MapP (observe (tryNonterminal (specListUserSpecifier O D))) fun r =>
    match r with | .ok users => users | .error _ => []

private abbrev groupList (O : Oracles) (D : Descriptions) : Parser (SpecList Identifier) := do
  trySyntax ':'
  tryNonterminal (specListIdentifier O D)

private abbrev groupsResult (O : Oracles) (D : Descriptions) : Parser (SpecList Identifier) :=
  MapP (Parser.maybe (groupList O D)) (·.getD [])

private theorem run_eq (O : Oracles) (D : Descriptions) (s : Stream) :
    (runAs O D).run s = (do
      trySyntax '('
      let users ← usersResult O D
      let groups ← groupsResult O D
      expectSyntax ')'
      pure (⟨users, groups⟩ : RunAs)).run s := by
  simp only [runAs, run_bind]
  cases (trySyntax '(').run s with
  | mk e t =>
    cases e with
    | error _ => rfl
    | ok _ =>
      simp only [run_observe, run_pure]
      cases (tryNonterminal (specListUserSpecifier O D)).run t with
      | mk r u =>
        cases (Parser.maybe (groupList O D)).run u with
        | mk g v => cases g <;> rfl

private theorem users_complete (O : Oracles) (D : Descriptions) {U : Gram Unit}
    (hf : FailureComplete (tryNonterminal (specListUserSpecifier O D)) U) :
    Complete (usersResult O D) (RunasUsersWithFailureG O U) := by
  intro c a r s h hs
  rcases h with hu | ⟨rfl, he⟩
  · obtain ⟨t, ht, hr⟩ := tryNonterminal_complete (userList_complete O D) _ _ _ _ hu hs
    exact ⟨t, by simp [usersResult, run_bind, ht], hr⟩
  · obtain ⟨e, t, ht, hr⟩ := hf _ _ _ he hs
    exact ⟨t, by simp [usersResult, run_bind, ht], hr⟩

private theorem users_sound (O : Oracles) (D : Descriptions) {U : Gram Unit}
    (hf : FailureSound (tryNonterminal (specListUserSpecifier O D)) U) :
    Sound (usersResult O D) (RunasUsersWithFailureG O U) := by
  intro s a t h
  simp only [usersResult, MapP, run_bind, run_observe] at h
  rcases hr : (tryNonterminal (specListUserSpecifier O D)).run s with ⟨r, u⟩
  rw [hr] at h
  cases r with
  | ok users =>
    cases h
    obtain ⟨c, hc, hg⟩ := tryNonterminal_sound (userList_sound O D) _ _ _ hr
    exact ⟨c, hc, .inl hg⟩
  | error e =>
    cases h
    obtain ⟨c, hc, hg⟩ := hf _ _ _ hr
    exact ⟨c, hc, .inr ⟨rfl, hg⟩⟩

private theorem groupReject_complete (O : Oracles) (D : Descriptions) {R : Gram Unit}
    (hR : RejectComplete (tryNonterminal (specListIdentifier O D)) R) :
    RejectComplete (groupList O D) (RunasGroupRejectG R) := by
  intro c r s hg hs
  rcases hg with ⟨rfl, hn⟩ | ⟨pre, suf, _, rfl, hc, hr⟩
  · have hd : (trySyntax ':').run s = (.error .reject, s) :=
      trySyntax_reject_iff.mpr ⟨rfl, by rw [hs]; exact hn⟩
    exact ⟨s, by rw [groupList, run_bind_of_error hd], by simpa using hs⟩
  · obtain ⟨u, hu, ur⟩ := trySyntax_complete ':' _ _ _ _ hc (by rw [hs, List.append_assoc])
    obtain ⟨t, ht, tr⟩ := hR _ _ _ hr ur
    exact ⟨t, by rw [groupList, run_bind_of_ok hu, ht], tr⟩

private theorem groupReject_sound (O : Oracles) (D : Descriptions) {R : Gram Unit}
    (hR : RejectSound (tryNonterminal (specListIdentifier O D)) R) :
    RejectSound (groupList O D) (RunasGroupRejectG R) := by
  intro s t h
  rcases run_bind_eq_error.mp h with he | ⟨_, u, hu, hr⟩
  · obtain ⟨rfl, hn⟩ := trySyntax_reject_iff.mp he
    exact ⟨[], rfl, .inl ⟨rfl, hn⟩⟩
  · obtain ⟨pre, hpre, hG⟩ := trySyntax_sound ':' _ _ _ hu
    obtain ⟨suf, hsuf, hF⟩ := hR _ _ hr
    exact ⟨pre ++ suf, by rw [hpre, hsuf, List.append_assoc],
      .inr ⟨pre, suf, (), rfl, hsuf ▸ hG, hF⟩⟩

/-- Exact failure boundaries suffice for completeness; no absence-of-success heuristic
or restriction to zero-consumption recovery is needed. -/
theorem runasWithFailure_complete (O : Oracles) (D : Descriptions) {U R : Gram Unit}
    (hU : FailureComplete (tryNonterminal (specListUserSpecifier O D)) U)
    (hR : RejectComplete (tryNonterminal (specListIdentifier O D)) R) :
    Complete (runAs O D) (RunasWithFailureG O U R) := by
  intro c a r s hg hs
  rw [run_eq]
  exact (seq_complete (trySyntax_complete '(') (fun _ => seq_complete (users_complete O D hU)
    (fun _ => seq_complete (mapP_complete (option_complete
      (seq_complete (trySyntax_complete ':') (fun _ => tryNonterminal_complete (identifierList_complete O D)))
      (groupReject_complete O D hR)) _) (fun _ => mapP_complete (expectSyntax_complete ')') _))))
    c a r s hg hs

theorem runasWithFailure_sound (O : Oracles) (D : Descriptions) {U R : Gram Unit}
    (hU : FailureSound (tryNonterminal (specListUserSpecifier O D)) U)
    (hR : RejectSound (tryNonterminal (specListIdentifier O D)) R) :
    Sound (runAs O D) (RunasWithFailureG O U R) := by
  intro s a t h
  rw [run_eq] at h
  exact (seq_sound (trySyntax_sound '(') (fun _ => seq_sound (users_sound O D hU)
    (fun _ => seq_sound (mapP_sound (option_sound
      (seq_sound (trySyntax_sound ':') (fun _ => tryNonterminal_sound (identifierList_sound O D)))
      (groupReject_sound O D hR)) _) (fun _ => mapP_sound (expectSyntax_sound ')') _)))) s a t h

/-- An exact fragment with all user-list lexical rejections, including quoted/nested
rejections that advanced, and no recovery after a consumed `:`. -/
abbrev RunasUserRejectG (O : Oracles) := RunasWithFailureG O (UserListRejectG O) EmptyG

theorem runasUserReject_complete (O : Oracles) (D : Descriptions) :
    Complete (runAs O D) (RunasUserRejectG O) := by
  apply runasWithFailure_complete
  · intro c r s h hs
    obtain ⟨t, ht, hr⟩ := userList_reject_complete O D _ _ _ h hs
    exact ⟨.reject, t, ht, hr⟩
  · intro _ _ _ h; exact h.elim

end SudoersSpec.Grammar
