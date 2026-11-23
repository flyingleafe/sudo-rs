import SudoersSpec.Grammar.SudoCommandAt
import SudoersSpec.Grammar.SudoCursorList
import SudoersSpec.Grammar.SudoListFailure
import SudoersSpec.Grammar.SudoRunasExact
import SudoersSpec.Grammar.SudoUserFailure

/-! Exact stable permission groups. Command tags retain their ambient positions; optional
runas clauses retain the true boundaries of recovered failures. -/

namespace SudoersSpec.Grammar

open SudoersSpec.Syntax SudoersSpec.Syntax.Parser

theorem expectNonterminal_at_iff {p : Parser α} {G : Stream → α → Stream → Prop}
    (hp : ∀ {s t a}, p.run s = (.ok a, t) ↔ G s a t) (desc : String) {s t : Stream} {a : α} :
    (expectNonterminal desc p).run s = (.ok a, t) ↔ CursorNontermG G s a t :=
  expectNonterminal_ok_iff.trans (tryNonterminal_at_iff hp)

/-- The exact recoverable user-list failure for runas, including failures in trailing space. -/
abbrev RunasUserFailureG (O : Oracles) : Gram Unit :=
  NontermFailureG (UserListG O) (SpecListFailureG (MetaUserG O) (MetaUserFailureG O) userSpecifierMany)

private theorem runasUserFailure_sound (O : Oracles) (D : Descriptions) :
    FailureSound (tryNonterminal (specListUserSpecifier O D)) (RunasUserFailureG O) :=
  tryNonterm_failure (userList_sound O D)
    (specList_failure_sound (parseMeta_sound O (userSpecifier_sound O D) _)
      (metaUser_failure_sound O D) userSpecifierMany D.userSpecifier)

private theorem runasUserFailure_complete (O : Oracles) (D : Descriptions) :
    FailureComplete (tryNonterminal (specListUserSpecifier O D)) (RunasUserFailureG O) :=
  tryNontermFailure_complete (userList_complete O D)
    (specList_failure_complete (parseMeta_complete O (userSpecifier_complete O D) _)
      (metaUser_failure_complete O D) userSpecifierMany D.userSpecifier)

/-- The runas outcome uses either user error, but only group rejection, as a fallback. -/
abbrev ExactRunasG (O : Oracles) := RunasWithFailureG O (RunasUserFailureG O) (IdentifierListRejectG O)

theorem exactRunas_sound (O : Oracles) (D : Descriptions) : Sound (runAs O D) (ExactRunasG O) :=
  runasWithFailure_sound O D (runasUserFailure_sound O D) (identifierList_reject_sound O D)

theorem exactRunas_complete (O : Oracles) (D : Descriptions) : Complete (runAs O D) (ExactRunasG O) :=
  runasWithFailure_complete O D (runasUserFailure_complete O D) (identifierList_reject_complete O D)

private abbrev OptionalRunasG (O : Oracles) : Gram (Option RunAs) :=
  NontermG (OptG (ExactRunasG O) (AbsentSyntaxG '('))

/-- Optional runas followed by the command, before the entry list's own trailing space. -/
def EntryAtG (O : Oracles) (s : Stream) (a : PermissionEntry) (t : Stream) : Prop :=
  ∃ u, AtCursor (OptionalRunasG O) s a.1 u ∧ CursorNontermG (CommandAtG O) u a.2 t

private theorem optionalRunas_sound (O : Oracles) (D : Descriptions) :
    Sound (tryNonterminal (parseOption (runAs O D))) (OptionalRunasG O) :=
  tryNonterminal_sound (option_sound (exactRunas_sound O D) (runAs_rejectSound O D))

private theorem optionalRunas_complete (O : Oracles) (D : Descriptions) :
    Complete (tryNonterminal (parseOption (runAs O D))) (OptionalRunasG O) :=
  tryNonterminal_complete (option_complete (exactRunas_complete O D) (runAs_rejectComplete O D))

theorem runasCommand_at_iff (O : Oracles) (D : Descriptions) {s t : Stream} {a : PermissionEntry} :
    (runasCommand O D).run s = (.ok a, t) ↔ EntryAtG O s a t := by
  constructor
  · intro h
    unfold runasCommand at h
    obtain ⟨ra, u, hra, hcmd⟩ := run_bind_eq_ok.mp h
    have hr := (optionalRunas_sound O D).atCursor hra
    cases ra with
    | none =>
      obtain ⟨cmd, v, hc, he⟩ := run_bind_eq_ok.mp hcmd
      cases he
      exact ⟨u, hr, (tryNonterminal_at_iff (commandSpec_at_iff O D)).mp hc⟩
    | some ra =>
      obtain ⟨cmd, v, hc, he⟩ := run_bind_eq_ok.mp hcmd
      cases he
      exact ⟨u, hr, (expectNonterminal_at_iff (commandSpec_at_iff O D) _).mp hc⟩
  · rintro ⟨u, hra, hc⟩
    obtain ⟨ra, cmd⟩ := a
    unfold runasCommand
    refine run_bind_eq_ok.mpr ⟨ra, u, hra.complete (optionalRunas_complete O D), ?_⟩
    cases ra with
    | none => exact run_bind_eq_ok.mpr ⟨cmd, t, (tryNonterminal_at_iff (commandSpec_at_iff O D)).mpr hc, rfl⟩
    | some ra => exact run_bind_eq_ok.mpr ⟨cmd, t,
        (expectNonterminal_at_iff (commandSpec_at_iff O D) _).mpr hc, rfl⟩

abbrev EntriesAtG (O : Oracles) := CursorListG (EntryAtG O) runasCommandMany.sep runasCommandMany.limit

theorem permissionEntries_at_iff (O : Oracles) (D : Descriptions) {s t : Stream} {a : List PermissionEntry} :
    (permissionEntries O D).run s = (.ok a, t) ↔ EntriesAtG O s a t :=
  parseList_at_iff (runasCommand_at_iff O D) _ _ _

/-- A host list, the required `=`, and the exact runas-command list with its trailing space. -/
def PermissionGroupAtG (O : Oracles) (s : Stream) (a : PermissionGroup) (t : Stream) : Prop :=
  ∃ u v, AtCursor (NontermG (HostListG O.char)) s a.1 u ∧ AtCursor (SynG '=') u () v ∧
    CursorNontermG (EntriesAtG O) v a.2 t

private theorem hostList_sound (O : Oracles) (D : Descriptions) :
    Sound (specListHostname O.char D) (HostListG O.char) := specList_sound (metaHostname_sound O.char) _ _

private theorem hostList_complete (O : Oracles) (D : Descriptions) :
    Complete (specListHostname O.char D) (HostListG O.char) := specList_complete (metaHostname_complete O.char) _ _

theorem permissionGroup_at_iff (O : Oracles) (D : Descriptions) {s t : Stream} {a : PermissionGroup} :
    (hostsRunasCommands O D).run s = (.ok a, t) ↔ PermissionGroupAtG O s a t := by
  constructor
  · intro h
    obtain ⟨hosts, u, hh, h₁⟩ := run_bind_eq_ok.mp h
    obtain ⟨_, v, he, h₂⟩ := run_bind_eq_ok.mp h₁
    obtain ⟨entries, w, hl, hf⟩ := run_bind_eq_ok.mp h₂
    cases hf
    exact ⟨u, v, (tryNonterminal_sound (hostList_sound O D)).atCursor hh,
      (expectSyntax_sound '=').atCursor he, (expectNonterminal_at_iff (permissionEntries_at_iff O D) _).mp hl⟩
  · rintro ⟨u, v, hh, he, hl⟩
    obtain ⟨hosts, entries⟩ := a
    exact run_bind_eq_ok.mpr ⟨hosts, u, hh.complete (tryNonterminal_complete (hostList_complete O D)),
      run_bind_eq_ok.mpr ⟨(), v, he.complete (expectSyntax_complete '='),
        run_bind_eq_ok.mpr ⟨entries, t, (expectNonterminal_at_iff (permissionEntries_at_iff O D) _).mpr hl, rfl⟩⟩⟩

abbrev PermissionsAtG (O : Oracles) :=
  CursorListG (PermissionGroupAtG O) hostsRunasCommandsMany.sep hostsRunasCommandsMany.limit

theorem permissions_at_iff (O : Oracles) (D : Descriptions) {s t : Stream} {a : List PermissionGroup} :
    (permissions O D).run s = (.ok a, t) ↔ PermissionsAtG O s a t :=
  parseList_at_iff (permissionGroup_at_iff O D) _ _ _

end SudoersSpec.Grammar
