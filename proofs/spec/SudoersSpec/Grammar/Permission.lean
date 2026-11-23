import SudoersSpec.Grammar.PermissionTags

namespace SudoersSpec.Grammar

open SudoersSpec.Syntax SudoersSpec.Syntax.Parser

abbrev CommandTokenG (O : Oracles) : Gram (Meta Command) :=
  TokenG (metaToken O.char (commandToken O))
abbrev QualifiedCommandG (O : Oracles) := QualG (CommandTokenG O)

/-- A keyword, with trailing whitespace, or the failed keyword probe and its whitespace.
A failed probe, unlike failure of the command lexer, is not a failure of the command spec. -/
abbrev TagProbeG (K : Gram (Meta Modifier)) : Gram (Option (Meta Modifier)) :=
  NontermG (OptG K TagRejectG)

/-- The finite tag sequence. Bare `ALL` and a bare alias resolve the command directly;
otherwise the caller consumes a qualified command token after the failed keyword probe. -/
inductive TagLoopG (K : Gram (Meta Modifier)) : List Modifier → Gram (List Modifier ⊕ CommandSpec)
  | stop : TagProbeG K c none r → TagLoopG K mods c (.inl mods) r
  | all : TagProbeG K c (some .all) r → TagLoopG K mods c (.inr ⟨mods, .allow .all⟩) r
  | alias : TagProbeG K c (some (.alias name)) r →
      TagLoopG K mods c (.inr ⟨mods, .allow (.alias name)⟩) r
  | modifier : TagProbeG K c (some (.only m)) (tail ++ r) →
      (mods ++ [m]).length ≤ identifierMany.limit →
      TagLoopG K (mods ++ [m]) tail a r → TagLoopG K mods (c ++ tail) a r

private abbrev tagProbe (O : Oracles) (D : Descriptions) :=
  tryNonterminal (parseOption (metaOrTag O D))

private abbrev tagLoop (O : Oracles) (D : Descriptions) (mods : List Modifier) :=
  whileSome (tagProbe O D) (tryNonterminal_parseOption_consumesSome (metaOrTag_consumes O D))
    commandSpecBody .inl mods

private theorem tagProbe_sound (O : Oracles) (D : Descriptions) :
    Sound (tagProbe O D) (TagProbeG (MetaTagG O)) :=
  tryNonterminal_sound (option_sound (metaOrTag_sound O D) (metaOrTag_rejectSound O D))

private theorem tagProbe_complete (O : Oracles) (D : Descriptions) :
    Complete (tagProbe O D) (TagProbeG (CleanMetaTagG O)) :=
  tryNonterminal_complete (option_complete (metaOrTag_complete O D) (metaOrTag_rejectComplete O D))

private theorem tagLoop_sound (O : Oracles) (D : Descriptions) (mods : List Modifier) :
    Sound (tagLoop O D mods) (TagLoopG (MetaTagG O) mods) := by
  intro s a t h
  let hp := whileSomeBody_progressive (tryNonterminal_parseOption_consumesSome (metaOrTag_consumes O D))
    commandSpecBody Sum.inl
  have endCase : ∀ st src b dst,
      (whileSomeBody (tagProbe O D) commandSpecBody Sum.inl st).run src = (.ok (.done b), dst) →
      ∃ c, src.rest = c ++ dst.rest ∧ TagLoopG (MetaTagG O) st c b dst.rest := by
    intro st src b dst hb
    obtain ⟨x, mid, hx, hh⟩ := run_bind_eq_ok.mp hb
    cases x with
    | none =>
      simp only [run_pure, Prod.mk.injEq, Except.ok.injEq, Step.done.injEq] at hh
      obtain ⟨rfl, rfl⟩ := hh
      obtain ⟨c, hc, hg⟩ := tagProbe_sound O D _ _ _ hx
      exact ⟨c, hc, .stop hg⟩
    | some m =>
      cases m with
      | all =>
        simp only [commandSpecBody, run_pure, Prod.mk.injEq, Except.ok.injEq, Step.done.injEq] at hh
        obtain ⟨rfl, rfl⟩ := hh
        obtain ⟨c, hc, hg⟩ := tagProbe_sound O D _ _ _ hx
        exact ⟨c, hc, .all hg⟩
      | alias name =>
        simp only [commandSpecBody, run_pure, Prod.mk.injEq, Except.ok.injEq, Step.done.injEq] at hh
        obtain ⟨rfl, rfl⟩ := hh
        obtain ⟨c, hc, hg⟩ := tagProbe_sound O D _ _ _ hx
        exact ⟨c, hc, .alias hg⟩
      | only m =>
        simp only [commandSpecBody] at hh
        split at hh <;> simp at hh
  have nextCase : ∀ st src st' mid a (dst : Stream),
      (whileSomeBody (tagProbe O D) commandSpecBody Sum.inl st).run src = (.ok (.next st'), mid) →
      (∃ d, mid.rest = d ++ dst.rest ∧ TagLoopG (MetaTagG O) st' d a dst.rest) →
      ∃ c, src.rest = c ++ dst.rest ∧ TagLoopG (MetaTagG O) st c a dst.rest := by
    intro st src st' mid a dst hb ⟨d, hd, ht⟩
    obtain ⟨x, u, hx, hh⟩ := run_bind_eq_ok.mp hb
    cases x with
    | none => simp at hh
    | some m =>
      cases m with
      | all | alias _ => simp [commandSpecBody] at hh
      | only m =>
        simp only [commandSpecBody] at hh
        split at hh
        · simp at hh
        · rename_i hn
          simp only [run_pure, Prod.mk.injEq, Except.ok.injEq, Step.next.injEq] at hh
          obtain ⟨rfl, rfl⟩ := hh
          obtain ⟨c, hc, hg⟩ := tagProbe_sound O D _ _ _ hx
          refine ⟨c ++ d, by rw [hc, hd, List.append_assoc], .modifier ?_ (Nat.le_of_not_gt hn) ht⟩
          rwa [← hd]
  have hrel := loop_rel hp
    (fun st src r dst => ∀ b, r = .ok b →
      ∃ c, src.rest = c ++ dst.rest ∧ TagLoopG (MetaTagG O) st c b dst.rest)
    (by intro st src b dst h b' e; cases e; exact endCase _ _ _ _ h)
    (by intro st src e dst _ b h; cases h)
    (by intro st src st' mid r dst hh ih b he; exact nextCase _ _ _ _ _ _ hh (ih b he))
    mods s
  change ∀ b, ((tagLoop O D mods).run s).1 = .ok b →
    ∃ c, s.rest = c ++ ((tagLoop O D mods).run s).2.rest ∧
      TagLoopG (MetaTagG O) mods c b ((tagLoop O D mods).run s).2.rest at hrel
  rw [h] at hrel
  exact hrel a rfl

private theorem tagLoop_complete (O : Oracles) (D : Descriptions) (mods : List Modifier) :
    Complete (tagLoop O D mods) (TagLoopG (CleanMetaTagG O) mods) := by
  intro c a r s hg
  induction hg generalizing s with
  | stop hk =>
    intro hs
    obtain ⟨u, hu, hr⟩ := tagProbe_complete O D _ _ _ _ hk hs
    refine ⟨u, ?_, hr⟩
    unfold tagLoop whileSome
    rw [loop_run, whileSomeBody, run_bind_of_ok hu]
    rfl
  | all hk =>
    intro hs
    obtain ⟨u, hu, hr⟩ := tagProbe_complete O D _ _ _ _ hk hs
    refine ⟨u, ?_, hr⟩
    unfold tagLoop whileSome
    rw [loop_run, whileSomeBody, run_bind_of_ok hu]
    rfl
  | alias hk =>
    intro hs
    obtain ⟨u, hu, hr⟩ := tagProbe_complete O D _ _ _ _ hk hs
    refine ⟨u, ?_, hr⟩
    unfold tagLoop whileSome
    rw [loop_run, whileSomeBody, run_bind_of_ok hu]
    rfl
  | modifier hk hlim _ ih =>
    intro hs
    obtain ⟨u, hu, hr⟩ := tagProbe_complete O D _ _ _ _ hk (by rw [hs, List.append_assoc])
    obtain ⟨t, ht, tr⟩ := ih u hr
    refine ⟨t, ?_, tr⟩
    unfold tagLoop whileSome
    rw [loop_run, whileSomeBody, run_bind_of_ok hu]
    simp only [commandSpecBody, ite_eq_right (Nat.not_lt.mpr hlim), run_pure]
    exact ht

abbrev CommandSpecForm (O : Oracles) (K : Gram (Meta Modifier)) : Gram CommandSpec :=
  SeqG (TagLoopG K []) fun
    | .inl mods => MapG (NontermG (QualifiedCommandG O)) (fun cmd => ⟨mods, cmd⟩)
    | .inr cmd => PureG cmd

abbrev CommandSpecG (O : Oracles) := CommandSpecForm O (MetaTagG O)
abbrev CleanCommandSpecG (O : Oracles) := CommandSpecForm O (CleanMetaTagG O)

theorem commandSpec_sound (O : Oracles) (D : Descriptions) :
    Sound (commandSpec O D) (CommandSpecG O) := by
  unfold commandSpec
  apply seq_sound (tagLoop_sound O D [])
  intro s; cases s with
  | inl mods => exact mapP_sound (expectNonterminal_sound (qualified_sound (token_sound _) _) _) _
  | inr cmd => exact pure_sound cmd

theorem commandSpec_complete (O : Oracles) (D : Descriptions) :
    Complete (commandSpec O D) (CleanCommandSpecG O) := by
  unfold commandSpec
  apply seq_complete (tagLoop_complete O D [])
  intro s; cases s with
  | inl mods => exact mapP_complete (expectNonterminal_complete (qualified_complete (token_complete _) _) _) _
  | inr cmd => exact pure_complete cmd

abbrev PermissionEntry := Option RunAs × CommandSpec
abbrev PermissionGroup := SpecList Hostname × List PermissionEntry

abbrev EntryForm (R : Gram RunAs) (C : Gram CommandSpec) : Gram PermissionEntry :=
  SeqG (NontermG (OptG R (AbsentSyntaxG '('))) fun x =>
    MapG (NontermG C) (fun cmd => (x, cmd))

abbrev EntryG (O : Oracles) := EntryForm (RunAsG O) (CommandSpecG O)
abbrev CleanEntryG (O : Oracles) := EntryForm (CleanRunAsG O) (CleanCommandSpecG O)

abbrev EntriesG (E : Gram PermissionEntry) := ListG E ',' 127

abbrev GroupForm (O : Oracles) (E : Gram PermissionEntry) : Gram PermissionGroup :=
  SeqG (NontermG (HostListG O.char)) fun h =>
    SeqG (SynG '=') fun _ => MapG (NontermG (EntriesG E)) (fun es => (h, es))

abbrev PermissionsForm (O : Oracles) (E : Gram PermissionEntry) := ListG (GroupForm O E) ':' 127

abbrev permissionEntries (O : Oracles) (D : Descriptions) :=
  parseVec runasCommandMany D.runasCommand (runasCommand O D)

theorem runasCommand_sound (O : Oracles) (D : Descriptions) :
    Sound (runasCommand O D) (EntryG O) := by
  unfold runasCommand
  apply seq_sound (tryNonterminal_sound (option_sound (runAs_sound O D) (runAs_rejectSound O D)))
  intro x; cases x with
  | none => exact mapP_sound (tryNonterminal_sound (commandSpec_sound O D)) _
  | some r => exact mapP_sound (expectNonterminal_sound (commandSpec_sound O D) _) _

theorem runasCommand_complete (O : Oracles) (D : Descriptions) :
    Complete (runasCommand O D) (CleanEntryG O) := by
  unfold runasCommand
  apply seq_complete (tryNonterminal_complete (option_complete (runAs_complete O D) (runAs_rejectComplete O D)))
  intro x; cases x with
  | none => exact mapP_complete (tryNonterminal_complete (commandSpec_complete O D)) _
  | some r => exact mapP_complete (expectNonterminal_complete (commandSpec_complete O D) _) _

private theorem hosts_sound (O : Oracles) (D : Descriptions) :
    Sound (specListHostname O.char D) (HostListG O.char) :=
  specList_sound (metaHostname_sound O.char) _ _

private theorem hosts_complete (O : Oracles) (D : Descriptions) :
    Complete (specListHostname O.char D) (HostListG O.char) :=
  specList_complete (metaHostname_complete O.char) _ _

theorem hostsRunasCommands_sound (O : Oracles) (D : Descriptions) :
    Sound (hostsRunasCommands O D) (GroupForm O (EntryG O)) := by
  unfold hostsRunasCommands
  apply seq_sound (tryNonterminal_sound (hosts_sound O D))
  intro a
  apply seq_sound (expectSyntax_sound '=')
  intro _
  exact mapP_sound (expectNonterminal_sound (parseList_sound (runasCommand_sound O D) ',' 127 _) _) _

theorem hostsRunasCommands_complete (O : Oracles) (D : Descriptions) :
    Complete (hostsRunasCommands O D) (GroupForm O (CleanEntryG O)) := by
  unfold hostsRunasCommands
  apply seq_complete (tryNonterminal_complete (hosts_complete O D))
  intro a
  apply seq_complete (expectSyntax_complete '=')
  intro _
  exact mapP_complete (expectNonterminal_complete (parseList_complete (runasCommand_complete O D) ',' 127 _) _) _

theorem permissions_sound (O : Oracles) (D : Descriptions) :
    Sound (permissions O D) (PermissionsForm O (EntryG O)) :=
  parseList_sound (hostsRunasCommands_sound O D) ':' 127 _

theorem permissions_complete (O : Oracles) (D : Descriptions) :
    Complete (permissions O D) (PermissionsForm O (CleanEntryG O)) :=
  parseList_complete (hostsRunasCommands_complete O D) ':' 127 _

/-- The user-list and permission-groups production, after choosing the permission alternative.
`Syntax.sudo` also handles directive dispatch and its distinct leading-`#` branch. -/
def permissionLine (O : Oracles) (D : Descriptions) : Parser PermissionSpec := do
  let u ← tryNonterminal (specListUserSpecifier O D)
  let p ← expectNonterminal D.hostsRunasCommands (permissions O D)
  pure ⟨u, p⟩

abbrev PermissionForm (O : Oracles) (E : Gram PermissionEntry) : Gram PermissionSpec :=
  SeqG (NontermG (UserListG O)) (fun u =>
    MapG (NontermG (PermissionsForm O E)) (fun p => ⟨u, p⟩))

abbrev PermissionG (O : Oracles) := PermissionForm O (EntryG O)
abbrev PositivePermissionG (O : Oracles) := PermissionForm O (CleanEntryG O)

theorem permissionLine_sound (O : Oracles) (D : Descriptions) :
    Sound (permissionLine O D) (PermissionG O) :=
  seq_sound (tryNonterminal_sound (userList_sound O D))
    (fun _ => mapP_sound (expectNonterminal_sound (permissions_sound O D) _) _)

theorem permissionLine_complete (O : Oracles) (D : Descriptions) :
    Complete (permissionLine O D) (PositivePermissionG O) :=
  seq_complete (tryNonterminal_complete (userList_complete O D))
    (fun _ => mapP_complete (expectNonterminal_complete (permissions_complete O D) _) _)

end SudoersSpec.Grammar
