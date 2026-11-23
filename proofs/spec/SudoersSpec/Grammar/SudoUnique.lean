import SudoersSpec.Grammar.SudoPermissionDispatchAt

/-!
# Exact stable file grammar

The declaration, include, and comment judgments already record enough information to run
backwards, including the failure cursors caught by hash dispatch. Permissions use the same
dispatch but with independent, exact judgments for the command cursor, ignored-tag positions,
and both runas recovery boundaries.
-/

namespace SudoersSpec.Grammar

open SudoersSpec.Syntax SudoersSpec.Syntax.Parser

private theorem present_mark {ch : Char} {s t : Stream} (h : AtCursor (SynG ch) s () t) :
    (isSyntax ch).run s = (.ok true, t) :=
  isSyntax_true_iff.mpr (h.complete (trySyntax_complete ch))

private theorem absent_mark {ch : Char} {s : Stream} (h : s.peek ≠ some ch) :
    (isSyntax ch).run s = (.ok false, s) :=
  isSyntax_false_iff.mpr ⟨rfl, fun _ hc he => h (he ▸ hc)⟩

private theorem defaultsChosen_complete (O : Oracles) (D : Descriptions) {rest : List Char}
    {s₀ s t : Stream} {scope : ConfigScope} (h : DefaultsScopeG O rest s₀ s scope t) :
    ((if rest.head? == some '@' || (s.getPos.1 == s₀.getPos.1 && s.getPos.2 - s₀.getPos.2 == 8)
      then defaultsScope O D rest s₀ else pure .generic : AParser s₀ ConfigScope).run s) = (.ok scope, t) := by
  cases h with
  | host hat hw hh =>
    have hw' := hw.complete skipTrailingWhitespace_complete
    have hh' := hh.complete (expectNonterminal_complete
      (specList_complete (metaHostname_complete O.char) hostnameMany D.hostname) D.hostname)
    change (expectNonterminal D.hostname (specListHostname O.char D)).run _ = _ at hh'
    simp [hat, defaultsScope, AParser.run_bind, AParser.run_lift, hw', hh']
  | unscoped ha hpos =>
    have he : (rest.head? == some '@') = false := by simpa using ha
    have hp : (s.getPos.1 == s₀.getPos.1 && s.getPos.2 - s₀.getPos.2 == 8) = false := by
      simpa [DefaultsSuffixPosition, Bool.and_eq_true] using hpos
    simp [he, hp]
  | punct ha hpos hp =>
    have he : (rest.head? == some '@') = false := by simpa using ha
    obtain ⟨hl, hc⟩ := hpos
    simp only [he, Bool.false_or, hl, hc, beq_self_eq_true, Bool.and_self, ite_true, defaultsScope,
      Bool.false_eq_true, ite_false]
    cases hp with
    | user hs hu =>
      have hu' := hu.complete (expectNonterminal_complete (userList_complete O D) D.userSpecifier)
      simp [AParser.run_bind, AParser.run_lift, present_mark hs, hu']
    | command hcolon hs hc =>
      have hc' := hc.complete (expectNonterminal_complete (simpleCommandList_complete O D) D.simpleCommand)
      simp [AParser.run_bind, AParser.run_lift, absent_mark hcolon, present_mark hs, hc']
    | runAs hcolon hbang hs hu =>
      have hu' := hu.complete (expectNonterminal_complete (userList_complete O D) D.userSpecifier)
      simp [AParser.run_bind, AParser.run_lift, absent_mark hcolon, absent_mark hbang, present_mark hs, hu']
    | generic hc hb hg =>
      simp [AParser.run_bind, AParser.run_lift, absent_mark hc, absent_mark hb, absent_mark hg]

/-- The existing directive grammar determines the AST and exact output cursor. -/
theorem directive_complete (O : Oracles) (D : Descriptions) {s₀ s t : Stream} {key : Spec UserSpecifier}
    {d : Directive} (h : DirectiveG O s₀ key s d t) : (getDirective O D key s₀).run s = (.ok d, t) := by
  cases h with
  | user hu => exact hu.complete (userAliasBody_complete O D)
  | host hh => exact hh.complete (hostAliasBody_complete O D)
  | command hword hc => rcases hword with rfl | rfl <;> exact hc.complete (cmndAliasBody_complete O D)
  | runAs hr => exact hr.complete (runasAliasBody_complete O D)
  | @defaults s scope u mods t word hpref hs hm =>
    have hs' := defaultsChosen_complete O D hs
    have hm' := hm.complete (expectNonterminal_complete (settings_complete O D) D.settingsModifier)
    dsimp only [DirectiveKey, getDirective]
    split
    · cases (by decide : "Defaults".toList.isPrefixOf "User_Alias".toList = false).symm.trans hpref
    · cases (by decide : "Defaults".toList.isPrefixOf "Host_Alias".toList = false).symm.trans hpref
    · cases (by decide : "Defaults".toList.isPrefixOf "Cmnd_Alias".toList = false).symm.trans hpref
    · cases (by decide : "Defaults".toList.isPrefixOf "Cmd_Alias".toList = false).symm.trans hpref
    · cases (by decide : "Defaults".toList.isPrefixOf "Runas_Alias".toList = false).symm.trans hpref
    · simp only [hpref, ite_true, AParser.run_bind, AParser.run_lift, run_getPos]
      by_cases hscope : ((word.toList.drop 8).head? == some '@' ||
          (s.getPos.1 == s₀.getPos.1 && s.getPos.2 - s₀.getPos.2 == 8)) = true
      · simp only [hscope, ite_true] at hs'
        simp only [hscope, ite_true, AParser.run_bind, AParser.run_lift, hs', hm', AParser.run_pure]
      · simp only [hscope, Bool.false_eq_true, ite_false] at hs'
        simp only [hscope, Bool.false_eq_true, ite_false, AParser.run_bind, AParser.run_lift,
          hs', hm', AParser.run_pure]

private theorem ordinary_guards {s : Stream} (h : OrdinaryStart s) :
    s.peek ≠ some '@' ∧ s.peek ≠ some '#' ∧ s.peek ≠ some '"' :=
  ⟨fun he => h '@' he (.inl rfl), fun he => h '#' he (.inr (.inl rfl)),
    fun he => h '"' he (.inr (.inr rfl))⟩

private theorem entry_at (O : Oracles) (D : Descriptions) {s : Stream} (ha : s.peek = some '@') :
    (sudo O D).run s = (parseInclude O D).run s.pop := by
  simp [sudo, run_bind, Stream.eatChar_eq, ha]

private theorem entry_hash (O : Oracles) (D : Descriptions) {s : Stream} (hh : s.peek = some '#') :
    (sudo O D).run s = (sudoHash O D).run s := by
  simp [sudo, run_bind, Stream.eatChar_eq, hh]

private theorem entry_ordinary (O : Oracles) (D : Descriptions) {s : Stream} (h : OrdinaryStart s) :
    (sudo O D).run s = (sudoMain O D s).run s := by
  obtain ⟨ha, hh, _⟩ := ordinary_guards h
  simp [sudo, run_bind, Stream.eatChar_eq, ha, hh]

/-- Every nonpermission rule of the broad grammar is exact, even when dispatch swallowed a
lexical failure. In particular both positions of included-path spans are fixed by the grammar. -/
theorem sudo_nonpermission_complete (O : Oracles) (D : Descriptions) {s t : Stream} {a : Sudo}
    (h : SudoG O s a t) (hn : ∀ p, a ≠ .spec p) : (sudo O D).run s = (.ok a, t) := by
  cases h.2 with
  | permission _ => exact (hn _ rfl).elim
  | atInclude ha hi => exact (entry_at O D ha).trans (include_complete O D hi)
  | hashInclude hh hi hd =>
    obtain ⟨e, he⟩ := hash_id_failure_complete O D hi
    rw [entry_hash O D hh]
    simp [sudoHash, run_bind, he, include_complete O D hd]
  | hashComment hh hi hd =>
    obtain ⟨e, he⟩ := hash_id_failure_complete O D hi
    obtain ⟨e', he'⟩ := include_failure_complete O D hd
    rw [entry_hash O D hh]
    simp [sudoHash, run_bind, he, he']
  | ordinaryComment ho hr =>
    have hq := (ordinary_guards ho).2.2
    rw [entry_ordinary O D ho]
    simp [sudoMain, AParser.run_bind, AParser.run_lift, hq, hr.reject_complete (userList_reject_complete O D)]
  | declaration ho hu hd hguard =>
    have hq := (ordinary_guards ho).2.2
    have hr := hu.complete (tryNonterminal_complete (userList_complete O D))
    have hd' := directive_complete O D hd
    simp only [List.headD_eq_head?_getD] at hd'
    rw [entry_ordinary O D ho]
    rcases hguard with hlen | hkind
    · simp [sudoMain, AParser.run_bind, AParser.run_lift, hq, hr, hd', hlen]
    · simp [sudoMain, AParser.run_bind, AParser.run_lift, hq, hr, hd', hkind]

/-- All stable item alternatives before the trailing whitespace checked by the file driver. -/
def ExactSudoG (O : Oracles) (s : Stream) (a : Sudo) (t : Stream) : Prop :=
  match a with
  | .spec p => ExactSudoPermissionG O s p t
  | _ => SudoG O s a t

/-- A stable item with trailing whitespace, before the driver's optional comment and newline. -/
def ExactSudoItemG (O : Oracles) : Stream → Sudo → Stream → Prop :=
  CursorNontermG (ExactSudoG O)

theorem exactSudo_at_iff (O : Oracles) (D : Descriptions) {s t : Stream} {a : Sudo} :
    (sudo O D).run s = (.ok a, t) ↔ ExactSudoG O s a t := by
  cases a with
  | spec p => exact sudo_permission_at_iff O D
  | decl _ | «include» _ _ | includeDir _ _ | lineComment =>
    exact ⟨sudo_sound O D, fun h => sudo_nonpermission_complete O D h (by intro p he; cases he)⟩

theorem exactSudo_item_iff (O : Oracles) (D : Descriptions) {s t : Stream} {a : Sudo} :
    (expectNonterminal D.sudo (sudo O D)).run s = (.ok a, t) ↔ ExactSudoItemG O s a t :=
  expectNonterminal_at_iff (exactSudo_at_iff O D) D.sudo

theorem exactSudo_item_complete (O : Oracles) (D : Descriptions) {s t : Stream} {a : Sudo}
    (h : ExactSudoItemG O s a t) : (expectNonterminal D.sudo (sudo O D)).run s = (.ok a, t) :=
  (exactSudo_item_iff O D).mpr h

/-- For a fixed starting cursor, the exact grammar fixes both value and stopping cursor. -/
theorem exactSudo_item_unique (O : Oracles) {s t₁ t₂ : Stream} {a₁ a₂ : Sudo}
    (ha : ExactSudoItemG O s a₁ t₁) (hb : ExactSudoItemG O s a₂ t₂) : a₁ = a₂ ∧ t₁ = t₂ := by
  have he := (exactSudo_item_complete O .release ha).symm.trans (exactSudo_item_complete O .release hb)
  exact ⟨Except.ok.inj (congrArg Prod.fst he), congrArg Prod.snd he⟩

/-- Unambiguity of the exact clean-file grammar, including its final position. -/
theorem exactSudo_cleanFile_unique (O : Oracles) {s t₁ t₂ : Stream} {a₁ a₂ : List Sudo}
    (ha : Recovery.CleanFile (ExactSudoItemG O) s a₁ t₁)
    (hb : Recovery.CleanFile (ExactSudoItemG O) s a₂ t₂) : a₁ = a₂ ∧ t₁ = t₂ := by
  induction ha generalizing a₂ t₂ with
  | eof he =>
    cases hb with
    | eof _ => exact ⟨rfl, rfl⟩
    | line hm _ _ _ => exact (hm he).elim
  | line hm hi hn _ ih =>
    cases hb with
    | eof he => exact (hm he).elim
    | line _ hj _ htail =>
      obtain ⟨rfl, rfl⟩ := exactSudo_item_unique O hi hj
      obtain ⟨rfl, rfl⟩ := ih htail
      exact ⟨rfl, rfl⟩

/-- An exact stable grammar derivation gives the implementation's successful file result. -/
theorem exactSudo_cleanFile_complete (D : Descriptions) (O : Oracles) {src : List Char}
    {items : List Sudo} {out : Stream}
    (h : Recovery.CleanFile (ExactSudoItemG O) (Stream.new src) items out) :
    parseSudoersWith D O src = .ok (items.map Except.ok) := by
  have hr := Recovery.cleanFile_complete (fun _ _ _ h => exactSudo_item_complete O D h) h
  simp only [parseSudoersWith, hr]
  have okItems : (items.map (Except.ok : Sudo → Parsed Sudo)).any
      (fun i => match i with | .error (.fatal _ .unwrapNone) => true | _ => false) = false := by
    clear h hr
    induction items with
    | nil => rfl
    | cons _ _ ih => exact ih
  change (if (items.map (Except.ok : Sudo → Parsed Sudo)).any
    (fun i => match i with | .error (.fatal _ .unwrapNone) => true | _ => false) then
      Except.error ErrKind.unwrapNone.render else Except.ok (items.map Except.ok) :
        Except String (List (Parsed Sudo))) = Except.ok (items.map Except.ok)
  simp only [okItems, Bool.false_eq_true, ite_false]

/-- A clean stable parse is the exact grammar derivation of its items. This includes ignored
spans and runas prefixes recovered without a line diagnostic. -/
theorem parseSudoersWith_exact_iff (D : Descriptions) (O : Oracles) (src : List Char)
    (items : List Sudo) :
    parseSudoersWith D O src = .ok (items.map Except.ok) ↔
      Recovery.CleanFile (ExactSudoItemG O) (Stream.new src) items ((Stream.new src).advance src.length) :=
  ⟨fun h => Recovery.cleanFile_sound (fun _ _ _ hr => (exactSudo_item_iff O D).mp hr)
      (parseSudoersWith_ok_lines D O src h),
    exactSudo_cleanFile_complete D O⟩

end SudoersSpec.Grammar
