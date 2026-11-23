import SudoersSpec.Grammar.PermissionAtoms
import SudoersSpec.Syntax.SettingsParser

namespace SudoersSpec.Grammar

open SudoersSpec.Syntax SudoersSpec.Syntax.Parser

private abbrev EnvNameG (O : Oracles) := TokenG (envVarToken O.char)
private abbrev ParamG (O : Oracles) := NontermG (TokenG (stringParameterToken O.char))
private abbrev EnvProbeG (O : Oracles) :=
  NontermG (OptG (EnvNameG O) (TokenRejectG (envVarToken O.char)))

private def EnvAppendG (O : Oracles) (items : List String) (name : String) :
    Gram (List String) :=
  SeqG (SyntaxMarkG '=') fun assign =>
    if assign then MapG (ParamG O) (fun value => items ++ [name ++ "=" ++ value])
    else PureG (items ++ [name])

/-- A quoted environment-variable list stops only at a lexical rejection of the next name.
The probe retains its trailing whitespace and any continuation consumed by the lexer. -/
private inductive EnvLoopG (O : Oracles) : List String → Gram (List String)
  | stop : EnvProbeG O c none r → EnvLoopG O items c items r
  | next : EnvProbeG O c (some name) (d ++ tail ++ r) →
      EnvAppendG O items name d items' (tail ++ r) →
      items'.length ≤ identifierMany.limit →
      EnvLoopG O items' tail result r → EnvLoopG O items (c ++ d ++ tail) result r

private abbrev envProbe (O : Oracles) := tryNonterminal (parseOption (token (envVarToken O.char)))

private theorem envProbe_sound (O : Oracles) : Sound (envProbe O) (EnvProbeG O) :=
  tryNonterminal_sound (option_sound (token_sound _) (token_rejectSound _))

private theorem envProbe_complete (O : Oracles) : Complete (envProbe O) (EnvProbeG O) :=
  tryNonterminal_complete (option_complete (token_complete _) (token_rejectComplete _))

private theorem parseVarsBody_ok (O : Oracles) (D : Descriptions) {items : List String}
    {name : String} {s t : Stream} {step : Step (List String) (List String)}
    (h : (parseVarsBody O D items name).run s = (.ok step, t)) :
    ∃ items' c, step = .next items' ∧ s.rest = c ++ t.rest ∧
      EnvAppendG O items name c items' t.rest ∧ items'.length ≤ identifierMany.limit := by
  let appendItem : Parser (List String) := do
    let eq ← isSyntax '='
    if eq then do
      let value ← expectNonterminal D.stringParameter (token (stringParameterToken O.char))
      pure (items ++ [name ++ "=" ++ value])
    else pure (items ++ [name])
  have hp : Sound appendItem (EnvAppendG O items name) := by
    unfold EnvAppendG
    apply seq_sound (syntaxMark_sound '=')
    intro assign
    cases assign
    · exact pure_sound _
    · exact mapP_sound (expectNonterminal_sound (token_sound _) _) _
  have finish (result : List String) (v : Stream)
      (hv : appendItem.run s = (.ok result, v))
      (hf : (if result.length > identifierMany.limit then fatalHere .envVarListTooLong
            else pure (.next result) : Parser (Step (List String) (List String))).run v =
            (.ok step, t)) :
      ∃ items' c, step = .next items' ∧ s.rest = c ++ t.rest ∧
        EnvAppendG O items name c items' t.rest ∧ items'.length ≤ identifierMany.limit := by
    split at hf
    · cases hf
    · rename_i hn
      simp only [run_pure, Prod.mk.injEq, Except.ok.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      obtain ⟨c, hc, hd⟩ := hp s result v hv
      exact ⟨result, c, rfl, hc, hd, Nat.le_of_not_gt hn⟩
  unfold parseVarsBody at h
  obtain ⟨assign, u, ha, h⟩ := run_bind_eq_ok.mp h
  cases assign
  · simp only [Bool.false_eq_true, ite_false, run_bind, run_pure] at h
    exact finish _ _ (by unfold appendItem; rw [run_bind_of_ok ha]; rfl) h
  · obtain ⟨value, v, hv, h⟩ := run_bind_eq_ok.mp h
    simp only [run_bind, run_pure] at h
    exact finish _ _ (by unfold appendItem; rw [run_bind_of_ok ha]; exact run_bind_of_ok hv _) h

private theorem parseVarsBody_complete (O : Oracles) (D : Descriptions) {items result : List String}
    {name : String} {c r : List Char} {s : Stream}
    (hg : EnvAppendG O items name c result r) (hlimit : result.length ≤ identifierMany.limit)
    (hs : s.rest = c ++ r) :
    ∃ t, (parseVarsBody O D items name).run s = (.ok (.next result), t) ∧ t.rest = r := by
  unfold EnvAppendG at hg
  obtain ⟨d, e, assign, rfl, ha, hg⟩ := hg
  obtain ⟨u, hu, hur⟩ := syntaxMark_complete '=' d assign (e ++ r) s ha
    (by rw [hs, List.append_assoc])
  unfold parseVarsBody
  rw [run_bind_of_ok hu]
  cases assign with
  | false =>
    obtain ⟨rfl, rfl⟩ := hg
    exact ⟨u, by
      simp only [Bool.false_eq_true, ite_false, run_bind, run_pure,
        ite_eq_right (Nat.not_lt.mpr hlimit)],
      hur⟩
  | true =>
    obtain ⟨value, hparam, rfl⟩ := hg
    obtain ⟨t, ht, htr⟩ := expectNonterminal_complete
      (token_complete (stringParameterToken O.char)) D.stringParameter e value r u hparam hur
    refine ⟨t, ?_, htr⟩
    simp only [ite_true, run_bind, ht, run_pure, ite_eq_right (Nat.not_lt.mpr hlimit)]

private abbrev envLoop (O : Oracles) (D : Descriptions) (items : List String) :=
  whileSome (envProbe O) (tryNonterminal_parseOption_consumesSome (token_consumes _))
    (parseVarsBody O D) id items

private theorem envLoop_sound (O : Oracles) (D : Descriptions) (items : List String) :
    Sound (envLoop O D items) (EnvLoopG O items) := by
  intro s result t h
  let progressive := whileSomeBody_progressive
    (tryNonterminal_parseOption_consumesSome (token_consumes (envVarToken O.char)))
    (parseVarsBody O D) id
  have hrel := loop_rel progressive
    (fun acc src r dst => ∀ a, r = .ok a →
      ∃ c, src.rest = c ++ dst.rest ∧ EnvLoopG O acc c a dst.rest)
    (by
      intro acc src a dst hb b he
      cases he
      obtain ⟨name, mid, hn, hf⟩ := run_bind_eq_ok.mp hb
      cases name with
      | none =>
        cases hf
        obtain ⟨c, hc, hd⟩ := envProbe_sound O _ _ _ hn
        exact ⟨c, hc, .stop hd⟩
      | some name =>
        obtain ⟨_, _, he, _⟩ := parseVarsBody_ok O D hf
        cases he)
    (by intro _ _ _ _ _ _ he; cases he)
    (by
      intro acc src acc' mid _ dst hb ih a he
      obtain ⟨name, u, hn, hf⟩ := run_bind_eq_ok.mp hb
      cases name with
      | none => cases hf
      | some name =>
        obtain ⟨c, hc, hd⟩ := envProbe_sound O _ _ _ hn
        obtain ⟨_, d, he, hd', hitem, hlimit⟩ := parseVarsBody_ok O D hf
        cases he
        obtain ⟨tail, ht, hloop⟩ := ih a he
        refine ⟨c ++ d ++ tail, by rw [hc, hd', ht]; simp [List.append_assoc],
          .next ?_ (by rwa [← ht]) hlimit hloop⟩
        simpa only [hd', ht, List.append_assoc] using hd)
    items s
  change ∀ a, ((envLoop O D items).run s).1 = .ok a →
    ∃ c, s.rest = c ++ ((envLoop O D items).run s).2.rest ∧
      EnvLoopG O items c a ((envLoop O D items).run s).2.rest at hrel
  rw [h] at hrel
  exact hrel result rfl

private theorem envLoop_complete (O : Oracles) (D : Descriptions) (items : List String) :
    Complete (envLoop O D items) (EnvLoopG O items) := by
  intro c result r s hg
  induction hg generalizing s with
  | stop hn =>
    intro hs
    obtain ⟨t, ht, hr⟩ := envProbe_complete O _ _ _ _ hn hs
    refine ⟨t, ?_, hr⟩
    unfold envLoop whileSome
    rw [loop_run, whileSomeBody, run_bind_of_ok ht]
    rfl
  | next hn hitem hlimit _ ih =>
    intro hs
    obtain ⟨u, hu, hur⟩ := envProbe_complete O _ _ _ _ hn
      (by simpa only [List.append_assoc] using hs)
    obtain ⟨v, hv, hvr⟩ := parseVarsBody_complete O D hitem hlimit
      (by simpa only [List.append_assoc] using hur)
    obtain ⟨t, ht, hr⟩ := ih v hvr
    refine ⟨t, ?_, hr⟩
    unfold envLoop whileSome
    rw [loop_run, whileSomeBody, run_bind_of_ok hu, hv]
    exact ht

private theorem empty_complete (p : Parser α) : Complete p EmptyG :=
  fun _ _ _ _ h => h.elim

private def EnvVarsG (O : Oracles) : Gram (List String) :=
  SeqG (MarkG '"') fun quoted =>
    if quoted then
      SeqG (EnvLoopG O []) fun items =>
        SeqG (SynG '"') fun _ => if items.isEmpty then EmptyG else PureG items
    else
      SeqG (NontermG (EnvNameG O)) fun name =>
        SeqG (SyntaxMarkG '=') fun assign => if assign then EmptyG else PureG [name]

private theorem parseVars_sound (O : Oracles) (D : Descriptions) :
    Sound (parseVars O D) (EnvVarsG O) := by
  unfold parseVars EnvVarsG
  apply seq_sound (mark_sound '"')
  intro quoted
  cases quoted
  · apply seq_sound (expectNonterminal_sound (token_sound _) _)
    intro name
    apply seq_sound (syntaxMark_sound '=')
    intro assign
    cases assign
    · exact pure_sound _
    · intro s a t h; cases h
  · apply seq_sound (envLoop_sound O D [])
    intro items
    apply seq_sound (expectSyntax_sound '"')
    intro _
    split
    · intro s a t h; cases h
    · exact pure_sound items

private theorem parseVars_complete (O : Oracles) (D : Descriptions) :
    Complete (parseVars O D) (EnvVarsG O) := by
  unfold parseVars EnvVarsG
  apply seq_complete (mark_complete '"')
  intro quoted
  cases quoted
  · apply seq_complete (expectNonterminal_complete (token_complete _) _)
    intro name
    apply seq_complete (syntaxMark_complete '=')
    intro assign
    cases assign
    · exact pure_complete _
    · exact empty_complete _
  · apply seq_complete (envLoop_complete O D [])
    intro items
    apply seq_complete (expectSyntax_complete '"')
    intro _
    split
    · exact empty_complete _
    · exact pure_complete items

private def TextItemG (O : Oracles) : Gram String :=
  SeqG (MarkG '"') fun quoted =>
    if quoted then
      SeqG (NontermG (TokenG (quotedStringParameterToken O.char))) fun text =>
        SeqG (SynG '"') fun _ => PureG text
    else ParamG O

private theorem textItem_sound (O : Oracles) (D : Descriptions) :
    Sound (textItem O D) (TextItemG O) := by
  unfold textItem TextItemG
  apply seq_sound (mark_sound '"')
  intro quoted
  cases quoted
  · exact expectNonterminal_sound (token_sound _) _
  · exact seq_sound (expectNonterminal_sound (token_sound _) _)
      (fun text => seq_sound (expectSyntax_sound '"') (fun _ => pure_sound text))

private theorem textItem_complete (O : Oracles) (D : Descriptions) :
    Complete (textItem O D) (TextItemG O) := by
  unfold textItem TextItemG
  apply seq_complete (mark_complete '"')
  intro quoted
  cases quoted
  · exact expectNonterminal_complete (token_complete _) _
  · exact seq_complete (expectNonterminal_complete (token_complete _) _)
      (fun text => seq_complete (expectSyntax_complete '"') (fun _ => pure_complete text))

private abbrev CheckedG (G : Gram α) (check : α → Option β) : Gram β :=
  SeqG G fun value => match check value with
  | some m => PureG m
  | none => EmptyG

private def ListItemsG (O : Oracles) (mode : Settings.ListMode) (kind : Settings.SettingKind) :
    Gram Settings.SettingsModifier :=
  SeqG (SynG '=') fun _ => match kind with
  | .List id => MapG (EnvVarsG O) (Settings.buildList id mode)
  | _ => EmptyG

private theorem listItems_sound (O : Oracles) (D : Descriptions) (pos : Nat × Nat)
    (mode : Settings.ListMode) (name : String) (kind : Settings.SettingKind) :
    Sound (listItems O D pos mode name kind) (ListItemsG O mode kind) := by
  unfold listItems ListItemsG
  apply seq_sound (expectSyntax_sound '=')
  intro _
  cases kind with
  | List id => exact mapP_sound (parseVars_sound O D) _
  | Flag _ | Integer _ | Text _ => intro s a t h; cases h

private theorem listItems_complete (O : Oracles) (D : Descriptions) (pos : Nat × Nat)
    (mode : Settings.ListMode) (name : String) (kind : Settings.SettingKind) :
    Complete (listItems O D pos mode name kind) (ListItemsG O mode kind) := by
  unfold listItems ListItemsG
  apply seq_complete (expectSyntax_complete '=')
  intro _
  cases kind with
  | List id => exact mapP_complete (parseVars_complete O D) _
  | Flag _ | Integer _ | Text _ => exact empty_complete _

private def NamedSettingG (O : Oracles) (kind : Settings.SettingKind) :
    Gram Settings.SettingsModifier :=
  SeqG (SyntaxMarkG '+') fun add =>
    if add then ListItemsG O .Add kind else
    SeqG (SyntaxMarkG '-') fun del =>
      if del then ListItemsG O .Del kind else
      SeqG (SyntaxMarkG '=') fun assign =>
        if assign then
          match kind with
          | .Flag _ => EmptyG
          | .Integer id => CheckedG (NontermG (TokenG numericToken)) (Settings.checkInteger id)
          | .List id => MapG (EnvVarsG O) (Settings.buildList id .Set)
          | .Text id => CheckedG (TextItemG O) (Settings.checkText id)
        else
          match kind with
          | .Flag m => PureG m
          | _ => EmptyG

/-- A setting name selects its kind and admissible operator; successful textual and numeric
assignments also satisfy the corresponding settings-model value checker. -/
def SettingG (O : Oracles) : Gram Settings.SettingsModifier :=
  SeqG (SyntaxMarkG '!') fun neg =>
    SeqG (NontermG (TokenG defaultNameToken)) fun name =>
      if neg then
        match Settings.negate name with
        | some m => PureG m
        | none => EmptyG
      else
        match Settings.set name with
        | some kind => NamedSettingG O kind
        | none => EmptyG

private theorem getPos_sound_ignored {p : (Nat × Nat) → Parser α} {G : Gram α}
    (h : ∀ pos, Sound (p pos) G) : Sound (getPos >>= p) G := by
  intro s a t hp
  exact h s.getPos s a t (by simpa only [run_bind_of_ok (run_getPos s)] using hp)

private theorem getPos_complete_ignored {p : (Nat × Nat) → Parser α} {G : Gram α}
    (h : ∀ pos, Complete (p pos) G) : Complete (getPos >>= p) G := by
  intro c a r s hg hs
  rw [run_bind_of_ok (run_getPos s)]
  exact h s.getPos c a r s hg hs

/-- Every successful `SettingsModifier` parse has a derivation with the same remainder. -/
theorem setting_sound (O : Oracles) (D : Descriptions) :
    Sound (settingsModifier O D) (SettingG O) := by
  unfold settingsModifier SettingG
  apply getPos_sound_ignored
  intro pos
  apply seq_sound (syntaxMark_sound '!')
  intro neg
  cases neg
  · apply seq_sound (tryNonterminal_sound (token_sound _))
    intro name
    cases Settings.set name with
    | none => intro s a t h; cases h
    | some kind =>
      unfold NamedSettingG
      apply seq_sound (syntaxMark_sound '+')
      intro add
      cases add
      · apply seq_sound (syntaxMark_sound '-')
        intro del
        cases del
        · apply seq_sound (syntaxMark_sound '=')
          intro assign
          cases assign
          · cases kind with
            | Flag m => exact pure_sound m
            | Integer _ | List _ | Text _ => intro s a t h; cases h
          · apply getPos_sound_ignored
            intro valuePos
            cases kind with
            | Flag _ => intro s a t h; cases h
            | Integer id =>
              apply seq_sound (expectNonterminal_sound (token_sound numericToken) D.numeric)
              intro value
              cases Settings.checkInteger id value with
              | some m => exact pure_sound m
              | none => intro s a t h; cases h
            | List id => exact mapP_sound (parseVars_sound O D) _
            | Text id =>
              apply seq_sound (textItem_sound O D)
              intro text
              cases Settings.checkText id text with
              | some m => exact pure_sound m
              | none => intro s a t h; cases h
        · exact listItems_sound O D pos .Del name kind
      · exact listItems_sound O D pos .Add name kind
  · apply getPos_sound_ignored
    intro valuePos
    apply seq_sound (expectNonterminal_sound (token_sound _) _)
    intro name
    cases Settings.negate name with
    | some m => exact pure_sound m
    | none =>
      intro s a t h
      by_cases hk : (Settings.set name).isSome = true <;> simp [hk] at h

/-- Every derivation of a setting is accepted with the same modifier and remainder. -/
theorem setting_complete (O : Oracles) (D : Descriptions) :
    Complete (settingsModifier O D) (SettingG O) := by
  unfold settingsModifier SettingG
  apply getPos_complete_ignored
  intro pos
  apply seq_complete (syntaxMark_complete '!')
  intro neg
  cases neg
  · apply seq_complete (tryNonterminal_complete (token_complete _))
    intro name
    cases Settings.set name with
    | none => exact empty_complete _
    | some kind =>
      unfold NamedSettingG
      apply seq_complete (syntaxMark_complete '+')
      intro add
      cases add
      · apply seq_complete (syntaxMark_complete '-')
        intro del
        cases del
        · apply seq_complete (syntaxMark_complete '=')
          intro assign
          cases assign
          · cases kind with
            | Flag m => exact pure_complete m
            | Integer _ | List _ | Text _ => exact empty_complete _
          · apply getPos_complete_ignored
            intro valuePos
            cases kind with
            | Flag _ => exact empty_complete _
            | Integer id =>
              apply seq_complete (expectNonterminal_complete (token_complete numericToken) D.numeric)
              intro value
              cases Settings.checkInteger id value with
              | some m => exact pure_complete m
              | none => exact empty_complete _
            | List id => exact mapP_complete (parseVars_complete O D) _
            | Text id =>
              apply seq_complete (textItem_complete O D)
              intro text
              cases Settings.checkText id text with
              | some m => exact pure_complete m
              | none => exact empty_complete _
        · exact listItems_complete O D pos .Del name kind
      · exact listItems_complete O D pos .Add name kind
  · apply getPos_complete_ignored
    intro valuePos
    apply seq_complete (expectNonterminal_complete (token_complete _) _)
    intro name
    cases Settings.negate name with
    | some m => exact pure_complete m
    | none => exact empty_complete _

abbrev SettingsG (O : Oracles) : Gram (List Settings.SettingsModifier) :=
  ListG (SettingG O) settingsModifierMany.sep settingsModifierMany.limit

theorem settings_sound (O : Oracles) (D : Descriptions) :
    Sound (parseVec settingsModifierMany D.settingsModifier (settingsModifier O D)) (SettingsG O) :=
  parseList_sound (setting_sound O D) _ _ _

theorem settings_complete (O : Oracles) (D : Descriptions) :
    Complete (parseVec settingsModifierMany D.settingsModifier (settingsModifier O D)) (SettingsG O) :=
  parseList_complete (setting_complete O D) _ _ _

end SudoersSpec.Grammar
