import SudoersSpec.Grammar.Permission
import SudoersSpec.Grammar.SudoTagPosition

namespace SudoersSpec.Grammar

open SudoersSpec.Syntax SudoersSpec.Syntax.Parser

/-- A successful keyword is anchored at the probe's actual start. Absence requires
lexical rejection, not just the lack of a successful keyword derivation. -/
def TagOptionAtG (O : Oracles) (s : Stream) (a : Option (Meta Modifier)) (u : Stream) : Prop :=
  match a with
  | some m => AtCursor (MetaTagAtG O s.getPos) s m u
  | none => AtCursor TagRejectG s () u

/-- Both a hit and a rejection recovered by `parseOption` are followed by whitespace. -/
def TagProbeAtG (O : Oracles) (s : Stream) (a : Option (Meta Modifier)) (t : Stream) : Prop :=
  ∃ u, TagOptionAtG O s a u ∧ AtCursor WsG u () t

private theorem metaTag_reject_at_iff (O : Oracles) (D : Descriptions) {s t : Stream} :
    (metaOrTag O D).run s = (.error .reject, t) ↔ AtCursor TagRejectG s () t := by
  constructor
  · intro h
    obtain ⟨c, hc, hg⟩ := metaOrTag_rejectSound O D s t h
    exact AtCursor.of_run h hc hg
  · exact AtCursor.reject_complete (metaOrTag_rejectComplete O D)

private theorem tagOption_at_iff (O : Oracles) (D : Descriptions) {s t : Stream}
    {a : Option (Meta Modifier)} :
    (parseOption (metaOrTag O D)).run s = (.ok a, t) ↔ TagOptionAtG O s a t := by
  rw [parseOption, run_maybe]
  cases a with
  | none =>
    change _ ↔ AtCursor TagRejectG s () t
    rw [← metaTag_reject_at_iff O D]
    cases (metaOrTag O D).run s with
    | mk r u => cases r with
      | ok m => simp
      | error e => cases e <;> simp
  | some m =>
    change _ ↔ AtCursor (MetaTagAtG O s.getPos) s m t
    rw [← metaOrTag_at_iff O D]
    cases (metaOrTag O D).run s with
    | mk r u => cases r with
      | ok kw => simp
      | error e => cases e <;> simp

private abbrev tagProbe (O : Oracles) (D : Descriptions) :=
  tryNonterminal (parseOption (metaOrTag O D))

private theorem tagProbe_at_iff (O : Oracles) (D : Descriptions) {s t : Stream}
    {a : Option (Meta Modifier)} :
    (tagProbe O D).run s = (.ok a, t) ↔ TagProbeAtG O s a t := by
  unfold tagProbe tryNonterminal
  constructor
  · intro h
    obtain ⟨kw, u, hkw, htail⟩ := run_bind_eq_ok.mp h
    obtain ⟨_, v, hw, hvalue⟩ := run_bind_eq_ok.mp htail
    cases hvalue
    exact ⟨u, (tagOption_at_iff O D).mp hkw, skipTrailingWhitespace_sound.atCursor hw⟩
  · rintro ⟨u, hkw, hw⟩
    rw [run_bind_of_ok ((tagOption_at_iff O D).mpr hkw),
      run_bind_of_ok (hw.complete skipTrailingWhitespace_complete)]
    rfl

/-- Tags advance the ambient cursor on every iteration; `ALL` and aliases finish the
specification directly, whereas an absent keyword leaves a qualified command to read. -/
inductive TagLoopAtG (O : Oracles) :
    List Modifier → Stream → (List Modifier ⊕ CommandSpec) → Stream → Prop
  | stop : TagProbeAtG O s none t → TagLoopAtG O mods s (.inl mods) t
  | all : TagProbeAtG O s (some .all) t → TagLoopAtG O mods s (.inr ⟨mods, .allow .all⟩) t
  | alias : TagProbeAtG O s (some (.alias name)) t →
      TagLoopAtG O mods s (.inr ⟨mods, .allow (.alias name)⟩) t
  | modifier : TagProbeAtG O s (some (.only m)) u →
      (mods ++ [m]).length ≤ identifierMany.limit → TagLoopAtG O (mods ++ [m]) u a t →
      TagLoopAtG O mods s a t

private abbrev tagLoop (O : Oracles) (D : Descriptions) (mods : List Modifier) :=
  whileSome (tagProbe O D) (tryNonterminal_parseOption_consumesSome (metaOrTag_consumes O D))
    commandSpecBody .inl mods

private theorem tagLoop_at_iff (O : Oracles) (D : Descriptions) {mods : List Modifier}
    {s t : Stream} {a : List Modifier ⊕ CommandSpec} :
    (tagLoop O D mods).run s = (.ok a, t) ↔ TagLoopAtG O mods s a t := by
  constructor
  · intro h
    let hp := whileSomeBody_progressive (tryNonterminal_parseOption_consumesSome (metaOrTag_consumes O D))
      commandSpecBody Sum.inl
    have hrel := loop_rel hp
      (fun st src r dst => ∀ b, r = .ok b → TagLoopAtG O st src b dst)
      (by
        intro st src a dst hb b he
        cases he
        obtain ⟨x, u, hx, hh⟩ := run_bind_eq_ok.mp hb
        have hg := (tagProbe_at_iff O D).mp hx
        cases x with
        | none =>
          cases hh
          exact .stop hg
        | some m =>
          cases m with
          | all =>
            cases hh
            exact .all hg
          | alias name =>
            cases hh
            exact .alias hg
          | only m =>
            simp only [commandSpecBody] at hh
            split at hh <;> simp at hh)
      (by intro _ _ _ _ _ _ he; cases he)
      (by
        intro st src st' u r dst hb ih b he
        obtain ⟨x, v, hx, hh⟩ := run_bind_eq_ok.mp hb
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
              exact .modifier ((tagProbe_at_iff O D).mp hx) (Nat.le_of_not_gt hn) (ih b he))
      mods s
    change ∀ b, ((tagLoop O D mods).run s).1 = .ok b →
      TagLoopAtG O mods s b ((tagLoop O D mods).run s).2 at hrel
    rw [h] at hrel
    exact hrel a rfl
  · intro h
    induction h with
    | stop hk | all hk | alias hk =>
      unfold tagLoop whileSome
      rw [loop_run, whileSomeBody, run_bind_of_ok ((tagProbe_at_iff O D).mpr hk)]
      rfl
    | modifier hk hlim _ ih =>
      unfold tagLoop whileSome
      rw [loop_run, whileSomeBody, run_bind_of_ok ((tagProbe_at_iff O D).mpr hk)]
      simp only [commandSpecBody, ite_eq_right (Nat.not_lt.mpr hlim), run_pure]
      exact ih

/-- Exact command-specification grammar, without printer or canonical-form restrictions. -/
inductive CommandAtG (O : Oracles) : Stream → CommandSpec → Stream → Prop
  | keyword : TagLoopAtG O [] s (.inr a) t → CommandAtG O s a t
  | qualified : TagLoopAtG O [] s (.inl mods) u →
      AtCursor (NontermG (QualifiedCommandG O)) u cmd t → CommandAtG O s ⟨mods, cmd⟩ t

private theorem qualifiedCommand_at_iff (O : Oracles) (D : Descriptions) {s t : Stream}
    {a : Spec Command} :
    (expectNonterminal D.command (specCommand O D)).run s = (.ok a, t) ↔
      AtCursor (NontermG (QualifiedCommandG O)) s a t :=
  ⟨(expectNonterminal_sound (qualified_sound (token_sound _) _) _).atCursor,
    AtCursor.complete (expectNonterminal_complete (qualified_complete (token_complete _) _) _)⟩

/-- A command specification succeeds exactly at the cursor derived by `CommandAtG`. -/
theorem commandSpec_at_iff (O : Oracles) (D : Descriptions) {s t : Stream} {a : CommandSpec} :
    (commandSpec O D).run s = (.ok a, t) ↔ CommandAtG O s a t := by
  unfold commandSpec
  constructor
  · intro h
    obtain ⟨r, u, hr, htail⟩ := run_bind_eq_ok.mp h
    have hg := (tagLoop_at_iff O D).mp hr
    cases r with
    | inr cs =>
      cases htail
      exact .keyword hg
    | inl mods =>
      obtain ⟨cmd, v, hcmd, hvalue⟩ := run_bind_eq_ok.mp htail
      cases hvalue
      exact .qualified hg ((qualifiedCommand_at_iff O D).mp hcmd)
  · intro h
    cases h with
    | keyword hk =>
      rw [run_bind_of_ok ((tagLoop_at_iff O D).mpr hk)]
      rfl
    | qualified hk hc =>
      rw [run_bind_of_ok ((tagLoop_at_iff O D).mpr hk),
        run_bind_of_ok ((qualifiedCommand_at_iff O D).mpr hc)]
      rfl

end SudoersSpec.Grammar
