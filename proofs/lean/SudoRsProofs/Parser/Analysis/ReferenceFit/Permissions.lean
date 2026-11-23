import SudoRsProofs.Parser.Analysis.ReferenceFit.Lexical

open Aeneas Aeneas.Std SudoersSpec SudoersSpec.Syntax SudoersSpec.Grammar

namespace SudoRsProofs.Parser.Analysis.Ref

private theorem hash_users_good (O : Oracles) : GrammarGood (listFits userFits) (HashUsersG O) := by
  intro c a r h
  obtain ⟨_, _, id, _, hi, h⟩ := h
  obtain ⟨_, _, comma, _, _, h⟩ := h
  have hf : specFits userFits (.allow (.only (.user id))) :=
    nonterm_good (identifier_good O) hi
  cases comma with
  | false =>
    obtain ⟨_, rfl⟩ := h
    intro x hx
    rw [List.mem_singleton] at hx
    subst x
    exact hf
  | true =>
    obtain ⟨_, hu, rfl⟩ := h
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hf
    · exact nonterm_good (users_good O) hu x hx

private theorem runas_users_good (O : Oracles) :
    GrammarGood (listFits userFits) (RunasUsersG O) := by
  intro _ _ _ h
  rcases h with h | ⟨rfl, _⟩
  · exact nonterm_good (users_good O) h
  · simp [listFits]

private theorem runas_groups_good (O : Oracles) :
    GrammarGood (listFits identFits) (RunasGroupsG O) := by
  intro _ _ _ h
  cases h with
  | present hg =>
    obtain ⟨_, _, _, _, _, hg⟩ := hg
    exact nonterm_good (identifiers_good O) hg
  | absent _ => simp [listFits]
  | missing _ _ => simp [listFits]

private theorem runas_good (O : Oracles) : GrammarGood runasFits (RunAsG O) := by
  intro _ _ _ h
  obtain ⟨_, _, _, _, _, h⟩ := h
  obtain ⟨_, _, _, _, hu, h⟩ := h
  obtain ⟨_, _, _, _, hg, _, _, rfl⟩ := h
  exact ⟨runas_users_good O hu, runas_groups_good O hg⟩

private theorem tag_rhs_alias {O : Oracles} {span : Span} {key nm : String} {c r : List Char}
    (h : TagRhsG O span key c (.alias nm) r) : nm = key := by
  unfold TagRhsG at h
  split at h <;> simp [MapG, SeqG, PureG, EmptyG] at h
  exact h.2.1

private theorem tag_probe_alias_fits {O : Oracles} {c r : List Char} {nm : String}
    (h : TagProbeG (MetaTagG O) c (some (.alias nm)) r) : Fits nm := by
  obtain ⟨_, _, _, h, _⟩ := h
  cases h with
  | some h =>
    obtain ⟨key, _, _, _, _, hk, hr⟩ := h
    rw [tag_rhs_alias hr]
    exact nonterm_good alias_name_grammar_good hk

private def command_fits (cmd : CommandSpec) : Prop :=
  cmd.mods.length ≤ identifierMany.limit ∧ specFits (fun _ => True) cmd.cmd

private def tag_out_fits : List Modifier ⊕ CommandSpec → Prop
  | .inl acc => acc.length ≤ identifierMany.limit
  | .inr cmd => command_fits cmd

private theorem tag_loop_good {O : Oracles} {mods : List Modifier} {c r : List Char}
    {out : List Modifier ⊕ CommandSpec} (h : TagLoopG (MetaTagG O) mods c out r) :
    mods.length ≤ identifierMany.limit → tag_out_fits out := by
  induction h with
  | stop _ => exact fun hmod => hmod
  | all _ => exact fun hmod => ⟨hmod, trivial⟩
  | «alias» h => exact fun hmod => ⟨hmod, tag_probe_alias_fits h⟩
  | modifier _ hlim _ ih => exact fun _ => ih hlim

private theorem command_good (O : Oracles) : GrammarGood command_fits (CommandSpecG O) := by
  intro _ _ _ h
  obtain ⟨_, _, out, _, ht, h⟩ := h
  have hfit := tag_loop_good ht (by decide)
  cases out with
  | inl mods =>
    obtain ⟨_, hc, rfl⟩ := h
    exact ⟨hfit, nonterm_good (qual_good (command_meta_good O)) hc⟩
  | inr cmd =>
    obtain ⟨_, rfl⟩ := h
    exact hfit

private def entry_names_fit (e : PermissionEntry) : Prop :=
  (∀ ra, e.1 = some ra → runasFits ra) ∧ specFits (fun _ => True) e.2.cmd

private theorem entry_good (O : Oracles) :
    GrammarGood (fun e => e.2.mods.length ≤ identifierMany.limit ∧ entry_names_fit e) (EntryG O) := by
  intro _ _ _ h
  obtain ⟨_, _, _, _, hr, _, hc, rfl⟩ := h
  have hc := nonterm_good (command_good O) hc
  refine ⟨hc.1, ?_, hc.2⟩
  obtain ⟨_, _, _, ho, _⟩ := hr
  cases ho with
  | some h =>
    intro ra he
    cases he
    exact runas_good O h
  | none _ =>
    intro ra he
    cases he

private theorem tag_sum_bound (es : List PermissionEntry)
    (h : ∀ e ∈ es, e.2.mods.length ≤ identifierMany.limit) :
    (es.map fun e => e.2.mods.length).sum ≤ es.length * identifierMany.limit := by
  induction es with
  | nil => simp
  | cons e es ih =>
    have he := h e (by simp)
    have ht := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    rw [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

private def group_fits (g : PermissionGroup) : Prop :=
  listFits Fits g.1 ∧ (g.2.map fun e => e.2.mods.length).sum ≤ Usize.max ∧
    ∀ e ∈ g.2, entry_names_fit e

private theorem group_good (O : Oracles) : GrammarGood group_fits (GroupForm O (EntryG O)) := by
  intro _ _ _ h
  obtain ⟨_, _, _, _, hh, h⟩ := h
  obtain ⟨_, _, _, _, _, es, he, rfl⟩ := h
  obtain ⟨_, _, _, he, _⟩ := he
  have hentries := list_good (entry_good O) he
  refine ⟨nonterm_good (hosts_good O.char) hh, ?_, fun e hm => (hentries e hm).2⟩
  calc
    (es.map fun e => e.2.mods.length).sum ≤ es.length * identifierMany.limit :=
      tag_sum_bound es (fun e hm => (hentries e hm).1)
    _ ≤ 127 * identifierMany.limit :=
      Nat.mul_le_mul_right _ (list_length_bound he (by decide))
    _ ≤ 4294967295 := by decide
    _ ≤ Usize.max := Usize.cMax_bound_concrete.1

private theorem dispatch_good {O : Oracles} {U : Gram (SpecList UserSpecifier)}
    (hU : GrammarGood (listFits userFits) U) : GrammarGood ruleFits (DispatchForm O U (EntryG O)) := by
  rintro _ _ _ ⟨_, _, _, _, hu, _, hp, rfl⟩
  exact ⟨hU hu, nonterm_good (list_good (group_good O)) hp⟩

/-- Permission grammar successes fit the names and tag counts used by the analysis and matcher. -/
theorem permission_rule_fits {O : Oracles} {s t : List Char} {p : PermissionSpec}
    (h : SudoPermissionG O s p t) : ruleFits p := by
  cases h with
  | hash _ h => exact dispatch_good (hash_users_good O) h
  | quoted _ h => exact dispatch_good (nonterm_good (users_good O)) h
  | ordinary _ _ h => exact dispatch_good (nonterm_good (users_good O)) h

end SudoRsProofs.Parser.Analysis.Ref
