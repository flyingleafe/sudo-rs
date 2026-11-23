import SudoRsProofs.Parser.Analysis.ReferenceFit.Common

open Aeneas Aeneas.Std SudoersSpec SudoersSpec.Syntax SudoersSpec.Grammar

namespace SudoRsProofs.Parser.Analysis.Ref

private theorem name_token_cap : 255 + 4 ≤ Usize.max := by scalar_tac
private theorem command_token_cap : 1024 + 4 ≤ Usize.max := by scalar_tac

private theorem trimEnd_utf8Len_le (O : CharOracle) (cs : List Char) :
    utf8Len (trimEnd O cs) ≤ utf8Len cs := by
  induction cs using List.reverseRecOn with
  | nil => exact Nat.le_refl _
  | append_singleton cs c ih =>
    rw [trimEnd_append_singleton]
    split
    · exact ih.trans (by rw [utf8Len_append]; omega)
    · exact Nat.le_refl _

private theorem username_construct_good (O : Oracles) (cs : List Char)
    (hlen : utf8Len cs ≤ (usernameToken O).maxLen + 4) (a : String)
    (hc : (usernameToken O).construct cs = .ok a) : Fits a := by
  let stripped := if cs.getLast? == some '$' then cs.dropLast else cs
  change (if stripped.contains '$' then .error .embeddedDollarInUsername
    else sudoStringNew O cs) = .ok a at hc
  by_cases hd : stripped.contains '$' = true
  · rw [ite_eq_left hd] at hc
    cases hc
  · rw [ite_eq_right hd] at hc
    unfold sudoStringNew at hc
    by_cases hn : cs.contains '\x00' = true
    · rw [ite_eq_left hn] at hc
      cases hc
    · rw [ite_eq_right hn] at hc
      cases hc
      exact token_text_fits hlen name_token_cap

private theorem hostname_construct_good (O : CharOracle) (cs : List Char)
    (hlen : utf8Len cs ≤ (hostnameToken O).maxLen + 4) (a : Hostname)
    (hc : (hostnameToken O).construct cs = .ok a) : Fits a := by
  change Hostname.construct O cs = .ok a at hc
  unfold Hostname.construct at hc
  split at hc
  · cases hc
  · cases hc
    exact token_text_fits hlen name_token_cap

/-- The alias branch uses trimmed token text; the `only` branch keeps the inner result. -/
private theorem meta_token_good {T : TokenSpec α} {good : α → Prop} (O : CharOracle)
    (hcap : T.maxLen + 4 ≤ Usize.max)
    (hgood : ∀ cs, utf8Len cs ≤ T.maxLen + 4 → ∀ a, T.construct cs = .ok a → good a) :
    GrammarGood (MetaFit good) (TokenG (metaToken O T)) := by
  apply token_construct_good
  intro cs hlen a hc
  change Meta.construct O T cs = .ok a at hc
  simp only [Meta.construct] at hc
  split at hc
  · cases hc
    trivial
  · split at hc
    · cases hc
      exact ofList_fits ((trimEnd_utf8Len_le O cs).trans (hlen.trans hcap))
    · cases h : T.construct cs with
      | error e =>
        rw [h] at hc
        cases hc
      | ok x =>
        rw [h] at hc
        cases hc
        exact hgood cs hlen x h

theorem alias_name_good : GrammarGood Fits (TokenG aliasNameToken) := by
  apply token_construct_good
  intro cs hlen n hc
  change (Except.ok (String.ofList cs) : Except ErrKind String) = .ok n at hc
  cases hc
  exact token_text_fits hlen name_token_cap

theorem alias_name_grammar_good : GrammarGood Fits AliasNameG := by
  intro _ _ _ h
  exact alias_name_good (tokenG_aliasName_iff.mpr h)

theorem identifier_good (O : Oracles) : GrammarGood identFits (IdentifierG O) := by
  intro _ _ _ h
  obtain ⟨_, _, isId, _, _, h⟩ := h
  cases isId
  · obtain ⟨_, hn, rfl⟩ := h
    exact nonterm_good (token_construct_good (username_construct_good O)) hn
  · obtain ⟨_, _, rfl⟩ := h
    trivial

private theorem parse_user_good (O : Oracles) : GrammarGood userFits (ParseUserG O) := by
  intro _ _ _ h
  obtain ⟨_, _, group, _, _, h⟩ := h
  cases group
  · obtain ⟨_, _, plus, _, _, h⟩ := h
    cases plus
    · obtain ⟨_, hi, rfl⟩ := h
      exact nonterm_good (identifier_good O) hi
    · exact False.elim h
  · obtain ⟨_, _, nonunix, _, _, h⟩ := h
    obtain ⟨_, _, rfl⟩ := h
    cases nonunix <;> trivial

private theorem user_specifier_good (O : Oracles) : GrammarGood userFits (UserSpecifierG O) := by
  intro _ _ _ h
  obtain ⟨_, _, quoted, _, _, h⟩ := h
  cases quoted
  · exact parse_user_good O h
  · obtain ⟨_, _, _, _, _, ⟨_, _, _, hu⟩, _⟩ := h
    exact parse_user_good O hu

private theorem meta_good {G : Gram α} {embed : String → α} {good : α → Prop} (O : Oracles)
    (hgood : GrammarGood good G) (hembed : ∀ n, Fits n → good (embed n)) :
    GrammarGood (MetaFit good) (MetaG O G embed) := by
  intro _ _ _ h
  obtain ⟨_, _, m, _, hm, hval⟩ := h
  cases m with
  | none =>
    obtain ⟨_, hx, rfl⟩ := hval
    exact hgood hx
  | some m =>
    obtain ⟨_, _, _, hm, _⟩ := hm
    cases hm with
    | some ht =>
      have hfit : MetaFit Fits m :=
        meta_token_good (T := usernameToken O) O.char name_token_cap
          (username_construct_good O) ht
      obtain ⟨_, rfl⟩ := hval
      cases m with
      | all => trivial
      | «only» n => exact hembed n hfit
      | «alias» _ => exact hfit

theorem meta_user_good (O : Oracles) : GrammarGood (MetaFit userFits) (MetaUserG O) :=
  meta_good O (user_specifier_good O) (fun _ h => h)

theorem meta_identifier_good (O : Oracles) : GrammarGood (MetaFit identFits) (MetaIdentifierG O) :=
  meta_good O (identifier_good O) (fun _ h => h)

theorem meta_hostname_good (O : CharOracle) : GrammarGood (MetaFit Fits) (HostItemG O) := by
  intro _ _ _ h
  exact meta_token_good (T := hostnameToken O) O name_token_cap (hostname_construct_good O)
    ((tokenG_metaHost_iff O).mpr h)

theorem users_good (O : Oracles) : GrammarGood (listFits userFits) (UserListG O) :=
  spec_list_good (meta_user_good O)

theorem identifiers_good (O : Oracles) : GrammarGood (listFits identFits) (IdentifierListG O) :=
  spec_list_good (meta_identifier_good O)

theorem hosts_good (O : CharOracle) : GrammarGood (listFits Fits) (HostListG O) :=
  spec_list_good (meta_hostname_good O)

theorem command_meta_good (O : Oracles) :
    GrammarGood (MetaFit (fun _ => True)) (TokenG (metaToken O.char (commandToken O))) :=
  meta_token_good O.char command_token_cap (fun _ _ _ _ => True.intro)

theorem simple_command_list_good (O : Oracles) :
    GrammarGood (listFits (fun _ => True)) (SimpleCommandListG O) :=
  spec_list_good (meta_token_good (T := simpleCommandToken O) O.char command_token_cap
    (fun _ _ _ _ => True.intro))

end SudoRsProofs.Parser.Analysis.Ref
