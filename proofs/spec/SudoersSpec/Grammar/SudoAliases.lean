import SudoersSpec.Grammar.Permission
import SudoersSpec.Syntax.Sudo

namespace SudoersSpec.Grammar

open SudoersSpec.Syntax SudoersSpec.Syntax.Parser

/-- A definition cannot bind any of the reserved alias names. -/
def NonreservedAlias (name : String) : Prop :=
  name ∉ ["ALL", "CHROOT", "CWD", "NOTAFTER", "NOTBEFORE", "ROLE", "TIMEOUT", "TYPE"]

private theorem nonreservedAlias_iff_not_reserved {name : String} :
    NonreservedAlias name ↔ ¬ isReservedAlias name = true := by
  simp [NonreservedAlias, isReservedAlias, Bool.or_eq_true, or_assoc]

/-- `NAME '=' Item_List`, with the token grammar for `NAME` and a separate reserved-word
condition. Each part sees the remaining parts and the final right context. -/
inductive AliasDefG (G : Gram (Meta α)) (m : Many) : Gram (Def α) where
  | mk : NontermG (TokenG aliasNameToken) n name (eq ++ body ++ r) →
      NonreservedAlias name → SynG '=' eq () (body ++ r) →
      NontermG (SpecListG G m) body items r →
      AliasDefG G m (n ++ eq ++ body) ⟨name, items⟩ r

/-- A nonempty, colon-separated sequence of alias definitions, subject to the definition limit. -/
def AliasDefsG (G : Gram (Meta α)) (m : Many) : Gram (List (Def α)) :=
  ListG (AliasDefG G m) defMany.sep defMany.limit

theorem aliasDef_sound {p : Parser (Meta α)} {G : Gram (Meta α)} (hp : Sound p G)
    (m : Many) (d : String) : Sound (defParser m d p) (AliasDefG G m) := by
  intro s a t h
  simp only [defParser, run_bind_of_ok (run_getPos s)] at h
  obtain ⟨name, u, hn, hbody⟩ := run_bind_eq_ok.mp h
  split at hbody
  · simp at hbody
  · rename_i hreserved
    obtain ⟨x, v, he, htail⟩ := run_bind_eq_ok.mp hbody
    cases x
    obtain ⟨items, w, hi, hpure⟩ := run_bind_eq_ok.mp htail
    simp only [run_pure, Prod.mk.injEq, Except.ok.injEq] at hpure
    obtain ⟨rfl, rfl⟩ := hpure
    obtain ⟨n, hns, hgn⟩ := tryNonterminal_sound (token_sound aliasNameToken) _ _ _ hn
    obtain ⟨e, hes, hge⟩ := expectSyntax_sound '=' _ _ _ he
    obtain ⟨i, his, hgi⟩ := expectNonterminal_sound (specList_sound hp m d) d _ _ _ hi
    refine ⟨n ++ e ++ i, ?_, .mk ?_ (nonreservedAlias_iff_not_reserved.mpr hreserved) ?_ hgi⟩
    · rw [hns, hes, his]; simp only [List.append_assoc]
    · rwa [List.append_assoc, ← his, ← hes]
    · rwa [← his]

theorem aliasDefs_sound {p : Parser (Meta α)} {G : Gram (Meta α)} (hp : Sound p G)
    (D : Descriptions) (m : Many) (d : String) : Sound (defs D m d p) (AliasDefsG G m) :=
  parseList_sound (aliasDef_sound hp m d) defMany.sep defMany.limit D.def_

theorem aliasDef_complete {p : Parser (Meta α)} {G : Gram (Meta α)} (hp : Complete p G)
    (m : Many) (d : String) : Complete (defParser m d p) (AliasDefG G m) := by
  intro c a r s hd hs
  cases hd with
  | mk hn hnr he hi =>
    obtain ⟨u, hrun, hu⟩ := tryNonterminal_complete (token_complete aliasNameToken) _ _ _ s hn
      (by simpa only [List.append_assoc] using hs)
    unfold defParser
    rw [run_bind_of_ok (run_getPos s), run_bind_of_ok hrun,
      ite_eq_right (nonreservedAlias_iff_not_reserved.mp hnr)]
    exact (seq_complete (expectSyntax_complete '=') (fun _ =>
      mapP_complete (expectNonterminal_complete (specList_complete hp m d) d)
        (fun items => Def.mk _ items))) _ _ _ u
      ⟨_, _, (), rfl, he, _, hi, rfl⟩ (by simpa only [List.append_assoc] using hu)

theorem aliasDefs_complete {p : Parser (Meta α)} {G : Gram (Meta α)} (hp : Complete p G)
    (D : Descriptions) (m : Many) (d : String) : Complete (defs D m d p) (AliasDefsG G m) :=
  parseList_complete (aliasDef_complete hp m d) defMany.sep defMany.limit D.def_

/-! The alias directive bodies begin after the keyword. `Cmd_Alias` uses the same body as
`Cmnd_Alias`, and runas aliases use the same member grammar as user aliases. -/

abbrev UserAliasBodyG (O : Oracles) : Gram Directive :=
  MapG (NontermG (AliasDefsG (MetaUserG O) userSpecifierMany)) Directive.userAlias

abbrev RunasAliasBodyG (O : Oracles) : Gram Directive :=
  MapG (NontermG (AliasDefsG (MetaUserG O) userSpecifierMany)) Directive.runasAlias

abbrev HostAliasBodyG (O : Oracles) : Gram Directive :=
  MapG (NontermG (AliasDefsG (HostItemG O.char) hostnameMany)) Directive.hostAlias

abbrev CmndAliasBodyG (O : Oracles) : Gram Directive :=
  MapG (NontermG (AliasDefsG (CommandTokenG O) {})) Directive.cmndAlias

theorem userAliasBody_sound (O : Oracles) (D : Descriptions) :
    Sound (MapP (expectNonterminal D.def_
      (defs D userSpecifierMany D.userSpecifier (metaUserSpecifier O D))) Directive.userAlias)
      (UserAliasBodyG O) :=
  mapP_sound (expectNonterminal_sound
    (aliasDefs_sound (parseMeta_sound O (userSpecifier_sound O D) _) D _ _) _) _

theorem userAliasBody_complete (O : Oracles) (D : Descriptions) :
    Complete (MapP (expectNonterminal D.def_
      (defs D userSpecifierMany D.userSpecifier (metaUserSpecifier O D))) Directive.userAlias)
      (UserAliasBodyG O) :=
  mapP_complete (expectNonterminal_complete
    (aliasDefs_complete (parseMeta_complete O (userSpecifier_complete O D) _) D _ _) _) _

theorem runasAliasBody_sound (O : Oracles) (D : Descriptions) :
    Sound (MapP (expectNonterminal D.def_
      (defs D userSpecifierMany D.userSpecifier (metaUserSpecifier O D))) Directive.runasAlias)
      (RunasAliasBodyG O) :=
  mapP_sound (expectNonterminal_sound
    (aliasDefs_sound (parseMeta_sound O (userSpecifier_sound O D) _) D _ _) _) _

theorem runasAliasBody_complete (O : Oracles) (D : Descriptions) :
    Complete (MapP (expectNonterminal D.def_
      (defs D userSpecifierMany D.userSpecifier (metaUserSpecifier O D))) Directive.runasAlias)
      (RunasAliasBodyG O) :=
  mapP_complete (expectNonterminal_complete
    (aliasDefs_complete (parseMeta_complete O (userSpecifier_complete O D) _) D _ _) _) _

theorem hostAliasBody_sound (O : Oracles) (D : Descriptions) :
    Sound (MapP (expectNonterminal D.def_
      (defs D hostnameMany D.hostname (metaHostname O.char))) Directive.hostAlias)
      (HostAliasBodyG O) :=
  mapP_sound (expectNonterminal_sound (aliasDefs_sound (metaHostname_sound O.char) D _ _) _) _

theorem hostAliasBody_complete (O : Oracles) (D : Descriptions) :
    Complete (MapP (expectNonterminal D.def_
      (defs D hostnameMany D.hostname (metaHostname O.char))) Directive.hostAlias)
      (HostAliasBodyG O) :=
  mapP_complete (expectNonterminal_complete
    (aliasDefs_complete (metaHostname_complete O.char) D _ _) _) _

theorem cmndAliasBody_sound (O : Oracles) (D : Descriptions) :
    Sound (MapP (expectNonterminal D.def_
      (defs D {} D.command (token (metaToken O.char (commandToken O))))) Directive.cmndAlias)
      (CmndAliasBodyG O) :=
  mapP_sound (expectNonterminal_sound (aliasDefs_sound (token_sound _) D _ _) _) _

theorem cmndAliasBody_complete (O : Oracles) (D : Descriptions) :
    Complete (MapP (expectNonterminal D.def_
      (defs D {} D.command (token (metaToken O.char (commandToken O))))) Directive.cmndAlias)
      (CmndAliasBodyG O) :=
  mapP_complete (expectNonterminal_complete (aliasDefs_complete (token_complete _) D _ _) _) _

/-- `Defaults!` uses simple command patterns, without the argument patterns of `Cmnd_Alias`. -/
def SimpleCommandListG (O : Oracles) : Gram (SpecList SimpleCommand) :=
  SpecListG (TokenG (metaToken O.char (simpleCommandToken O))) {}

theorem simpleCommandList_sound (O : Oracles) (D : Descriptions) :
    Sound (specListSimpleCommand O D) (SimpleCommandListG O) :=
  specList_sound (token_sound _) _ _

theorem simpleCommandList_complete (O : Oracles) (D : Descriptions) :
    Complete (specListSimpleCommand O D) (SimpleCommandListG O) :=
  specList_complete (token_complete _) _ _

end SudoersSpec.Grammar
