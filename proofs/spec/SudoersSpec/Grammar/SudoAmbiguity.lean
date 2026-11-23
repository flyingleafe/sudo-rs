import SudoersSpec.Grammar.SudoFile
import SudoersSpec.Grammar.SudoTagPosition

/-! Two independent reasons why the soundness grammar is not an exact grammar. These are
structural witnesses about grammar rules, with abstract lexical contexts, not policy runs. -/

namespace SudoersSpec.Grammar

open SudoersSpec.Syntax

private theorem nonterm_nil {G : Gram α} {c r : List Char} {a : α}
    (h : G c a r) (hw : Ws [] r) : NontermG G c a r :=
  ⟨c, [], (List.append_nil c).symm, h, hw⟩

private theorem singleton_list {G : Gram α} {sep : Char} {max : Nat} {c r : List Char} {a : α}
    (h : NontermG G c a r) (hn : NextNot (· = sep) r) : ListG G sep max c [a] r := by
  simpa only [List.append_nil, List.nil_append] using ListG.mk (max := max) h (ListTail.nil hn) (.inl rfl)

/-- `MissG` leaves any split of its input possible. In a runas clause with no valid user
list and a valid group clause, it can consume none of the group clause or all of it. -/
theorem runas_miss_ambiguity (O : Oracles) {opening groups closing rest : List Char} {gs : SpecList Identifier}
    (ho : SynG '(' opening () (groups ++ (closing ++ rest)))
    (hm : NoMatch (NontermG (UserListG O)) (groups ++ (closing ++ rest)))
    (hg : RunasGroupListG O groups gs (closing ++ rest)) (hne : gs ≠ [])
    (hc : SynG ')' closing () rest) :
    ∃ a b, a ≠ b ∧ RunAsG O (opening ++ (groups ++ closing)) a rest ∧
      RunAsG O (opening ++ (groups ++ closing)) b rest := by
  have hclose : NextNot (· = ':') (closing ++ rest) := by
    obtain ⟨w, rfl, _⟩ := hc
    exact NextNot.cons_iff.mpr (by decide)
  have ho' : SynG '(' opening () ((groups ++ closing) ++ rest) := by simpa only [List.append_assoc] using ho
  refine ⟨⟨[], gs⟩, ⟨[], []⟩, ?_, ?_, ?_⟩
  · intro h; exact hne (congrArg RunAs.groups h)
  · refine ⟨opening, groups ++ closing, (), rfl, ho', [], groups ++ closing, [], rfl, .inr ⟨rfl, ?_⟩,
      groups, closing, gs, rfl, .present hg, (), hc, rfl⟩
    simpa only [MissG, List.nil_append, List.append_assoc] using hm
  · refine ⟨opening, groups ++ closing, (), rfl, ho', groups, closing, [], rfl, .inr ⟨rfl, hm⟩,
      [], closing, [], rfl, .absent hclose, (), hc, rfl⟩

private abbrev ignoredSpec (users : SpecList UserSpecifier) (hosts : SpecList Hostname)
    (command : String) (span : Span) : PermissionSpec :=
  ⟨users, [(hosts, [(none, ⟨[.ignored span], .allow (.alias command)⟩)])]⟩

/-- In any ordinary single-command context of this shape, an ignored tag gives distinct
`SudoItemG` ASTs at the *same* input and output cursors. Pinning the cursor of the outer
item does not pin the start of that tag's source span. -/
theorem sudoItem_ignored_span_ambiguity (O : Oracles)
    {u h eq tag cmd : List Char} {users : SpecList UserSpecifier} {hosts : SpecList Hostname}
    {name : String} {span : Span} (start : Nat × Nat)
    (hu : NontermG (UserListG O) u users (h ++ (eq ++ (tag ++ (cmd ++ ['\n'])))))
    (hh : NontermG (HostListG O.char) h hosts (eq ++ (tag ++ (cmd ++ ['\n']))))
    (he : SynG '=' eq () (tag ++ (cmd ++ ['\n'])))
    (hk : OrdinaryKey (users.headD (.allow .all)))
    (hfirst : NextNot (fun d => d = '@' ∨ d = '#' ∨ d = '"') ((u ++ (h ++ (eq ++ (tag ++ cmd)))) ++ ['\n']))
    (hnoRunAs : NextNot (· = '(') (tag ++ (cmd ++ ['\n'])))
    (hws₁ : Ws [] (tag ++ (cmd ++ ['\n']))) (hws₂ : Ws [] (cmd ++ ['\n']))
    (ht : MetaTagG O tag (.only (.ignored span)) (cmd ++ ['\n']))
    (hlast : TagProbeG (MetaTagG O) cmd (some (.alias name)) ['\n']) :
    ∃ s t a b, a ≠ b ∧ SudoItemG O s a t ∧ SudoItemG O s b t := by
  let c := u ++ (h ++ (eq ++ (tag ++ cmd)))
  let s : Stream := ⟨c ++ ['\n'], start.1, start.2⟩
  let stop := posAfter c s.getPos
  let t : Stream := ⟨['\n'], stop.1, stop.2⟩
  have hw : Ws [] ['\n'] := Ws.nil_iff.mpr (by decide)
  have item (sp : Span) (ht' : MetaTagG O tag (.only (.ignored sp)) (cmd ++ ['\n'])) :
      SudoItemG O s (.spec (ignoredSpec users hosts name sp)) t := by
    let cs : CommandSpec := ⟨[.ignored sp], .allow (.alias name)⟩
    have hprobe : TagProbeG (MetaTagG O) tag (some (.only (.ignored sp))) (cmd ++ ['\n']) :=
      nonterm_nil (.some ht') hws₂
    have hloop : TagLoopG (MetaTagG O) [] (tag ++ cmd) (.inr cs) ['\n'] :=
      .modifier hprobe (by change 1 ≤ 127; decide) (.alias hlast)
    have hcs : CommandSpecG O (tag ++ cmd) cs ['\n'] :=
      ⟨tag ++ cmd, [], .inr cs, (List.append_nil _).symm, hloop, rfl, rfl⟩
    have hEntry : EntryG O (tag ++ cmd) (none, cs) ['\n'] := by
      refine ⟨[], tag ++ cmd, none, rfl, nonterm_nil (.none ⟨rfl, ?_⟩) ?_, cs, nonterm_nil hcs hw, rfl⟩
      · simpa only [List.append_assoc] using hnoRunAs
      · simpa only [List.append_assoc] using hws₁
    have hEntries : NontermG (EntriesG (EntryG O)) (tag ++ cmd) [(none, cs)] ['\n'] :=
      nonterm_nil (singleton_list (nonterm_nil hEntry hw) (by decide)) hw
    have hGroup : GroupForm O (EntryG O) (h ++ (eq ++ (tag ++ cmd))) (hosts, [(none, cs)]) ['\n'] := by
      refine ⟨h, eq ++ (tag ++ cmd), hosts, rfl, ?_, eq, tag ++ cmd, (), rfl, ?_, _, hEntries, rfl⟩
      · simpa only [List.append_assoc] using hh
      · simpa only [List.append_assoc] using he
    have hPermissions : NontermG (PermissionsForm O (EntryG O)) (h ++ (eq ++ (tag ++ cmd)))
        [(hosts, [(none, cs)])] ['\n'] :=
      nonterm_nil (singleton_list (nonterm_nil hGroup hw) (by decide)) hw
    have hForm : PermissionForm O (EntryG O) c (ignoredSpec users hosts name sp) ['\n'] := by
      refine ⟨u, _, users, rfl, ?_, _, hPermissions, rfl⟩
      simpa only [List.append_assoc] using hu
    have ha : AtCursor (SudoPermissionG O) s (ignoredSpec users hosts name sp) t :=
      ⟨c, rfl, .ordinary hfirst hk hForm, by simp [t, stop, Stream.getPos]⟩
    exact ⟨t, ⟨ha.reaches, .permission ha⟩, [], rfl, hw, rfl⟩
  obtain ⟨stop₁, h₁⟩ := metaTagG_ignored_rebase O ht (1, 1)
  obtain ⟨stop₂, h₂⟩ := metaTagG_ignored_rebase O ht (2, 1)
  refine ⟨s, t, _, _, ?_, item ⟨(1, 1), stop₁⟩ h₁, item ⟨(2, 1), stop₂⟩ h₂⟩
  simp [ignoredSpec]

private def lexicalOracle : Oracles where
  char := CharOracle.latin1
  fs := ⟨fun _ => .err⟩
  glob := ⟨fun _ => none⟩
  fmt := ⟨id, id⟩

/-- A witness stated using only lexical segments and unresolved aliases. No policy is
evaluated: the two derivations differ solely in ignored-tag metadata. -/
theorem broadSudoItem_not_functional :
    ∃ O s t a b, a ≠ b ∧ SudoItemG O s a t ∧ SudoItemG O s b t := by
  let O := lexicalOracle
  let sourceTag := "LOG_INPUT".toList
  let ws : List Char := [' ']
  let restTag : List Char := ':' :: ' ' :: 'Q' :: ['\n']
  let span : Span := ⟨(1, 1), posAfter sourceTag (1, 1)⟩
  have hn : NextNot (fun d => AliasName.accept d = true) restTag := by decide
  have htagName : AliasNameG sourceTag "LOG_INPUT" restTag := ⟨by decide, by decide, hn, rfl⟩
  have htagRhs : SynG ':' [':', ' '] () ['Q', '\n'] := ⟨ws, rfl, .stop (by decide) (by decide)⟩
  have htag : MetaTagG O (sourceTag ++ [':', ' ']) (.only (.ignored span)) ['Q', '\n'] :=
    ⟨"LOG_INPUT", sourceTag, [':', ' '], (1, 1), rfl, nonterm_nil htagName (Ws.nil_iff.mpr (by decide)),
      (), htagRhs, rfl⟩
  have hcmdRaw : MetaTagG O ['Q'] (.alias "Q") ['\n'] :=
    ⟨"Q", ['Q'], [], (1, 1), rfl, nonterm_nil ⟨by decide, by decide, by decide, rfl⟩ (by
      exact Ws.nil_iff.mpr (by decide)), rfl, rfl, by decide⟩
  have hcmd : TagProbeG (MetaTagG O) ['Q'] (some (.alias "Q")) ['\n'] :=
    nonterm_nil (.some hcmdRaw) (Ws.nil_iff.mpr (by decide))
  let afterHost := ['=', ' '] ++ ((sourceTag ++ [':', ' ']) ++ ['Q', '\n'])
  let afterUser := ['H', ' '] ++ afterHost
  have hUserRaw : TokenG (MetaUsernameToken O) ['U'] (.alias "U") (' ' :: afterUser) :=
    .mk (.plain (by decide) (fun _ => by decide)) (.stop (NextNot.cons_iff.mpr (by decide))) trivial (by decide)
  have hUserValue : MetaUserG O ['U', ' '] (.alias "U") afterUser :=
    ⟨['U', ' '], [], some (.alias "U"), rfl,
      ⟨['U'], ws, rfl, .some hUserRaw, .stop (by decide) (by decide)⟩, rfl, rfl⟩
  have hUws : Ws [] afterUser := Ws.nil_iff.mpr (by decide)
  have hUqualified : QualG (MetaUserG O) ['U', ' '] (.allow (.alias "U")) afterUser :=
    QualG.mk (n := 0) (b := []) .nil (by decide) (nonterm_nil hUserValue hUws)
  have hUser : NontermG (UserListG O) ['U', ' '] [.allow (.alias "U")] afterUser :=
    nonterm_nil (singleton_list (nonterm_nil hUqualified hUws) (by decide)) hUws
  have hHostRaw : HostItemG O.char ['H'] (.alias "H") (' ' :: afterHost) :=
    ⟨by decide, by decide, by decide, by decide, .alias (by decide) (by decide)⟩
  have hHws : Ws [] afterHost := Ws.nil_iff.mpr (by decide)
  have hHqualified : QualG (HostItemG O.char) ['H', ' '] (.allow (.alias "H")) afterHost :=
    QualG.mk (n := 0) (b := []) .nil (by decide) ⟨['H'], ws, rfl, hHostRaw, .stop (by decide) (by decide)⟩
  have hHost : NontermG (HostListG O.char) ['H', ' '] [.allow (.alias "H")] afterHost :=
    nonterm_nil (singleton_list (nonterm_nil hHqualified hHws) (by decide)) hHws
  have hEq : SynG '=' ['=', ' '] () ((sourceTag ++ [':', ' ']) ++ ['Q', '\n']) :=
    ⟨ws, rfl, .stop (by decide) (by decide)⟩
  refine ⟨O, sudoItem_ignored_span_ambiguity O (1, 1) hUser hHost hEq (by trivial) (by decide)
    (by decide) (Ws.nil_iff.mpr (by decide)) (Ws.nil_iff.mpr (by decide)) htag hcmd⟩

end SudoersSpec.Grammar
