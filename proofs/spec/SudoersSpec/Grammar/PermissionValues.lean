import SudoersSpec.Grammar.PermissionCommands

namespace SudoersSpec.Grammar

open SudoersSpec.Syntax hiding specList
open PermissionPrint (specList)

/-! ## Runas values and lexical boundaries -/

abbrev UserItems (O : Oracles) := BoundedItems (fun q : Spec UserSpecifier => UserValue O q.who)
abbrev IdentifierItems (O : Oracles) := BoundedItems (fun q : Spec Identifier => IdentifierValue O q.who)

structure RunasValue (O : Oracles) (a : RunAs) : Prop where
  users : a.users = [] ∨ UserItems O a.users
  groups : a.groups = [] ∨ IdentifierItems O a.groups

private theorem syntaxGap {ch : Char} {r : List Char} {b : Bool} (hw : Boundary b r) :
    SynG ch (ch :: gap b) () r := ⟨gap b, rfl, hw.ws⟩

private theorem commaAbsent {d : Char} {r : List Char} (h : d ≠ ',') :
    NextNot (· = ',') (d :: r) := NextNot.cons_iff.mpr h

private theorem noRunasUsers {O : Oracles} (hO : PermissionLexical O.char) {d : Char}
    {r : List Char} (hd : d = ':' ∨ d = ')') : EmptyRunasUsers O (d :: r) := by
  have h : d.toNat < 128 := by rcases hd with rfl | rfl <;> decide
  apply NextNot.cons_iff.mpr
  simp only [Username.accept1st, Username.accept, hO.alnum_ascii d h, hO.host.upper_ascii d h]
  rcases hd with rfl | rfl <;> decide

private theorem beforeParen {r : List Char} :
    CleanRunasGroupsG O [] [] (')' :: ' ' :: r) :=
  .absent (NextNot.cons_iff.mpr (by decide))

private theorem runasJoin {O : Oracles} {u : SpecList UserSpecifier} {g : SpecList Identifier}
    {cu cg r : List Char} (hw : WsStop r) (hstart : WsStop (cu ++ cg ++ ')' :: ' ' :: r))
    (hu : CleanRunasUsersG O cu u (cg ++ ')' :: ' ' :: r))
    (hg : CleanRunasGroupsG O cg g (')' :: ' ' :: r)) :
    CleanRunAsG O ('(' :: cu ++ cg ++ [')', ' ']) ⟨u, g⟩ r := by
  exact ⟨['('], cu ++ cg ++ [')', ' '], (), rfl, ⟨[], rfl, by
      simpa only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]
        using hstart.nil⟩,
    cu, cg ++ [')', ' '], u, List.append_assoc .., by
      simpa only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] using hu,
    cg, [')', ' '], g, rfl, hg, mapG (syntaxGap (ch := ')') (b := true) hw.boundary)⟩

private theorem listStarts {P : α → Prop} {xs : List α} (h : BoundedItems P xs) (sep : String)
    (f : α → String) (hf : ∀ x, P x → SurfaceStart (f x)) :
    SurfaceStart (sep.intercalate (xs.map f)) := by
  obtain ⟨hn, _, hall⟩ := h
  cases xs with
  | nil => exact False.elim (hn rfl)
  | cons x xs =>
    obtain ⟨d, hd, hb, hbs, hc, hcol⟩ := hf x (hall _ (by simp))
    refine ⟨d, ?_, hb, hbs, hc, hcol⟩
    cases xs with
    | nil => simpa using hd
    | cons y ys => simp [String.intercalate_cons_cons, String.toList_append, List.head?_append, hd]

private theorem usersStart {O : Oracles} {xs : SpecList UserSpecifier} (h : UserItems O xs) :
    SurfaceStart (specList PermissionPrint.user xs) :=
  listStarts h ", " _ (fun _ hq => memberPrinted_start (userValue_start hq))

private theorem groupsStart {O : Oracles} {xs : SpecList Identifier} (h : IdentifierItems O xs) :
    SurfaceStart (specList PermissionPrint.identifier xs) :=
  listStarts h ", " _ (fun _ hq => memberPrinted_start (identValue_start hq))

private theorem canonicalRunasGroups {O : Oracles} (hO : PermissionLexical O.char)
    {g : SpecList Identifier} (hg : IdentifierItems O g) {r : List Char} :
    CleanRunasGroupsG O (':' :: ' ' :: (specList PermissionPrint.identifier g).toList) g (')' :: ' ' :: r) := by
  apply CleanRunasGroupsG.present
  have hstart := (groupsStart hg).append (')' :: ' ' :: r)
  have hEnd : Boundary false (')' :: ' ' :: r) := Boundary.cons (.inr (.inr (.inl rfl))) _ false
  have hlist := identList_value hO hg hEnd (commaAbsent (by decide))
  have hh : NontermG (IdentifierListG O) (specList PermissionPrint.identifier g).toList g
      (')' :: ' ' :: r) := nonterm (by simpa [gap] using hlist) hEnd.1
  exact seqG (syntaxGap (ch := ':') (b := true) hstart.1.boundary) hh

theorem runasValue_grammar {O : Oracles} (hO : PermissionLexical O.char) {a : RunAs}
    (ha : RunasValue O a) {r : List Char} (hr : WsStop r) :
    CleanRunAsG O ((PermissionPrint.runas a).toList ++ [' ']) a r := by
  rcases a with ⟨u, gs⟩
  obtain ⟨hu, hg⟩ := ha
  rcases hg with rfl | hg
  · have he : Boundary false (')' :: ' ' :: r) := Boundary.cons (.inr (.inr (.inl rfl))) _ false
    have hs : CleanRunasUsersG O (specList PermissionPrint.user u).toList u (')' :: ' ' :: r) := by
      rcases hu with rfl | hu
      · exact .inr ⟨rfl, rfl, noRunasUsers hO (.inr rfl)⟩
      · have hj := userList_value hO hu he (commaAbsent (by decide))
        exact .inl (nonterm (by simpa [gap] using hj) he.1)
    have hw : WsStop ((specList PermissionPrint.user u).toList ++ ')' :: ' ' :: r) := by
      rcases hu with rfl | hu
      · exact he.1
      · exact ((usersStart hu).append _).1
    have h := runasJoin hr (cu := (specList PermissionPrint.user u).toList) (cg := []) (by simpa using hw)
      hs beforeParen
    simpa [PermissionPrint.runas, String.toList_append, List.append_assoc] using h
  · let cg := ':' :: ' ' :: (specList PermissionPrint.identifier gs).toList
    have hG : CleanRunasGroupsG O cg gs (')' :: ' ' :: r) := canonicalRunasGroups hO hg
    have hGstart : Boundary true (cg ++ ')' :: ' ' :: r) :=
      Boundary.cons (.inr (.inl rfl)) _ true
    rcases hu with rfl | hu
    · have hU : CleanRunasUsersG O [] [] (cg ++ ')' :: ' ' :: r) :=
        .inr ⟨rfl, rfl, noRunasUsers hO (.inl rfl)⟩
      have h := runasJoin hr (cu := []) (by simpa using hGstart.1) hU hG
      cases gs with
      | nil => exact False.elim (hg.1 rfl)
      | cons g gs => simpa [PermissionPrint.runas, cg, String.toList_append, List.append_assoc] using h
    · let cu := (specList PermissionPrint.user u).toList ++ [' ']
      have hU : CleanRunasUsersG O cu u (cg ++ ')' :: ' ' :: r) :=
        .inl (nonterm (userList_value hO hu hGstart (commaAbsent (by decide))) hGstart.1)
      have hw : WsStop (cu ++ cg ++ ')' :: ' ' :: r) := by
        simp only [cu, List.append_assoc]
        exact ((usersStart hu).append _).1
      have h := runasJoin hr hw hU hG
      cases u with
      | nil => exact False.elim (hu.1 rfl)
      | cons k u =>
        cases gs with
        | nil => exact False.elim (hg.1 rfl)
        | cons g gs => simpa [PermissionPrint.runas, cu, cg, String.toList_append, List.append_assoc] using h

/-! ## The outer lists -/

abbrev EntryValue (O : Oracles) (a : PermissionEntry) : Prop :=
  (∀ x ∈ a.1, RunasValue O x) ∧ CommandSpecValue O a.2

abbrev HostItems (O : Oracles) := BoundedItems (fun q : Spec Hostname => PrintableMeta O.char q.who)

abbrev GroupValue (O : Oracles) (a : PermissionGroup) : Prop :=
  HostItems O a.1 ∧ BoundedItems (EntryValue O) a.2

private theorem hostValue_member {O : Oracles} (hO : PermissionLexical O.char)
    {m : Meta Hostname} (hm : PrintableMeta O.char m) :
    MemberStart (PermissionPrint.metaItem id m) := by
  have htext : (PermissionPrint.metaItem id m).toList = printMeta m := by cases m <;> rfl
  obtain ⟨d, ds, hds, hd⟩ := printMeta_cons hm
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hO.host.hostChar_ne hd
  have hc : d ≠ ':' := by
    rintro rfl
    rw [hO.ascii_host (by decide)] at hd
    contradiction
  exact literalMember (by rw [htext, hds]; rfl) h₁ h₂ h₃ hc h₄

private theorem hostValue_grammar {O : Oracles} (hO : PermissionLexical O.char) {q : Spec Hostname}
    (hq : PrintableMeta O.char q.who) {b : Bool} {r : List Char} (hr : Boundary b r) :
    NontermG (QualG (HostItemG O.char)) ((PermissionPrint.spec id q).toList ++ gap b) q r := by
  have hs : NextNot (fun d => hostChar O.char d = true) (gap b ++ r) := by
    intro d hd ha
    have ht := hr.gapHead hd
    have hAscii : d.toNat < 128 := by
      rcases ht with rfl | ht
      · decide
      · rcases ht with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hO.ascii_host hAscii] at ha
    rcases ht with rfl | ht
    · contradiction
    · rcases ht with rfl | rfl | rfl | rfl | rfl <;> contradiction
  have hp := printMeta_item hO.host hq hs
  have htext : (PermissionPrint.metaItem id q.who).toList = printMeta q.who := by
    cases q.who <;> rfl
  apply memberPrinted_grammar (hostValue_member hO hq) _ hr
  rw [htext]
  exact takeGap hp hr

private theorem hostList_value {O : Oracles} (hO : PermissionLexical O.char) {xs : SpecList Hostname}
    (h : HostItems O xs) {b : Bool} {r : List Char} (hr : Boundary b r) (hsep : NextNot (· = ',') r) :
    HostListG O.char ((specList id xs).toList ++ gap b) xs r :=
  canonicalList _ .comma (fun r => Boundary.cons (.inl rfl) (' ' :: r) false)
    (fun _ hq _ _ h => hostValue_grammar hO hq h)
    (fun _ hq => memberPrinted_start (hostValue_member hO hq)) h hr hsep

private theorem entryStart {O : Oracles} {e : PermissionEntry} (h : EntryValue O e) :
    SurfaceStart (PermissionPrint.entry e) := by
  rcases e with ⟨_ | ra, cs⟩
  · exact commandSpec_start h.2
  · have hr : ∀ r : RunAs, (PermissionPrint.runas r).toList.head? = some '(' := by
      intro r; rcases r with ⟨u, gs⟩; cases u <;> cases gs <;> simp [PermissionPrint.runas,
        String.toList_append]
    exact ⟨'(', by simp [PermissionPrint.entry, String.toList_append, List.head?_append, hr],
      by decide, by decide, by decide, by decide⟩

private theorem entryValue_grammar {O : Oracles} (hO : PermissionLexical O.char) {e : PermissionEntry}
    (he : EntryValue O e) {b : Bool} {r : List Char} (hr : CommandBoundary b r) :
    NontermG (CleanEntryG O) ((PermissionPrint.entry e).toList ++ gap b) e r := by
  rcases e with ⟨ra, cs⟩
  cases ra with
  | none =>
    have hw := (commandSpec_start he.2).append (gap b ++ r)
    have hn : NextNot (· = '(') ((PermissionPrint.commandSpec cs).toList ++ gap b ++ r) := by
      intro d hd h
      have raw := commandSpec_neParen he.2
      subst d
      obtain ⟨j, hj, _, _, _, _⟩ := commandSpec_start he.2
      have e : j = '(' := by simpa [List.append_assoc, List.head?_append, hj] using hd
      exact raw (e ▸ hj)
    have hnone : NontermG (OptG (CleanRunAsG O) (AbsentSyntaxG '(')) [] none
        ((PermissionPrint.commandSpec cs).toList ++ gap b ++ r) :=
      nonterm (.none ⟨rfl, hn⟩) (by simpa only [List.append_assoc] using hw.1)
    exact nonterm (⟨[], _, none, rfl, hnone, mapG (commandSpec_value hO he.2 hr)⟩ : CleanEntryG O _ _ _) hr.ws
  | some ra =>
    have hw := (commandSpec_start he.2).append (gap b ++ r)
    have hm := runasValue_grammar hO (he.1 ra rfl)
      (r := (PermissionPrint.commandSpec cs).toList ++ gap b ++ r) (by simpa only [List.append_assoc] using hw.1)
    have hnt := nonterm (OptG.some hm : OptG (CleanRunAsG O) (AbsentSyntaxG '(') _ (some ra) _)
      (by simpa only [List.append_assoc] using hw.1)
    have he' : CleanEntryG O _ (some ra, cs) r :=
      ⟨_, _, some ra, rfl, hnt, mapG (commandSpec_value hO he.2 hr)⟩
    exact nonterm (by
      simpa [PermissionPrint.entry, String.toList_append, List.append_assoc] using he') hr.ws

private theorem groupStart {O : Oracles} (hO : PermissionLexical O.char) {g : PermissionGroup}
    (hg : GroupValue O g) : SurfaceStart (PermissionPrint.group g) := by
  obtain ⟨d, hd, hb, he, hc, hcol⟩ := listStarts hg.1 ", " _
    (fun _ h => memberPrinted_start (hostValue_member hO h))
  change (specList id g.1).toList.head? = some d at hd
  exact ⟨d, by rw [PermissionPrint.group, String.toList_append, String.toList_append,
      List.head?_append, List.head?_append, hd]; rfl, hb, he, hc, hcol⟩

private theorem groupValue_grammar {O : Oracles} (hO : PermissionLexical O.char) {g : PermissionGroup}
    (hg : GroupValue O g) {b : Bool} {r : List Char} (hr : CommandBoundary b r)
    (hcomma : NextNot (· = ',') r) :
    NontermG (GroupForm O (CleanEntryG O)) ((PermissionPrint.group g).toList ++ gap b) g r := by
  rcases g with ⟨hosts, cmds⟩
  let c := (", ".intercalate (cmds.map PermissionPrint.entry)).toList ++ gap b
  have he : EntriesG (CleanEntryG O) c cmds r :=
    canonicalList PermissionPrint.entry .comma (fun r _ h => by cases h; exact .inl rfl)
      (fun _ hh _ _ hr => entryValue_grammar hO hh hr)
      (fun _ hh => entryStart hh) hg.2 hr hcomma
  have hstart := listStarts hg.2 ", " PermissionPrint.entry (fun _ h => entryStart h)
  have hw : WsStop (c ++ r) := by
    rw [List.append_assoc]; exact (hstart.append _).1
  have hEq : Boundary true ('=' :: ' ' :: c ++ r) := Boundary.cons (.inr (.inr (.inr (.inr rfl)))) _ true
  have hhost := nonterm (hostList_value hO hg.1 hEq (commaAbsent (by decide))) hEq.1
  have heq : SynG '=' ['=', ' '] () (c ++ r) := syntaxGap (b := true) hw.boundary
  have hp : GroupForm O (CleanEntryG O) _ (hosts, cmds) r :=
    ⟨_, ['=', ' '] ++ c, hosts, rfl, by simpa [List.append_assoc] using hhost,
      ['=', ' '], c, (), rfl, heq, mapG (nonterm he hr.ws)⟩
  exact nonterm (by simpa [PermissionPrint.group, c, gap, String.toList_append, List.append_assoc] using hp) hr.ws

/-! ## Permission values -/

/-- The numeric first-user alternative is distinct from ordinary directive dispatch. -/
def FirstUserValue (q : Spec UserSpecifier) : Prop :=
  (∃ n, q = .allow (.only (.user (.id n)))) ∨
    (OrdinaryKey q ∧ NextNot (fun d => d = '@' ∨ d = '#' ∨ d = '"')
      (PermissionPrint.spec PermissionPrint.user q).toList)

/-- A compositional, value-side check for the canonical permission renderer. There is
no `Gram` or stream parser among its fields. Leaf lexical and constructor checks are
finite and use the given character, filesystem and glob oracle snapshot. -/
structure PermissionValue (O : Oracles) (a : PermissionSpec) : Prop where
  users : UserItems O a.users
  first : FirstUserValue (a.users.headD (.allow .all))
  groups : BoundedItems (GroupValue O) a.permissions

private theorem hashUsers_value {O : Oracles} (hO : PermissionLexical O.char) {n : Nat}
    {ks : SpecList UserSpecifier} (h : IdLiteral n)
    (hks : ∀ q ∈ ks, UserValue O q.who) (hlim : ks.length ≤ 127) {r : List Char}
    (hr : Boundary true r) (hc : NextNot (· = ',') r) :
    HashUsersG O ((specList PermissionPrint.user (.allow (.only (.user (.id n))) :: ks)).toList ++ gap true)
      (.allow (.only (.user (.id n))) :: ks) r := by
  cases ks with
  | nil =>
    have hg := nonterm (rawIdG hO (i := .id n) h hr) hr.1
    exact ⟨_, [], .id n, (List.append_nil _).symm, hg,
      [], [], false, rfl, .absent hc, pureG _ r⟩
  | cons k ks =>
    let c := (specList PermissionPrint.user (k :: ks)).toList ++ gap true
    have hV : UserItems O (k :: ks) := ⟨by simp, hlim, hks⟩
    have hw : WsStop (c ++ r) := by
      rw [show c ++ r = (specList PermissionPrint.user (k :: ks)).toList ++ (gap true ++ r) from
        List.append_assoc ..]
      exact ((usersStart hV).append _).1
    have hi := nonterm (rawIdG hO (i := .id n) h (Boundary.cons (.inl rfl) (' ' :: c ++ r) false))
      (Boundary.cons (.inl rfl) (' ' :: c ++ r) false).1
    have hu := nonterm (userList_value hO hV hr hc) hr.1
    have hhash : HashUsersG O (((PermissionPrint.identifier (.id n)).toList ++ [',', ' ']) ++ c)
        (.allow (.only (.user (.id n))) :: k :: ks) r := by
      refine ⟨_, [',', ' '] ++ c, .id n, ?_, hi, [',', ' '], c, true, rfl, .present
        (syntaxGap (ch := ',') (b := true) hw.boundary), mapG hu⟩
      simp [gap, List.append_assoc]
    simpa [specList, PermissionPrint.spec, PermissionPrint.qualified, PermissionPrint.metaItem,
      PermissionPrint.user, String.intercalate_cons_cons, String.toList_append, List.append_assoc, c, gap] using hhash

/-- Structural printability produces the positive, dispatch-aware grammar judgment. -/
theorem permissionValue_printable {O : Oracles} (hO : PermissionLexical O.char)
    {a : PermissionSpec} (ha : PermissionValue O a) : PrintableSudoPermission O a := by
  rcases a with ⟨u, gs⟩
  let c := (" : ".intercalate (gs.map PermissionPrint.group)).toList
  let r := ['\n']
  have hw : WsStop r := NextNot.cons_iff.mpr (by decide)
  have hg : PermissionsForm O (CleanEntryG O) (c ++ gap false) gs r :=
    canonicalList (Follow := fun _ src => ∀ d, src.head? = some d → d = ':' ∨ d = '\n')
      PermissionPrint.group .colon (fun r _ h => by cases h; exact .inl rfl)
      (fun g hh b r hr => groupValue_grammar hO hh
        (fun d e => .inr (hr d e)) (fun d e hd => by subst d; have h := hr ',' e; rcases h with h | h <;> contradiction))
      (fun _ hh => groupStart hO hh) ha.groups
      (fun d e => by cases e; exact .inr rfl) (NextNot.cons_iff.mpr (by decide))
  have hstart := (listStarts ha.groups " : " _ (fun _ hg => groupStart hO hg)).append r
  have hperms : NontermG (PermissionsForm O (CleanEntryG O)) c gs r :=
    nonterm (by simpa [gap] using hg) hw
  have hu := userList_value hO ha.users hstart.1.boundary hstart.2.1
  change PositiveSudoPermissionG O _ ⟨u, gs⟩ r
  have htext : (PermissionPrint.permissionSpec ⟨u, gs⟩).toList =
      (specList PermissionPrint.user u).toList ++ gap true ++ c := by
    simp [PermissionPrint.permissionSpec, String.toList_append, c, gap, List.append_assoc]
  rw [htext]
  rcases ha.first with ⟨n, hn⟩ | ⟨hk, hn⟩
  · cases u with
    | nil => exact False.elim (ha.users.1 rfl)
    | cons k ks =>
      change k = .allow (.only (.user (.id n))) at hn
      subst k
      apply SudoPermissionForm.hash
      · cases ks <;> simp [specList, PermissionPrint.spec, PermissionPrint.qualified,
          PermissionPrint.user, PermissionPrint.metaItem, String.toList_append,
          String.intercalate_cons_cons, idText]
      · refine ⟨_, c, _, rfl, ?_, mapG hperms⟩
        have hN : IdLiteral n := ha.users.2.2 (.allow (.only (.user (.id n)))) (by simp)
        exact hashUsers_value hO hN
          (fun q hq => ha.users.2.2 q (List.mem_cons_of_mem _ hq))
          (by have := ha.users.2.1; simp at this; omega) hstart.1.boundary hstart.2.1
  · refine .ordinary ?_ hk ?_
    · cases u with
      | nil => exact False.elim (ha.users.1 rfl)
      | cons k ks =>
        obtain ⟨d, hd, _, _, _, _⟩ := memberPrinted_start (userValue_start (ha.users.2.2 k (by simp)))
        intro x hx he
        apply hn x _ he
        cases ks with
        | nil =>
          simpa [specList, List.head?_append, hd] using hx
        | cons j js =>
          simp [specList, String.intercalate_cons_cons, String.toList_append, List.head?_append, hd] at hx
          exact hd.trans (congrArg some hx)
    · exact ⟨_, c, u, rfl, nonterm hu hstart.1, mapG hperms⟩

/-- PT5 from the compositional predicate on values, for the very renderer used by the
normal differential harness. The physical newline stays in the remainder. -/
theorem sudo_permission_structural_roundTrip (O : Oracles) (D : Descriptions)
    (hO : PermissionLexical O.char) {a : PermissionSpec} (ha : PermissionValue O a)
    (rest : List Char) (line col : Nat) :
    let c := (PermissionPrint.permissionSpec a).toList
    (sudo O D).run ⟨c ++ '\n' :: rest, line, col⟩ =
      (.ok (.spec a), ⟨'\n' :: rest, (posAfter c (line, col)).1, (posAfter c (line, col)).2⟩) :=
  sudo_permission_roundTrip O D (permissionValue_printable hO ha) rest line col

end SudoersSpec.Grammar
