import SudoersSpec.Grammar.PermissionPrint
import SudoersSpec.Grammar.Examples

namespace SudoersSpec.Grammar.PermissionExamples

open SudoersSpec.Syntax

/-- In-memory oracles for one ordinary conformance example. No system command is executed. -/
def O : Oracles where
  char := CharOracle.latin1
  fs := ⟨fun _ => .err⟩
  glob := ⟨fun _ => none⟩
  fmt := ⟨id, id⟩

abbrev simpleUsers : SpecList UserSpecifier := [.allow .all]
abbrev simpleHosts : SpecList Hostname := [.allow .all]
abbrev simpleCmd : Command := ⟨"/s", .prefix []⟩
abbrev simpleCS : CommandSpec := ⟨[], .allow (.only simpleCmd)⟩
abbrev simpleEntry : PermissionEntry := (none, simpleCS)
abbrev simpleGroup : PermissionGroup := (simpleHosts, [simpleEntry])
abbrev simpleRule : PermissionSpec := ⟨simpleUsers, [simpleGroup]⟩

private theorem charsALL (T : TokenSpec α) (ha : T.accept1st 'A' = true)
    (hl : T.accept 'L' = true) (hs : EscStop T T.accept r)
    (hL : LenOK T.maxLen ['A'] ['L', 'L']) (hv : T.construct ['A', 'L', 'L'] = .ok a) :
    TokenG T ['A', 'L', 'L'] a r :=
  .mk (EscUnit.plain ha (fun _ => by decide))
    (.cons (.plain hl (fun _ => by decide)) (.cons (.plain hl (fun _ => by decide)) (.stop hs))) hL hv

private theorem nontermNil {G : Gram α} {c r : List Char} {a : α}
    (hd : G c a r) (hw : Ws [] r) : NontermG G c a r :=
  ⟨c, [], by simp, hd, hw⟩

private theorem singletonList {G : Gram α} {sep : Char} {n : Nat} {c r : List Char} {a : α}
    (hd : NontermG G c a r) (hs : NextNot (· = sep) r) : ListG G sep n c [a] r := by
  simpa using (ListG.mk (max := n) hd (ListTail.nil hs) (.inl rfl))

private theorem allowG {G : Gram α} {c r : List Char} {a : α}
    (hn : NextNot (· = '!') (c ++ r)) (hd : NontermG G c a r) : QualG G c (.allow a) r :=
  QualG.mk (n := 0) (b := []) .nil hn hd

private abbrev userRest := "ALL = /s\n".toList
private abbrev hostRest := "= /s\n".toList
private abbrev cmdRest := ['\n']

private theorem userExample : NontermG (UserListG O) "ALL ".toList simpleUsers userRest := by
  have hg : TokenG (MetaUsernameToken O) "ALL".toList .all (' ' :: userRest) := by
    exact charsALL _ (by decide) (by decide) (NextNot.cons_iff.mpr (by decide))
      ⟨by decide, by decide, trivial⟩ (by decide)
  have hw : Ws [' '] userRest := .stop (by decide) (by decide)
  have hm : MetaUserG O "ALL ".toList .all userRest :=
    ⟨"ALL ".toList, [], some .all, rfl, ⟨"ALL".toList, [' '], rfl, .some hg, hw⟩, rfl, rfl⟩
  have hw' : Ws [] userRest := Ws.nil_iff.mpr (by decide)
  have hq : QualG (MetaUserG O) "ALL ".toList (.allow .all) userRest :=
    allowG (by decide) (nontermNil hm hw')
  exact nontermNil (singletonList (nontermNil hq hw') (by decide)) hw'

private theorem hostExample : NontermG (HostListG O.char) "ALL ".toList simpleHosts hostRest := by
  have hitem : HostItemG O.char "ALL".toList .all (' ' :: hostRest) :=
    ⟨by decide, by decide, by decide, by decide, .all (by decide)⟩
  have hw : Ws [' '] hostRest := .stop (by decide) (by decide)
  have hw' : Ws [] hostRest := Ws.nil_iff.mpr (by decide)
  have hq : QualG (HostItemG O.char) "ALL ".toList (.allow .all) hostRest :=
    allowG (by decide) ⟨"ALL".toList, [' '], rfl, hitem, hw⟩
  exact nontermNil (singletonList (nontermNil hq hw') (by decide)) hw'

private theorem commandExample : NontermG (CleanEntryG O) "/s".toList simpleEntry cmdRest := by
  have hw : Ws [] cmdRest := Ws.nil_iff.mpr (by decide)
  have hw' : Ws [] ("/s".toList ++ cmdRest) := Ws.nil_iff.mpr (by decide)
  have hg : CommandTokenG O "/s".toList (.only simpleCmd) cmdRest :=
    .mk (.plain (by decide) (fun _ => by decide))
      (.cons (.plain (by decide) (fun _ => by decide)) (.stop (by apply NextNot.cons_iff.mpr; decide)))
      ⟨by decide, trivial⟩ (by decide)
  have hq : QualifiedCommandG O "/s".toList (.allow (.only simpleCmd)) cmdRest :=
    allowG (by decide) (nontermNil hg hw)
  have htag : TagProbeG (CleanMetaTagG O) [] none ("/s".toList ++ cmdRest) :=
    nontermNil (.none ⟨rfl, by decide⟩) hw'
  have hc : CleanCommandSpecG O "/s".toList simpleCS cmdRest :=
    ⟨[], "/s".toList, .inl [], rfl, .stop htag, _, nontermNil hq hw, rfl⟩
  have he : CleanEntryG O "/s".toList simpleEntry cmdRest :=
    ⟨[], "/s".toList, none, rfl, nontermNil (.none ⟨rfl, by decide⟩) hw', _, nontermNil hc hw, rfl⟩
  exact nontermNil he hw

/-- A canonical value certified by the grammar constructors, without running the parser. -/
theorem simplePrintable : PrintablePermission O simpleRule := by
  have hw : Ws [] cmdRest := Ws.nil_iff.mpr (by decide)
  have he : NontermG (EntriesG (CleanEntryG O)) "/s".toList [simpleEntry] cmdRest :=
    nontermNil (singletonList commandExample (by decide)) hw
  have hg : GroupForm O (CleanEntryG O) "ALL = /s".toList simpleGroup cmdRest :=
    ⟨"ALL ".toList, "= /s".toList, simpleHosts, rfl, hostExample,
      "= ".toList, "/s".toList, (), rfl, ⟨[' '], rfl, .stop (by decide) (by decide)⟩,
      [simpleEntry], he, rfl⟩
  have hp : NontermG (PermissionsForm O (CleanEntryG O)) "ALL = /s".toList [simpleGroup] cmdRest :=
    nontermNil (singletonList (nontermNil hg hw) (by decide)) hw
  change PositivePermissionG O "ALL ALL = /s".toList simpleRule cmdRest
  exact ⟨"ALL ".toList, "ALL = /s".toList, simpleUsers, rfl, userExample, [simpleGroup], hp, rfl⟩

example : (permissionLine O Descriptions.release).run (Stream.ofString "ALL ALL = /s\n") =
    (.ok simpleRule, ⟨['\n'], 1, 13⟩) :=
  permissionLine_roundTrip O Descriptions.release simplePrintable [] 1 1

theorem simpleSudoPrintable : PrintableSudoPermission O simpleRule := by
  exact .ordinary (by decide) trivial simplePrintable

example : (sudo O Descriptions.release).run (Stream.ofString "ALL ALL = /s\n") =
    (.ok (.spec simpleRule), ⟨['\n'], 1, 13⟩) :=
  sudo_permission_roundTrip O Descriptions.release simpleSudoPrintable [] 1 1

end SudoersSpec.Grammar.PermissionExamples
