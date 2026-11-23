import SudoersSpec.Grammar.Permission
import SudoersSpec.Grammar.Follow
import SudoersSpec.Grammar.PermissionDispatch

namespace SudoersSpec.Grammar

open SudoersSpec.Syntax

/-! ## Canonical permission text

These renderers have the equations of `Differential.Print` for permission nodes. They are
in the core spec package (which cannot import the differential harness). Validity is a
judgment on the resulting text, not on executing the parser. -/
namespace PermissionPrint

def metaItem (f : α → String) : Meta α → String
  | .all => "ALL"
  | .only a => f a
  | .alias n => n

def qualified (f : α → String) : Qualified α → String
  | .allow a => f a
  | .forbid a => "!" ++ f a

def spec (f : α → String) (s : Spec α) : String := qualified (metaItem f) s

def specList (f : α → String) (ss : SpecList α) : String := ", ".intercalate (ss.map (spec f))

def identifier : Identifier → String
  | .name n => n
  | .id n => s!"#{n}"

def user : UserSpecifier → String
  | .user i => identifier i
  | .group i => "%" ++ identifier i
  | .nonunixGroup i => "%:" ++ identifier i

def args : Args → String
  | .prefix [] => ""
  | .prefix as => " " ++ " ".intercalate as ++ " *"
  | .exact [] => " \"\""
  | .exact as => " " ++ " ".intercalate as

def command (c : Command) : String := c.pattern ++ args c.args

def runas (r : RunAs) : String :=
  match r.users, r.groups with
  | us, [] => "(" ++ specList user us ++ ")"
  | [], gs => "(: " ++ specList identifier gs ++ ")"
  | us, gs => "(" ++ specList user us ++ " : " ++ specList identifier gs ++ ")"

def modifier : Modifier → Option String
  | .exec => some "EXEC:"
  | .noexec => some "NOEXEC:"
  | .setenv => some "SETENV:"
  | .nosetenv => some "NOSETENV:"
  | .passwd => some "PASSWD:"
  | .nopasswd => some "NOPASSWD:"
  | _ => none

def commandSpec (a : CommandSpec) : String :=
  " ".intercalate (a.mods.filterMap modifier ++ [spec command a.cmd])

def entry : PermissionEntry → String
  | (some r, a) => runas r ++ " " ++ commandSpec a
  | (none, a) => commandSpec a

def group (g : PermissionGroup) : String :=
  specList id g.1 ++ " = " ++ ", ".intercalate (g.2.map entry)

def permissionSpec (a : PermissionSpec) : String :=
  specList user a.users ++ " " ++ " : ".intercalate (a.permissions.map group)

end PermissionPrint

/-! ## Right contexts of the positive grammar -/

private theorem mapHead {G : Gram α} {f : α → β} (h : HeadOnly G) : HeadOnly (MapG G f) := by
  rintro c b r r' he ⟨a, hg, hb⟩
  exact ⟨a, h c a r r' he hg, hb⟩

private theorem seqHead {G : Gram α} {H : α → Gram β} (h : HeadOnly G)
    (hh : ∀ a, HeadOnly (H a)) : HeadOnly (SeqG G H) := by
  rintro c b r r' he ⟨x, y, a, rfl, hg, hd⟩
  exact ⟨x, y, a, rfl, h _ _ _ _ (head_append_eq (.inr he)) hg, hh a y b r r' he hd⟩

private theorem pureHead (a : α) : HeadOnly (PureG a) := fun _ _ _ _ _ h => h

private theorem synHead (ch : Char) : HeadOnly (SynG ch) := by
  rintro c a r r' he ⟨w, hc, hw⟩
  exact ⟨w, hc, hw.of_head he⟩

private theorem markHead (ch : Char) : HeadOnly (MarkG ch) := by
  intro c b r r' he hd
  cases hd with
  | present => exact .present
  | absent hn => exact .absent (hn.of_head he)

private theorem escHead {T : TokenSpec α} {pred : Char → Bool} {u : List Char} {a : Char}
    {r r' : List Char} (he : r.head? = r'.head?) (h : EscUnit T pred u a r) :
    EscUnit T pred u a r' := by
  cases h with
  | plain ha hb => exact .plain ha hb
  | escaped ha hb => exact .escaped ha hb
  | backslash ha hb hc => exact .backslash ha hb (hc.of_head he)
  | continuation ha hb hc hd => exact .continuation ha hb hc hd

private theorem tailHead {T : TokenSpec α} {u xs r r' : List Char} (he : r.head? = r'.head?)
    (h : TokTail T u xs r) : TokTail T u xs r' := by
  induction h with
  | stop hn => exact .stop (NextNot.of_head he hn)
  | term h => exact .term h
  | cons hu _ ih => exact .cons (escHead (head_append_eq (.inr he)) hu) (ih he)

private theorem tokenHead (T : TokenSpec α) : HeadOnly (TokenG T) := by
  intro c a r r' he h
  cases h with
  | mk hu ht hl hc => exact .mk (escHead (head_append_eq (.inr he)) hu) (tailHead he ht) hl hc

private theorem rejectTokenHead (T : TokenSpec α) : HeadOnly (TokenRejectG T) := by
  intro c a r r' he h
  cases h with
  | stop hn => exact .stop (NextNot.of_head he hn)
  | continuation h => exact .continuation h

private theorem optHead {G : Gram α} {R : Gram Unit} (h : HeadOnly G) (hr : HeadOnly R) :
    HeadOnly (OptG G R) := by
  intro c a r r' he hd
  cases hd with
  | some hg => exact .some (h _ _ _ _ he hg)
  | none hg => exact .none (hr _ _ _ _ he hg)

private theorem tailListHead {G : Gram α} (h : HeadOnly G) {sep : Char} {c a r r'}
    (he : r.head? = r'.head?) (hd : ListTail G sep c a r) : ListTail G sep c a r' := by
  induction hd with
  | nil hn => exact .nil (hn.of_head he)
  | cons hw hg _ ih =>
    exact .cons (hw.of_head (head_append_eq (.inr he)))
      (NontermG.headOnly h _ _ _ _ (head_append_eq (.inr he)) hg) (ih he)

private theorem listHead {G : Gram α} (h : HeadOnly G) (sep : Char) (max : Nat) :
    HeadOnly (ListG G sep max) := by
  intro c a r r' he hd
  cases hd with
  | mk hg ht hl =>
    exact .mk (NontermG.headOnly h _ _ _ _ (head_append_eq (.inr he)) hg)
      (tailListHead h he ht) hl

private theorem identifierHead (O : Oracles) : HeadOnly (IdentifierG O) := by
  apply seqHead (markHead '#')
  intro b; cases b
  · exact mapHead (NontermG.headOnly (tokenHead _))
  · exact mapHead (NontermG.headOnly (tokenHead _))

private theorem parseUserHead (O : Oracles) : HeadOnly (ParseUserG O) := by
  apply seqHead (markHead '%')
  intro b; cases b
  · apply seqHead (markHead '+'); intro b; cases b
    · exact mapHead (NontermG.headOnly (identifierHead O))
    · exact fun _ _ _ _ _ h => h
  · exact seqHead (markHead ':') (fun _ => mapHead (NontermG.headOnly (identifierHead O)))

private theorem userSpecifierHead (O : Oracles) : HeadOnly (UserSpecifierG O) := by
  apply seqHead (markHead '"'); intro b; cases b
  · exact parseUserHead O
  · apply seqHead (NontermG.headOnly (tokenHead _)); intro _ c a r r' h hd
    exact ⟨hd.1, synHead '"' _ _ _ _ h hd.2⟩

private theorem metaHead (O : Oracles) {G : Gram α} (hG : HeadOnly G) (embed : String → α) :
    HeadOnly (MetaG O G embed) := by
  apply seqHead (NontermG.headOnly (optHead (tokenHead _) (rejectTokenHead _)))
  intro o; cases o
  · exact mapHead hG
  · exact pureHead _

private theorem usersHead (O : Oracles) : HeadOnly (UserListG O) :=
  listHead (QualG.headOnly (metaHead O (userSpecifierHead O) _)) _ _

private theorem idsHead (O : Oracles) : HeadOnly (IdentifierListG O) :=
  listHead (QualG.headOnly (metaHead O (identifierHead O) _)) _ _

private theorem cleanRunasHead (O : Oracles) : HeadOnly (CleanRunAsG O) := by
  apply seqHead (synHead '('); intro _
  apply seqHead (G := CleanRunasUsersG O)
  · intro c a r r' he hd
    rcases hd with h | ⟨hc, ha, hn⟩
    · exact .inl (NontermG.headOnly (usersHead O) _ _ _ _ he h)
    · exact .inr ⟨hc, ha, NextNot.of_head he hn⟩
  · intro _; apply seqHead (G := CleanRunasGroupsG O)
    · intro c a r r' he hd
      cases hd with
      | present h => exact .present (seqHead (synHead ':') (fun _ => NontermG.headOnly (idsHead O)) _ _ _ _ he h)
      | absent hn => exact .absent (hn.of_head he)
    · intro _; exact mapHead (synHead ')')

private theorem tagRhsHead (O : Oracles) (span : Span) (keyword : String) :
    HeadOnly (TagRhsG O span keyword) := by
  unfold TagRhsG
  split
  all_goals first
    | exact mapHead (synHead ':')
    | exact seqHead (synHead '=') (fun _ => mapHead (NontermG.headOnly (tokenHead _)))
    | exact pureHead _
    | exact fun _ _ _ _ _ h => h
    | exact fun _ _ _ _ he ⟨hc, ha, hn⟩ => ⟨hc, ha, hn.of_head he⟩

private theorem metaTagHead (O : Oracles) : HeadOnly (CleanMetaTagG O) := by
  rintro c a r r' he ⟨⟨k, x, y, start, hc, hx, hy⟩, hfree⟩
  exact ⟨⟨k, x, y, start, hc, NontermG.headOnly (fun _ _ _ _ h d =>
    ⟨d.shape, d.len, d.stop.of_head h, d.value⟩) _ _ _ _ (head_append_eq (.inr he)) hx,
    tagRhsHead O _ k _ _ _ _ he hy⟩, hfree⟩

private theorem tagLoopHead {K : Gram (Meta Modifier)} (h : HeadOnly K) (mods : List Modifier) :
    HeadOnly (TagLoopG K mods) := by
  have probe : HeadOnly (TagProbeG K) := NontermG.headOnly
    (optHead h (fun _ _ _ _ he ⟨hc, hn⟩ => ⟨hc, hn.of_head he⟩))
  intro c a r r' he hg
  induction hg with
  | stop hp => exact .stop (probe _ _ _ _ he hp)
  | all hp => exact .all (probe _ _ _ _ he hp)
  | alias hp => exact .alias (probe _ _ _ _ he hp)
  | modifier hp hn _ ih => exact .modifier (probe _ _ _ _ (head_append_eq (.inr he)) hp) hn (ih he)

private theorem cleanCmdHead (O : Oracles) : HeadOnly (CleanCommandSpecG O) := by
  apply seqHead (tagLoopHead (metaTagHead O) [])
  intro v; cases v
  · exact mapHead (NontermG.headOnly (QualG.headOnly (tokenHead _)))
  · exact pureHead _

private theorem cleanEntryHead (O : Oracles) : HeadOnly (CleanEntryG O) :=
  seqHead (NontermG.headOnly (optHead (cleanRunasHead O)
    (fun _ _ _ _ he ⟨hc, hn⟩ => ⟨hc, hn.of_head he⟩)))
    (fun _ => mapHead (NontermG.headOnly (cleanCmdHead O)))

private theorem hostListHead (O : CharOracle) : HeadOnly (HostListG O) :=
  listHead (QualG.headOnly (HostItemG.headOnly O)) ',' 127

theorem positivePermission_headOnly (O : Oracles) : HeadOnly (PositivePermissionG O) :=
  seqHead (NontermG.headOnly (usersHead O)) (fun _ => mapHead (NontermG.headOnly
    (listHead (seqHead (NontermG.headOnly (hostListHead O.char)) (fun _ =>
      seqHead (synHead '=') (fun _ => mapHead (NontermG.headOnly
        (listHead (cleanEntryHead O) ',' 127))))) ':' 127)))

theorem positiveSudoPermission_headOnly (O : Oracles) : HeadOnly (PositiveSudoPermissionG O) := by
  intro c a r r' he hd
  have hhead := head_append_eq (x := c) (.inr he)
  cases hd with
  | hash hn hd =>
    apply SudoPermissionForm.hash (hhead.symm.trans hn)
    have hg : HeadOnly (HashUsersG O) := by
      apply seqHead (NontermG.headOnly (identifierHead O))
      intro p
      apply seqHead (G := SyntaxMarkG ',')
      · intro c b r r' he hd
        cases hd with
        | present h => exact .present (synHead ',' _ _ _ _ he h)
        | absent h => exact .absent (h.of_head he)
      · intro b; cases b
        · exact pureHead _
        · exact mapHead (NontermG.headOnly (usersHead O))
    have hp : HeadOnly (PermissionsForm O (CleanEntryG O)) :=
      listHead (seqHead (NontermG.headOnly (hostListHead O.char)) (fun _ =>
        seqHead (synHead '=') (fun _ => mapHead (NontermG.headOnly
          (listHead (cleanEntryHead O) ',' 127))))) ':' 127
    exact seqHead hg (fun _ => mapHead (NontermG.headOnly hp)) _ _ _ _ he hd
  | quoted hn hd => exact .quoted (hhead.symm.trans hn) (positivePermission_headOnly O _ _ _ _ he hd)
  | ordinary hn hk hd => exact .ordinary (hn.of_head hhead) hk (positivePermission_headOnly O _ _ _ _ he hd)

/-! ## Position, printability and follow -/

/-- A canonical text is printable if it has a clean derivation before a line terminator.
This is an oracle-relative *grammar* criterion. It checks token classes, classification,
length/count bounds, command constructor semantics, and intervening lexical boundaries.
It imposes no claim that arbitrary AST values or arbitrary choices of oracles are printable. -/
def PrintablePermission (O : Oracles) (a : PermissionSpec) : Prop :=
  PositivePermissionG O (PermissionPrint.permissionSpec a).toList a ['\n']

/-- Printability for the actual `Sudo` production additionally checks directive dispatch
and the distinct lexical rule for a first `#id`. -/
def PrintableSudoPermission (O : Oracles) (a : PermissionSpec) : Prop :=
  PositiveSudoPermissionG O (PermissionPrint.permissionSpec a).toList a ['\n']

/-- PT3 for the permission alternative. -/
theorem permissionLine_pt3 (O : Oracles) (D : Descriptions) {s t : Stream} {a : PermissionSpec}
    (h : (permissionLine O D).run s = (.ok a, t)) :
    ∃ c, s.rest = c ++ t.rest ∧ PermissionG O c a t.rest ∧ t.getPos = posAfter c s.getPos :=
  (permissionLine_sound O D).pos h

/-- PT4 for the clean positive permission grammar. The right context is part of the
judgment; it enforces maximal munch at both inner and outer boundaries. -/
theorem permissionLine_pt4 (O : Oracles) (D : Descriptions) {c r : List Char} {a : PermissionSpec}
    (hd : PositivePermissionG O c a r) (line col : Nat) :
    (permissionLine O D).run ⟨c ++ r, line, col⟩ =
      (.ok a, ⟨r, (posAfter c (line, col)).1, (posAfter c (line, col)).2⟩) :=
  (permissionLine_complete O D).run_eq hd line col

/-- PT5 for the canonical printable fragment. The follow character is a physical newline,
which belongs to the remainder, not to the permission production. -/
theorem permissionLine_roundTrip (O : Oracles) (D : Descriptions) {a : PermissionSpec}
    (h : PrintablePermission O a) (rest : List Char) (line col : Nat) :
    let c := (PermissionPrint.permissionSpec a).toList
    (permissionLine O D).run ⟨c ++ '\n' :: rest, line, col⟩ =
      (.ok a, ⟨'\n' :: rest, (posAfter c (line, col)).1, (posAfter c (line, col)).2⟩) := by
  dsimp only
  have hd := positivePermission_headOnly O (PermissionPrint.permissionSpec a).toList a
    ['\n'] ('\n' :: rest) rfl h
  exact permissionLine_pt4 O D hd line col

/-- PT5 for the actual permission alternative of `Syntax.sudo`. -/
theorem sudo_permission_roundTrip (O : Oracles) (D : Descriptions) {a : PermissionSpec}
    (h : PrintableSudoPermission O a) (rest : List Char) (line col : Nat) :
    let c := (PermissionPrint.permissionSpec a).toList
    (sudo O D).run ⟨c ++ '\n' :: rest, line, col⟩ =
      (.ok (.spec a), ⟨'\n' :: rest, (posAfter c (line, col)).1, (posAfter c (line, col)).2⟩) := by
  dsimp only
  let c := (PermissionPrint.permissionSpec a).toList
  have hd := positiveSudoPermission_headOnly O c a ['\n'] ('\n' :: rest) rfl h
  exact sudo_permission_pt4 O D hd line col

end SudoersSpec.Grammar
