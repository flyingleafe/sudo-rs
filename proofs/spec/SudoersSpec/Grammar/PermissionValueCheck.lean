import SudoersSpec.Grammar.PermissionValues

namespace SudoersSpec.Grammar

open SudoersSpec.Syntax

/-! The value check is executable when the oracle snapshot is executable. It never
runs the stream parser and does not try to decide `PermissionLexical`'s global laws. -/

private def decidableHead (p : Char → Prop) [DecidablePred p] (cs : List Char) :
    Decidable (∀ d, cs.head? = some d → p d) :=
  match cs with
  | [] => isTrue (by intro _ h; cases h)
  | d :: _ => decidable_of_iff (p d)
      ⟨fun h _ he => (Option.some.inj he) ▸ h, fun h => h d rfl⟩

private def decidableBoolAll (P : Bool → Prop) [DecidablePred P] : Decidable (∀ b, P b) :=
  decidable_of_iff (P false ∧ P true)
    ⟨fun ⟨h₁, h₂⟩ b => match b with | false => h₁ | true => h₂,
      fun h => ⟨h false, h true⟩⟩

instance (T : TokenSpec α) (c : List Char) : Decidable (LiteralLexeme T c) := by
  letI := decidableHead (fun d => T.accept1st d = true) c
  apply decidable_of_iff (c ≠ [] ∧ (∀ d, c.head? = some d → T.accept1st d = true) ∧
    (∀ d ∈ c.drop 1, T.accept d = true) ∧ '\\' ∉ c ∧ utf8Len c.dropLast < T.maxLen)
  exact ⟨(fun ⟨hn, hf, ht, hq, hb⟩ => ⟨hn, hf, ht, hq, hb⟩),
    fun h => ⟨h.ne, h.first, h.tail, h.noEscape, h.bytes⟩⟩

instance [DecidableEq α] (T : TokenSpec α) (c : List Char) (a : α) : Decidable (LiteralValue T c a) :=
  decidable_of_iff (LiteralLexeme T c ∧ T.construct c = .ok a)
    ⟨fun ⟨hc, ha⟩ => hc.withValue ha,
      fun h => ⟨h.toLiteralLexeme, h.value⟩⟩

instance (s : String) : Decidable (NameStart s) := by
  unfold NameStart
  cases he : s.toList.head? with
  | none => exact isFalse (by rintro ⟨_, e, _⟩; cases e)
  | some d =>
    exact decidable_of_iff (Hostname.accept d = true)
      ⟨fun h => ⟨d, rfl, h⟩, fun ⟨_, he, h⟩ => by cases he; exact h⟩

instance (O : Oracles) (v : Identifier) : Decidable (RawIdentifierValue O v) := by
  unfold RawIdentifierValue
  cases v <;> infer_instance

instance (O : Oracles) (a : Meta UserSpecifier) : Decidable (UserValue O a) := by
  unfold UserValue
  cases a with
  | all | alias _ => infer_instance
  | only a =>
    cases a with
    | user x => cases x <;> infer_instance
    | group _ | nonunixGroup _ => infer_instance

instance (O : Oracles) (a : Meta Identifier) : Decidable (IdentifierValue O a) := by
  unfold IdentifierValue
  cases a with
  | all | alias _ => infer_instance
  | only x => cases x <;> infer_instance

instance (O : CharOracle) (a : Meta Hostname) : Decidable (PrintableMeta O a) := by
  unfold PrintableMeta
  cases a <;> infer_instance

instance (P : α → Prop) [DecidablePred P] (a : List α) : Decidable (BoundedItems P a) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance (O : Oracles) (a : RunAs) : Decidable (RunasValue O a) :=
  decidable_of_iff ((a.users = [] ∨ UserItems O a.users) ∧ (a.groups = [] ∨ IdentifierItems O a.groups))
    ⟨fun ⟨hu, hg⟩ => ⟨hu, hg⟩, fun h => ⟨h.users, h.groups⟩⟩

instance (O : Oracles) (p : String) : Decidable (CommandPathValue O p) :=
  decidable_of_iff (p.toList.head? = some '/' ∧ p.toList.getLast? ≠ some '/' ∧
    (∀ d ∈ p.toList, O.char.isWhitespace d = false) ∧
    (O.fs.canonicalize p = .err ∨ O.fs.canonicalize p = .ok p) ∧ O.glob.compile p = none)
    ⟨fun ⟨ha, hn, hw, hs, hg⟩ => ⟨ha, hn, hw, hs, hg⟩,
      fun h => ⟨h.absolute, h.notDir, h.oneWord, h.stable, h.glob⟩⟩

instance (O : Oracles) (a : Args) : Decidable (CommandArgsValue O a) :=
  decidable_of_iff ((∀ s ∈ argWords a, s.toList ≠ [] ∧ ∀ d ∈ s.toList, O.char.isWhitespace d = false) ∧
    Command.argPattern ((argWords a).map String.toList) = .ok a)
    ⟨fun ⟨hw, hs⟩ => ⟨hw, hs⟩, fun h => ⟨h.words, h.sentinel⟩⟩

instance (O : Oracles) (a : Command) : Decidable (CommandValue O a) := by
  letI := decidableBoolAll (fun b => LiteralLexeme (metaToken O.char (commandToken O))
    ((PermissionPrint.command a).toList ++ gap b))
  exact decidable_of_iff (CommandPathValue O a.pattern ∧ CommandArgsValue O a.args ∧
    ∀ b, LiteralLexeme (metaToken O.char (commandToken O)) ((PermissionPrint.command a).toList ++ gap b))
    ⟨fun ⟨hp, ha, hl⟩ => ⟨hp, ha, hl⟩, fun h => ⟨h.path, h.args, h.lexeme⟩⟩

instance (n : String) : Decidable (FreeCommandAlias n) := by unfold FreeCommandAlias; infer_instance

instance (O : Oracles) (a : Meta Command) : Decidable (CommandMemberValue O a) := by
  unfold CommandMemberValue
  cases a with
  | only c => exact inferInstanceAs (Decidable (CommandValue O c))
  | all => exact decidableBoolAll _
  | alias n =>
    letI := decidableBoolAll (fun b => LiteralValue (metaToken O.char (commandToken O))
      (n.toList ++ gap b) (.alias n))
    infer_instance

instance (m : Modifier) : Decidable (supportedModifier m) := by unfold supportedModifier; infer_instance

instance (O : Oracles) (a : CommandSpec) : Decidable (CommandSpecValue O a) :=
  decidable_of_iff (a.mods.length ≤ 127 ∧ (∀ m ∈ a.mods, supportedModifier m) ∧
    CommandMemberValue O a.cmd.who)
    ⟨fun ⟨hc, hs, ha⟩ => ⟨hc, hs, ha⟩, fun h => ⟨h.count, h.supported, h.command⟩⟩

instance (O : Oracles) (a : PermissionEntry) : Decidable (EntryValue O a) := by
  unfold EntryValue
  infer_instance

instance (O : Oracles) (a : PermissionGroup) : Decidable (GroupValue O a) :=
  inferInstanceAs (Decidable (HostItems O a.1 ∧ BoundedItems (EntryValue O) a.2))

instance (q : Spec UserSpecifier) : Decidable (OrdinaryKey q) := by
  unfold OrdinaryKey
  split <;> infer_instance

private def isNumericFirst : Spec UserSpecifier → Bool
  | .allow (.only (.user (.id _))) => true
  | _ => false

private theorem isNumericFirst_iff (q : Spec UserSpecifier) :
    isNumericFirst q = true ↔ ∃ n, q = .allow (.only (.user (.id n))) := by
  constructor
  · unfold isNumericFirst
    split
    · intro _; exact ⟨_, rfl⟩
    · simp
  · rintro ⟨_, rfl⟩; rfl

instance (q : Spec UserSpecifier) : Decidable (FirstUserValue q) := by
  letI := decidable_of_iff (isNumericFirst q = true) (isNumericFirst_iff q)
  unfold FirstUserValue
  infer_instance

instance (O : Oracles) (a : PermissionSpec) : Decidable (PermissionValue O a) :=
  decidable_of_iff (UserItems O a.users ∧ FirstUserValue (a.users.headD (.allow .all)) ∧
    BoundedItems (GroupValue O) a.permissions)
    ⟨fun ⟨hu, hf, hg⟩ => ⟨hu, hf, hg⟩, fun h => ⟨h.users, h.first, h.groups⟩⟩

/-- Check an AST against the structural value criterion for this snapshot. -/
def checkPermissionValue (O : Oracles) (a : PermissionSpec) : Bool := decide (PermissionValue O a)

theorem checkPermissionValue_iff (O : Oracles) (a : PermissionSpec) :
    checkPermissionValue O a = true ↔ PermissionValue O a := decide_eq_true_iff

/-- PT5 with the executable value check as its premise. -/
theorem sudo_permission_checked_roundTrip (O : Oracles) (D : Descriptions)
    (hO : PermissionLexical O.char) {a : PermissionSpec} (h : checkPermissionValue O a = true)
    (rest : List Char) (line col : Nat) :
    let c := (PermissionPrint.permissionSpec a).toList
    (sudo O D).run ⟨c ++ '\n' :: rest, line, col⟩ =
      (.ok (.spec a), ⟨'\n' :: rest, (posAfter c (line, col)).1, (posAfter c (line, col)).2⟩) :=
  sudo_permission_structural_roundTrip O D hO ((checkPermissionValue_iff O a).mp h) rest line col

end SudoersSpec.Grammar
