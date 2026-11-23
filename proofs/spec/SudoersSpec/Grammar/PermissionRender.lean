import SudoersSpec.Ast

/-! The canonical positive-fragment renderer shared by the grammar proofs and the
   differential harness. It is a renderer, not a serializer for arbitrary ASTs: it does
   not quote or escape names, and has no spelling for the unsupported modifiers. -/

namespace SudoersSpec.Grammar.PermissionPrint

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

def entry : Option RunAs × CommandSpec → String
  | (some r, a) => runas r ++ " " ++ commandSpec a
  | (none, a) => commandSpec a

def group (g : SpecList Hostname × List (Option RunAs × CommandSpec)) : String :=
  specList id g.1 ++ " = " ++ ", ".intercalate (g.2.map entry)

def permissionSpec (a : PermissionSpec) : String :=
  specList user a.users ++ " " ++ " : ".intercalate (a.permissions.map group)

/-- The lexical spelling alone does not distinguish the abstract name constructors. -/
theorem metaItem_not_injective (f : α → String) (a : α) :
    ∃ x y : Meta α, x ≠ y ∧ metaItem f x = metaItem f y := by
  refine ⟨.only a, .alias (f a), ?_, rfl⟩
  intro h; cases h

end SudoersSpec.Grammar.PermissionPrint
