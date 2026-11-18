/-!
# Abstract syntax of a parsed sudoers policy

Mirrors `src/sudoers/ast.rs` and `src/sudoers/tokens.rs` after parsing and after
`analyze` has collected the permission lines and alias definitions. Everything the
authorization decision does not look at (`Defaults`, include directives, spans of
diagnostics other than ignored tags) is left out.
-/

namespace SudoersSpec

/-- `tokens.rs` `Meta<T>`: the `ALL` wildcard, a direct item, or a reference to an alias. -/
inductive Meta (α : Type) where
  | all
  | only (x : α)
  | alias (name : String)
  deriving DecidableEq, Repr

/-- `ast.rs` `Qualified<T>`: an item preceded by an even (`allow`) or odd (`forbid`)
number of `!`; the parser already folds repeated negations. -/
inductive Qualified (α : Type) where
  | allow (x : α)
  | forbid (x : α)
  deriving DecidableEq, Repr

/-- `ast.rs` `Spec<T> = Qualified<Meta<T>>`. -/
abbrev Spec (α : Type) := Qualified (Meta α)

/-- `ast.rs` `SpecList<T>`. -/
abbrev SpecList (α : Type) := List (Spec α)

/-- The underlying `Meta` of a spec, ignoring the qualifier (Why3 `who`). -/
def Qualified.who : Qualified α → α
  | .allow x | .forbid x => x

/-- Flip the qualifier (`!` in front of an alias reference, Why3 `negated`). -/
def Qualified.negate : Qualified α → Qualified α
  | .allow x => .forbid x
  | .forbid x => .allow x

/-- `ast.rs` `Identifier`: a name or a `#number`. Ids are `u32` in Rust; the spec uses `Nat`. -/
inductive Identifier where
  | name (n : String)
  | id (n : Nat)
  deriving DecidableEq, Repr

/-- `ast.rs` `UserSpecifier`: `user`, `#uid`, `%group`, `%#gid`, `%:nonunix_group`. -/
inductive UserSpecifier where
  | user (i : Identifier)
  | group (i : Identifier)
  | nonunixGroup (i : Identifier)
  deriving DecidableEq, Repr

/-- `tokens.rs` `Args`: the argument pattern of a command. A bare command or a trailing `*`
gives `prefix`; explicit arguments or `""` give `exact`. -/
inductive Args where
  | prefix (args : List String)
  | exact (args : List String)
  deriving DecidableEq, Repr

/-- `tokens.rs` `Command = (SimpleCommand, Args)`; the path pattern is a glob kept as text,
its meaning is supplied by `Oracle.globMatches`. -/
structure Command where
  pattern : String
  args : Args
  deriving DecidableEq, Repr

/-- `tokens.rs` `Hostname`. -/
abbrev Hostname := String

/-- `ast.rs` `RunAs`: `(users : groups)`; either list may be empty. -/
structure RunAs where
  users : SpecList UserSpecifier
  groups : SpecList Identifier
  deriving DecidableEq, Repr

/-- `ast.rs` `Authenticate`. -/
inductive Authenticate where
  | none
  | passwd
  | nopasswd
  deriving DecidableEq, Repr

/-- `ast.rs` `EnvironmentControl`. -/
inductive EnvironmentControl where
  | implicit
  | setenv
  | nosetenv
  deriving DecidableEq, Repr

/-- `ast.rs` `ExecControl`. -/
inductive ExecControl where
  | implicit
  | exec
  | noexec
  deriving DecidableEq, Repr

/-- `tokens.rs` `ChDir`: `CWD=/path` or `CWD=*`. -/
inductive ChDir where
  | path (p : String)
  | any
  deriving DecidableEq, Repr

/-- `basic_parser.rs` `Span`, only carried around for tags that sudo-rs ignores. -/
structure Span where
  start : Nat × Nat
  stop : Nat × Nat
  deriving DecidableEq, Repr

/-- `ast.rs` `Tag`, the result of a successful authorization. The default value is
`Tag::default()`. There is no CHROOT field: `CHROOT=`, `INTERCEPT:`, `TIMEOUT=`,
`NOTBEFORE=`, `NOTAFTER=`, `ROLE=`, `TYPE=` are parse errors in sudo-rs. -/
structure Tag where
  authenticate : Authenticate := .none
  cwd : Option ChDir := none
  env : EnvironmentControl := .implicit
  apparmorProfile : Option String := none
  noexec : ExecControl := .implicit
  ignored : List Span := []
  deriving DecidableEq, Repr

/-- `ast.rs` `Tag::needs_passwd`. -/
def Tag.needsPasswd (t : Tag) : Bool :=
  match t.authenticate with
  | .none | .passwd => true
  | .nopasswd => false

/-- The tag modifiers of `ast.rs` `MetaOrTag::parse`. In Rust a `Modifier` is a boxed
closure `Fn(&mut Tag)`; here it is first-order data with `Modifier.apply` as its meaning. -/
inductive Modifier where
  | exec
  | noexec
  | setenv
  | nosetenv
  | passwd
  | nopasswd
  | cwd (d : ChDir)
  | apparmorProfile (p : String)
  /-- `LOG_INPUT`, `NOLOG_INPUT`, `LOG_OUTPUT`, `NOLOG_OUTPUT`, `MAIL`, `NOMAIL`, `FOLLOW`. -/
  | ignored (s : Span)
  /-- `NOFOLLOW`, `NOINTERCEPT`: accepted, no effect. -/
  | noop
  deriving DecidableEq, Repr

/-- The closure each `Modifier` stands for (`ast.rs` lines 354-399). -/
def Modifier.apply : Modifier → Tag → Tag
  | .exec, t => { t with noexec := .exec }
  | .noexec, t => { t with noexec := .noexec }
  | .setenv, t => { t with env := .setenv }
  | .nosetenv, t => { t with env := .nosetenv }
  | .passwd, t => { t with authenticate := .passwd }
  | .nopasswd, t => { t with authenticate := .nopasswd }
  | .cwd d, t => { t with cwd := some d }
  | .apparmorProfile p, t => { t with apparmorProfile := some p }
  | .ignored s, t => { t with ignored := t.ignored ++ [s] }
  | .noop, t => t

/-- `ast.rs` `CommandSpec(Vec<Modifier>, Spec<Command>)`: tags followed by a command. -/
structure CommandSpec where
  mods : List Modifier
  cmd : Spec Command
  deriving DecidableEq, Repr

/-- `ast.rs` `PermissionSpec`: one user specification line
`users  hosts = runas? cmdspec, ... : hosts = ...`. -/
structure PermissionSpec where
  users : SpecList UserSpecifier
  permissions : List (SpecList Hostname × List (Option RunAs × CommandSpec))
  deriving DecidableEq, Repr

/-- `ast.rs` `Def<T>`: `NAME = item, item, ...`. -/
structure Def (α : Type) where
  name : String
  items : SpecList α
  deriving DecidableEq, Repr

/-- `mod.rs` `AliasTable`. Each list is given in processing order, i.e. the iteration order
of the Rust `VecOrd` that `sanitize_alias_table` produced (dependencies first). -/
structure AliasTable where
  user : List (Def UserSpecifier) := []
  host : List (Def Hostname) := []
  cmnd : List (Def Command) := []
  runas : List (Def UserSpecifier) := []
  deriving DecidableEq, Repr

/-- The part of `mod.rs` `Sudoers` that the authorization decision reads. -/
structure Policy where
  rules : List PermissionSpec
  aliases : AliasTable := {}
  deriving DecidableEq, Repr

end SudoersSpec
