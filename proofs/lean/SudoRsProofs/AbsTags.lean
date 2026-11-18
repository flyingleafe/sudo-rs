import SudoRsProofs.Abs

/-!
# Abstraction functions for tags, modifiers and command specs

Rust `Tag`, `Modifier`, `Authenticate`, `EnvironmentControl`, `ExecControl`, `ChDir`, `Span`,
`CommandSpec` and the `(Option<RunAs>, CommandSpec)` entries of a `Cmnd_Spec_List`, abstracted
to the `SudoersSpec` types.

The spec's `Modifier` has no counterpart for the Rust values `Modifier::Authenticate(None)`,
`Modifier::Env(Implicit)` and `Modifier::Exec(Implicit)`; the parser never builds them
(`src/sudoers/ast.rs` `MetaOrTag::parse` only produces `PASSWD`/`NOPASSWD`, `SETENV`/`NOSETENV`,
`EXEC`/`NOEXEC`). `ModifierWF` excludes them.

The abstraction of runas specs and commands is a parameter (`fr`, `fc`): the tag layer never
looks inside them.
-/

open Aeneas Aeneas.Std Result

namespace SudoRsProofs

def absAuthenticate : sudo_rs.sudoers.ast.Authenticate → SudoersSpec.Authenticate
  | .None => .none
  | .Passwd => .passwd
  | .Nopasswd => .nopasswd

def absEnv : sudo_rs.sudoers.ast.EnvironmentControl → SudoersSpec.EnvironmentControl
  | .Implicit => .implicit
  | .Setenv => .setenv
  | .Nosetenv => .nosetenv

def absExec : sudo_rs.sudoers.ast.ExecControl → SudoersSpec.ExecControl
  | .Implicit => .implicit
  | .Exec => .exec
  | .Noexec => .noexec

/-- `ChDir::Path(SudoPath { inner })` is the path text. -/
def absChDir : sudo_rs.sudoers.tokens.ChDir → SudoersSpec.ChDir
  | .Path p => .path p.inner
  | .Any => .any

def absSpan (s : sudo_rs.sudoers.basic_parser.Span) : SudoersSpec.Span :=
  ⟨(s.start.1.val, s.start.2.val), (s.«end».1.val, s.«end».2.val)⟩

def absTag (t : sudo_rs.sudoers.ast.Tag) : SudoersSpec.Tag where
  authenticate := absAuthenticate t.authenticate
  cwd := t.cwd.map absChDir
  env := absEnv t.env
  apparmorProfile := t.apparmor_profile
  noexec := absExec t.noexec
  ignored := t.ignored.val.map absSpan

/-- Modifiers the parser can produce. -/
def ModifierWF : sudo_rs.sudoers.ast.Modifier → Prop
  | .Authenticate .None | .Env .Implicit | .Exec .Implicit => False
  | _ => True

/-- The values excluded by `ModifierWF` are sent to `noop`; no theorem relies on that. -/
def absModifier : sudo_rs.sudoers.ast.Modifier → SudoersSpec.Modifier
  | .Authenticate .Passwd => .passwd
  | .Authenticate .Nopasswd => .nopasswd
  | .Authenticate .None => .noop
  | .Env .Setenv => .setenv
  | .Env .Nosetenv => .nosetenv
  | .Env .Implicit => .noop
  | .Exec .Exec => .exec
  | .Exec .Noexec => .noexec
  | .Exec .Implicit => .noop
  | .Cwd d => .cwd (absChDir d)
  | .AppArmorProfile p => .apparmorProfile p
  | .Ignored s => .ignored (absSpan s)
  | .NoOp => .noop

/-- Rust `Command = (glob::Pattern, Args)`. -/
abbrev RCommand := glob.Pattern × sudo_rs.sudoers.tokens.Args

/-- One entry of a `Cmnd_Spec_List`: `(Option<RunAs>, CommandSpec)`. -/
abbrev REntry := Option sudo_rs.sudoers.ast.RunAs × sudo_rs.sudoers.ast.CommandSpec

/-- The modifiers of a Rust `CommandSpec(Vec<Modifier>, Spec<Command>)`. -/
def csMods (cs : sudo_rs.sudoers.ast.CommandSpec) : List sudo_rs.sudoers.ast.Modifier := cs.1.val

/-- The command of a Rust `CommandSpec`. -/
def csCmd (cs : sudo_rs.sudoers.ast.CommandSpec) : RSpec RCommand := cs.2

def absCommandSpec (fc : RCommand → SudoersSpec.Command) (cs : sudo_rs.sudoers.ast.CommandSpec) :
    SudoersSpec.CommandSpec :=
  ⟨(csMods cs).map absModifier, absSpec fc (csCmd cs)⟩

/-- A `Cmnd_Spec_List` (`Vec<(Option<RunAs>, CommandSpec)>`). -/
def absLine (fr : sudo_rs.sudoers.ast.RunAs → SudoersSpec.RunAs) (fc : RCommand → SudoersSpec.Command)
    (l : List REntry) : List (Option SudoersSpec.RunAs × SudoersSpec.CommandSpec) :=
  l.map fun e => (e.1.map fr, absCommandSpec fc e.2)

/-- Every modifier on the line is one the parser can produce. -/
def LineWF (l : List REntry) : Prop := ∀ e ∈ l, ∀ m ∈ csMods e.2, ModifierWF m

/-- All modifiers of a line, in order. -/
def lineMods (l : List REntry) : List sudo_rs.sudoers.ast.Modifier := l.flatMap fun e => csMods e.2

/-- The runas spec a position returned by `distribute_tags` refers to. -/
def resolveRunas (fr : sudo_rs.sudoers.ast.RunAs → SudoersSpec.RunAs) (l : List REntry)
    (p : Option Usize) : Option SudoersSpec.RunAs :=
  (p.bind fun j => (l[j.val]?).bind (·.1)).map fr

/-- An entry of the Rust `distribute_tags` result, read against its line entry `e`. -/
def resolveEntry (fr : sudo_rs.sudoers.ast.RunAs → SudoersSpec.RunAs)
    (fc : RCommand → SudoersSpec.Command) (l : List REntry) (e : REntry)
    (x : Option Usize × sudo_rs.sudoers.ast.Tag) : SudoersSpec.MatchedCommand :=
  (resolveRunas fr l x.1, (absTag x.2, absSpec fc (csCmd e.2)))

end SudoRsProofs
