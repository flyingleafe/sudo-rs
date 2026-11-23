import SudoRsProofs.AbsPolicy
import SudoRsProofs.Defaults.Abs
import SudoersSpec.Analysis.Collect

/-! The parser's outer sums, using the same rule, command, Defaults and span views as the
refinement of the decision and the individual grammar productions. -/

open Aeneas.Std.alloc.vec (Vec)
open sudo_rs

namespace SudoRsProofs.Parser.Analysis

open SudoersSpec
open SudoersSpec.Analysis (NonCommandScope)

/-- The scope of a parsed `Defaults` directive, before command argument restrictions are added. -/
def absConfigScope (A : GlobAbs) : sudoers.ast.ConfigScope → Syntax.ConfigScope
  | .Generic => .generic
  | .Host xs => .host (absSpecList id xs.val)
  | .User xs => .user (absSpecList absUserSpecifier xs.val)
  | .RunAs xs => .runAs (absSpecList absUserSpecifier xs.val)
  | .Command xs => .command (absSpecList A.pat xs.val)

def absDirective (A : GlobAbs) : sudoers.ast.Directive → Syntax.Directive
  | .UserAlias ds => .userAlias (ds.val.map (absDef absUserSpecifier))
  | .HostAlias ds => .hostAlias (ds.val.map (absDef id))
  | .CmndAlias ds => .cmndAlias (ds.val.map (absDef (absCommand A)))
  | .RunasAlias ds => .runasAlias (ds.val.map (absDef absUserSpecifier))
  | .Defaults ms s => .defaults (ms.val.map Defaults.absModifier) (absConfigScope A s)

def absSudo (A : GlobAbs) : sudoers.ast.Sudo → Syntax.Sudo
  | .Spec rule => .spec (absPermissionSpec A rule)
  | .Decl d => .decl (absDirective A d)
  | .Include path span => .include path (absSpan span)
  | .IncludeDir path span => .includeDir path (absSpan span)
  | .LineComment => .lineComment

/-- A command scope cannot occur in the first pass for the output of collection. -/
def absNonCommandScope : sudoers.ast.ConfigScope → Option NonCommandScope
  | .Generic => some .generic
  | .Host xs => some (.host (absSpecList id xs.val))
  | .User xs => some (.user (absSpecList absUserSpecifier xs.val))
  | .RunAs xs => some (.runAs (absSpecList absUserSpecifier xs.val))
  | .Command _ => none

/-- The first pass, in collection order. `NonCommandOnly` rules out filtering any entry. -/
def absNonCommand
    (entries : Vec (sudoers.ast.ConfigScope × Vec defaults.SettingsModifier)) :
    List (NonCommandScope × List Settings.SettingsModifier) :=
  entries.val.filterMap fun (scope, mods) =>
    (absNonCommandScope scope).map fun s => (s, mods.val.map Defaults.absModifier)

/-- The second pass, in collection order. -/
def absCommandCustomisers (A : GlobAbs)
    (entries : Vec (Vec (RSpec RCommand) × Vec defaults.SettingsModifier)) :
    List (SpecList Command × List Settings.SettingsModifier) :=
  entries.val.map fun (scope, mods) =>
    (absSpecList (absCommand A) scope.val, mods.val.map Defaults.absModifier)

/-- Every entry of the first pass has a non-command scope. -/
def NonCommandOnly (entries : Vec (sudoers.ast.ConfigScope × Vec defaults.SettingsModifier)) : Prop :=
  ∀ entry ∈ entries.val, (absNonCommandScope entry.1).isSome

end SudoRsProofs.Parser.Analysis
