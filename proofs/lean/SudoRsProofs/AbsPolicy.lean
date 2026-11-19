import SudoRsProofs.AbsMatch
import SudoRsProofs.AbsTags

/-!
# Abstraction of a whole policy, and its well-formedness

`absPolicy A rules aliases` is the `SudoersSpec.Policy` of the Rust `rules: &[PermissionSpec]`
and `aliases: &AliasTable` that `check_permission` takes. `PolicyOK` collects the side
conditions every lemma below it needs: valid processing orders, names that fit in memory,
and modifier counts that fit in `usize`.
-/

open Aeneas Aeneas.Std Result

namespace SudoRsProofs

/-- A `Host_List = Cmnd_Spec_List` group of a rule. -/
abbrev RSeg := alloc.vec.Vec (RSpec sudo_rs.sudoers.tokens.Hostname) × alloc.vec.Vec REntry

def absSeg (A : GlobAbs) (seg : RSeg) :
    SudoersSpec.SpecList SudoersSpec.Hostname × List (Option SudoersSpec.RunAs × SudoersSpec.CommandSpec) :=
  (absSpecList id seg.1.val, absLine absRunAs (absCommand A) seg.2.val)

def absPermissionSpec (A : GlobAbs) (ps : sudo_rs.sudoers.ast.PermissionSpec) :
    SudoersSpec.PermissionSpec :=
  ⟨absSpecList absUserSpecifier ps.users.val, ps.permissions.val.map (absSeg A)⟩

def absAliasTable (A : GlobAbs) (t : sudo_rs.sudoers.AliasTable) : SudoersSpec.AliasTable where
  user := absTable absUserSpecifier t.user
  host := absTable id t.host
  cmnd := absTable (absCommand A) t.cmnd
  runas := absTable absUserSpecifier t.runas

def absPolicy (A : GlobAbs) (rules : Slice sudo_rs.sudoers.ast.PermissionSpec)
    (aliases : sudo_rs.sudoers.AliasTable) : SudoersSpec.Policy :=
  ⟨rules.val.map (absPermissionSpec A), absAliasTable A aliases⟩

/-! ## Side conditions -/

/-- A runas spec whose names fit in memory. -/
def RunAsOK (ra : sudo_rs.sudoers.ast.RunAs) : Prop :=
  ItemsFit ra.users.val ∧ ItemsGood UserSpecFits ra.users.val ∧
    ItemsFit ra.groups.val ∧ ItemsGood IdentFits ra.groups.val

/-- A command spec whose alias name (if any) fits in memory. -/
def CmdOK (cmd : RSpec RCommand) : Prop := ∀ n, aliasName cmd = some n → Fits n

/-- A `Cmnd_Spec_List`: few enough modifiers and names that fit. -/
def LineOK (l : List REntry) : Prop :=
  (lineMods l).length ≤ Usize.max ∧
    ∀ e ∈ l, (∀ r, e.1 = some r → RunAsOK r) ∧ CmdOK (csCmd e.2)

/-- A `Host_List = Cmnd_Spec_List` group. -/
def SegOK (seg : RSeg) : Prop :=
  ItemsFit seg.1.val ∧ ItemsGood Fits seg.1.val ∧ LineOK seg.2.val

/-- A user specification line. -/
def RuleOK (ps : sudo_rs.sudoers.ast.PermissionSpec) : Prop :=
  ItemsFit ps.users.val ∧ ItemsGood UserSpecFits ps.users.val ∧ ∀ seg ∈ ps.permissions.val, SegOK seg

/-- The alias tables: valid processing orders, names that fit. -/
def AliasTableOK (t : sudo_rs.sudoers.AliasTable) : Prop :=
  (TableWF t.user ∧ TableFits t.user ∧ TableGood UserSpecFits t.user) ∧
  (TableWF t.host ∧ TableFits t.host ∧ TableGood Fits t.host) ∧
  (TableWF t.cmnd ∧ TableFits t.cmnd) ∧
  (TableWF t.runas ∧ TableFits t.runas ∧ TableGood UserSpecFits t.runas)

/-- All side conditions on the policy. -/
def PolicyOK (rules : Slice sudo_rs.sudoers.ast.PermissionSpec) (aliases : sudo_rs.sudoers.AliasTable) :
    Prop :=
  AliasTableOK aliases ∧ ∀ ps ∈ rules.val, RuleOK ps

end SudoRsProofs
