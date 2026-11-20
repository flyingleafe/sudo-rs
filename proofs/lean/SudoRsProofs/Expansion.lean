import SudoRsProofs.Permission
import SudoRsProofs.SanitizeTables
import SudoersSpec.Expansion

/-!
# `permission_flags` decides like the flattened policy

The extracted `permission_flags` works with the alias tables (`get_aliases` + `find_item`).
Combining `permission_flags_eq` with `SudoersSpec.authorize_expandAliases` (and its
`SetenvAdded` variant): if `analyze` ran `sanitize_alias_tables` without adding a diagnostic,
the Rust result equals `authorize` on the policy with every alias reference expanded and no
alias tables (`SudoersSpec.Policy.expandAliases`).

Which hypotheses of the spec theorem come from the sanitizer:
* `SudoersSpec.AliasTable.OK` (unique names, sorted processing order, per table) follows from
  `sanitize_alias_tables_sorted` (`absAliasTable_OK_of_sanitize`);
* `PolicyOK` follows from `AliasTableOK.of_sanitize_alias_tables` and the per-rule conditions,
  as for `permission_flags_eq`;
* `RunasUsersKept` is not among them: the sanitizer theorems are about the alias tables, not
  about the references in the rules, and a runas user list `(UNDEF)` naming only undefined
  aliases decides differently from the empty `()` it expands to
  (`expandAliases_runas_counterexample`). `SudoersSpec.Policy.runasUsersKept_of_defined` gives
  it when every alias named in a runas user list is defined and no `Runas_Alias` body is empty
  (`basic_parser.rs` `parse_list` requires at least one item);
* `CmndAliasesNoAll` is needed for equality only; without it the results are related by
  `SetenvAdded` (`expandAliases_setenv_counterexample`).
-/

open Aeneas Aeneas.Std Result
open Aeneas.Std.alloc.vec (Vec)
open sudo_rs sudo_rs.sudoers

namespace SudoRsProofs

/-- **The sanitizer establishes the table hypotheses.** After a `sanitize_alias_tables` that
added no diagnostic, every abstracted table is uniquely named and sorted. -/
theorem absAliasTable_OK_of_sanitize {t t' : AliasTable} {diags diags' : Vec sudoers.Error}
    (h : sanitize_alias_tables t diags = ok (t', diags'))
    (hclean : diags'.val.length = diags.val.length) (A : GlobAbs) :
    (absAliasTable A t').OK := by
  obtain ⟨hu, hh, hc, hr⟩ := sanitize_alias_tables_sorted h hclean
  exact ⟨⟨(hu _ absUserSpecifier).2.1, (hu _ absUserSpecifier).2.2⟩,
    ⟨(hh _ id).2.1, (hh _ id).2.2⟩,
    ⟨(hc _ (absCommand A)).2.1, (hc _ (absCommand A)).2.2⟩,
    ⟨(hr _ absUserSpecifier).2.1, (hr _ absUserSpecifier).2.2⟩⟩

variable {U G UG : Type} {uInst : sudo_rs.system.interface.UnixUser U UG}
  {eqInst : core.cmp.PartialEq U U} {gInst : sudo_rs.system.interface.UnixGroup G}
  {O : SudoersSpec.Oracle U G} {A : GlobAbs}

/-- **`permission_flags` against the flattened policy, up to the implicit `SETENV`.** The
alias tables are the output of a clean `sanitize_alias_tables` run on tables whose names fit
and whose items are matched purely (the hypotheses of `AliasTableOK.of_sanitize_alias_tables`),
the rules satisfy `RuleOK`, and expansion empties no runas user list. Then `permission_flags`
returns `ok r`, and `r` is the decision on the alias-free policy except that the latter may add
`SETENV` where the tag's `env` was implicit. -/
theorem permission_flags_expandAliases_rel (hO : InstOracle uInst eqInst gInst O)
    (hG : GlobOracle A O) (hH : O.SudoRsHosts) (rules : Slice sudo_rs.sudoers.ast.PermissionSpec)
    {t aliases : AliasTable} {diags diags' : Vec sudoers.Error}
    (hsan : sanitize_alias_tables t diags = ok (aliases, diags'))
    (hclean : diags'.val.length = diags.val.length)
    (userFits : TableFits t.user) (userGood : TableGood UserSpecFits t.user)
    (hostFits : TableFits t.host) (hostGood : TableGood Fits t.host)
    (cmndFits : TableFits t.cmnd)
    (runasFits : TableFits t.runas) (runasGood : TableGood UserSpecFits t.runas)
    (hrules : ∀ ps ∈ rules.val, RuleOK ps)
    (hkeep : (absPolicy A rules aliases).RunasUsersKept) (amUser : U)
    (onHost : sudo_rs.system.Hostname) (hhost : Fits onHost.inner)
    (request : sudo_rs.sudoers.Request U G UG) :
    ∃ r, sudo_rs.sudoers.permission_flags uInst eqInst gInst rules aliases amUser onHost request =
        ok r ∧
      Option.Rel SudoersSpec.SetenvAdded (r.map absTag)
        (SudoersSpec.authorize O (absPolicy A rules aliases).expandAliases
          (absRequest A amUser onHost request)) := by
  have hpol : PolicyOK rules aliases :=
    ⟨AliasTableOK.of_sanitize_alias_tables hsan userFits userGood hostFits hostGood cmndFits
      runasFits runasGood, hrules⟩
  obtain ⟨r, hr, heq⟩ := permission_flags_eq hO hG hH rules aliases hpol amUser onHost hhost request
  refine ⟨r, hr, ?_⟩
  rw [heq]
  exact SudoersSpec.authorize_expandAliases_rel O _ (absAliasTable_OK_of_sanitize hsan hclean A)
    hkeep _

/-- **`permission_flags` equals `authorize` on the flattened, alias-free policy** when, in
addition, no `Cmnd_Alias` body mentions `ALL`. -/
theorem permission_flags_expandAliases (hO : InstOracle uInst eqInst gInst O)
    (hG : GlobOracle A O) (hH : O.SudoRsHosts) (rules : Slice sudo_rs.sudoers.ast.PermissionSpec)
    {t aliases : AliasTable} {diags diags' : Vec sudoers.Error}
    (hsan : sanitize_alias_tables t diags = ok (aliases, diags'))
    (hclean : diags'.val.length = diags.val.length)
    (userFits : TableFits t.user) (userGood : TableGood UserSpecFits t.user)
    (hostFits : TableFits t.host) (hostGood : TableGood Fits t.host)
    (cmndFits : TableFits t.cmnd)
    (runasFits : TableFits t.runas) (runasGood : TableGood UserSpecFits t.runas)
    (hrules : ∀ ps ∈ rules.val, RuleOK ps)
    (hkeep : (absPolicy A rules aliases).RunasUsersKept)
    (hall : SudoersSpec.CmndAliasesNoAll (absTable (absCommand A) aliases.cmnd)) (amUser : U)
    (onHost : sudo_rs.system.Hostname) (hhost : Fits onHost.inner)
    (request : sudo_rs.sudoers.Request U G UG) :
    ∃ r, sudo_rs.sudoers.permission_flags uInst eqInst gInst rules aliases amUser onHost request =
        ok r ∧
      r.map absTag = SudoersSpec.authorize O (absPolicy A rules aliases).expandAliases
        (absRequest A amUser onHost request) := by
  have hpol : PolicyOK rules aliases :=
    ⟨AliasTableOK.of_sanitize_alias_tables hsan userFits userGood hostFits hostGood cmndFits
      runasFits runasGood, hrules⟩
  obtain ⟨r, hr, heq⟩ := permission_flags_eq hO hG hH rules aliases hpol amUser onHost hhost request
  refine ⟨r, hr, ?_⟩
  rw [heq]
  exact (SudoersSpec.authorize_expandAliases O _ (absAliasTable_OK_of_sanitize hsan hclean A)
    hkeep hall _).symm

end SudoRsProofs
