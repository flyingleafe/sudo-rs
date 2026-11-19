import SudoRsProofs.GetAliases
import SudoRsProofs.SanitizeAliases
import SudoRsProofs.Permission
import SudoRsProofs.NonVacuity

/-!
# Axiom audit

Every main theorem may depend on `propext`, `Classical.choice`, `Quot.sound` only. The externals
of `SudoRs/{Types,Funs}External.lean` are definitions or `opaque` constants, never axioms (see
`proofs/lean/ASSUMPTIONS.md`).
-/

#print axioms SudoRsProofs.FoundAliases.get_spec
#print axioms SudoRsProofs.FoundAliases.insert_spec
#print axioms SudoRsProofs.FoundAliases.default_spec
#print axioms SudoRsProofs.item_verdict_spec
#print axioms SudoRsProofs.find_item_after_spec
#print axioms SudoRsProofs.find_item_spec
#print axioms SudoRsProofs.find_item_eq
#print axioms SudoRsProofs.get_aliases_spec
#print axioms SudoRsProofs.get_aliases_eq
#print axioms SudoRsProofs.sanitize_alias_table_tableWF
#print axioms SudoRsProofs.AliasTableOK.of_sanitize
#print axioms SudoRsProofs.Tag.clone_spec
#print axioms SudoRsProofs.Tag.default_spec
#print axioms SudoRsProofs.Modifier.apply_spec
#print axioms SudoRsProofs.apply_modifiers_spec
#print axioms SudoRsProofs.command_tag_spec
#print axioms SudoRsProofs.distribute_tags_spec
#print axioms SudoRsProofs.command_verdict_spec
#print axioms SudoRsProofs.check_commands_spec
#print axioms SudoRsProofs.checkRules_eq
#print axioms SudoRsProofs.perm_closure_call
#print axioms SudoRsProofs.check_permission_spec
#print axioms SudoRsProofs.check_permission_eq
#print axioms SudoRsProofs.permission_flags_spec
#print axioms SudoRsProofs.permission_flags_eq
#print axioms SudoRsProofs.NonVacuity.permits_member
#print axioms SudoRsProofs.NonVacuity.denies_excluded_member
#print axioms SudoRsProofs.NonVacuity.deny_only_not_refinement
