import SudoRsProofs.GetAliases
import SudoRsProofs.SanitizeTotal
import SudoRsProofs.Permission
import SudoRsProofs.ListValidate
import SudoRsProofs.NonVacuity
import SudoRsProofs.Authorization
import SudoRsProofs.Properties
import SudoRsProofs.Expansion
import SudoRsProofs.Escape
import SudoRsProofs.Parser.Examples

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
#print axioms SudoRsProofs.sanitize_alias_table_distinct
#print axioms SudoRsProofs.sanitize_alias_table_sorted
#print axioms SudoRsProofs.sanitize_alias_table_demonstration
#print axioms SudoRsProofs.sanitize_find_item_expanded
#print axioms SudoRsProofs.sanitize_alias_tables_ok
#print axioms SudoRsProofs.sanitize_alias_tables_tableWF
#print axioms SudoRsProofs.AliasTableOK.of_sanitize_alias_tables
#print axioms SudoRsProofs.sanitize_alias_tables_sorted
#print axioms SudoRsProofs.sanitize_alias_table_returns
#print axioms SudoRsProofs.sanitize_alias_tables_returns
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
#print axioms SudoRsProofs.selRules_eq
#print axioms SudoRsProofs.select_commands_spec
#print axioms SudoRsProofs.select_tag_spec
#print axioms SudoRsProofs.validate_flags_spec
#print axioms SudoRsProofs.validate_flags_eq
#print axioms SudoRsProofs.list_flags_self_spec
#print axioms SudoRsProofs.list_flags_spec
#print axioms SudoRsProofs.list_flags_eq
#print axioms SudoRsProofs.NonVacuity.validate_member
#print axioms SudoRsProofs.NonVacuity.validate_excluded
#print axioms SudoRsProofs.NonVacuity.list_self_member
#print axioms SudoRsProofs.to_auth_eq
#print axioms SudoRsProofs.authorization_eq
#print axioms SudoRsProofs.authorization_panics_of_passwd_tries
#print axioms SudoRsProofs.authorization_panics_of_umask
#print axioms SudoRsProofs.authorization_permission_flags_eq
#print axioms SudoRsProofs.authorization_permission_flags_props
#print axioms SudoRsProofs.permission_flags_some_authorize
#print axioms SudoRsProofs.permission_flags_none_authorize
#print axioms SudoRsProofs.permission_flags_eq_none
#print axioms SudoRsProofs.permission_flags_allow_witness
#print axioms SudoRsProofs.permission_flags_unmentioned_user
#print axioms SudoRsProofs.permission_flags_unmentioned_host
#print axioms SudoRsProofs.permission_flags_unmentioned_command
#print axioms SudoRsProofs.authorization_unmentioned_forbidden
#print axioms SudoRsProofs.permission_flags_unmentioned_runas_target
#print axioms SudoRsProofs.permission_flags_deny_needs_cmd_negation
#print axioms SudoRsProofs.permission_flags_myself_no_impersonation
#print axioms SudoRsProofs.permission_flags_runas_group_justified
#print axioms SudoRsProofs.permission_flags_nopasswd_needs_explicit_tag
#print axioms SudoRsProofs.permission_flags_last_line_decides
#print axioms SudoRsProofs.permission_flags_insert_other_user_irrelevant
#print axioms SudoRsProofs.permission_flags_add_positive_preserves_allow
#print axioms SudoRsProofs.absAliasTable_OK_of_sanitize
#print axioms SudoRsProofs.permission_flags_expandAliases_rel
#print axioms SudoRsProofs.permission_flags_expandAliases
#print axioms SudoRsProofs.Escape.is_unescaped_eq
#print axioms SudoRsProofs.Escape.escape_arg_into_loop_eq
#print axioms SudoRsProofs.Escape.escaped_loop_eq
#print axioms SudoRsProofs.Escape.escaped_eq
#print axioms SudoRsProofs.Escape.escaped_spec
#print axioms SudoRsProofs.Escape.escaped_overflow
#print axioms SudoRsProofs.Escape.escaped_ok_iff
#print axioms SudoRsProofs.Escape.escaped_ok_eq
#print axioms SudoRsProofs.Escape.escaped_flatMap
#print axioms SudoRsProofs.Escape.escaped_injective
#print axioms SudoRsProofs.Escape.escaped_collision
#print axioms SudoRsProofs.Escape.escaped_unescape
#print axioms SudoRsProofs.Parser.token_refines
#print axioms SudoRsProofs.Parser.parse_list_refines
#print axioms SudoRsProofs.Parser.vec_refines
#print axioms SudoRsProofs.Parser.qualified_refines
#print axioms SudoRsProofs.Parser.hostname_token_refines
#print axioms SudoRsProofs.Parser.meta_token_refines
#print axioms SudoRsProofs.Parser.hostname_description
#print axioms SudoRsProofs.Parser.spec_list_hostname_refines
#print axioms SudoRsProofs.Parser.host_list_refines
#print axioms SudoRsProofs.Parser.host_list_refines_text
#print axioms SudoRsProofs.Parser.parse_lines_refines
#print axioms SudoRsProofs.Parser.parse_lines_refines_text
#print axioms SudoRsProofs.Parser.parse_lines_no_reject_no_message
#print axioms SudoRsProofs.Parser.host_list_example
#print axioms SudoRsProofs.Parser.parse_lines_example
#print axioms SudoRsProofs.Parser.token_refines_at
#print axioms SudoRsProofs.Parser.skip_trailing_whitespace_ok_next
#print axioms SudoRsProofs.Parser.acceptEscaped_at_noBlankNext
#print axioms SudoRsProofs.Parser.parse_lines_syntax_example
