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
import SudoRsProofs.Parser.Grammar
import SudoRsProofs.Parser.File
import SudoRsProofs.Parser.EndToEnd
import SudoRsProofs.Parser.NoDefaults
import SudoRsProofs.Defaults.Range
import SudoRsProofs.Defaults.Observations
import SudoRsProofs.Parser.Analysis.AliasOrder
import SudoRsProofs.Parser.Analysis.Collect
import SudoRsProofs.Parser.Analysis.Input
import SudoRsProofs.Parser.PermissionLines.Refinement
import SudoRsProofs.Parser.AliasName
import SudoRsProofs.Parser.Username
import SudoRsProofs.Parser.Digits
import SudoRsProofs.Parser.Parameters
import SudoRsProofs.Parser.Command
import SudoRsProofs.Parser.Scoping.Modifiers
import SudoRsProofs.Parser.Scoping.NonCommand
import SudoRsProofs.Parser.Scoping.Command
import SudoRsProofs.Parser.Analysis.Includes
import SudoRsProofs.Parser.Analysis.Provenance
import SudoRsProofs.Parser.DefaultsParse.Main
import SudoRsProofs.Parser.Scoping.Functions
import SudoRsProofs.Parser.Scoping.Clone
import SudoRsProofs.Parser.Scoping.Check
import SudoRsProofs.Parser.Directives.Main
import SudoRsProofs.Parser.Analysis.ReferenceFit
import SudoRsProofs.Parser.TextExample
import SudoRsProofs.Parser.Scoping.ListValidate
import SudoRsProofs.Request

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
#print axioms SudoRsProofs.Parser.host_list_grammar_iff
#print axioms SudoRsProofs.Parser.host_list_printed
#print axioms SudoRsProofs.Parser.parse_lines_recovery
#print axioms SudoRsProofs.Parser.parse_lines_refines_on
#print axioms SudoRsProofs.Parser.parseSudoersWith_of_refinement

#print axioms SudoRsProofs.Defaults.absDefaults_eq
#print axioms SudoRsProofs.Defaults.apply_eq
#print axioms SudoRsProofs.Defaults.set_eq
#print axioms SudoRsProofs.Defaults.negate_eq
#print axioms SudoRsProofs.Defaults.fromStrRadix_eq
#print axioms SudoRsProofs.Defaults.fractional_minutes_run_eq
#print axioms SudoRsProofs.Defaults.check_integer_eq
#print axioms SudoRsProofs.Defaults.check_text_eq
#print axioms SudoRsProofs.Defaults.build_list_eq
#print axioms SudoRsProofs.Defaults.default_eq
#print axioms SudoRsProofs.Defaults.initialModel_sets
#print axioms SudoRsProofs.Defaults.effective_authorization_of_initial
#print axioms SudoRsProofs.Defaults.reachable_inRange
#print axioms SudoRsProofs.Defaults.authorization_reachable_eq
#print axioms SudoRsProofs.sanitize_alias_table_exact
#print axioms SudoRsProofs.sanitize_alias_tables_exact
#print axioms SudoRsProofs.sanitize_alias_tables_exact_returns
#print axioms SudoRsProofs.sanitize_alias_table_exact_returns
#print axioms SudoRsProofs.Parser.Analysis.process_item_refines
#print axioms SudoRsProofs.Parser.Analysis.process_refines
#print axioms SudoRsProofs.Parser.Analysis.no_include_dispatch
#print axioms SudoRsProofs.Parser.Analysis.analyze_refines
#print axioms SudoRsProofs.Parser.Analysis.AnalysisResult.aliasesOK_of_clean
#print axioms SudoRsProofs.Parser.Analysis.itemSize_sum_eq_of_rel
#print axioms SudoRsProofs.Parser.Analysis.itemsFit_of_rel
#print axioms SudoRsProofs.Parser.Analysis.analyze_refines_of_reference
#print axioms SudoRsProofs.Parser.qualified_refines_on
#print axioms SudoRsProofs.Parser.vec_refines_on
#print axioms SudoRsProofs.Parser.quoteRoom_stable
#print axioms SudoRsProofs.Parser.identifier_refines
#print axioms SudoRsProofs.Parser.meta_identifier_refines
#print axioms SudoRsProofs.Parser.user_specifier_refines
#print axioms SudoRsProofs.Parser.meta_user_specifier_refines
#print axioms SudoRsProofs.Parser.spec_list_user_refines
#print axioms SudoRsProofs.Parser.run_as_refines
#print axioms SudoRsProofs.Parser.meta_or_tag_refines_release
#print axioms SudoRsProofs.Parser.command_tag_step_refines
#print axioms SudoRsProofs.Parser.command_spec_loop_eq
#print axioms SudoRsProofs.Parser.command_spec_refines_release
#print axioms SudoRsProofs.Parser.runas_command_refines
#print axioms SudoRsProofs.Parser.hosts_runas_commands_refines
#print axioms SudoRsProofs.Parser.user_list_refines
#print axioms SudoRsProofs.Parser.expect_user_list_refines
#print axioms SudoRsProofs.Parser.permissions_refines
#print axioms SudoRsProofs.Parser.user_list_refines_text
#print axioms SudoRsProofs.Parser.expect_user_list_refines_text
#print axioms SudoRsProofs.Parser.permissions_refines_text
#print axioms SudoRsProofs.Parser.alias_name_parse_refines
#print axioms SudoRsProofs.Parser.username_parse_refines
#print axioms SudoRsProofs.Parser.meta_username_parse_refines
#print axioms SudoRsProofs.Parser.digits_u32_construct_iff
#print axioms SudoRsProofs.Parser.digits_u32_parse_refines
#print axioms SudoRsProofs.Parser.string_parameter_token_refines
#print axioms SudoRsProofs.Parser.unquoted_token_refines
#print axioms SudoRsProofs.Parser.string_parameter_parse_refines
#print axioms SudoRsProofs.Parser.unquoted_parse_refines
#print axioms SudoRsProofs.Parser.unquoted_construct_size
#print axioms SudoRsProofs.Parser.chdir_parse_refines
#print axioms SudoRsProofs.Parser.split_words_refines
#print axioms SudoRsProofs.Parser.simple_command_token_refines
#print axioms SudoRsProofs.Parser.command_construct_refines
#print axioms SudoRsProofs.Parser.command_parse_refines_at
#print axioms SudoRsProofs.Parser.meta_command_parse_refines_at
#print axioms SudoRsProofs.Parser.Scoping.apply_settings_eq
#print axioms SudoRsProofs.Parser.Scoping.nonCommandModifiers_cons
#print axioms SudoRsProofs.Parser.Scoping.specify_host_user_runas_loop_eq
#print axioms SudoRsProofs.Parser.Scoping.absNonCommand_cons
#print axioms SudoRsProofs.Parser.Scoping.specify_command_loop_eq
#print axioms SudoRsProofs.Parser.Analysis.Includes.Walk.count_le
#print axioms SudoRsProofs.Parser.Analysis.Includes.process_refines
#print axioms SudoRsProofs.Parser.Analysis.Includes.analyze_refines
#print axioms SudoRsProofs.Parser.Analysis.settings_modifier_on_return
#print axioms SudoRsProofs.Parser.Analysis.vec_parse_on_return
#print axioms SudoRsProofs.Parser.Analysis.parse_lines_on_return
#print axioms SudoRsProofs.Parser.Analysis.parse_sudoers_produced
#print axioms SudoRsProofs.Parser.DefaultsParse.numeric_parse_refines
#print axioms SudoRsProofs.Parser.DefaultsParse.defaultName_parse_refines
#print axioms SudoRsProofs.Parser.DefaultsParse.envVar_parse_refines
#print axioms SudoRsProofs.Parser.DefaultsParse.quotedStringParameter_parse_refines
#print axioms SudoRsProofs.Parser.DefaultsParse.join_var_eq
#print axioms SudoRsProofs.Parser.DefaultsParse.parse_defaults_text_refines
#print axioms SudoRsProofs.Parser.DefaultsParse.parse_defaults_vars_refines
#print axioms SudoRsProofs.Parser.parse_defaults_list_refines
#print axioms SudoRsProofs.Parser.settingsModifier_parse_refines
#print axioms SudoRsProofs.Parser.settingsModifier_vec_refines
#print axioms SudoRsProofs.Parser.parsed_modifier_produced
#print axioms SudoRsProofs.Parser.Scoping.specify_host_user_runas_eq
#print axioms SudoRsProofs.Parser.Scoping.specify_command_eq
#print axioms SudoRsProofs.Parser.Scoping.settings_clone_eq
#print axioms SudoRsProofs.Parser.Scoping.check_eq
#print axioms SudoRsProofs.Parser.Scoping.check_authorization_eq
#print axioms SudoRsProofs.Parser.sudo_refines
#print axioms SudoRsProofs.Parser.parse_sudoers_refines
#print axioms SudoRsProofs.Parser.Analysis.Ref.permission_rule_fits
#print axioms SudoRsProofs.Parser.Analysis.Ref.sudo_grammar_item_fits
#print axioms SudoRsProofs.Parser.Analysis.Ref.parseSudoersWith_items_fit
#print axioms SudoRsProofs.Parser.Analysis.Ref.parseSudoers_items_fit
#print axioms SudoRsProofs.Parser.text_to_authorization
#print axioms SudoRsProofs.Parser.TextAgreement.clean_unique
#print axioms SudoRsProofs.Parser.TextAgreement.clean_expanded_flags
#print axioms SudoRsProofs.Parser.TextAgreement.no_defaults
#print axioms SudoRsProofs.Parser.TextExample.text_allows
#print axioms SudoRsProofs.Parser.TextExample.text_refuses
#print axioms SudoRsProofs.Parser.TextExample.textRun
#print axioms SudoRsProofs.Parser.TextExample.allowed_eval
#print axioms SudoRsProofs.Parser.TextExample.refused_eval
#print axioms SudoRsProofs.Parser.TextExample.domain_eval
#print axioms SudoRsProofs.Parser.Scoping.check_validate_permission_eq
#print axioms SudoRsProofs.Parser.Scoping.check_list_permission_self_eq
#print axioms SudoRsProofs.Parser.Scoping.check_list_permission_other_eq
#print axioms SudoRsProofs.Parser.Scoping.check_list_permission_eq
#print axioms SudoRsProofs.Parser.Scoping.search_path_then_check_list_permission_eq
#print axioms SudoRsProofs.Request.target_fallback_eq
#print axioms SudoRsProofs.Request.select_target_eq
#print axioms SudoRsProofs.Request.resolve_target_refines
#print axioms SudoRsProofs.Request.select_command_path_eq
#print axioms SudoRsProofs.Request.command_path_refines
#print axioms SudoRsProofs.Request.direct_command_refines
