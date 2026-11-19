import SudoersSpec.Theorems
import SudoersSpec.ListValidate

/-! Axiom audit: every main result depends on at most `propext`, `Classical.choice` and
`Quot.sound`. `lake build` prints the lists. -/

open SudoersSpec

#print axioms findItem_eq_spec
#print axioms findItem_eq_some_iff
#print axioms findItem_eq_none_iff
#print axioms distributeTags_eq_spec
#print axioms checkPermission_eq_spec
#print axioms authorize_eq_spec
#print axioms getAliases_fixpoint
#print axioms demonstration
#print axioms checkPermission_eq_some_iff
#print axioms checkPermission_eq_none_iff
#print axioms default_deny
#print axioms default_deny_no_rules
#print axioms default_deny_no_applicable_line
#print axioms trailing_forbid_denies
#print axioms trailing_forbid_all_denies
#print axioms trailing_allow_grants
#print axioms authorize_nopasswd
#print axioms authorize_of_skipPasswd
#print axioms authorize_isSome_iff
#print axioms inapplicable_line_irrelevant
#print axioms allow_all_setenv
#print axioms maxByKey_eq
#print axioms entryTags_eq
#print axioms applicableEntries_eq_nil_iff
#print axioms validateFlags_eq
#print axioms validateFlags_eq_none_iff
#print axioms validateFlags_needsPasswd
#print axioms validateFlags_of_entry
#print axioms listFlags_other
#print axioms listFlags_other_of_not_root
#print axioms listFlags_other_root
#print axioms listFlags_self_eq_none_iff
#print axioms listFlags_self_needsPasswd
#print axioms listFlags_self_of_entry
