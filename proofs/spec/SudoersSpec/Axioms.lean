import SudoersSpec.Theorems

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
