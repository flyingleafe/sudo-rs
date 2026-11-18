import SudoRsProofs.GetAliases

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
