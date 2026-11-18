-- Hand-maintained models of external definitions used by the generated code.
-- Seeded from TypesExternal_Template.lean by proofs/extract.sh; never overwritten by it.
-- [sudo_rs]: external types.
module
public import Aeneas
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.internalConstructors false

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048

/-- [std::collections::hash::map::HashMap]
    Source: '/rustc/library/std/src/collections/hash/map.rs', lines 245:0-250:1
    Name pattern: [std::collections::hash::map::HashMap]
    Visibility: public -/
@[rust_type "std::collections::hash::map::HashMap"]
axiom std.collections.hash.map.HashMap (K : Type _) (V : Type _) (S : Type _)
  (A : Type _) : Type

/-- [std::hash::random::RandomState]
    Source: '/rustc/library/std/src/hash/random.rs', lines 35:0-35:22
    Name pattern: [std::hash::random::RandomState]
    Visibility: public -/
@[rust_type "std::hash::random::RandomState"]
axiom std.hash.random.RandomState : Type

/-- [std::hash::random::DefaultHasher]
    Source: '/rustc/library/std/src/hash/random.rs', lines 94:0-94:24
    Name pattern: [std::hash::random::DefaultHasher]
    Visibility: public -/
@[rust_type "std::hash::random::DefaultHasher"]
axiom std.hash.random.DefaultHasher : Type

