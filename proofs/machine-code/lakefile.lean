import Lake
open Lake DSL

/-!
Machine-code proof of one sudo-rs function against Google DeepMind's AArch64 semantics
(`arm64-semantics` v0.51.2, the copy inside `google-deepmind/code-verification` at commit
`b0f729ac`). The engine is fetched by Lake at that commit; nothing of it is vendored here.
-/

package «sudo-rs-machine-code» where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]
  weakLeanArgs := #["-M", "8192"]

require prooflib from git
  "https://github.com/google-deepmind/code-verification" @
    "b0f729accbc21a0413e7ca4e1da43fa45b5f2e1b" / "arm64-semantics" / "ProofLib"

@[default_target]
lean_lib SudoRsMachineCode where
  globs := #[.andSubmodules `SudoRsMachineCode]
