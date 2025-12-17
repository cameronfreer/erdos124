import Lake
open Lake DSL

package «erdos124» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`linter.unusedVariables, true⟩,
    ⟨`linter.unusedTactic, true⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "2df2f0150c275ad53cb3c90f7c98ec15a56a1a67"

@[default_target]
lean_lib «Erdos124» where
