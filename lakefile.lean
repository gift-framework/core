import Lake
open Lake DSL

package «GIFT» where
  version := v"3.3.47"
  keywords := #["mathematics", "physics", "G2", "E8", "holonomy", "formal-verification"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.27.0"

require checkdecls from git
  "https://github.com/PatrickMassot/checkdecls.git" @ "master"

require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "v4.27.0"

@[default_target]
lean_lib «GIFT» where
  globs := #[.submodules `GIFT]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.unnecessarySimpa, false⟩
  ]

lean_lib «GIFTTest» where
  globs := #[.submodules `GIFTTest]
