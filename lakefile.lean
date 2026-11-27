import Lake
open Lake DSL

package mathGenome where
  version := v!"0.29.0"
  fixedToolchain := true
  enableArtifactCache := false

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "56a005855ea17e0b0958f73ec801ae140b0a1679"

@[default_target]
lean_lib MathGenome where
  globs := #[`MathGenome.*]

lean_lib Examples where
  globs := #[`Examples.+]

lean_lib MathGenomeChecks where
  roots := #[`MathGenomeChecks.AllModules]
