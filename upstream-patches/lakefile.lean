import Lake
open Lake DSL

-- Trimmed build of the upstream development (github.com/openai/math, lean/): only the
-- modules needed for the mathematical core of its compression section, with the same
-- toolchain (lean-toolchain: leanprover/lean4:v4.34.1) and the same Mathlib revision.
package OAI where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"

lean_lib OAI
