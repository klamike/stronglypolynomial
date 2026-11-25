import Lake
open Lake DSL

-- Trimmed build of the upstream development (github.com/openai/math, lean/): only the
-- modules needed for the compression section, with the same toolchain and Mathlib revision.
package OAI where
  leanOptions := #[⟨`autoImplicit, false⟩]

require HexBareiss from git
  "https://github.com/leanprover/hex-bareiss.git" @ "fea7d537c14531b3a699530f5c7776f69f0ed9a9"

require HexLLLMathlib from git
  "https://github.com/leanprover/hex-lll-theory.git" @ "761108380d7bdae23181785d52703b4883388da1"

-- Declared last so that its pin wins, as in the upstream lakefile.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"

lean_lib OAI
