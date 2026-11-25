import Lake
open Lake DSL

-- The SPLP library of this repository under upstream's toolchain and Mathlib revision.
package SPLPPort

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"

@[default_target] lean_lib SPLP

-- Upstream's own definition of the price-game query model (one file, unchanged).
lean_lib OAI

-- The bridge stated against upstream's definitions.
lean_lib SPLPUpstream
