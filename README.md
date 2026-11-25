# Lowering the complexity of strongly polynomial LP

Working notes. Starting point: *Strongly polynomial linear programming* (OpenAI preprint,
24 November 2026, [github.com/openai/math](https://github.com/openai/math/tree/main/preprints/Strongly-polynomial-linear-programming-November-24-2026)).
This repository is self-contained: it holds its own Lean development and none of the upstream
files (`scripts/fetch-upstream.sh` checks the preprint out under `src/` for reference).
Ground rule for this project: **an argument counts only if it is formalized in
Lean**. Everything under "Proved" is machine-checked; everything under "Not formalized" is
orientation only and should not be relied on.

## Proved (Lean, `formal/`)

The preprint's engine is its Theorem 2 ("Extremal prices"): a recursive market algorithm that
turns sign labels, reliable only at slots of maximum surplus, into prices meeting every demand
of every consistent hypothesis. Its cost is counted in *probes*: each probe makes one label
query and one market step (minimize a potential over an implicit pool of experts, then update
their wealth). `formal/` formalizes that algorithm with all numerical constants as parameters,
and proves two kinds of statements. The ones to read are in
[formal/SPLP/Summary.lean](formal/SPLP/Summary.lean).

### 1. Number of probes

All four algorithms below also round every updated wealth value down to 41 significant bits
(see section 2); the preprint keeps wealth exact.

| Theorem | Expert arity `k` | Probes per node `r` | Share `c` | Rate `η` | Label queries |
| --- | --- | --- | --- | --- | --- |
| preprint (`preprint_exponent`) | 4 | 2^19 + 1 = 524289 | 2^-14 | 1/16 | exponent between 59 and 60 |
| `price_search_k3` | 3 | 121100 | 2^-17 | 1/25 | `≤ 2 r₀ (2N)^66` |
| `price_search_k4_total` | 4 | 125800 | 2^-17 | 1/16 | `≤ 2 r₀ (2N)^46` |
| `price_search_k5_total` | 5 | 213700 | 2^-18 | 1/11 | `≤ 2 r₀ (2N)^39` |
| `price_search_k6_total` | 6 | 1352300 | 2^-22 | 1/27 | `≤ 2 r₀ (2N)^35` |

`N` is the number of coordinates and `r₀` the number of probes at the root, with
`r₀ ≤ 125801 + 10112 · log(1 + |E|)` for arity 4 (`K4_r₀_le`) and
`|E| = (2N)^k |V|^k (2DN|V| + 1)` the size of the expert pool (`card_expert`). For integer
demands in `[-R, R]` this is `O(N^46 log(NR))` against the preprint's `O(N^60 log(NR+1))`.

Each `*_total` theorem says: for every rule answering the label queries (it may depend on the
position of the probe in the recursion, hence on the whole past) a run of the algorithm
exists; and **every** run returns prices `x` with `val (a s) ≤ ± x_i` for every slot
`s = (i, ±)` of every hypothesis consistent with the labels it received, within the stated
number of queries.

The general statement is `Consts.price_search`
([formal/SPLP/Final.lean](formal/SPLP/Final.lean)): any rational constants satisfying
`Consts.Good` give a correct algorithm with at most `2 r₀ (2N)^e` queries whenever
`r² ≤ (ρ²/β)^e`. Checking a new set of constants is one `norm_num` call
([formal/SPLP/Instances.lean](formal/SPLP/Instances.lean)).

### 2. Cost of the market step

The pool of experts is exponentially large in the bit length of the demands, so the market
step can only be run on aggregates. The following is proved for every valid run from the root
(`probe_cost`, [formal/SPLP/Cost.lean](formal/SPLP/Cost.lean); the pieces are in
[Cells.lean](formal/SPLP/Cells.lean), [Arrangement.lean](formal/SPLP/Arrangement.lean),
[Bits.lean](formal/SPLP/Bits.lean), [Eval.lean](formal/SPLP/Eval.lean),
[VertexRun.lean](formal/SPLP/VertexRun.lean)). At every probe, with `t` probes completed
before it:

- **Cells.** For every test point `y'` of the market step, the experts fall into at most
  `(2N)^k (2ND+1) · faceBound(pairs k · (t+1), k)` cells such that all experts of a cell have
  the same wealth, the same maximizing options at `y'`, and the same gain at `y'` for every
  feedback. Here `pairs k = (k+1 choose 2)` and
  `faceBound n k = ∑_{i ≤ k} 2^i (n choose i) ≤ (2n+1)^k`.
- **Why that many.** Experts of one group (same slots and pivot) differ only by a point of
  `ℝ^k` (guessed demands relative to the pivot guess); each probe cuts `ℝ^k` by `pairs k`
  hyperplanes; `n` hyperplanes in `ℝ^k` have at most `faceBound n k` faces
  (`card_signVectors_le`, proved by deletion and restriction). The preprint only says the
  number of cells "remains polynomial"; the product of its interval partitions would give
  degree `(k+2 choose 2) = 15` in `t` for arity 4, against degree `k = 4` here.
- **A coarser partition suffices** (`Exec.wealth_agreeMax`): wealth depends only on which
  options were maximizing at each completed probe, not on the full order of the options. No
  better count is proved for this coarser partition.
- **Relative to a node** (`Exec.wealth_factor`, `Exec.cells_relative`,
  `Exec.potential_relative`, exact arithmetic only). At every probe below a node, wealth is
  the node's input wealth times a multiplier that is constant on the cells of the probes
  completed *inside that node*. So the potential is a sum of at most
  `(2N)^k (2ND+1) · faceBound(pairs k · (n+1), k)` terms, `n` the number of probes completed
  inside the node, each a multiplier times a sum over one cell of (input wealth × one affine
  function). This does not yet lower any cost: the input wealth still varies over the cells
  of all earlier probes, so each of those sums is as expensive as before. It also does not
  combine with rounding to significant bits, which is not compatible with factoring out an
  arbitrary input wealth.
- **One evaluation of the potential** (`Phi_eq_cellSum`): at a test point the potential equals
  the sum over cells of (wealth of the cell) × (sum of the cell's bids on its common best
  option − size of the cell × one price term). So an evaluation needs, per cell, its wealth,
  its size and one sum of bids.
- **Wealth can be rounded** (new relative to the preprint). The algorithm stays correct, with
  the same probe counts, if every updated wealth value is rounded down to `p + 1` significant
  bits (`Alg.rnd`; `p = 40` in the instances). Rounding only loses wealth, so total wealth
  still never grows, and the loss enters the analysis exactly like the investment share `c`.
  Then every wealth value is a float `m · 2^j` with `m < 2^41`, lies in `(0, |E|]`, and is at
  least `ρ₀^t · c^l` with `ρ₀ = (1 - 2^-40)(1 - c)(1 - η)` (`Exec.wealth_float`,
  `Exec.wealth_lower`). Its size is 41 bits plus an exponent of `O(log t)` bits. With exact
  arithmetic, as in the preprint, the denominators grow by about 21 bits per completed probe.
  Caveat (not formalized): the exponents `j` of two experts can differ by an amount
  proportional to `t` (one lost at every probe, the other won), so an *exact sum* of wealth
  over many cells, which an exact evaluation of the potential needs, can still have a number
  of bits proportional to `t`. Rounding shortens what is stored and updated, not yet the
  arithmetic of an exact market step. That needs markets cleared for approximate weights,
  which is not proved (see "Open directions").
- **Proposals** (`Consts.exists_vertex_run`, `exists_vertex_min`, `halfInt_of_vertex`,
  `bound_of_vertex`). The potential always has a minimizer that is a vertex (no direction
  preserves all ties between options). With integer demands in `[-R, R]`, every vertex is
  half-integral and bounded by `(l + 1) · 2R(N + 1)` at level `l`. So runs exist, against
  every labelling rule, in which each proposal coordinate is one of at most `8DR(N+1) + 1`
  half-integers, whatever the wealth.

Summing the cell bound over all probes of a run (`total_cells_k*`):

| Arity `k` | Cell bound summed over all probes |
| --- | --- |
| 3 | `2 r₀ (24 r₀ + 1)^3 (2ND+1) (2N)^267` |
| 4 | `2 r₀ (40 r₀ + 1)^4 (2ND+1) (2N)^234` |
| 5 | `2 r₀ (60 r₀ + 1)^5 (2ND+1) (2N)^239` |
| 6 | `2 r₀ (84 r₀ + 1)^6 (2ND+1) (2N)^251` |

`D` is the depth of the recursion (the least `D` with `(2N)² < (ρ²/β)^D`, logarithmic in `N`).

### Which arity

Arity 4. In the table above it has the smallest exponent of `N` and a smaller power of `r₀`
than arities 5 and 6, and arity 3 is worse than all of them. This compares proved upper
bounds, not true costs. With rounded wealth each cell stores numbers of logarithmic size, so
the table is, up to logarithmic factors, also the size of the stored state in bits. (With
exact wealth the stored state would carry one more factor of the number of probes, which
made arities 4 and 5 nearly tie.) This does not yet cover the arithmetic of an exact market
step; see the caveat under "Wealth can be rounded".

For comparison, the preprint's own probe count with the cell bound proved here would give an
exponent of about `59.02 · 5 + 4 ≈ 299`, and one more factor of the number of probes for its
exact wealth (not formalized, since the preprint's count is not).

### What changed relative to the preprint's analysis of the probe count

The algorithm is the preprint's (same experts, markets, feedback rule, investment recursion,
medians); only `r`, `c`, `η` and the depth differ. The savings come from the accounting:

- Reserve masses for future pivot levels are a free geometric sequence `ω₀ θ^i` instead of
  `2^{-i}`. The transfer constant becomes `max(ρ^k / ((δ-γ) ω₀), ρ^{k+1} / θ)` (1437 for
  arity 4) instead of `80 · (5/2)^4 = 3125`.
- Gains and losses are kept as exact logarithms, `ε = q log(1+η) + (1-q) log(1-η)` and
  `λ = -log(1-η)`, with `q = 1 - (1-γ)^k`, instead of `1/256` and `2η`.
- The bonus per failed probe `σ` is chosen so the "failed child pays for its feedback"
  inequality is tight, instead of `ε/4`; the bonus scale is `c/(1+η)` instead of `c/2`.
- Depth: `(2N)² < (ρ²/β)^D` with weak medians and no parity conditions.
- Boosting and pivot selection are done by level sets (no sorting, ties treated
  symmetrically): the valid pivots carry mass at least `δ - γ`.
- `β, δ, γ, η, c, ω₀, θ` re-optimized under the resulting constraints.

### Layout and build

```
formal/SPLP/Defs.lean         hypotheses, experts, runs (Exec.Valid, Exec.Consistent)
formal/SPLP/Market.lean       market lemma (no profit at a minimizer)
formal/SPLP/Median.lean       weak medians
formal/SPLP/Boost.lean        boost profile, pivot selection
formal/SPLP/Product.lean      product measures on tuples, hit probability
formal/SPLP/Bonus.lean        bonus inequality along the probes of a node
formal/SPLP/Experts.lean      utilities, payoffs, gains of experts
formal/SPLP/Weights.lean      weights of aligned experts, transfer lemmas
formal/SPLP/Invariant.lean    node invariant, leaf lemma, gain bounds
formal/SPLP/Main.lean         Params, charging induction, price_search_correct
formal/SPLP/Float.lean        rounding to a fixed number of significant bits
formal/SPLP/Consts.lean       rational constants -> Params (log bounds)
formal/SPLP/Count.lean        query count, least depth
formal/SPLP/Final.lean        Consts.price_search
formal/SPLP/Instances.lean    K3, K4, K5, K6
formal/SPLP/Total.lean        valid runs exist (market clears, medians exist)
formal/SPLP/Arrangement.lean  sign vectors of n affine forms in dimension k
formal/SPLP/Cells.lean        probes of a run, cells of experts, wealth constant on cells
formal/SPLP/CellsMax.lean     wealth depends only on the best options at past probes
formal/SPLP/Bits.lean         wealth values are floats of logarithmic size
formal/SPLP/Cost.lean         ProbeCost at every probe, totals
formal/SPLP/Vertex.lean       vertex minimizers of the potential exist
formal/SPLP/HalfInt.lean      vertices are half-integral and bounded
formal/SPLP/VertexRun.lean    runs with vertex proposals
formal/SPLP/Eval.lean         the potential as a sum over cells
formal/SPLP/Local.lean        wealth relative to a node's input wealth (exact arithmetic)
formal/SPLP/Summary.lean      the statements to read
```

About 6500 lines. No `sorry`; every headline theorem depends only on `propext`,
`Classical.choice`, `Quot.sound`.

Repository layout:

```
README.md                  results, scope, open directions
formal/                    the Lean project (library SPLP)
scripts/fetch-upstream.sh  sparse checkout of openai/math into src/ (pinned commit)
src/                       upstream reference checkout; not tracked, nothing depends on it
```

To build from a fresh clone (needs [elan](https://github.com/leanprover/elan); the first
command downloads prebuilt Mathlib instead of compiling it):

```bash
cd formal && lake exe cache get && lake build
```

Toolchain: Lean `v4.33.0-rc1` (`formal/lean-toolchain`), Mathlib `9e47bf70`
(`formal/lake-manifest.json`).

## Not covered by the formal results

- **No machine model.** Runs are mathematical objects over the reals and proposals are
  arbitrary minimizers of the potential. The cost statements bound what the market step has to
  handle (number of cells, size of the numbers), not the running time of an implementation.
  Missing between the two:
  - the number of potential evaluations one market step needs to find a vertex minimizer (it
    depends on the convex minimization method; the preprint uses the ellipsoid method). What
    is proved is that the target is a half-integral point of a bounded box;
  - the cost of the per-cell aggregates (how many experts a cell contains and the sum of
    their bids), which the preprint obtains by eliminating the guessed demands one at a time.
    What is proved is that these two numbers per cell, with the cell's wealth, suffice.
- **No end-to-end exponent for LP.** Calibration, compression and the reduction from LP are
  not formalized here, and `r₀` depends on `log R`, which they determine.
- The comparison figure for the preprint (59 to 60) is its own stated bound; only the
  arithmetic `(5/4)^59 < 2^19 + 1 < (5/4)^60` is checked.
- The upstream repository's Lean development (`lean/OAI/Optimization/LinearProgramming` in
  openai/math) formalizes
  a different variant with `2^600 + 1` probes per node (`PriceGame/Complexity.lean`,
  `trial_nodes_le`: `(2n)^602` nodes) and an existential exponent in the final theorem. It is
  untouched; nothing here is connected to its RAM-level statement.
- The arity comparison compares proved upper bounds. No lower bound on any cost is proved.

## Not formalized: where the running time comes from

Informal reading of the preprint, for orientation only.

- Probes: `T ≈ N^e · log R`, and `log R` is polynomial in `N` through calibration and
  compression (about `N^27` with the preprint's constants `D = (d+1)^6`, `H = 2^{100 N²}`;
  the upstream Lean development already has `(7N²+8) log₂(N+1)` restarts in place of
  `(d+1)^6`).
- Outside the price search: restarts of compression, `N` side decisions per recovered
  witness, and the primal-dual reduction multiply by low-degree polynomials.

## Open directions

On the number of cells, an independent search (and my own) found no variant of the scheme with
fewer cells. Not formalized: betting on the best of `k` slots with abstention, together with
exact conservation of total wealth under per-expert compounding, appears to force about `t^k`
distinct wealth values per group; any further gain would have to come from sharing work
between evaluations (range-sum structures over cells), for which there is no cost model here.
Unproved estimates from that search: with the node-relative form above, the number of
multipliers summed over all probes would have exponent about `46·4 + 4 = 188` for arity 4
instead of 234; and that correctness only needs a bound on the root's returned wealth, so the
market could be cleared for approximate weights.

1. Inside the present analysis the arity-4 probe exponent cannot go below about 45.5
   (numerical optimum of the constraints in `Consts.Good`). The three remaining
   multiplicative losses are the pivot band `1/(δ-γ)`, the tuple transfer `ρ^k`, and the
   loss-to-gain ratio `1 + λ/ε ≈ 1 + 1/(2q-1)`. Removing any one needs a change to the scheme.
2. The total cost is now roughly (probes)^(k+1): each probe exponent point costs five in the
   total for arity 4. A market step whose cost does not grow with the number of completed
   probes (fewer cells, or cells that can be merged or forgotten) would matter more than any
   further constant tuning.
3. Markets cleared for approximate weights (next concrete step, not yet proved). Claim: the
   price search stays correct if each proposal minimizes the potential for weights whose
   total distance from the true ones is at most `ζ` times the total wealth, for instance
   wealth rounded to a common grid. Total wealth would then grow by at most a factor
   `1 + ηζ` per probe, and only the condition at the root changes. This would give the market
   step short integer weights, where exact sums of float wealth are long (caveat under
   "Wealth can be rounded"), and let an approximate solver stand in for the exact minimizer.
4. Formalize the two missing pieces of the market step in an explicit cost model: the number
   of evaluations needed to reach a vertex minimizer, and counting the experts of a cell.
5. Tighten the constants feeding `log R` (`H`, `P`, `K`) with proofs.
6. The LP label oracle is stronger than the abstract one: labels are correct on every slot
   within a polynomial additive margin of the maximum surplus, not only at exact maximizers.
   The price theorem does not use this.
