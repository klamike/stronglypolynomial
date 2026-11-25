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
and proves seven kinds of statements. The ones to read are in
[formal/SPLP/Summary.lean](formal/SPLP/Summary.lean) and, for results 4 to 7, in
[formal/SPLP/Margin.lean](formal/SPLP/Margin.lean),
[formal/SPLP/LabelTest.lean](formal/SPLP/LabelTest.lean),
[formal/SPLP/Dissociated.lean](formal/SPLP/Dissociated.lean) and
[formal/SPLP/PairTest.lean](formal/SPLP/PairTest.lean).

### 1. Number of probes

All four algorithms below also round every updated wealth value down to 41 significant bits
(see section 2); the preprint keeps wealth exact. This is a deliberate change, not a
restriction: the theorems below are proved for the rounded algorithms, with the loss of at
most a factor `1 - 2^-40` per update absorbed by the constants. The general correctness
theorem (`price_search_correct`) takes the rounding as a parameter and admits the identity
(exact wealth); the four instances below fix it to 41 bits. The rounding is there because
exact wealth values grow by about 21 bits per completed probe.

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
  which is the next item.
- **Markets may be cleared approximately** (`price_search_k4_approx_total`,
  `price_search_correct_approx`, `Exec.wealth_approx`, in
  [formal/SPLP/Approx.lean](formal/SPLP/Approx.lean)). A proposal may minimize the potential
  for any nonnegative weights `w'` with `∑ |w' - w| ≤ ζ · ∑ w`, where `w` is the true wealth
  (`approxMarket`). Then the aggregate gain at the proposal is at most `ζ` times the total
  wealth (`approx_gain_le`), total wealth grows by at most a factor `1 + ηζ` per probe, and
  only the condition at the root changes. For arity 4, with the root making `2 r₀` probes
  and `ζ ≥ 2^-12 / (2N)^46` (depending only on `N`, not on the range or the pool), every
  such run meets all demands and makes at most `4 r₀ (2N)^46` label queries; wealth is still
  rounded to 41 bits. `ζ = 0` is the exact case.
  The tolerance can in fact be a constant (`price_search_k4_approx_const_total`,
  `Exec.wealth_approx_level`, `growthAt_zero_le_exp`, in
  [formal/SPLP/ApproxLevel.lean](formal/SPLP/ApproxLevel.lean)): a child node receives only
  the invested share `c` of the wealth and its output is added back, so the growth factor of
  a node of height `h + 1` is `((1 - c)(1 + ηζ) + c · G_h)^r`, and for arity 4,
  `c · r ≈ 0.96 < 1` makes this recursion close. With the same `2 r₀` root probes and the
  same bound `4 r₀ (2N)^46` on label queries, `ζ = 2^-25` suffices, independent of `N`, of
  the range and of the pool. So the weights entering a market step need only a constant
  relative accuracy in total, for instance a common grid of relative mesh
  `2^-25 / (number of cells)`. Not formalized: a procedure producing such weights (the theorem
  takes any `w'` within the tolerance), and the cell, bit-size and vertex-proposal results
  are still stated for exactly cleared markets only.
- **Only the aggregate gain matters** (`price_search_k4_gain_const`, `approxMarket_gain`,
  `gainMarket_of_selection`, in [formal/SPLP/GainMarket.lean](formal/SPLP/GainMarket.lean)).
  The proof uses a proposal `y` only through one property: for every feedback `v`, the
  aggregate gain `∑ w_e · gain(y, v, e)` is at most `ζ` times the total wealth
  (`gainMarket`). Any run whose proposals have this property with `ζ = 2^-25` meets all
  demands within the same query bound; no potential has to be minimized, exactly or
  approximately, and approximately cleared markets are a special case. The property is
  certified by `N` numbers: if each expert's weight is split among its best options at `y`
  and the resulting signed slot masses satisfy `∑_i |m_i| ≤ ζ · (total wealth)`, the proposal
  is admissible. Without ties `m_i` is the wealth betting on slot `(i, +)` minus the wealth
  betting on `(i, -)`.
- **The maximum cannot be factored** (`argmax_factor_const`, in
  [formal/SPLP/ArgmaxFactor.lean](formal/SPLP/ArgmaxFactor.lean)). The factor applied to an
  expert at a probe depends on which of its options is best. A nonvanishing function of the
  index of the maximum of three values that is a product of functions of the three pairwise
  comparisons is constant. So the wealth measure is not a pairwise product model, and
  dynamic programming along the comparisons (which would cost `t²` instead of `t^k`) is not
  available; computing the maximum by a chain or a tournament does not change this.
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

### 3. The problem is easy in the range of the demands (new)

Not in the preprint: two elementary algorithms with no experts and no markets
([formal/SPLP/Descent.lean](formal/SPLP/Descent.lean)).

- **Exact labels, `2R` queries** (`lockstep_2R`, `lockstep_meets_demands`). In the model of
  the preprint's price theorem (integer demands in `[-R, R]`, labels correct only at slots of
  maximum surplus): start at the origin and move *every* price by `1/2` in the direction of
  its label. After `2R` queries, and at every later step, the prices meet every demand of
  every consistent hypothesis. Reason: all prices move in lockstep, so all surpluses stay in
  one residue class modulo 1; a slot that is not maximal is a full unit below the maximum and
  cannot overtake it, so the maximum surplus drops by `1/2` per query while it is nonnegative.
- **Labels with a margin, `n₁ + e₁ - 1` queries** (`descent_meets_demands`,
  `descent_step_decrease`). If labels are correct at every slot within an additive margin
  `G` of the maximum surplus (`Hyp.ConsistentAtMargin`; `G = 0` is the preprint's notion,
  `Hyp.consistentAtMargin_zero`), steps of size `e₁ ≤ G/2` lower the maximum by `e₁` per
  query: `n₁ ≥ B₀/e₁` coarse steps and `e₁ - 1` unit steps suffice, where `B₀` bounds the
  initial surplus.

What this says about the complexity: the price problem is trivial when cost may be linear
in `R`. Everything the recursive market buys, including all the exponents above, is the
replacement of `R` by `log R`. For linear programming that is the difference between a
bound depending on the size of the numbers and a strongly polynomial one, so these
algorithms do not replace the market in general (after compression `R` is exponential in
`N`). They do replace it whenever `R` is polynomially bounded: `2R` trivial queries against
`2 r₀ (2N)^46` queries with a market step each.

### 4. Why the range cannot simply be reduced by rounding (new)

Range reduction would be the largest saving available: for a bounded range the number of
cells is at most the size of the pool, whatever the number of probes. The statements below
([formal/SPLP/Margin.lean](formal/SPLP/Margin.lean)) are the tools for it, and the exact
point at which it fails.

- **A margin allows rounded demands** (`consistentAt_of_margin_of_round`,
  `surplus_le_of_round_meets`). If labels are correct on every slot within `G` of the
  maximum surplus, they are exact labels for the hypothesis with demands rounded down by up
  to `G`, at every point. Meeting the rounded demands leaves every true surplus at most `G`.
- **Exact labels give a margin, at linear cost** (`lockstep_feedback_margin`). After `n`
  lockstep queries from an integral point `y`, the feedback at `y` is correct on every slot
  within `n/2` of the maximum surplus at `y`.
- **A margin costs no more than a price search of that range**
  (`Hyp.localize_consistentAt`, `Hyp.localize_range`, `Hyp.localize_meets`,
  `feedback_margin_of_localized`). Lower all demands by `τ ≥ 0` and truncate them to the cube
  of radius `r` around `y`. If the surpluses at `y` are below `τ + r`, the result is a
  hypothesis with demands within `r` of `y`, consistent with the original labels after an
  explicit override outside the cube. Any point meeting it yields feedback at `y` that is
  correct on every slot of surplus at least `τ`.
- **With exact labels, rounding is impossible** (`RoundingExample.oracle_consistent`,
  `RoundingExample.no_common_label`). There are two hypotheses on two coordinates and one
  label rule on the integer points, consistent with both, whose demands rounded down to
  integers require opposite labels at the origin. So no procedure that turns labels observed
  at grid points into labels for the rounded hypothesis is right for both.

What this says: a rounded problem needs labels with a margin as large as the rounding, and a
margin `G` costs either `2G` exact queries or one price search of range `G`. Scaling
therefore multiplies the query count by the cost of a full price search at every level, and
does not give `log R` cheap phases. The cause is that all slots in one rounded level look
alike at grid points, while an exact label is guaranteed only for the single largest one.

### 5. The label test has a margin governed by its tolerance (new, first step outside Theorem 2)

In the preprint a label comes from a feasibility test at the queried prices: give `i` the
label `+` if the scaled space has a vector with all entries at least `-ε` and `i`th entry at
least `θ` (its Section 3, with `θ = 1/4`). [formal/SPLP/LabelTest.lean](formal/SPLP/LabelTest.lean)
proves, for the test on the true scaled space:

- `falsePositive_bound`, `falsePositive_bound_max`: if the test passes at `i`, every
  nonnegative vector `u` of the orthogonal complement has scaled entry at `i` at most
  `(N - 1) ε / θ` times its largest scaled entry. A wrong `+` therefore needs the true
  witness to be invisible at `i` by that factor.
- `exact_test_sound`: with `ε = 0` the test is never wrong.

So the labels of the reduction are not merely correct at exact maxima. On the true scaled
space they are correct within a margin of about `log₂ (θ / (N ε))` in the units of the
demands, and that margin grows linearly with the bits of precision spent on the test. Not
formalized: the preprint runs the test on a calibrated approximation and with compressed
demands (its Sections 4 and 5), and I have not checked that a margin survives those steps.
By result 4 a margin `G` allows demands rounded by `G`, which divides the range by `G` and
so changes `log R` only by `log G`; by result 3 it allows descent steps of `G/2`. Neither
lowers the exponent of the price search.

### 6. The compression constant: `d² log d` instead of `(d+1)^6` (new, the preprint's Section 5)

The range `R` of the demands is not a property of the linear program. It is the size of the
short substitutes that the preprint's Section 5 computes for the logarithms of the minors
(Frank–Tardos rounding, on demand). That section fixes one constant, `D = (d+1)^6`, as a bound
on the size of a *dissociated* set of minors: one whose log-magnitudes have subset sums
pairwise far apart (its Lemma 5.1). `D` bounds the number of restarts of the price search and
enters every parameter that determines `R`.

[formal/SPLP/Dissociated.lean](formal/SPLP/Dissociated.lean) formalizes the counting argument
of Lemma 5.1 and shows that a much smaller constant suffices.

- `dissociated_count`: for a dissociated family of `D` integer polynomials in `n` variables,
  with individual degrees at most `δ` and coefficient 1-norms at most `L`, evaluated at any
  real point, `2^(2^D) ≤ (2 · 2^D · L^D + 1)^((δ D + 1)^n)`. The proof is the preprint's:
  subset products have magnitudes that more than double in sorted order, so all `2^(2^D)`
  subset sums of subset products are distinct values (`subsetSum_injective_of_sep`), hence
  distinct polynomials, and there are few polynomials of that shape
  (`card_le_of_degreeOf_norm1`).
- `minors_dissociated_card_lt`: every dissociated family of nonzero minors of a real matrix
  with at most `d` rows and `d` columns has fewer than `Dnew d = 12 d² ⌈log₂ (d+1)⌉` members.
  Minors are polynomials with individual degrees at most one and 1-norm at most `d!`
  (`Minors.lean`). `minors_proxy_dissociated_card_lt` is the same statement in the preprint's
  form, with proxies within `η` of the logarithms and tolerance two.
- `Dnew_lt_paper`: `Dnew d < (d+1)^6` for every `d ≥ 1`.

What is and is not new here. The last line of the preprint's own proof already yields
`(7d²+8) log₂ (d+1)`, and the upstream Lean development proves that bound for the number of
restarts (from the counting inequality as a hypothesis). Both nevertheless keep `(d+1)^6` as
the constant in the parameters of Section 5 (upstream: `paperWidth N = (N+1)^6`). The point
made here is that the constant itself can be replaced.

What the constant is worth. [formal/SPLP/RangeBound.lean](formal/SPLP/RangeBound.lean)
transcribes the preprint's formulas for the bound `F` on the substitutes (Lemmas 5.2 and 5.3
and Section 5.4; the range is `R = 4F`) as a function `cF D K` of the constant `D` and the
precision parameter `K`, and proves `D⁴ K ≤ log₂ (cF D K) ≤ 64 D⁴ (K + ⌈log₂ D⌉ + 3)`
(`le_cF`, `cF_le`). So `log R` is of order `D⁴ K`: at least `(d+1)^24 K` with the preprint's
constant (`cF_paper_ge`) and at most `64 (Dnew d)⁴ (K + ⌈log₂ (Dnew d)⌉ + 3)` with the new one
(`cF_new_le`). The price search runs on a row basis with `d = 2N` columns, and `K` is about
`10⁴ N³` with the preprint's precision, so `log R` goes from order `N^27` to order
`N^11 log⁴ N`, and the bound on restarts from `(2N+1)^6` to `48 N² ⌈log₂ (2N+1)⌉`. Both
multiply the number of label queries of a side decision: about `N^16 / log⁴ N` fewer from
`log R`, on top of the restart bound that upstream already has.

Not formalized, and the reason the last paragraph is an estimate and not a theorem about the
algorithm:

- That the rest of Section 5 goes through with the smaller constant. On my reading it does,
  because `D` is used there only as a bound on the size of dissociated sets (`|I| < D` in
  Lemma 5.2, `m < D` in Sections 5.4 and 5.5) and in the definition of the grid `η`.
- That `cF` is the bound the algorithm needs. It is a transcription of the formulas in the
  text with the largest admissible parameters, not derived from a formalization of
  Lemmas 5.2 to 5.4.
- The value of `K` and the count of queries per side decision.

Checked by the compiler in upstream's own development. With the width `(N+1)^6` replaced by
the polynomial `(7N²+8)·N + 1`, the mathematical core of upstream's compression section
builds: its theorem `minor_transcript_guarantees` (restart bound, and a common rational
assignment for all nonzero minors with numerators and denominators below
`2^(onlineMinorBitPolynomial.eval N)`) holds unchanged in form, with standard axioms only,
and the polynomial in the exponent drops from degree 48 to degree 24 in `N` (for `N = 16`,
from about `2^202` bits to about `2^129`). The change is three files and 52 lines of diff:
[upstream-patches/core-width.patch](upstream-patches/core-width.patch), reproducible with
[upstream-patches/build-core.sh](upstream-patches/build-core.sh) (Lean 4.34.1 and upstream's
Mathlib revision; the unchanged core is built first as a control). The core is the 54
modules that `MinorAssignments`, `AdaptiveRequests`, `BitBudget` and `Offline` import, and
needs only Mathlib. Not yet covered: the layers above the core (the machine-model
implementation and its cost accounting, 769 modules in all), which use the old closed form
in about 25 places.

How the upstream Lean development handles this constant (from reading its sources; apart
from the core just described, nothing in this paragraph is checked by a compiler). Its `paperWidth N =
(N+1)^6` occurs 88 times in 31 files of `Compression/`. The mathematical core is generic in a
`width` with hypotheses of the form `I.card ≤ width` (`epoch_realization`,
`epoch_commit_extends_accepted`, `exists_offline_assignment_of_dissociated_bound`); no step
was found that needs the width to be large. Its final bound is cruder than the text's:
`log₂ F` is about `8 w⁷ (10 w + 12 B)` with `w` the width and `B = 100 (N+1)³`, so about
`80 (N+1)^48` as it stands. With `w` of order `N² log N` that would be of order
`N^17 log⁷ N`. Replacing the width in the mathematics looks like a local change (definitions
and about 25 short arithmetic repairs). Lowering the stated bound all the way is not local
there, because the bit budget is evaluated on the machine model as a polynomial in `N` and a
logarithm is not one; a polynomial width of order `N³`, which `log_bound_lt_cutoff` already
supports, keeps everything polynomial and would give order `N^24`.

### 7. The precision constants `H`, `P`, `K` can be much smaller (new)

`log R` is of order `D⁴ K` (result 6), and `K ≈ (N+1) P` where `P ≈ 10⁴ N²` is the precision
of calibration, fixed in the preprint by `H = 2^(100 N²)`, `ε = H^-10`, `2^-P = H^-100`.
[formal/SPLP/PairTest.lean](formal/SPLP/PairTest.lean) proves the preprint's Lemma 3.1
(opposing slots cannot both pass the label test) with explicit constants: for a convex set of
vectors with entries in `[-ε, 2]` and `Q ≤ q`, at most one slot of each coordinate reaches `θ`
provided `q < ((θ - ε)/2)² - 2ε(N - 1)` (`opposing_slots`); for `θ = 1/4` it is enough that
`ε ≤ 1/(400 N)` and `Q ≤ 1/100` (`opposing_slots_quarter`). So this lemma needs a tolerance
of order `1/N`, not `2^(-1000 N²)`.

[formal/SPLP/DiffConstraints.lean](formal/SPLP/DiffConstraints.lean) proves the fact that
would remove a factor `N` from `K`. A system of difference constraints `p_i - p_j ≤ w_ij` is
feasible exactly when no closed walk with at most `n` vertices has negative weight
(`diff_feasible_iff`, `n` the number of unknowns). Hence, if the weights are integer affine
forms of 1-norm at most `A` in some data, feasibility at data `g` passes to any data `f` on
which every form of norm at most `n · A` that is nonnegative at `g` is nonnegative
(`diff_feasible_of_type`). The preprint's Lemma 4.1, for a general system, needs agreement up
to norm `(n+1) A^(n+1)`.

[formal/SPLP/BlockMinors.lean](formal/SPLP/BlockMinors.lean) proves that this is the
situation of the LP reduction. The preprint's inequalities (its Section 4.3) compare two
slots `s = (i, h)`, `t = (i', h')` on the support of one cofactor vector
`c_s = det B0[rows, (T, s)]`, through `h p_i - h' p_i'` with weak inequalities; they are
difference constraints when `h = h'`. For a basis of `C × C⊥` that vanishes off its two
diagonal blocks, a square minor is zero unless it uses as many positive columns as rows of
`C` (`det_eq_zero_of_block_card`), so a cofactor vector cannot be nonzero at a positive and
at a negative slot (`block_minors_one_sided`): `h = h'` always.

[formal/SPLP/Precision.lean](formal/SPLP/Precision.lean) does the same for the precision
`P`, following the preprint's own proof of Theorem 3, which derives a coefficient bound
`3^(j-1)` and then relaxes it to `2^(100 N²)`.

- `coeff_bound`: for rows with pivot entries of magnitude one, zeros at earlier pivots and
  entries at most two (the form calibration produces), a combination of sup norm at most one
  has `j`th coefficient at most `3^j`, rows counted from zero. So `H = 3^(r-1)` serves for
  `r` rows.
- `label_test_sound`: let `B` be within `η` entrywise of rows `B*` on whose span `Q`
  vanishes, and let `δ = r H η`. If `δ ≤ ε ≤ 1/(400 N)` and `δ ≤ 1/(500 N)`, then opposing
  slots never both pass the test at threshold `1/4`, and every combination of `B*` with
  coefficients at most `H`, entries in `[0, 1]` and an entry at least `1/3` makes the test
  pass at that slot. These are the two facts the preprint's "Deciding all coordinates" uses.

So `2^-P` of order `1/(N r H)` with `H = 3^(r-1)` is enough for the label test: `P` about
`1.6 r + 2 log₂ N + 9`, linear in `N`, against `10⁴ N²`.

Not formalized (the first item is my reading of Section 4.3; the others are readings of
Section 4 by an agent, checked by me only in outline):

- That the system of Section 4.3 is exactly the set of two-slot comparisons described above,
  for a block-diagonal basis. Given that, `2^K ≥ N · A` replaces `2^K ≥ (N+1) A^(N+1)` and
  `K ≈ P + log₂ P + log₂ N`, a factor `N` less in `K` and in `log R`.
- That calibration's rows have the form assumed in `coeff_bound`, and that nothing else in
  Section 4 needs the larger `P`. The proof of Theorem 3 also uses `9e ≤ 2^-P` with
  `e = 2^-(P+6)` and the bound `1/3` on visible entries, which do not depend on `H`.
- The preprint's Sections 7 to 9 use other spaces `W`, where slots of both sides can occur
  in one cofactor vector (two-variable constraints with signs); the theorems here do not
  cover that case.
- Together: `K` from about `10⁴ N³` to about `2N` to `4N`, and `log R` to order
  `N⁹ log⁴ N`. Later sections of the preprint reuse these constants and were not checked.

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
formal/SPLP/Descent.lean      descent without experts: exact labels in 2R queries, margins
formal/SPLP/Margin.lean       margins, rounded demands, localization; rounding counterexample
formal/SPLP/LabelTest.lean    the label test: tolerance gives a margin, exact tests are sound
formal/SPLP/Dissociated.lean  Lemma 5.1 of the preprint with the constant 12 d² ⌈log₂ (d+1)⌉
formal/SPLP/SubsetSums.lean   subset sums of numbers separated by factors of two are distinct
formal/SPLP/PolyCount.lean    counting integer polynomials of bounded degree and 1-norm
formal/SPLP/Norm1.lean        the coefficient 1-norm
formal/SPLP/Minors.lean       minors as integer polynomials in the matrix entries
formal/SPLP/CountArith.lean   the counting inequality fails at the smaller constant
formal/SPLP/RangeBound.lean   size of the preprint's demand bound as a function of its constant
formal/SPLP/Approx.lean       approximately cleared markets: correctness and query bound
formal/SPLP/ApproxLevel.lean  the same with a constant tolerance (errors weighted by invested share)
formal/SPLP/GainMarket.lean   the market condition reduced to the aggregate gain; N-number certificate
formal/SPLP/ArgmaxFactor.lean the factor of the best option is not a product of pairwise comparisons
formal/SPLP/PairTest.lean     Lemma 3.1 of the preprint with explicit constants
formal/SPLP/DiffConstraints.lean  difference constraints: negative-cycle criterion, sign transfer
formal/SPLP/BlockMinors.lean  cofactor vectors of a block-diagonal basis are one-sided
formal/SPLP/Precision.lean    coefficient bound 3^j; the label test with explicit precision
formal/SPLP/Summary.lean      the statements to read
```

About 10700 lines. No `sorry`; every headline theorem depends only on `propext`,
`Classical.choice`, `Quot.sound`.

Repository layout:

```
README.md                  results, scope, open directions
formal/                    the Lean project (library SPLP)
scripts/fetch-upstream.sh  sparse checkout of openai/math into src/ (pinned commit)
src/                       upstream reference checkout; not tracked, nothing in formal/ depends on it
upstream-patches/          patch and script that rebuild upstream's compression core with a smaller width
upstream-build/            output of that script; not tracked
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
  `(d+1)^6`). With the smaller constant of result 6 carried into the parameters, `log R`
  would be about `N^11 log⁴ N`.
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

Ideas tried on 25 November 2026 for a structurally cheaper scheme, none formalized unless
stated:

- *Range reduction by rounding (closed, see result 4).* For small `R` the number of cells is
  at most the size of the pool, about `N^(k+1) D R^(k+1)`, whatever the number of probes, so
  `log R` phases of bounded range would replace the exponent 234 by roughly `46 + 5`. It
  fails for exact labels: rounded demands need a margin as large as the rounding
  (`RoundingExample`), and a margin `G` costs `2G` queries or a price search of range `G`.
  Not formalized: variants that keep rank information inside each rounded level (demands
  `K m + rank`) are consistent at grid points, but their market proposals leave the grid; a
  market restricted to the grid with finite-difference gains keeps total wealth from growing
  but then needs feedback correct one grid step below the threshold, which is the same
  margin again. In the LP reduction the test behind the labels has a margin of a constant
  factor only (visibility threshold `1/2` or `1/3`); a margin `G` there needs about `G` more
  bits of precision, so it cannot follow the scale.
- *Coarse descent.* Lockstep descent with step `e > 1/2` splits the slots into residue
  classes modulo `2e`; only the class of the maximal slot is protected, and with three or
  more classes wrong labels can raise the maximum by about `e/3` per query. So step sizes
  cannot simply be doubled.
- *Independent per-slot pools* (a product-form market over single guesses, which would need
  no recursion and only `O(N log R)` queries). Refuted by simulation: labels that always push
  the non-maximal coordinates away from the box keep it from converging even for `N = 2`.
- *Reusing one child for many probes, or a chain of reference points instead of a tree.*
  Feedback against a fixed reference point carries no new information: label information
  enters the recursion only through ties between a proposal and its child's prices.
- *Experts thresholded on the current proposal* (pivot at the same level). Makes the market
  step a fixed-point problem instead of a convex minimization, with no gain in the hit
  probability for a random pivot.

1. Inside the present analysis the arity-4 probe exponent cannot go below about 45.5
   (numerical optimum of the constraints in `Consts.Good`). The three remaining
   multiplicative losses are the pivot band `1/(δ-γ)`, the tuple transfer `ρ^k`, and the
   loss-to-gain ratio `1 + λ/ε ≈ 1 + 1/(2q-1)`. Removing any one needs a change to the scheme.
2. The total cost is now roughly (probes)^(k+1): each probe exponent point costs five in the
   total for arity 4. A market step whose cost does not grow with the number of completed
   probes (fewer cells, or cells that can be merged or forgotten) would matter more than any
   further constant tuning.
3. Markets cleared for approximate weights: proved, with a constant tolerance for arity 4
   (see "Markets may be cleared approximately"). Open: a formal procedure that produces the
   approximate weights from the cells; the cell, bit-size and vertex-proposal results for
   approximately cleared markets; `c · r < 1` for arities 3, 5, 6. Not formalized, and
   negative: a sparse weighted sample of experts does not work as the approximate weights,
   since its error on ranges grows by a factor `1 + η(k+1)` per update; only closeness in
   total variation is stable under the multiplicative updates.
   Further findings on a cheaper market step (not formalized unless a theorem is named):
   - An approximate minimizer of the potential in value does not give the gain condition
     (for `Φ(y) = W|y|` the point `y = ε/W` has value `ε` and slope `-W`), so with a
     first-order oracle exact minimization remains; the number of evaluations is polynomial
     and is not the bottleneck.
   - Letting an expert bet on every slot above its threshold, or replacing it by `k`
     single-slot experts, breaks the analysis: feedback is guaranteed only above the child's
     threshold, and for `k = 1` the average log gain is negative.
   - Multiplying per-slot factors would make the wealth a product measure but adds about
     `1.5 · 10^-3` per probe to wealth growth, against about `3 · 10^-9` tolerated.
   - Open lead: the wealth evolution is a sequence of range updates on the cells of a tropical
     arrangement, and the sets summed are simplicial cones; partition trees with lazy updates
     might cost `t^(k-1+o(1))` per update or evaluation in place of `t^k` (for arity 4,
     roughly exponent 234 to 188). The dynamic details are unverified.
4. Formalize the two missing pieces of the market step in an explicit cost model: the number
   of evaluations needed to reach a vertex minimizer, and counting the experts of a cell.
5. Tighten the constants feeding `log R` (`H`, `P`, `K`) with proofs.
6. The LP label oracle is stronger than the abstract one: labels are correct on every slot
   within a polynomial additive margin of the maximum surplus, not only at exact maximizers.
   The price theorem does not use this.
