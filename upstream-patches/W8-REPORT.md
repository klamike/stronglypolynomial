# Bit length of the compressed values (`onlineMinorBitFormula`): trace and repair

Build directory: `/Users/mike/Git/stronglypolynomial/upstream-build-w8` (Lean v4.34.1, pins
unchanged; width, clock and radius patches left in place). Reference state:
`/Users/mike/Git/stronglypolynomial/upstream-build-radius`. All paths below are relative to
`OAI/Optimization/LinearProgramming/`. "ref" line numbers are in the reference tree, "new" line
numbers in this tree.

## Result

| quantity | old (reference) | new |
|---|---|---|
| leading term of `onlineMinorBitFormula` in `w = (7N^2+8)N+1` | `80·w^8` | `10·w^5` |
| leading term in `N` | `461184080·N^24` (`= 80·7^8`) | `168070·N^15` (`= 10·7^5`) |
| degree in `N` | 24 | 15 |

Three powers of `w` (nine powers of `N`) and a factor 8 in the leading constant are removed.
No `sorry`, `axiom`, `native_decide`. No theorem deleted. 11 files changed, 1 file added
(`Compression/PinnedPoint.lean`), all under `Compression/`.

**Provenance.** Every source edit in `w8.patch` was already present in this directory as the
unverified work of the agent that was stopped. This run read the complete diff, judged it a
coherent tightening, and built it; it compiled as found, so this run made **no further source
edit**. What this run did: the review of the diff against the rules, all builds, the axiom
check, the table, the trace, the patch and its round-trip test.

## Final build

    lake build OAI.Optimization.LinearProgramming.Optimization OAI.Optimization.LinearProgramming.Feasibility
    Build completed successfully (10782 jobs).

(10781 jobs of the reference plus the new module `PinnedPoint`.) Logs in this directory:

* `w8-build-core-1.log`: `lake build …Compression.MinorAssignments`, 3307 jobs, clean.
* `w8-build-full-1.log`: the two targets, 10782 jobs, clean; 98 modules compiled in that run
  (everything downstream of `BitBudget`, including `ProxyFuel`, `RoundingBudgets`,
  `ServiceParameters`, `ServiceResources`, `DimensionBounds`, `NativePriceEpoch`,
  `NativePublic`). The only non-`✔` lines are replayed `info:` lines of the dependency
  `HexBareiss`.
* `w8-build-all.log`: every one of the 1555 `.lean` files under `OAI/` passed as a target,
  10784 jobs, clean (only the two aggregates `OAI/WidthAll`, `OAI/WidthExtra` were stale).
* `w8-build-final.log`: confirming no-op run of the two targets, 10782 jobs, no warning, no error.

* Because the ten core files had been compiled by the stopped agent (lake found their
  `.olean` up to date), each of `Projection`, `ProjectionCuts`, `ProjectionRational`,
  `FiberProjection`, `PinnedPoint`, `BitBudget`, `Commit`, `CommitProgram`, `Epoch`,
  `ComputedEpoch` was additionally compiled from its current source with `lake env lean`:
  no output (no error, no warning) for any of them.

Not built: nothing else exists in this trimmed tree. No git command was run. Only this
directory was written to.

Axioms (`w8-axioms.out`, produced with a temporary file and `lake env lean`, file deleted):

    'OAI.Optimization.LinearProgramming.strongly_polynomial_optimization' depends on axioms: [propext, Classical.choice, Quot.sound]
    'OAI.Optimization.LinearProgramming.strongly_polynomial_feasibility' depends on axioms: [propext, Classical.choice, Quot.sound]

and the same three for `fiber_manuscript_value_height`, `epoch_realization`,
`all_prefixes_extend`.

`w8.patch`: `diff -uN` of the 12 files against the same paths under `upstream-build-radius`
(29 hunks, headers `--- a/OAI/...`, `+++ b/OAI/...`). It was applied with `patch -p1` to a
fresh copy of the 11 reference files and the result compared byte for byte with this
directory. `w8-checkpoint-1.patch` is identical to it (saved after the first full build).

## Table

`#eval` of `Nat.log 2 (formula N)`; "old" is the reference formula copied into the temporary
file, "new" is `onlineMinorBitFormula` of this tree.

| N | 1 | 4 | 16 | 64 | 256 | 1024 |
|---|---|---|---|---|---|---|
| old `log2` | 41 | 77 | 124 | 172 | 220 | 268 |
| new `log2` | 26 | 48 | 77 | 107 | 137 | 167 |
The formula itself (a bound on `log2 F`) at `N = 1` goes from `2205881311193` to `100293404`,
at `N = 4` from about `2.6·10^23` to about `3.3·10^14`.

## 1. Trace

Notation: `k` = number of committed generators, `d` or `s` = number of generators of a
completion, both `≤ w`; `E = 2^(B+7)`; `C` = height of the affine coefficients; `H` = height
of a row of the clipping system; `Q` = cut budget; `G` = height of the commitment.

| line of the reference formula | quantity bounded | theorem (ref) | bound upstream proves (bits) | same argument done tightly | powers of `w` lost |
|---|---|---|---|---|---|
| `a = (2w+B+14)+B+8` | `C = max (requestCutoff (k+1)·E) (2E)`, `requestCutoff d = 2^(d+2)(d+3)` (`Request.lean:60`) | `fiber_request_height_le_two_pow` `BitBudget.lean:170`, `fiberCoefficientHeight_le_two_pow` `:119` | `2w+2B+22` | `k + log2(k+4) + B + 10`: upstream bounds `k+4 ≤ 2^(k+4)`, and adds `B+8` again for the `max` although the first argument already dominates | 0 (factor 2) |
| `L = (B+17)+(2+a)+1+(B+7)+4a` | `H = epochRowHeight B E C = (B+17+4C)(E·C^4)` (`Epoch.lean:20`, from `clipping_system_height` `AffineRows.lean:259`) | `fiberClipHeight_le_two_pow` `BitBudget.lean:130` | `5a+2B+27 ≈ 10w` | exact for the stated interface (`C` bounds numerators and denominators of four summed fractions) | 0 |
| `u = L·(w+w+2)` | integer row after clearing denominators, `clearedProjectionRowBound k d H = H^(k+d+2)` (`ProjectionRational.lean:19`, `exists_integer_projection_system` `:67`, `clear_bounded_row` `ProjectionCramer.lean:87`) | `projection_test_height_le_pow` `ProjectionRational.lean:30` | `L(k+d+2) ≈ 2wL` | the `k` retained columns of the fiber system are `0, ±1` (`fiberParameter_height` `Fiber.lean:109`), only `d+2` entries carry denominators: `L(d+2)`. With one multiplier per row (see future work): `L` | 1 (still lost) + factor 2 (fixed) |
| `cuts = w+1+(n+((n·n+(n+2u)·n)·2+u))` | `Q = fiberProjectionBudget = Σ_{d≤w} projectionCoefficientBound d (cleared row)`, `projectionCoefficientBound d B = (d+1)·projectionMultiplierBound d B·B` (`ProjectionCuts.lean:16`), `projectionMultiplierBound = ((d+1)!·((d+1)·B^2)^(d+1))^2` (`Projection.lean:143`) | `fiberProjectionBudget_le_two_pow` `BitBudget.lean:30` | `≈ 4·u·n ≈ 8w^2·L` | the multipliers are Cramer quotients of the Gram system with denominator `det^2` (`exists_bounded_scaled_integer_solution` `Projection.lean:84`); `|det|` suffices: `2·u·n`. A square subsystem instead of the Gram matrix would give `u·n` | 0 (factor 2 fixed, factor 2 open) |
| `m = w+1+cuts+1` | sign-form budget `M = (k+1)·Q+1` (`exists_bounded_projection_commit` `Commit.lean:187`) | `fiberCommitInput_le_two_pow` `BitBudget.lean:56` | `cuts + w + 2` | tight | 0 |
| `commitment = fiberCommitCapFormula w m` | `G = fiberCommitCap k M = max (commitHeight k M) (2^(radixWidth (k+1) M·(k+1)))` (`CommitCap.lean:12`), `commitHeight d M = comparisonRadix (d+1) M^(d+1)`, `comparisonRadix p M = 2M((4pM)^p+1)+2` (`Commit.lean:20`, `Lattice/Rounding.lean:16-19`), `radixWidth p M = M.size+(4(p+1)+M.size+6)(p+1)+3` (`Lattice/Precision.lean:20`) | `fiberCommitCap_le_two_pow` `CommitCap.lean:27` | `≈ m·k^2` | same order: a radix of `≈ p·log M` bits raised to the power `p`. `d = k ≤ w` is the right parameter | 0 |
| `pinned = L+commitment+2` | `fiberPinnedHeight = H+G+1`: one height for clipping rows and for the pin rows `y(anchor j) = γ j` (`Epoch.lean:102-109`) | `fiberPinnedHeight_le_two_pow` `BitBudget.lean:82` | `L+G_bits+2` | the commitment is not a row height: it is a right-hand side | see next line |
| `point = w·w+pinned·(w+2)·w` | Cramer point of the pinned system, `offlinePointCap s K = s!·(K^(s+2))^s` (`OfflineBudget.lean:19`; `exists_small_rat_feasible_with_fixed` `ProjectionSmallPoint.lean:107`, `exists_small_rat_of_tight_system` `ProjectionCramer.lean:134`) | `fiberPointHeight_le_two_pow` `BitBudget.lean:97` | `≈ G_bits·(s+2)·s` | `γ = z/q` with one integer denominator; solving for `q·y`, the pin rows need no clearing and `G` enters only the replaced column of Cramer's determinants, once: `(s+1)^2 + L(s+2)(s+1) + G_bits` | **2** (fixed) |
| `w+1+((a+1)+(point+1))·(w+2)` | value of an affine form at the point, `offlineValueCap s C Y = (s+1)((C+1)(Y+1))^(s+2)` (`OfflineBudget.lean:22`; `affine_evalRat_height` `AffineValue.lean:14`, `AffineFamily.evalRat_height` `AffineRows.lean:291`) | `fiberValueHeight_le_two_pow` `BitBudget.lean:105` | `≈ point·(s+2)` | every coordinate is treated as a separate fraction, so `s` denominators are multiplied; Cramer gives one common denominator: `(s+1)+(A+1)(s+2)+point` | **1** (fixed) |

`fiber_uniform_value_height_le_two_pow` (`BitBudget.lean:155`) evaluates
`fiberValueBits width width width …`, i.e. replaces `k`, the width and the dimension by the
width. This costs nothing in the exponent: `k = d = w` is attained (a full dissociated set).

**Where the powers come from, in the terms of the task.**

* (i) `u = L(2w+2)`, `cuts ≈ n·u`: one power of `w` is an artefact of row clearing with
  unrelated denominators (`H^(d+2)`); it is **not** removed here. A factor 8 in the constant
  was available (retained columns, `det^2`, the `2w` in `a`) and is removed; a further factor
  2 (Gram matrix) is not.
* (ii) `commitment = fiberCommitCapFormula w m`, quadratic in `d`: no loss. It is the formal
  counterpart of the text's `C = 2^(m(m+1))(2/ε)^(m+1)` followed by `B^(p+2)`, which is also
  `D^2·log M`.
* (iii) `point ≈ pinned·w^2`: two powers lost, both removed.
* (iv) the final `·(w+2)`: one power lost, removed.

**Correspondence with the text's Section 5.**

| text | formal | comment |
|---|---|---|
| `A = 2^K(D+4)/η` | `C = requestCutoff (k+1)·E`, `requestCutoff (k+1) = 2^(k+3)(k+4)` | the role of `2^K(D+4)` is played by the LLL cutoff, so `K` corresponds to `k+3 ≤ w+3`, not to the radius `B`. `log A ≈ w` in the formal chain; `D^4·K` then reads `w^5` |
| `M = (D+1)A^(D+1)`, `log M ≈ D·K` | `Q`, bits `cuts` | formal: `≈ 2·n·L·(d+2) ≈ 10w^3` now (was `80w^3`), text: `w^2`. The extra power is the row clearing; `L ≈ 5a` and the Gram factor 2 are also formal artefacts |
| `C`, base `B = 10M(mH+3)`, numerators `≤ B^(p+2)/η` | `G = fiberCommitCap` | same order `D^2·log M` |
| extension `(D+2)(AU+1)^(D+1)·U/η`, `log ≈ D·log U` | pinned system, Cramer point, affine evaluation | upstream: `log U·D^3` (artefact: `G` as a row height and one denominator per coordinate). Now: `log U` enters once, which is one power *better* than the text's own step |

So upstream lost four powers against a tight version of its own argument; three of them are
in the last two lines of the formula. The new chain is `10w^3 (cuts) × w^2 (commitment)`,
which has the text's exponent `w^5` with a different distribution: one power more than the
text in the elimination, one power less in the extension.

## 2. Edits

### 2a. Tightenings of existing arguments (no new mathematics)

1. **`det^2 → |det|`.** `Projection.lean` new `:86-140`: `exists_bounded_scaled_integer_solution`
   returns `q = |det G|` and `w i = sign(det G)·det(G with column i replaced)`; conclusion
   `≤ T` instead of `≤ T^2` (statement strengthened). `projectionMultiplierBound` (new `:150`)
   loses its outer square; `bounded_integer_obstruction` is unchanged in text and stronger.
   `ProjectionCuts.lean` `projectionCoefficientBound_le_pow` (new `:21`): statement unchanged
   (the old exponent is kept as an upper bound), proof adapted.
2. **Request cutoff.** `BitBudget.lean` new `:284` `manuscript_request_height_le_two_pow`:
   `requestCutoff (k+1)·2^(B+7) ≤ 2^(w+3N+B+13)` for `k ≤ w = (7N^2+8)N+1`, from
   `k+4 ≤ 8(N+1)^3 ≤ 2^(3N+3)`. The generic `fiber_request_height_le_two_pow` is kept.
   This is specific to the manuscript width, which keeps the formula a polynomial in `N`.

### 2b. Additions (new arguments; flagged)

3. **Row clearing of the fiber system over `d+2` entries.** `ProjectionRational.lean`: new
   `fiberClearedRowBound d B = B^(d+2)` (`:24`), `fiberTestBitBound` (`:35`),
   `projectionCoefficientBound_le_two_pow` (`:41`, the common core of the old and new bit
   bounds), `fiber_test_height_le_pow` (`:75`), `exists_integer_projection_system_of_unit`
   (`:196`), private `integer_projection_presentation_of_unit` (`:245`),
   `rational_projection_of_preserving_affine_tests_of_unit` (`:278`): when the retained
   columns are `0, ±1` only the eliminated columns and the constant are cleared.
   `projection_test_height_le_pow`, `exists_integer_projection_system`,
   `rational_projection_of_preserving_affine_tests`, `projectionTestBitBound`,
   `clearedProjectionRowBound` are kept unchanged. About 130 lines.
   `FiberProjection.lean:31` `preserves_generator_fiber` uses the new lemma; its `tests`
   hypothesis now has the smaller bound (statement stronger).
4. **Common denominator of the commitment and of the pinned point.**
   * `Compression/PinnedPoint.lean` (new file, 388 lines): `RowClears`, `rowClears_of_height`,
     `rowClears_of_unit`, `det_updateCol_natAbs_le` (expansion along the replaced column
     through the adjugate), `exists_common_denominator_of_tight_system`,
     `exists_common_denominator_feasible`, `exists_common_denominator_feasible_with_fixed`,
     `affine_evalRat_common_height`. It repeats the tight-rank and Cramer argument of
     `ProjectionSmallPoint` / `ProjectionCramer` for `q·y`.
   * `Commit.lean:203` `exists_bounded_projection_commit_common`,
     `CommitProgram.lean:76,118` `computeCommitWith_common`, `computeCommit_common`: both the
     existential and the computed commitment are an integer vector divided by its last
     coordinate, so `γ j = z j / q` with `q > 0` and all of `q`, `z j` below the height cap.
     The existing `…_spec` theorems are unchanged.
   * `Epoch.lean:35` **`ValidEpochCommit` has a third field `common`** recording exactly that.
     This is a change of a hypothesis structure: theorems that produce it
     (`epochCommit_valid`, `computedEpochCommit_valid`, `computedEpochCommitWith_valid`) prove
     more, theorems that consume it (`epoch_realization`, `epoch_commit_extends_accepted`,
     `all_successful_requests_extend`, `all_prefixes_extend`, and the users in
     `MinorNative`, `MinorAssignments`) assume more. All producers in the tree supply it.
   * `ComputedEpoch.lean:15` **`validEpochCommit_of_encoded_signs` has a new hypothesis
     `hcommon`** (it constructs the structure; its only callers are the two theorems in the
     same file). This is the one theorem whose statement gained a hypothesis.
   * `Epoch.lean:25` `epochCommit` chooses from `exists_bounded_projection_commit_common`.
   * `Epoch.lean:65` `epochValueCap` is now
     `pinnedValueCap width C (pinnedPointCap width H G)`; `epoch_realization` (`:79`) uses
     `exists_common_denominator_feasible_with_fixed` and `affine_evalRat_common_height`.

### 2c. Budget definitions and the formula (`BitBudget.lean`)

* `:22` `fiberProjectionBudget`, `:31` `fiberProjectionBits`: `fiberClearedRowBound` /
  `fiberTestBitBound` instead of `clearedProjectionRowBound k` / `projectionTestBitBound k`.
  The first argument is kept for the callers and is unused. Statements of
  `fiberProjectionBudget_term_le`, `fiberProjectionBudget_le_two_pow` change only through
  these formulas.
* `:195-282` new: `pinnedPointCap s H G = (s+1)!·(H^(s+2))^(s+1)·G`,
  `pinnedValueCap s C Y = (s+1)(C+1)^(s+2)·Y`, `pinnedPointCap_mono`,
  `pinnedPointCap_le_two_pow`, `pinnedPointBits`, `pinnedPointHeight_le_two_pow`,
  `pinnedValueBits`, `pinnedValueHeight_le_two_pow`, `pinnedValueBits_mono`,
  `pinned_uniform_value_height_le_two_pow`, and the 'new ≤ old' lemma
  **`pinnedValueBits_le_fiberValueBits`** (`:257`, for `1 ≤ dim`).
* All old definitions and theorems (`fiberPinnedHeight`, `fiberPinnedBits`, `fiberPointBits`,
  `fiberValueBits`, `fiberValueHeight_le_two_pow`, `fiberValueBits_mono`,
  `fiber_uniform_value_height_le_two_pow`, `fiber_request_height_le_two_pow`) are kept.
* `:312` `onlineMinorBitFormula`:

      let w := (7*N^2+8)*N+1
      let B := 6*N+16
      let a := (w+3*N+B+13)+B+8
      let L := ((B+17)+(2+a)+1)+((B+7)+a*4)
      let n := w+1
      let u := L*(w+2)
      let cuts := w+1+(n+((n*n+(n+u*2)*n)+u))
      let m := w+1+cuts+1
      let commitment := fiberCommitCapFormula w m
      let point := (w+1)*(w+1)+L*(w+2)*(w+1)+commitment
      w+1+(a+1)*(w+2)+point

  Still a polynomial in `N` (`onlineMinorBitPolynomial`, `onlineMinorBitPolynomial_eval`
  unchanged in text).
* `:338` `fiber_manuscript_value_height`: the left-hand side is the new cap
  `pinnedValueCap dim C (pinnedPointCap dim H (fiberCommitCap k ((k+1)·Q+1)))`, the
  right-hand side `2^(onlineMinorBitPolynomial.eval N)` as before. The old statement about
  `offlineValueCap … (offlinePointCap … (fiberPinnedHeight …))` is kept as
  `fiber_manuscript_value_height_coarse` (`:353`) with its own exponent `fiberValueBits`.

### 2d. Machine-model layer (old over-estimates kept)

* `ProxyFuel.lean`: `proxyRoundingInputFormula`, `manuscriptProxyFuelFormula` (the fuel /
  cutoff exponent) are **unchanged**. New private `coarseInputBits` (`:65`) is the old summand
  and `fiberCommitInputBits_le_coarse` (`:69`) is the 'new ≤ old' lemma;
  `manuscript_commit_inputWidth`, `manuscript_request_inputWidth` keep their statements.
* `RoundingBudgets.lean:69-88`: the private procedures `proj` and `fiber`, which compute
  `fiberProjectionBudget`, follow the new definition (row `H^(d+2)`, multiplier bound not
  squared). No public statement changes.
* Nothing outside `Compression/` needed an edit: `ServiceParameters`, `ServiceResources`,
  `ServiceContract`, `DimensionBounds`, `NativePriceEpoch`, `AddressHorner`, `NativePublic`
  use `onlineMinorBitPolynomial` as an opaque polynomial and recompiled unchanged.

### Effect of each change on the leading term

`80·w^8` → (1: `|det|`) `40·w^8` → (3: `d+2` entries) `20·w^8` → (2: cutoff) `10·w^8`
→ (4: point with common denominator) `10·w^6` → (4: value with common denominator) `10·w^5`.

## 3. What remains, and why

1. **Row clearing: one power of `w` (`10·w^5 → 12·w^4`, degree 15 → 12 in `N`; `log2` table
   would be 22, 39, 62, 86, 110, 134).** Not done: it needs a new argument that is neither
   short nor local.
   `u = L(d+2)` is forced by the interface: `GoodRequestRows` (`AdaptiveRequests.lean:64`)
   and `clipping_system_height` only say that every entry has numerator and denominator
   `≤ H`, and then a row of `d+2` entries has a common denominator up to `H^(d+1)`. The rows
   actually produced are better: `runMinorRequest` (`RequestAlgorithm.lean:75`) returns
   `requestSlope z i = -z_i / z_last` (`Request.lean:164`), one denominator `|z_last| ≤
   requestCutoff` for the whole coefficient row, and an offset `k/q` with `q = E`; the
   completed minors have ternary coefficients and offsets `k/E`
   (`exists_completed_affineFamily`, `Representatives.lean:58`); the endpoints of
   `comparisonRow` are multiples of `1/E`. Hence a four-term row `(a,s)` of the clipping
   system is cleared by the single multiplier `E·∏_{u ∈ supp a} D_u ≤ E·C^4` to integers of
   magnitude `≤ (B+17+4C)(E·C^4) = H`: the cleared height is `H` itself, `u = L`.
   Plan: (a) lemma next to `runMinorRequest_height` (`RequestSize.lean:66`) giving the common
   denominator; (b) a new clause in `GoodRequestRows`, supplied by `knownRequestFamily_spec`
   (`RequestFamily.lean:115`) for the three producers (`RequestGraphRounding.lean:59`,
   `RequestNative.lean:68`, `RequestRows.lean:16`); (c) the same clause through
   `exists_completed_affineFamily`; (d) a row-clearing lemma for `clippingMatrix` /
   `clippingRhs` (the integrality of the endpoints is proved inside
   `comparisonRow_endpoint_bounds`, `AffineRows.lean:212`, which states only `den ≤ E`); (e) variants of
   `exists_integer_projection_system_of_unit` and of
   `exists_common_denominator_feasible_with_fixed` that take the cleared rows (the predicate
   `RowClears` of `PinnedPoint.lean` already has the right shape); (f) `fiberClearedRowBound d
   B := B`, `proj` in `RoundingBudgets`, the formula. `epoch_realization` and
   `epoch_commit_extends_accepted` would gain a hypothesis. Estimate: 350-450 lines in about
   14 files.
2. **Gram matrix: factor 2 in the leading constant (`10 → 5`).** `bounded_integer_obstruction`
   solves the `(d+1) × |t|` system through `AᵀA`, whose entries are `≤ (d+1)·B^2`. Selecting
   `|t|` independent rows and using Cramer on the square subsystem gives `n!·B^n`. Needs a
   nonsingular-square-submatrix lemma; one bit of `log2 log2 F`.
3. **Lower-order slack, not touched:** `fiberCoefficientBits B Xbits = Xbits+B+8` adds `B+8`
   for the `max` with `2E` although `requestCutoff·E ≥ 2E` (changes `a` by `6N+24`; the
   `log2` table is unchanged at all six values of `N`); `(width+1) ≤ 2^(width+1)` in
   `fiberProjectionBudget_le_two_pow`; `L ≈ 5a` (with separate bounds for magnitudes and
   denominators `clipping_system_height` already supports `(B+17+4C)(E·D^4)`).
4. **Not a loss:** `commitment ≈ m·d^2`. After item 1 it is the leading term (`12·w^2·w^2`);
   lowering it further means a different rounding lemma than `Lattice/Rounding.lean`
   (radix `≈ M^(p+1)` raised to the power `p`), which is also what the text does.

## 4. Failures

None in this run: the leftover edits compiled at the first attempt, and no proof needed
repair. The stopped agent left no log, so nothing is known about attempts it abandoned.
