# Precision radius `paperRadius`: trace and repair

Build directory: `/Users/mike/Git/stronglypolynomial/upstream-build-radius` (Lean v4.34.1, pins
unchanged, width and clock patches left in place). All paths below are relative to
`OAI/Optimization/LinearProgramming/`. Line numbers refer to the files *before* this change,
i.e. to `/Users/mike/Git/stronglypolynomial/upstream-build-clock`.

## Result

| quantity | where | old | new |
|---|---|---|---|
| `paperRadius N` | `Compression/AdaptiveRequests.lean:18` | `100*(N+1)^3` | `6*N+16` |
| `MinorLog.threshold n` (statement of Theorem 1.4) | `OracleSpec/Compression.lean:38` | `100*(n+1)^3` | `6*n+16` |
| `geoCutoff n` (Proposition 2.1) | `Geometry/LabelBasis.lean:17` | `100*(n+1)^3` | `6*n+16` |
| `paperGrid N = 2^(paperRadius N+7)` | `Compression/AdaptiveRequests.lean:19` | `2^(100(N+1)^3+7)` | `2^(6N+23)` |
| `B` in `onlineMinorBitFormula` | `Compression/BitBudget.lean:185` | `100*(N+1)^3` | `6*N+16` |
| leading term of `onlineMinorBitFormula` | | `(80+9600/7)·w^8 ≈ 1451·w^8` | `80·w^8` |
| degree of `onlineMinorBitFormula` in `N` | | 24 | 24 (unchanged, see section 4) |

`w = (7N^2+8)N+1` is the width. The radius is no longer part of the leading term of the bit
formula: the formula evaluated at radius 0 has the same `Nat.log 2` as the new one for
`N ≥ 4` (table in section 4).

No `sorry`, `axiom`, `native_decide`. No theorem deleted. One new lemma
(`paperRadius_le_cube`), one new private lemma (`proxyRoundingInput_mono_radius`).

**What the statement change means.** The three definitions above are one number (they are
identified by `rfl`/`simp only` in `Geometry/PriceStepRAM.lean:29`,
`Geometry/WireConsensus.lean:41,119`, `Geometry/ComparatorAccuracy.lean:54-58`,
`Compression/PublicTransport.lean:59`, `OracleSpec/NativePublic.lean:58`). Lowering it makes
the *promise* of the compression theorem (`OnlineMinorLogCompression`, `ValidMinorAssignment`:
four-term comparisons agree after clipping at radius `K` up to `2^-K`) weaker in precision and
smaller in bits, and makes Proposition 2.1 (`geometricLabel_correct`, hypothesis
`FourLogAccuracy (geoCutoff n)`) stronger, because it now needs less. The statements of
`strongly_polynomial_feasibility` / `strongly_polynomial_optimization` do not mention the
radius and are unchanged.

## Final build

    lake build OAI.Optimization.LinearProgramming.Optimization OAI.Optimization.LinearProgramming.Feasibility
    Build completed successfully (10781 jobs).

Log of the confirming no-op run: `radius-build-final.log` (no warnings, no errors).
Earlier logs: `radius-build-1.log` (the edited modules and their dependents, passed first
time), `radius-build-2.log` (full build, one failure: `OracleSpec/Companion.lean`, see
"Failures"), `radius-build-3.log` (full build after the fix, 10781 jobs, clean),
`radius-build-all.log` (every one of the 1554 `.lean` files under `OAI/` passed as a target:
nothing outside the closure of the two targets was stale except the two aggregates
`OAI/WidthAll.lean`, `OAI/WidthExtra.lean` of the width patch, which rebuilt).
No git command was run.

`radius.patch`: `diff -uN` of the 25 changed files against `upstream-build-clock`
(42 hunks, headers `--- a/OAI/...`, `+++ b/OAI/...`). It was applied with `patch -p1` to a
fresh copy of those 25 files from `upstream-build-clock` and the result compared byte for
byte with this directory.

## 1. Where the size of the radius is needed from below

There are exactly three such places, and all three are linear or logarithmic in the
dimension. Upstream's formal geometry has no calibration layer with `H = 2^(100N^2)`,
`2^-P = H^-100`, `K ≈ (N+1)P` (the word "calibrat" does not occur in the tree): the label
test is proved from pivot frames whose coefficient sums are bounded by `2^n`
(`Geometry/Triangular.lean:17-52` `triangular_l1_bound`, `Geometry/FrameControl.lean:37-39`
`IsPivotFrame.coeff_bound`), so the informal slack is already there and `100(N+1)^3` was only
a generous closed form.

**L1. Projection precision (the binding one).**
* `Geometry/Triangular.lean:56-82`, `projection_precision`:
  `30 * n^3 * 4^n * 2^(-K) ≤ 1/(2000 n)` for `0 < n`, i.e. `60000 * n^4 * 4^n ≤ 2^K`.
  Proof (`:67-73`): `60000 ≤ 2^16`, `n^4 ≤ (2^n)^4`, `4^n = 2^(2n)`, hence the proof needs
  exactly `16 + n*4 + 2*n ≤ K`; the last step (`:71-73`) compared this with `100(n+1)^3` by
  `nlinarith`.
* Only consumer: `Geometry/LabelBasis.lean:72-75` (`label_from_rounded_row_bounds`), which
  passes it as `hbudget` to `rounded_projector_estimates` (`Geometry/Projection.lean:433-445`,
  hypothesis at `:437`). There `δ = geoDelta n = 2^-K` is the error of each rounded frame
  entry and of each four-term comparison; `4^n = 2^n * 2^n` is the product of the two frame
  coefficient bounds (`hrepD`, `hrepE`, `:442-443`), `1/(2000 n)` is half the label tolerance
  `1/(1000 n)` (`Geometry/Oracle.lean:89`, `LabelBasis.lean:33-42`).
* True requirement: `K ≥ 2n + 4 log2 n + log2 60000 = 2n + 4 log2 n + 15.87`
  (`n = 1, 2, 3`: `K ≥ 18, 24, 29`). Requirement of the existing proof: `K ≥ 6n + 16`.

**L2. Clipping lemma.**
* `Geometry/Admissible.lean:89-90` (`roundedRegistered_dot_bound`): `2 ≤ geoCutoff n`, passed
  as `hB` to `registered_dot_bound` (`:39-42`) and from there to
  `almostOrthogonal_normalizedMinorRows` (`Geometry/Clipping.lean:200-201`) and
  `rpow_error_of_clipped_log` (`Clipping.lean:59-61`).
* The latter uses `hB` only for `2^-B ≤ 1` and `0 ≤ B` (`:64-65`, `:78`), so the true
  requirement is `K ≥ 0`; the stated one is `K ≥ 2`.

**L3. Injectivity of subset sums in the restart count.**
* `Compression/Bound.lean:101-112`, `proxy_error_at_cutoff`:
  `4 * (N+1)^6 * 2^-(K+7) ≤ 1`, proved from `N+1 ≤ 2^N` and `2 + N*6 ≤ K+7` (`:104-105`).
* Only consumer: `Compression/MinorIndex.lean:41-47` (`dissociated_minor_card_le`), which
  needs `t.card * η ≤ 1` for `t.card ≤ (N+1)^6` and `η = 2^-(K+7)` (the proxy error), to
  apply `dissociated_subsetProduct_subsetSum_injOn` (`Compression/Separation.lean:13-16`).
  The factor 4 is not used.
* True requirement: `K ≥ 6 log2(N+1) - 7`. Requirement of the existing proof: `K ≥ 6N - 5`.

**Not requirements on the radius.**
* `Compression/Epoch.lean:160-165` (`seventeen_units_le_clip_precision`,
  `17 * 2^-(B+7) ≤ 2^-B`), used at `Compression/AdaptiveRequests.lean:106`: holds for every
  `B`; it is the reason for the `+7` in the grid exponent.
* `Compression/MinorAssignments.lean:98-99`: `1 ≤ paperGrid 0`.
* `epoch_commit_extends_accepted` (`Compression/Epoch.lean:125-143`), the lattice request
  (`GoodRequestRows`, `AdaptiveRequests.lean:57-66`), `logProxyValue_error`
  (`MinorAssignments.lean:45`), `roundedPivotMatrix` / `rounded_approximates_extension` /
  `isPivotFrame` (`Geometry/PivotBasis.lean:17,45,59`, used at
  `Geometry/LabelTheorem.lean:48-74`) take the radius or the grid as a free parameter.

**Completeness.** After the change only the three arithmetic steps L1-L3 had to be re-proved
as lower bounds; every other repair (section 3) is a synchronisation or an upper bound, and
the whole tree builds. The proofs that unfold one of the three definitions are exactly:
L2, and the transports listed under "What the statement change means" plus
`Compression/NumericROMBounds.lean:64`, `Compression/MinorAssignments.lean:67`,
`Compression/ProxyFuelQueries.lean:88`, `OracleSpec/Companion.lean:91`, none of which
compares the radius with anything from below.

**Answers.**
* `100(N+1)^3` is a rounded-up closed form of `6N+16` (existing proofs), which is itself a
  rounded-up form of `2N + 4 log2 N + 15.87`.
* Smallest radius of each shape that the existing proof steps support verbatim (binding case
  `n = 1`, where they need 22; `2 ≤ K` at `n = 0`):
  `3*(N+1)^3`, `6*(N+1)^2`, `11*(N+1)`, and `6*N+16`.
  With the exact inequality `60000 n^4 4^n ≤ 2^K` instead (needs 18 at `n = 1`, 24 at
  `n = 2`): `3*(N+1)^3`, `5*(N+1)^2`, `9*(N+1)`.
* Implemented: `6*N+16`, the exponent that `projection_precision` itself produces.

## 2. Where the radius is only used from above

A smaller radius can only help in all of these.

* **Bit budget of the committed values.** `Compression/BitBudget.lean:117`
  (`fiberCoefficientBits`), `:128` (`fiberClipBits`), `:155-166`, `:170-180`
  (`fiber_request_height_le_two_pow`), `:183-196` (`onlineMinorBitFormula`), `:210-219`
  (`fiber_manuscript_value_height`, used at `Compression/AdaptiveRequests.lean:94` for the
  size clause of `ValidMinorAssignment`). Downstream: `Geometry/DimensionBounds.lean:36`
  (`minorCostMagnitude`), `:42` (`subspaceQueryClock`), `:57` (`subspaceMinorCallsPolynomial`),
  `BitRAM/NativePriceEpoch.lean:82-91`.
* **Cutoff exponent (fuel).** `Compression/ProxyFuel.lean:29-34`
  (`manuscriptProxyFuelFormula`), `:64-80`, `:84-107`, `:111-118`;
  `Compression/ProxyFuelQueries.lean:23-33`, `:36-43`, `:81-91`;
  `Compression/ProxyHomogeneousFuel.lean:11-37`; `Compression/ProxyFuelCoefficients.lean:70-89`
  (explicit coefficient list of the fuel polynomial); `Compression/InnerRAMAdapter.lean:15-28`
  (`coefficientCap = 2^(fuel-(radius+7))`, needs `radius+7 ≤ fuel`);
  `Compression/InnerNativeWords.lean:17`, `InnerNativeRound.lean:18,48`,
  `NativeProxyCost.lean:24-39`.
* **Programs that compute or carry the radius, and their time/space bounds.**
  `Compression/ParameterRAM.lean:24-38` (polynomial and coefficient lists), `:82-96` (step
  count, counter cap, bits), `:100-108` (`ParameterOutput`);
  `Compression/ProxyNormalHeader.lean:22-26,43-45,50-55,98`;
  `Compression/ProxyNumericCache.lean:21-35`; `Compression/ProxyNumericComplexity.lean:21-91`;
  `Compression/NumericROMBounds.lean:43,56-71`; `Compression/RoundingBudgets.lean:57-66,113-114`
  (bit-stack procedures for the radius, the grid and `epochHeightFor`);
  `Compression/RequestGraphInputSize.lean:16-19,46-47`; and the files that only pass
  `p = paperRadius N+7` along (`InnerClock:75`, `InnerNative:40`, `InnerNativeSemantics:150-160`,
  `InnerCoordinates:47`, `MinorNative:22-57`, `NativeCache:77-79`, `NumericROMLogic:16`,
  `ServiceNumericSpec:16`, `RequestGraphPaper:26-145`).
  `Geometry/LabelHeader.lean:19-21,60` (address-bank computation of the precision, register
  138), `Geometry/LabelBuffers.lean:63`, `Geometry/PivotPrefixContract.lean:114-116`
  (`stepCost`, `stepWidth`), `Geometry/OracleBudget.lean:22-72`,
  `Geometry/AfterPrefix.lean:61-76`, `Geometry/OracleAssembly.lean:39-41,56-89`,
  `Geometry/LabelRAMCode.lean:30`.
* **Offline version of Theorem 1.4.** `Compression/OfflineBudget.lean:94-148`,
  `Compression/Offline.lean:98-135`, `OracleSpec/Companion.lean:40-92`.

## 3. Edits (25 files)

**Definitions** (statement changes; each literally contained the closed form).

| File | Declaration | Change |
|---|---|---|
| `Compression/AdaptiveRequests` | `paperRadius` | `6*N+16` |
| `Compression/AdaptiveRequests` | `paperRadius_le_cube` (new) | `paperRadius N ≤ 100*(N+1)^3` |
| `OracleSpec/Compression` | `MinorLog.threshold` | `6*n+16` |
| `Geometry/LabelBasis` | `geoCutoff` | `6*n+16` |
| `Compression/BitBudget` | `onlineMinorBitFormula`, statement of `fiber_manuscript_value_height` | `let B := 6*N+16`; proofs unchanged |
| `Compression/ParameterRAM` | `parameterRadiusPolynomial`, `radiusCoefficients`, `gridExponentCoefficients` | `6*X+16`, `[16,6]`, `[23,6]` (was `100*(X+1)^3`, `[100,300,300,100]`, `[107,300,300,100]`) |
| `Compression/ParameterRAM` | `parameterRadiusPolynomial_eval`, `parameterGridExponent_eval`, `parameterStepsFromCoefficients`, `ParameterOutput.{radius,gridExponent,grid}` | literal replaced; the two private `*_value` lemmas now `rw` the eval lemma, `simp only`, `ring` |
| `Compression/ProxyNormalHeader` | `proxyParameter_exponents_safe`, `normalProxyHeaderSteps`, `NormalProxyHeader.{precision,protectedEnd}`, local `prec` | literal replaced; proofs unchanged |
| `Compression/ProxyNumericCache` | `numericCachePrecision` | `6*N+16+7` |
| `Compression/RoundingBudgets` | `radius` (private) | bit-stack procedure `uadd (umul (uconst e 6) n) (uconst e 16)` instead of `umul (uconst e 100) (upow (uadd n (uconst e 1)) 3)` |
| `Geometry/LabelHeader` | `alloc` (private), `modifiedHeaderRegisters`, `pivotWords` (private) | the address program sets register 213 to 16 and computes register 138 as `16 + 6*n` by one reservation (`.reserve 138 213 212 204`); the three reservations that built `n+1`, `(n+1)^2`, `(n+1)^3` in registers 215-217 are removed, and those registers leave the list of modified registers (so `prepareHeader_frame` / `prepareHeader_spec` preserve three more registers). `allocationTime ≤ 5000*(r+n+1)^3` and all proofs unchanged |

**Lower-bound proofs (L1-L3).**

| File | Declaration | Change |
|---|---|---|
| `Geometry/Triangular` | `projection_precision` | statement at `6*n+16`; last step `16+n*4+2*n ≤ 6*n+16` by `omega` instead of `nlinarith` |
| `Geometry/Admissible` | `roundedRegistered_dot_bound` | `2 ≤ geoCutoff n` by `omega` |
| `Compression/Bound` | `proxy_error_at_cutoff` | statement at `6*N+16+7`; `hexp` by `omega` |

**Hypotheses that carry the proxy precision `1/2^(radius+7)`** (literal replaced, hypothesis
is now weaker, proofs unchanged): `Compression/MinorIndex` `dissociated_minor_card_le`,
`dissociated_nonzeroPairMinor_card_le`; `Compression/Restart` `minor_request_restarts_le`;
`Compression/MinorAssignments` `minorProxy_independent_bound` (local `hclose`);
`Geometry/GeneratorService` `generatorCap_of_minor_proxy`; `Geometry/SubspaceDecision`
`SubspaceRequestCorrect`.

**Upper-bound proofs.**

| File | Declaration | Change |
|---|---|---|
| `Geometry/OracleBudget` | `pivotTime_bound`, `pivotWidth_bound`, `time_budget`, `width_budget` | statements at `(6*n+16)`; `hb : 6*n+16 ≤ 100*z^3` by `omega` from `n+1 ≤ z ≤ z^3`. Right-hand sides (`3443*(r+n+1)^5`, `prefixWidthCoefficient`, `postWidthCoefficient`) unchanged |
| `Geometry/AfterPrefix` | `afterPrefixBits_dimension` | statement at `8+2*(6*n+16+4)`; same bound `217*z^3`, an unused `have` removed |
| `Compression/ProxyFuel` | `manuscript_commit_inputWidth` | `let B := 6*N+16` (the proof never used the value of `B`) |
| `Compression/ProxyFuelQueries` | `proxyRoundingInput_mono_radius` (new, private) | `proxyRoundingInputFormula w ·` is monotone |
| `Compression/ProxyFuelQueries` | `manuscript_commit_fuel`, `manuscript_request_fuel`, `manuscript_grid_query_l1` | reduce to the unchanged `manuscript_rounding_fuel` through `paperRadius_le_cube` and the monotonicity lemma |
| `Compression/ProxyHomogeneousFuel` | `manuscript_homogeneous_grid_fuel` | `paperRadius N ≤ B` inserted before `omega` |
| `Compression/RequestGraphInputSize` | `paper_graph_input_length_for` | right-hand side of the `change` written with the kept `100*(N+1)^3+7`; `gcongr` uses `paperRadius_le_cube` |
| `Compression/OfflineBudget` | `offlineValueBits`, `offlineValueCap_le_two_pow`, `offlineValueBits_le` | `let B := 6*N+16`; new expansion `36u^19+167u^18+144u^13+666u^12+150u^7+685u^6+12u+41` (`u = N+1`); the bound `6689*(N+1)^21` is kept |
| `Compression/Offline` | `exists_bounded_minor_log_assignment` | `let B := 6*N+16`; proof unchanged |

No other file needed a change; in particular `OracleSpec/{NativePublic,Companion}`,
`Compression/{PublicTransport,NumericROMBounds,ServiceBound,InnerRAMAdapter}`,
`Geometry/{ComparatorAccuracy,OracleConcreteBounds,PriceStepRAM,WireConsensus}` compile
unchanged against the new definitions.

### Old over-estimates deliberately kept

Still stated with `100*(N+1)^3` and still valid because the new radius is smaller
(`paperRadius_le_cube`): `manuscriptProxyFuelFormula` with `manuscript_request_inputWidth`,
`manuscript_rounding_fuel` (`Compression/ProxyFuel.lean`; this fuel is the cutoff exponent
the algorithm really uses, and its 43 explicit coefficients in
`Compression/ProxyFuelCoefficients.lean` are written in `u = (N+1)^3` with `B = 100u`, so a
linear `B` does not fit that file's substitution scheme), `paperInputFormula`
(`Compression/RequestGraphInputSize.lean`), the local `B` in
`manuscript_homogeneous_grid_fuel`, `BudgetAlgebra.cubic_prefix` and the constants `3443`,
`101^5`, `217^105` in `Geometry/OracleBudget*.lean`, `offlineValueBits_le`.

## 4. The bit formula

`lake env lean RadiusAxioms.lean` (temporary file in the build directory, output saved in
`radius-axioms.out`; `oldFormula` is the formula of `upstream-build-clock` copied verbatim,
`zeroRadiusFormula` the same with `B := 0`):

| N | old radius | new radius | `Nat.log 2` old | `Nat.log 2` new | `Nat.log 2` at radius 0 | old / new |
|---|---|---|---|---|---|---|
| 1 | 800 | 22 | 45 | 41 | 40 | 17.62 |
| 4 | 12500 | 40 | 82 | 77 | 77 | 28.54 |
| 16 | 491300 | 112 | 129 | 124 | 124 | 21.36 |
| 64 | 27462500 | 400 | 177 | 172 | 172 | 18.94 |
| 256 | 1697459300 | 1552 | 224 | 220 | 220 | 18.34 |
| 1024 | 107689062500 | 6160 | 272 | 268 | 268 | 18.19 |

So the number of bits of the price range (and the base of `subspaceQueryClock`) drops by a
factor 17.6 to 28.5, tending to `(80+9600/7)/80 = 18.14`.

**Degree.** The degree stays 24. The description "roughly `96·B·w^7`" was the old leading
term only because `B = 100(N+1)^3` happened to have the same degree as `w`. In the formula
(`BitBudget.lean:183-196`) `a = (2w+B+14)+B+8` and `L = 2B+27+5a ≈ 10w+12B`; then
`u ≈ 2wL`, `cuts ≈ 4wu`, `commitment ≈ w^2·cuts`, `point ≈ w^2·commitment`, value
`≈ w·point`, i.e. `8·w^7·L = 80·w^8 + 96·B·w^7`. With `w ≈ 7N^3`: old
`(80·7^8 + 96·100·7^7)·N^24 ≈ 8.37e9·N^24`, new `80·7^8·N^24 ≈ 4.61e8·N^24` (checked
numerically at `N = 10^9`; not a Lean statement). The remaining `80·w^8` does not depend on
the radius at all: the `2w` in `a` is the height `requestCutoff (k+1) ≤ 2^(2k+7)` of a
lattice request row (`fiber_request_height_le_two_pow`, `BitBudget.lean:170-180`).

## 5. What remains loose

* The radius itself: `6N+16` against a true need of `2N + 4 log2 N + 15.87` (L1), and
  `n^4 ≤ 2^(4n)` is the only wasteful step. It no longer matters for the bit formula, where
  the radius is now a lower-order term (degree 22 of 24).
* The bit formula is now governed by the width alone, `80·w^8` with `w = 7N^3+8N+1`. Lowering
  it further means lowering the width, the factor `2w` from the request height, or the
  exponent 8 (projection test, commitment cap, pinned system, Cramer point, value: one or
  two factors of `w` each).
* The fuel (`manuscriptProxyFuel`) and the RAM resource polynomials still use the old radius
  and the old width `(N+1)^6` as upper bounds; they only enter existential constants of the
  compression service.
* L2 asks for `2 ≤ K` where `0 ≤ K` suffices; L3 for `K ≥ 6N-5` where `6 log2(N+1) - 7`
  suffices. Neither binds.

## Failures

One, repaired. The first full build (`radius-build-2.log`) failed in
`OracleSpec/Companion.lean:91` (`offline_bounded_assignment`): the offline companion of
Theorem 1.4 is stated with `threshold n` but proved from
`Compression.exists_bounded_minor_log_assignment`, which had its own literal
`B = 100*(N+1)^3`. I had first left `Offline.lean` / `OfflineBudget.lean` untouched as an
independent theorem; they are now synchronised (table above), and `Companion.lean` compiles
unchanged. (The alternative, deriving the comparison at the smaller radius from the one at
the larger radius, is true because clipping at a smaller radius is 1-Lipschitz and factors
through clipping at a larger one, but it is not formalized.)

Everything else compiled on the first attempt.

## Axioms

```
def OAI.Optimization.LinearProgramming.Compression.paperRadius : ℕ → ℕ :=
fun N => 6 * N + 16
def OAI.Optimization.LinearProgramming.OracleSpec.MinorLog.threshold : ℕ → ℕ :=
fun n => 6 * n + 16
def OAI.Optimization.LinearProgramming.Geometry.geoCutoff : ℕ → ℕ :=
fun n => 6 * n + 16
paperRadius_le_cube : ∀ (N : ℕ), paperRadius N ≤ 100 * (N + 1) ^ 3
Geometry.projection_precision : ∀ (n : ℕ), 0 < n → 30 * ↑n ^ 3 * 4 ^ n * 2 ^ (-↑(6 * n + 16)) ≤ 1 / (2000 * ↑n)
proxy_error_at_cutoff : ∀ (N : ℕ), 4 * (↑N + 1) ^ 6 * (1 / 2 ^ (6 * N + 16 + 7)) ≤ 1
'OAI.Optimization.LinearProgramming.strongly_polynomial_optimization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'OAI.Optimization.LinearProgramming.Compression.minor_transcript_guarantees' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'OAI.Optimization.LinearProgramming.Geometry.geometricLabel_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'OAI.Optimization.LinearProgramming.Geometry.subspaceMinorCalls_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
[(1, 45, 41, 40), (4, 82, 77, 77), (16, 129, 124, 124), (64, 177, 172, 172), (256, 224, 220, 220),
  (1024, 272, 268, 268)]
[(1, 1762), (4, 2854), (16, 2136), (64, 1894), (256, 1834), (1024, 1819)]
[(1, 800, 22), (4, 12500, 40), (16, 491300, 112), (64, 27462500, 400), (256, 1697459300, 1552),
  (1024, 107689062500, 6160)]
```
