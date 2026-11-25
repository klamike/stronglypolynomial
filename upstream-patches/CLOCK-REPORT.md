# Query-clock exponents of the price search: trace and repair

Build directory: `/Users/mike/Git/stronglypolynomial/upstream-build-clock` (Lean v4.34.1, pins
unchanged, width patch left in place). All paths below are relative to
`OAI/Optimization/LinearProgramming/`. Line numbers in the trace refer to the files *before*
this change, i.e. to `/Users/mike/Git/stronglypolynomial/upstream-build`.

## Result

| quantity | where | old | new |
|---|---|---|---|
| probes per node `Moment.probes` = `Complexity.probes` | `PriceGame/MomentConstants.lean`, `PriceGame/Complexity.lean` | `2^600+1` | `2^557+1` |
| trial tree nodes `trial_nodes_le`, `trial_calls_polynomial` | `PriceGame/Complexity.lean` | `(2N)^602` | `(2N)^559` |
| `probeBudget N` | `PriceGame/LearningPolynomial.lean` | `probes*(2N)^602` | `probes*(2N)^559` |
| `catalogueExponent` | `PriceGame/LearningPolynomial.lean` | `1+(201+1821*66^2)` = 7 932 478 | `1+(201+1692*66^2)` = 7 370 554 |
| probe log `probeBranchPow_le`, `probeLogBound_polynomial` | `PriceGame/TrialQueryArithmetic.lean` | `(2(N+1))^604` | `(2(N+1))^560` |
| per-trial queries `queryBound_polynomial` | `PriceGame/TrialExecutionComplexity.lean` | `(2(N+1))^605` | `(2(N+1))^561` |
| `rounds N R` | `PriceGame/CampaignRounds.lean` | `x^150*x^150 = x^300` | `x^130*x^130 = x^260` |
| `recursive_query_bound` | `PriceGame/RecursiveRecovery.lean` | `x^1510` | `x^989` |
| `recursive_query_bound_machine`, `campaignSolver_queryBound` | `RecursiveRecovery.lean`, `PriceGame/ControlSign.lean` | `2^1510 * (N+log2(R+1)+1)^1510` | `2^989 * (...)^989` |
| `subspaceQueryClock n`, `subspaceMinorCallsPolynomial` | `Geometry/DimensionBounds.lean` | `(n+bits+3)^1510` | `(n+bits+3)^989` |
| control fuel `Replay.fuelPolynomial` | `PriceGame/ControlReplayBound.lean` | `x^300*(5(2x)^602+(2(x+1))^605)+1` | `x^260*(5(2x)^559+(2(x+1))^561)+1` |
| exchange count `Wire.queryPolynomial` | `PriceGame/ControlCampaignWirePolynomial.lean` | `x^300*(2(x+1))^605` | `x^260*(2(x+1))^561` |

Here `x = inputSize N R = N + R.size + 1`. With the unchanged combination step
(`rounds * (x^2)^k`) the new parameters alone give `260 + 2*561 = 1382`; the further drop to
989 comes from one new arithmetic lemma in the leaf theorem (section 2, edit E).

No `sorry`, `axiom`, `native_decide`. No theorem deleted or weakened. Statement changes are
limited to the literals above (and one private lemma, see "Edits").

## Final build

    lake build OAI.Optimization.LinearProgramming.Optimization OAI.Optimization.LinearProgramming.Feasibility
    Build completed successfully (10781 jobs).

Log: `clock-build-full.log` (170 modules rebuilt, no warnings, no errors). Earlier partial
builds: `clock-build-1.log`, `clock-build-2.log`. Every proof compiled on the first attempt;
nothing failed and nothing was left unrepaired. No git command was run.

`clock.patch` is `diff -uN` of the 27 changed files against
`/Users/mike/Git/stronglypolynomial/upstream-build` with `a/OAI/...`, `b/OAI/...` headers; it
was applied with `patch -p1` to a fresh copy of those files and the result compared
byte for byte with this directory.

## 1. Trace

### 1a. Why `rounds = x^300`

* Definition: `PriceGame/CampaignRounds.lean:13` (`x^150 * x^150`), closed form `rounds_eq`
  at `:18`.
* The only lemma that needs `rounds` to be large is the final vote.
  `PriceGame/CampaignRecovery.lean:19-22` (`rounds_eq_source_exponent`) rewrites
  `300 = Pool.exceptionExponent + 1 + 74 = 225 + 1 + 74`; `correct_of_roundGuarantees`
  (`:163-210`) feeds this (`:179`) into `vote_at_time` (`:148-160`, called at `:206-209` with
  `e := 225`, `c := Pool.catalogueExponent`, `j := 74`), which is
  `polynomial_trials_vote` (`PriceGame/Majority.lean:266-284`).
* What that lemma uses (`Majority.lean`):
  `total_failures_bound` (`:230-263`) gives
  `failed ≤ E + T/8 + (E+1) * log2(64*m)`; `majority_of_few_failures` (`:107`) needs
  `2*failed < T`; `trial_overhead_bound` (`:165-210`) supplies
  `E + (E+1) * log2(64*m) < T/4`.
  So the **true requirement** is

      E + (E+1) * log2(64*m) < (3/8) * T        (the proof asks for < T/4)

  with
  - `E = Phases.Trace.budget N R = |Skeleton.enumerate N| * 66^2 * (1 + 66*(1 + R.size))`
    (`PriceGame/PhasesTrace.lean:80`, exception count `:82-84`), and
    `|Skeleton.enumerate N| ≤ depth N * (2 * ((2N^2)^64 * (1 + depth N * 2N^2)))`
    (`PriceGame/Skeletons.lean:118-119`); so `E ≈ 2^84 * N^130 * log^2 N * log R`;
  - `m` = size of the expert pool,
    `m ≤ T * (|Skeleton.enumerate N| * (2*(T*probeBudget N*4160)+1)^(66^2))`
    (`PriceGame/LearningPool.lean:91-94`, used through `current_pool_le`,
    `CampaignRecovery.lean:71-81`), so `log2 m = O(66^2 * (log T + 559 log N))`.
  In words: `T ≥ const * (#skeletons * log R) * log(pool size)`, about
  `2^107 * N^130 * log^2 N * log R * log(N + log R)` trials (my arithmetic from the two
  cited bounds, not a Lean statement).
* How the closed form is obtained: `E ≤ X^225` (`exception_size_power`,
  `PriceGame/LearningPolynomial.lean:63-69`: `201 + 14 + 10`, with skeletons `≤ X^201` at
  `:46-58`), `m ≤ (X*T)^c` (`catalogue_size_power`, `:87-108`), and the purely numerical
  side condition `4 * (13 + 2*c*(e+1+j+1)) < 2^j` (`trial_exponent_adequate`, `:110-113`),
  which is all that `trial_overhead_bound` asks of `j`.
* **Smallest exponent with the existing proof.** `j = 74` is not needed: with
  `e = 225` and `c = 7 932 478` (old) or `7 370 554` (new) the side condition holds for
  `j = 34` (`15 389 716 804 < 2^34 = 17 179 869 184`) and fails for `j = 33`
  (`15 330 752 372 > 2^33`). Hence `p = 225 + 1 + 34 = 260` is the least exponent that the
  unchanged lemma chain supports. Done (edit B).
* What stays loose in `260`: `225` is itself a closed form in which every constant is paid for
  by a power of `X ≥ 2` (`66 ≤ X^7`, `depth N ≤ X^2`, `2N^2 ≤ X^3` used 64 times,
  `1 + depth*2N^2 ≤ X^6`, `1+66*(1+R.size) ≤ X^10`). Re-deriving those absorptions would give
  about `e = 220` (`p ≈ 255`); I did not do this constant tuning because it changes the
  statement of `skeleton_size_power` (`B^201`), which is outside the listed exponents. The
  inequality itself needs only about `x^155` as a pure power valid for all `N, R`
  (`N^130` times logarithms asymptotically; the worst case is `N` between 8 and 20; this is
  an estimate, not formalized). Reaching it needs a different way of absorbing the constants
  `2^65`, `66^3` and `66^2 * 819` than one power of `x` per factor of two, so it is not a
  local edit.

### 1b. Why `(2N)^602` and `605`

* The recursion's parameters: `probes = 2^600 + 1` (`PriceGame/Complexity.lean:16`,
  `PriceGame/MomentConstants.lean:17`), fan-out `2*probes` per node, depth
  `depth N = N.log2 + 1` (`PriceGame/StatesMass.lean:29`). So this is not
  `probes^(log_{5/4} N)`: the depth is binary, and the whole exponent is the bit length of
  the constant `probes`.
* Nodes: `nodeCount b l ≤ (b+1)^l` (`Complexity.lean:23-31`),
  `2*(2^k+1)+1 ≤ 2^(k+2)` (`:43-50`), `b ≤ 2^k → b^(depth n) ≤ (2n)^k` (`:33-41`), hence
  `trial_nodes_le : nodeCount (2*probes) (depth n) ≤ (2n)^602` (`:52-59`).
  Exactly: nodes `≤ (2^601+3)^(log2 n + 1)`, real exponent `log2(2^601+3) = 601.00…`, and
  602 is the least integer exponent (because `2^601+3 > 2^601`). So **602 is tight for
  `probes = 2^600+1`**; it is `600 + 2`, not a rounded recursion exponent.
* Queries: recursion `queryBound` (`PriceGame/TrialExecution.lean:56-58`),
  `queryBound N r k l ≤ N * 2^l * (6r+1)^k` (`PriceGame/TrialQueryArithmetic.lean:13-29`,
  `TrialExecutionComplexity.lean:31-33`), `6*(2^n+1)+1 ≤ 2^(n+4)`
  (`TrialQueryArithmetic.lean:38-42`), `probeBranchPow_le ≤ (2(N+1))^604` (`:54-61`), one
  more factor for the leading `N` (`TrialExecutionComplexity.lean:35-45`): 605.
  Here `6*(2^n+1)+1 ≤ 2^(n+3)` already holds for `n ≥ 2`, so **605 was one too large**
  even for the old `probes`.
* What pins `probes`: only two facts use its size, `trialBranch_deeper`
  (`MomentConstants.lean:72-77`) and `trialBranch_local` (`:79-91`), consumed at
  `PriceGame/MomentGroups.lean:20` and `:52`. Both go through `trialBranch_of_large`
  (`:42-66`): `2^325 ≤ K → scale ≤ K ∧ 1 + 2 * 2^(-K*sigma/4) ≤ 2^tau`, with
  `sigma = 2^-272`, `tau = eta = sigma/8`, `scale = 2/sigma` (`:13-16`).
  Its proof uses exactly `scale ≤ K` and `277 ≤ K*sigma/4` (`:48-50`), i.e.
  `K ≥ 277 * 2^274 ≈ 2^282.1`; the hypothesis `2^325` is `2^43` larger than the argument
  needs. (`277` is tight to the integer: the inequality needs `K*sigma/4 ≥ 276.53`.)
  - `trialBranch_deeper`: `K = 2*probes`, needs `probes ≥ 277 * 2^273`.
  - `trialBranch_local`: `K = eta*probes/log 2`, needs
    `probes ≥ 277 * 2^549 * log 2 ≈ 2^556.6`. Upstream bounds `log 2 ≤ 1` (`:84-85`).
  So the learning inequality supports `probes = 2^557+1` (using `log 2 ≤ 256/277`; I prove
  `log 2 ≤ 9/10` from `1 + x + x^2/2 ≤ exp x`), or `2^558+1` with literally the old proof.
* Resulting exponents for `probes = 2^557+1`: nodes `(2N)^559` (`557+2`), probe log
  `(2(N+1))^560` (`557+3`), queries `(2(N+1))^561`. Smallest integer exponents the argument
  supports: 559 / 561. (A non-`2^n+1` choice, `probes = 2^557-1`, would give 558 for the node
  count only; not done, the helper lemmas are written for `2^n+1`.)
* What stays loose: `sigma = 2^-272` is the charging constant
  `(1/16) / (32 * (8 / (1/16)^65))` (`PriceGame/ChargingState.lean:18`,
  `PriceGame/StatesChargingScores.lean:44`, used at
  `PriceGame/TrialExecutionCharge.lean:72,85`), which comes from the 64-coordinate skeletons.
  The learning inequality forces `probes ≥ 8864 * ln 2 / sigma^2 ≈ 6144 / sigma^2`, so
  `557 = 2*272 + 13`.
  Lowering it further means changing the charging argument (the 64 and the `1/16`), which is
  structural. This is the whole gap to the `(2N)^46` of the independent formalization.

### 1c. Downstream uses of the literals

Classification: **S** = source (definition or the lemma that produces the number),
**M** = monotone upper bound (a hypothesis `T ≤ x^300`, or a bound passed on unchanged),
**C** = closed form relied on (an equation or a computation must match exactly).

| literal | file:line (old) | kind |
|---|---|---|
| 300 | `PriceGame/CampaignRounds.lean:13,18,20` | S |
| 300 (=225+1+74), 150 | `PriceGame/CampaignRecovery.lean:19-22,181,207`; `LearningPolynomial.lean:110-113` | C (the vote lemma is stated for `Fin (X^(e+1+j))`) |
| 300 | `PriceGame/OracleTrialCount.lean:42-43` (`sourcePowerUnaryP 300`), matched with `rounds_eq` by `simp` at `PriceGame/ControlCampaignInit.lean:25` | C (the machine computes exactly `x^300`) |
| 300 | `FixedSharePopulationWire.lean:46,85,88,97`; `FixedShareCursorWire.lean:43,60,75`; `ControlCampaignWirePolynomial.lean:18,20,39-40,51-53,66,96`; `ControlCampaignWireGuard.lean:20,48`; `ControlCampaignArrayBounds.lean:14,40,73`; `FixedShareCombinedWire.lean:21,96,119,125,131`; `ControlTrialRoundWidth.lean:39,85`; `CampaignWeightCost.lean:52,56,62,67-69,121,147`; `ControlReplayBound.lean:27,30-31,58` (all `PriceGame/`) | M |
| 602 | `PriceGame/Complexity.lean:53-59,87,94` | S |
| 602 | `PriceGame/LearningPolynomial.lean:72` (`probeBudget`), `:74-82` (`→ 1805 → 1821 → catalogueExponent`) | S; the budget is only ever an upper bound on the probe log (`RoundGuarantees.log_bound`) |
| 602 | `PriceGame/TrialExecutionComplexity.lean:140` (`change` to the closed form of `probeBudget`) | C |
| 602 | `TrialExecutionSize.lean:135`; `ControlTrialCost.lean:46`; `ControlCampaignNative.lean:148-159`; `ControlTrialEnvelope.lean:24`; `FixedShareCursorWire.lean:43,65`; `FixedShareCombinedWire.lean:107`; `ControlReplayBound.lean:27-31,57-58` | M |
| 602 (`2*probes ≤ 2^602`) | `PriceGame/ControlPrepareBudget.lean:32-37` | C on the value of `probes`; result only compared with `(2N)^1024` |
| 604 | `PriceGame/TrialQueryArithmetic.lean:54-61,92-94`; `TrialExecutionComplexity.lean:44,124,132` | S |
| 604 | `ControlTrialEnvelope.lean:22,34`; `FixedShareCombinedWire.lean:110` | M |
| 605 | `PriceGame/TrialExecutionComplexity.lean:42-50` | S |
| 605 | `FixedShareActualAllReplies.lean:44`; `TrialWireBound.lean:159`; `ControlTrialCost.lean:46`; `ControlCampaignNative.lean:148-159`; `ControlTrialEnvelope.lean:24`; `ControlCampaignWirePolynomial.lean:20,53`; `FixedShareCombinedWire.lean:107`; `ControlReplayBound.lean:27-31,57-58` | M |
| 1510 | `PriceGame/RecursiveRecovery.lean:61,70,91-92` | S (`300 + 2*605`) |
| 1510 | `PriceGame/ControlSign.lean:27`; `Geometry/DimensionBounds.lean:42,57` | leaf: nothing consumes them |

Two observations.

* The exponent 1510 is a dead end. `recursive_query_bound`, `recursive_query_bound_machine`,
  `campaignSolver_queryBound`, `subspaceQueryClock`, `subspaceMinorCallsPolynomial` and
  `subspaceMinorCalls_bound` have no user anywhere in upstream (checked in all of
  `src/lean`, not only in this trimmed copy), and `Geometry/DimensionBounds.lean` does not
  import the price game: its 1510 is a copied literal. The machine-model cost accounting
  uses `300`, `602`, `605` directly, through `Replay.fuelPolynomial`, `Wire.queryPolynomial`,
  `Wire.combinedPolynomial` and `Campaign.registerWeightPolynomial`.
* In that accounting the query clock is not the dominant term. The word-size polynomials
  contain the pool bound `(x*(x^300+1))^catalogueExponent` (`Formula.price`,
  `poolWordPolynomial`), of degree `301 * 7 932 478 ≈ 2.4e9`; after the change
  `261 * 7 370 554 ≈ 1.9e9`.

All files of the full upstream tree that mention these literals or
`Campaign.rounds`/`probeBudget`/`Moment.probes` are present in this build directory.

## 2. Edits

27 files, all under `OAI/Optimization/LinearProgramming/`.

**A. `probes` (`2^600+1 → 2^557+1`).**
* `PriceGame/MomentConstants.lean`: `probes`; `probes_pos`, `probes_odd`, `probes_coe`
  (private) re-proved with 557. New `trialBranch_of_threshold`
  (`277 * 2^274 ≤ K → …`, the old proof of `trialBranch_of_large` with the threshold it
  actually uses) and a private `pow274`. `trialBranch_of_large` keeps its statement
  (`2^325 ≤ K`) and is now a corollary. `trialBranch_deeper` and `trialBranch_local` keep
  their statements; the latter replaces `log 2 ≤ 1` by `log 2 ≤ 9/10`
  (`Real.quadratic_le_exp_of_nonneg`).
* `PriceGame/Complexity.lean`: `probes`; `trial_nodes_le`, `trial_calls_polynomial`,
  `trial_label_calls_le` at 559.
* `PriceGame/LearningPolynomial.lean`: `probeBudget` at 559; private `probeBudget_power`
  `B^1805 → B^1676` (`558 + 2*559`); `catalogueExponent` `1821 → 1692`.
* `PriceGame/ControlPrepareBudget.lean`: `2*probes ≤ 2^559` inside
  `scoreBudget_le_machineBudget` (statement unchanged).

**B. `rounds` (`x^300 → x^260`).**
* `PriceGame/CampaignRounds.lean`: `rounds`, `rounds_eq`.
* `PriceGame/LearningPolynomial.lean`: `trial_exponent_adequate` with gap 34 instead of 74.
* `PriceGame/CampaignRecovery.lean`: `rounds_eq_source_exponent` (`225+1+34`), `j := 34` and
  the positivity step in `correct_of_roundGuarantees`.
* `PriceGame/OracleTrialCount.lean`: `trialCountUnaryP`, `trialCountBinaryP` compute `x^260`.

**C. Per-trial queries (`605 → 561`, `604 → 560`).**
* `PriceGame/TrialQueryArithmetic.lean`: private `six_times_probe_le` sharpened to
  `2 ≤ n → 6*(2^n+1)+1 ≤ 2^(n+3)` (this is the "one too large"); new public
  `probeBranch_le : 6*Moment.probes+1 ≤ 2^560`; `probeBranchPow_le`,
  `probeLogBound_polynomial` at 560.
* `PriceGame/TrialExecutionComplexity.lean`: `queryBound_polynomial`,
  `run_height_polynomial` at 561; `run_log_length_polynomial`, `run_reaches_log_length` at
  560; the `change` in `probeLogBound_le_probeBudget`; new
  `queryBound_dimension : 0 < N → queryBound N probes (depth N) 0 ≤ N * (2*N)^560`.

**D. Literal propagation (statements and definitions that carry 300/602/604/605).**
`PriceGame/`: `FixedShareActualAllReplies`, `FixedSharePopulationWire`,
`FixedShareCursorWire`, `FixedShareCombinedWire`, `ControlCampaignWireGuard`,
`ControlCampaignWirePolynomial`, `ControlCampaignArrayBounds`, `ControlCampaignNative`,
`ControlTrialCost`, `ControlTrialEnvelope`, `ControlTrialRoundWidth`, `ControlReplayBound`,
`CampaignWeightCost`, `TrialExecutionSize`, `TrialWireBound`. No proof needed repair beyond
the substitution. The `set_option exponentiation.threshold 300/605/1024` lines were left as
they are (they are upper limits and still sufficient; no new one was needed).

**E. Leaf theorem (`1510 → 989`).**
* `PriceGame/RecursiveRecovery.lean`: `recursive_query_bound` is now
  `rounds * queries ≤ x^260 * x^729`. Upstream bounded one trial by `(2(N+1))^605` and then
  used `2(N+1) ≤ x^2`, which doubles the exponent and is forced by that base (it is tight
  at `N = 1`). The new private lemmas `double_pow_ten_le : (2N)^10 ≤ (N+1)^13` and
  `trial_queries_le_size` use the base `2N` instead (`queryBound_dimension`):
  `N * (2N)^560 ≤ x * (x^13)^56 = x^729`. `13/10` is within one percent of the best
  possible ratio `log 6 / log 4 = 1.2925` (attained at `N = 3`). The helper
  `combine_query_bounds` is reused unchanged. `recursive_query_bound_machine` follows with
  989.
* `PriceGame/ControlSign.lean`: `campaignSolver_queryBound` with 989.
* `Geometry/DimensionBounds.lean`: `subspaceQueryClock`, `subspaceMinorCallsPolynomial`
  with 989 (literal only; see 1c).

Statement changes outside the listed literals: none for public theorems. Private lemmas
changed: `six_times_probe_le`/`six_times_fixed_probe_le` (extra hypothesis `2 ≤ n`, stronger
conclusion), `probeBudget_power`, `probes_coe`. New declarations: `trialBranch_of_threshold`,
`probeBranch_le`, `queryBound_dimension` (public); `pow274`, `double_pow_ten_le`,
`trial_queries_le_size` (private).

## 3. What remains loose, and why

1. `557`: pinned by `sigma = 2^-272` through `trialBranch_local`
   (`probes ≥ 277 * 2^549 * ln 2`). Needs a different charging constant, not a local edit.
2. `559`/`561` versus `557`: the `+2`/`+4` are the bit length of the fan-out `2*probes+1`
   and of `6*probes+1`, plus one factor `N`; integer-tight for `probes = 2^557+1`.
3. `260`: `225` (exceptions as a power of `x`) `+ 1 + 34` (the constant
   `8 * catalogueExponent * 261` as a power of two). About 5 more are available by
   re-deriving `exception_size_power`/`skeleton_size_power`; the inequality itself needs
   roughly `x^155` (estimate).
4. `989 = 260 + 1 + 728`: `728 = 1.3 * 560` is the cost of writing `(2N)^560` as a power of
   `x ≥ N+1` for all `N ≥ 1`. In the variables `N` and `log R` separately the bound is
   `x^260 * N * (2N)^560`, i.e. degree 821 (old proofs: `300 + 605 = 905`).

## Axioms

Output of `lake env lean` on a temporary file (saved as `clock-axioms.out`), after the final
build:

```
'OAI.Optimization.LinearProgramming.strongly_polynomial_optimization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'OAI.Optimization.LinearProgramming.PriceGame.Campaign.recursive_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'OAI.Optimization.LinearProgramming.PriceGame.Campaign.recover_sign' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'OAI.Optimization.LinearProgramming.PriceGame.Control.campaignSolver_queryBound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'OAI.Optimization.LinearProgramming.Geometry.subspaceMinorCalls_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
@PriceGame.Campaign.recursive_query_bound : ∀ {N : ℕ} (R : ℕ) (anchor : Fin N),
  (PriceGame.Campaign.referenceStrategy R (PriceGame.Campaign.rounds N R) anchor).height ≤
    PriceGame.Campaign.inputSize N R ^ 989
@PriceGame.Campaign.recursive_query_bound_machine : ∀ {N : ℕ} (R : ℕ) (anchor : Fin N),
  (PriceGame.Campaign.referenceStrategy R (PriceGame.Campaign.rounds N R) anchor).height ≤
    2 ^ 989 * (N + (R + 1).log2 + 1) ^ 989
PriceGame.Campaign.rounds_eq : ∀ (N R : ℕ), PriceGame.Campaign.rounds N R = PriceGame.Campaign.inputSize N R ^ 260
PriceGame.TrialExecution.queryBound_polynomial : ∀ (N : ℕ),
  PriceGame.TrialExecution.queryBound N PriceGame.Moment.probes (PriceGame.States.Mass.depth N) 0 ≤ (2 * (N + 1)) ^ 561
PriceGame.Complexity.trial_nodes_le : ∀ (n : ℕ),
  0 < n →
    PriceGame.Complexity.nodeCount (2 * PriceGame.Complexity.probes) (PriceGame.States.Mass.depth n) ≤ (2 * n) ^ 559
def OAI.Optimization.LinearProgramming.PriceGame.Moment.probes : ℕ :=
2 ^ 557 + 1
def OAI.Optimization.LinearProgramming.PriceGame.Campaign.rounds : ℕ → ℕ → ℕ :=
fun N R => PriceGame.Campaign.inputSize N R ^ 130 * PriceGame.Campaign.inputSize N R ^ 130
def OAI.Optimization.LinearProgramming.PriceGame.Learning.Pool.probeBudget : ℕ → ℕ :=
fun N => PriceGame.Complexity.probes * (2 * N) ^ 559
def OAI.Optimization.LinearProgramming.PriceGame.Learning.Pool.catalogueExponent : ℕ :=
1 + (201 + 1692 * 66 ^ 2)
def OAI.Optimization.LinearProgramming.Geometry.subspaceQueryClock : ℕ → ℕ :=
fun n => (n + Compression.onlineMinorBitFormula n + 3) ^ 989
@PriceGame.Moment.trialBranch_of_large : ∀ {K : ℝ},
  2 ^ 325 ≤ K → PriceGame.Moment.scale ≤ K ∧ 1 + 2 * 2 ^ (-K * PriceGame.Moment.sigma / 4) ≤ 2 ^ PriceGame.Moment.tau
@PriceGame.Moment.trialBranch_of_threshold : ∀ {K : ℝ},
  277 * 2 ^ 274 ≤ K →
    PriceGame.Moment.scale ≤ K ∧ 1 + 2 * 2 ^ (-K * PriceGame.Moment.sigma / 4) ≤ 2 ^ PriceGame.Moment.tau
```

