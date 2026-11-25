import Mathlib
import SPLP.Summary
import SPLP.GainMarket

/-!
# Constant tolerances for arities 3, 5 and 6

`SPLP/ApproxLevel.lean` and `SPLP/GainMarket.lean` show for arity 4 that the tolerance of the
market condition can be the constant `2^-25`. The argument needs `c · r < 1`: a child receives
only the share `c` of the wealth, so the error of the `r` children of a node is damped by
`c · r` per level. The same holds for the other three instances:

| arity | `c · r`                          | `α`    | `u`        | tolerance | exponent |
|-------|----------------------------------|--------|------------|-----------|----------|
| 3     | `30275/32768 ≈ 0.9239`           | `1/25` | `961/1000` | `2^-22`   | 66       |
| 4     | `15725/16384 ≈ 0.9598`           | `1/50` | `979/1000` | `2^-25`   | 46       |
| 5     | `53425/65536 ≈ 0.8152`           | `1/10` | `9/10`     | `2^-21`   | 39       |
| 6     | `338075/1048576 ≈ 0.3224`        | `1/2`  | `1/2`      | `2^-18`   | 35       |

(`K3_cr`, `K5_cr`, `K6_cr`.) In each case the binding condition is `r η ζ ≤ α (1 - u)`; the
root condition `2 Pm η ζ ≤ σ (1 - u)` has a factor of more than `50` to spare. The tolerances
are the largest powers of two for which some `α ≤ 1`, `u < 1` with `c r (1 + α) ≤ u` satisfy
`r η ζ ≤ α (1 - u)` (`K3_tolerance_sharp`, `K5_tolerance_sharp`, `K6_tolerance_sharp`).

* `Consts.price_search_approx_level_double`, `Consts.price_search_gain_level_double`: the general theorems
  of the two files with `2 r₀` probes at the root and rational `ζ`, `α`, `u`, so that all
  hypotheses are inequalities between rationals.
* `price_search_k3_approx_const`, `price_search_k5_approx_const`,
  `price_search_k6_approx_const`: approximately cleared markets.
* `price_search_k3_gain_const`, `price_search_k5_gain_const`, `price_search_k6_gain_const`:
  the aggregate gain condition.
* `price_search_k3_approx_const_total`, `price_search_k5_approx_const_total`,
  `price_search_k6_approx_const_total`: with the existence of a run against every labelling
  rule.
-/

set_option linter.unusedSectionVars false

namespace SPLP

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V]

namespace Consts

variable {k : ℕ}

/-- The root condition of `price_search_approx_level` for `2 r₀` probes at the root. -/
theorem root_double (K : Consts k) {ζ u : ℚ} (hu1 : u < 1)
    (hζ : 2 * K.Pm * K.η * ζ ≤ K.σ * (1 - u)) (r₀ : ℕ) :
    (K.Pm : ℝ) * (((2 * r₀ : ℕ) : ℝ) * ((K.η : ℝ) * (ζ : ℝ)) / (1 - (u : ℝ)))
      ≤ (K.σ : ℝ) * (((2 * r₀ : ℕ) : ℝ) - r₀) := by
  have hu1' : (0 : ℝ) < 1 - (u : ℝ) := by
    have : (u : ℝ) < 1 := by exact_mod_cast hu1
    linarith
  have hζ' : 2 * (K.Pm : ℝ) * (K.η : ℝ) * (ζ : ℝ) ≤ (K.σ : ℝ) * (1 - (u : ℝ)) := by
    exact_mod_cast hζ
  have h1 : 2 * (K.Pm : ℝ) * (K.η : ℝ) * (ζ : ℝ) / (1 - (u : ℝ)) ≤ (K.σ : ℝ) := by
    rw [div_le_iff₀ hu1']
    exact hζ'
  have h2 := mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg r₀ : (0 : ℝ) ≤ (r₀ : ℝ))
  push_cast
  calc (K.Pm : ℝ) * (2 * (r₀ : ℝ) * ((K.η : ℝ) * (ζ : ℝ)) / (1 - (u : ℝ)))
      = 2 * (K.Pm : ℝ) * (K.η : ℝ) * (ζ : ℝ) / (1 - (u : ℝ)) * (r₀ : ℝ) := by ring
    _ ≤ (K.σ : ℝ) * (r₀ : ℝ) := h2
    _ = (K.σ : ℝ) * (2 * (r₀ : ℝ) - r₀) := by ring

/-- **Approximate markets, constant tolerance, doubled root.** Let `ζ`, `α`, `u` be rationals
with `0 ≤ ζ`, `α ≤ 1`, `c r (1 + α) ≤ u < 1`, `r η ζ ≤ α (1 - u)` and
`2 Pm η ζ ≤ σ (1 - u)`. With `2 r₀` probes at the root, every run with approximately cleared
markets of tolerance `ζ` meets all demands of every consistent hypothesis and makes at most
`4 r₀ (2N)^e` label queries. -/
theorem price_search_approx_level_double (K : Consts k) (hK : K.Good) (e : ℕ)
    (he : ((K.r : ℚ)) ^ 2 ≤ (K.ρ ^ 2 / K.β) ^ e) [Nonempty ι] (val : V → ℝ) {ζ α u : ℚ}
    (hζ0 : 0 ≤ ζ) (hα1 : α ≤ 1) (hu : K.c * K.r * (1 + α) ≤ u) (hu1 : u < 1)
    (hζα : K.r * (K.η * ζ) ≤ α * (1 - u)) (hζ : 2 * K.Pm * K.η * ζ ≤ K.σ * (1 - u))
    (X : Exec ι (Expert ι V k (K.depth hK (Fintype.card ι)))) (hist₀ : ℕ → ι → ℝ)
    (hX : X.ValidWith (approxMarket val (ζ : ℝ))
      (K.algRoot ι V val (2 * K.r₀ ι V (K.depth hK (Fintype.card ι)))) 0 hist₀ (fun _ => 1)) :
    (∀ H : Hyp ι V, X.Consistent val H → ∀ s ∈ H.S, val (H.a s) ≤ sp X.x s) ∧
    X.queries ≤ 4 * K.r₀ ι V (K.depth hK (Fintype.card ι)) * (2 * Fintype.card ι) ^ e := by
  have h := K.price_search_approx_level hK e he val
    (2 * K.r₀ ι V (K.depth hK (Fintype.card ι))) (by omega)
    (ζ := (ζ : ℝ)) (α := (α : ℝ)) (u := (u : ℝ)) (by exact_mod_cast hζ0)
    (by exact_mod_cast hα1) (by exact_mod_cast hu) (by exact_mod_cast hu1)
    (by exact_mod_cast hζα) (K.root_double hu1 hζ _) X hist₀ hX
  refine ⟨h.1, h.2.trans (le_of_eq ?_)⟩
  ring

/-- **Gain condition, constant tolerance, doubled root.** As `price_search_approx_level_double`
for runs whose proposals satisfy the aggregate gain condition `gainMarket val ζ`. -/
theorem price_search_gain_level_double (K : Consts k) (hK : K.Good) (e : ℕ)
    (he : ((K.r : ℚ)) ^ 2 ≤ (K.ρ ^ 2 / K.β) ^ e) [Nonempty ι] (val : V → ℝ) {ζ α u : ℚ}
    (hζ0 : 0 ≤ ζ) (hα1 : α ≤ 1) (hu : K.c * K.r * (1 + α) ≤ u) (hu1 : u < 1)
    (hζα : K.r * (K.η * ζ) ≤ α * (1 - u)) (hζ : 2 * K.Pm * K.η * ζ ≤ K.σ * (1 - u))
    (X : Exec ι (Expert ι V k (K.depth hK (Fintype.card ι)))) (hist₀ : ℕ → ι → ℝ)
    (hX : X.ValidWith (gainMarket val (ζ : ℝ))
      (K.algRoot ι V val (2 * K.r₀ ι V (K.depth hK (Fintype.card ι)))) 0 hist₀ (fun _ => 1)) :
    (∀ H : Hyp ι V, X.Consistent val H → ∀ s ∈ H.S, val (H.a s) ≤ sp X.x s) ∧
    X.queries ≤ 4 * K.r₀ ι V (K.depth hK (Fintype.card ι)) * (2 * Fintype.card ι) ^ e := by
  have h := K.price_search_gain_level hK e he val
    (2 * K.r₀ ι V (K.depth hK (Fintype.card ι))) (by omega)
    (ζ := (ζ : ℝ)) (α := (α : ℝ)) (u := (u : ℝ)) (by exact_mod_cast hζ0)
    (by exact_mod_cast hα1) (by exact_mod_cast hu) (by exact_mod_cast hu1)
    (by exact_mod_cast hζα) (K.root_double hu1 hζ _) X hist₀ hX
  refine ⟨h.1, h.2.trans (le_of_eq ?_)⟩
  ring

end Consts

/-! ### The products `c · r` -/

theorem K3_cr : K3.c * K3.r = 30275 / 32768 := by norm_num [K3, Consts.c]

theorem K5_cr : K5.c * K5.r = 53425 / 65536 := by norm_num [K5, Consts.c]

theorem K6_cr : K6.c * K6.r = 338075 / 1048576 := by norm_num [K6, Consts.c]

/-! ### The numerical conditions -/

/-- Arity 3: `ζ = 2^-22`, `α = 1/25`, `u = 961/1000`. -/
theorem K3_level :
    K3.c * K3.r * (1 + 1 / 25) ≤ 961 / 1000 ∧
    K3.r * (K3.η * (1 / 2 ^ 22)) ≤ 1 / 25 * (1 - 961 / 1000) ∧
    2 * K3.Pm * K3.η * (1 / 2 ^ 22) ≤ K3.σ * (1 - 961 / 1000) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [K3, Consts.c, Consts.σ, Consts.ε, Consts.q, Consts.lp, Consts.lam, Consts.Pm]

/-- Arity 5: `ζ = 2^-21`, `α = 1/10`, `u = 9/10`. -/
theorem K5_level :
    K5.c * K5.r * (1 + 1 / 10) ≤ 9 / 10 ∧
    K5.r * (K5.η * (1 / 2 ^ 21)) ≤ 1 / 10 * (1 - 9 / 10) ∧
    2 * K5.Pm * K5.η * (1 / 2 ^ 21) ≤ K5.σ * (1 - 9 / 10) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [K5, Consts.c, Consts.σ, Consts.ε, Consts.q, Consts.lp, Consts.lam, Consts.Pm]

/-- Arity 6: `ζ = 2^-18`, `α = 1/2`, `u = 1/2`. -/
theorem K6_level :
    K6.c * K6.r * (1 + 1 / 2) ≤ 1 / 2 ∧
    K6.r * (K6.η * (1 / 2 ^ 18)) ≤ 1 / 2 * (1 - 1 / 2) ∧
    2 * K6.Pm * K6.η * (1 / 2 ^ 18) ≤ K6.σ * (1 - 1 / 2) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [K6, Consts.c, Consts.σ, Consts.ε, Consts.q, Consts.lp, Consts.lam, Consts.Pm]

/-! ### The tolerances cannot be doubled

For `c r (1 + α) ≤ u` the product `α (1 - u)` is at most `(1 - c r)² / (4 c r)`, so the
condition `r η ζ ≤ α (1 - u)` bounds `ζ` whatever `α` and `u` are. -/

/-- If `x (1 + α) ≤ u` with `0 < x` and `0 ≤ α` then `4 x α (1 - u) ≤ (1 - x)²`. -/
theorem alpha_gap_le {x α u : ℚ} (hx : 0 < x) (hα : 0 ≤ α) (hu : x * (1 + α) ≤ u) :
    4 * x * (α * (1 - u)) ≤ (1 - x) ^ 2 := by
  have h1 : α * (1 - u) ≤ α * (1 - x * (1 + α)) :=
    mul_le_mul_of_nonneg_left (by linarith) hα
  have h2 : 4 * x * (α * (1 - u)) ≤ 4 * x * (α * (1 - x * (1 + α))) :=
    mul_le_mul_of_nonneg_left h1 (by linarith)
  nlinarith [sq_nonneg (1 - x - 2 * x * α)]

/-- Arity 3: no `α ≥ 0`, `u` admit the tolerance `2^-21`. -/
theorem K3_tolerance_sharp {α u : ℚ} (hα : 0 ≤ α) (hu : K3.c * K3.r * (1 + α) ≤ u) :
    ¬ K3.r * (K3.η * (1 / 2 ^ 21)) ≤ α * (1 - u) := by
  intro h
  have h1 := alpha_gap_le (by rw [K3_cr]; norm_num) hα hu
  rw [K3_cr] at h1
  have h2 : (K3.r : ℚ) * (K3.η * (1 / 2 ^ 21)) = 1211 / 524288 := by norm_num [K3]
  rw [h2] at h
  nlinarith

/-- Arity 5: no `α ≥ 0`, `u` admit the tolerance `2^-20`. -/
theorem K5_tolerance_sharp {α u : ℚ} (hα : 0 ≤ α) (hu : K5.c * K5.r * (1 + α) ≤ u) :
    ¬ K5.r * (K5.η * (1 / 2 ^ 20)) ≤ α * (1 - u) := by
  intro h
  have h1 := alpha_gap_le (by rw [K5_cr]; norm_num) hα hu
  rw [K5_cr] at h1
  have h2 : (K5.r : ℚ) * (K5.η * (1 / 2 ^ 20)) = 53425 / 2883584 := by norm_num [K5]
  rw [h2] at h
  nlinarith

/-- Arity 6: no `0 ≤ α ≤ 1`, `u` admit the tolerance `2^-17`. (Here the constraint `α ≤ 1`
of `growthAt_zero_le_exp` is the binding one.) -/
theorem K6_tolerance_sharp {α u : ℚ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hu : K6.c * K6.r * (1 + α) ≤ u) :
    ¬ K6.r * (K6.η * (1 / 2 ^ 17)) ≤ α * (1 - u) := by
  intro h
  rw [K6_cr] at hu
  have h2 : (K6.r : ℚ) * (K6.η * (1 / 2 ^ 17)) = 338075 / 884736 := by norm_num [K6]
  rw [h2] at h
  nlinarith

/-! ### Arities 3, 5 and 6 -/

variable [Nonempty ι]

/-- **Arity 3 with a constant tolerance.** With `2 r₀` probes at the root, every run whose
proposals minimize the potential for weights within total distance `2^-22 · (total wealth)`
of the true wealth, and whose wealth is rounded to 41 significant bits after every update,
meets all demands of every consistent hypothesis and makes at most `4 r₀ (2N)^66` label
queries. -/
theorem price_search_k3_approx_const (val : V → ℝ)
    (X : Exec ι (Expert ι V 3 (K3.depth K3_good (Fintype.card ι)))) (hist₀ : ℕ → ι → ℝ)
    (hX : X.ValidWith (approxMarket val (1 / 2 ^ 22))
      (K3.algRoot ι V val (2 * K3.r₀ ι V (K3.depth K3_good (Fintype.card ι)))) 0 hist₀
      (fun _ => 1)) :
    (∀ H : Hyp ι V, X.Consistent val H → ∀ s ∈ H.S, val (H.a s) ≤ sp X.x s) ∧
    X.queries ≤ 4 * K3.r₀ ι V (K3.depth K3_good (Fintype.card ι))
      * (2 * Fintype.card ι) ^ 66 := by
  have hζ : (((1 / 2 ^ 22 : ℚ)) : ℝ) = 1 / 2 ^ 22 := by norm_num
  rw [← hζ] at hX
  exact K3.price_search_approx_level_double K3_good 66 K3_exp val (α := 1 / 25) (u := 961 / 1000)
    (by positivity) (by norm_num) K3_level.1 (by norm_num) K3_level.2.1 K3_level.2.2 X hist₀ hX

/-- **Arity 3 under the gain condition.** With `2 r₀` probes at the root, every run in which
at each proposal no feedback gives the market an aggregate gain above `2^-22` times its
wealth meets all demands of every consistent hypothesis and makes at most `4 r₀ (2N)^66`
label queries. -/
theorem price_search_k3_gain_const (val : V → ℝ)
    (X : Exec ι (Expert ι V 3 (K3.depth K3_good (Fintype.card ι)))) (hist₀ : ℕ → ι → ℝ)
    (hX : X.ValidWith (gainMarket val (1 / 2 ^ 22))
      (K3.algRoot ι V val (2 * K3.r₀ ι V (K3.depth K3_good (Fintype.card ι)))) 0 hist₀
      (fun _ => 1)) :
    (∀ H : Hyp ι V, X.Consistent val H → ∀ s ∈ H.S, val (H.a s) ≤ sp X.x s) ∧
    X.queries ≤ 4 * K3.r₀ ι V (K3.depth K3_good (Fintype.card ι))
      * (2 * Fintype.card ι) ^ 66 := by
  have hζ : (((1 / 2 ^ 22 : ℚ)) : ℝ) = 1 / 2 ^ 22 := by norm_num
  rw [← hζ] at hX
  exact K3.price_search_gain_level_double K3_good 66 K3_exp val (α := 1 / 25) (u := 961 / 1000)
    (by positivity) (by norm_num) K3_level.1 (by norm_num) K3_level.2.1 K3_level.2.2 X hist₀ hX

/-- **Arity 5 with a constant tolerance.** With `2 r₀` probes at the root, every run whose
proposals minimize the potential for weights within total distance `2^-21 · (total wealth)`
of the true wealth meets all demands of every consistent hypothesis and makes at most
`4 r₀ (2N)^39` label queries. -/
theorem price_search_k5_approx_const (val : V → ℝ)
    (X : Exec ι (Expert ι V 5 (K5.depth K5_good (Fintype.card ι)))) (hist₀ : ℕ → ι → ℝ)
    (hX : X.ValidWith (approxMarket val (1 / 2 ^ 21))
      (K5.algRoot ι V val (2 * K5.r₀ ι V (K5.depth K5_good (Fintype.card ι)))) 0 hist₀
      (fun _ => 1)) :
    (∀ H : Hyp ι V, X.Consistent val H → ∀ s ∈ H.S, val (H.a s) ≤ sp X.x s) ∧
    X.queries ≤ 4 * K5.r₀ ι V (K5.depth K5_good (Fintype.card ι))
      * (2 * Fintype.card ι) ^ 39 := by
  have hζ : (((1 / 2 ^ 21 : ℚ)) : ℝ) = 1 / 2 ^ 21 := by norm_num
  rw [← hζ] at hX
  exact K5.price_search_approx_level_double K5_good 39 K5_exp val (α := 1 / 10) (u := 9 / 10)
    (by positivity) (by norm_num) K5_level.1 (by norm_num) K5_level.2.1 K5_level.2.2 X hist₀ hX

/-- **Arity 5 under the gain condition.** Tolerance `2^-21`, at most `4 r₀ (2N)^39` label
queries. -/
theorem price_search_k5_gain_const (val : V → ℝ)
    (X : Exec ι (Expert ι V 5 (K5.depth K5_good (Fintype.card ι)))) (hist₀ : ℕ → ι → ℝ)
    (hX : X.ValidWith (gainMarket val (1 / 2 ^ 21))
      (K5.algRoot ι V val (2 * K5.r₀ ι V (K5.depth K5_good (Fintype.card ι)))) 0 hist₀
      (fun _ => 1)) :
    (∀ H : Hyp ι V, X.Consistent val H → ∀ s ∈ H.S, val (H.a s) ≤ sp X.x s) ∧
    X.queries ≤ 4 * K5.r₀ ι V (K5.depth K5_good (Fintype.card ι))
      * (2 * Fintype.card ι) ^ 39 := by
  have hζ : (((1 / 2 ^ 21 : ℚ)) : ℝ) = 1 / 2 ^ 21 := by norm_num
  rw [← hζ] at hX
  exact K5.price_search_gain_level_double K5_good 39 K5_exp val (α := 1 / 10) (u := 9 / 10)
    (by positivity) (by norm_num) K5_level.1 (by norm_num) K5_level.2.1 K5_level.2.2 X hist₀ hX

/-- **Arity 6 with a constant tolerance.** With `2 r₀` probes at the root, every run whose
proposals minimize the potential for weights within total distance `2^-18 · (total wealth)`
of the true wealth meets all demands of every consistent hypothesis and makes at most
`4 r₀ (2N)^35` label queries. -/
theorem price_search_k6_approx_const (val : V → ℝ)
    (X : Exec ι (Expert ι V 6 (K6.depth K6_good (Fintype.card ι)))) (hist₀ : ℕ → ι → ℝ)
    (hX : X.ValidWith (approxMarket val (1 / 2 ^ 18))
      (K6.algRoot ι V val (2 * K6.r₀ ι V (K6.depth K6_good (Fintype.card ι)))) 0 hist₀
      (fun _ => 1)) :
    (∀ H : Hyp ι V, X.Consistent val H → ∀ s ∈ H.S, val (H.a s) ≤ sp X.x s) ∧
    X.queries ≤ 4 * K6.r₀ ι V (K6.depth K6_good (Fintype.card ι))
      * (2 * Fintype.card ι) ^ 35 := by
  have hζ : (((1 / 2 ^ 18 : ℚ)) : ℝ) = 1 / 2 ^ 18 := by norm_num
  rw [← hζ] at hX
  exact K6.price_search_approx_level_double K6_good 35 K6_exp val (α := 1 / 2) (u := 1 / 2)
    (by positivity) (by norm_num) K6_level.1 (by norm_num) K6_level.2.1 K6_level.2.2 X hist₀ hX

/-- **Arity 6 under the gain condition.** Tolerance `2^-18`, at most `4 r₀ (2N)^35` label
queries. -/
theorem price_search_k6_gain_const (val : V → ℝ)
    (X : Exec ι (Expert ι V 6 (K6.depth K6_good (Fintype.card ι)))) (hist₀ : ℕ → ι → ℝ)
    (hX : X.ValidWith (gainMarket val (1 / 2 ^ 18))
      (K6.algRoot ι V val (2 * K6.r₀ ι V (K6.depth K6_good (Fintype.card ι)))) 0 hist₀
      (fun _ => 1)) :
    (∀ H : Hyp ι V, X.Consistent val H → ∀ s ∈ H.S, val (H.a s) ≤ sp X.x s) ∧
    X.queries ≤ 4 * K6.r₀ ι V (K6.depth K6_good (Fintype.card ι))
      * (2 * Fintype.card ι) ^ 35 := by
  have hζ : (((1 / 2 ^ 18 : ℚ)) : ℝ) = 1 / 2 ^ 18 := by norm_num
  rw [← hζ] at hX
  exact K6.price_search_gain_level_double K6_good 35 K6_exp val (α := 1 / 2) (u := 1 / 2)
    (by positivity) (by norm_num) K6_level.1 (by norm_num) K6_level.2.1 K6_level.2.2 X hist₀ hX

/-! ### End to end -/

variable [Nonempty V]

/-- **Arity 3 with a constant tolerance, end to end.** Let the root make `2 r₀` probes.
Against any rule answering label queries there is a run; **every** run in which each proposal
minimizes the potential for weights within total distance `2^-22 · (total wealth)` of the true
wealth returns prices meeting all demands of every hypothesis consistent with the labels it
received, and makes at most `4 r₀ (2N)^66` label queries. -/
theorem price_search_k3_approx_const_total (val : V → ℝ) (hist₀ : ℕ → ι → ℝ) :
    (∀ oracle : List ℕ → (ι → ℝ) → (ι → Bool),
      ∃ X : Exec ι (Expert ι V 3 (K3.depth K3_good (Fintype.card ι))),
        X.ValidWith (approxMarket val (1 / 2 ^ 22))
          (K3.algRoot ι V val (2 * K3.r₀ ι V (K3.depth K3_good (Fintype.card ι)))) 0 hist₀
          (fun _ => 1) ∧ X.LabelsFrom oracle []) ∧
    (∀ X : Exec ι (Expert ι V 3 (K3.depth K3_good (Fintype.card ι))),
      X.ValidWith (approxMarket val (1 / 2 ^ 22))
          (K3.algRoot ι V val (2 * K3.r₀ ι V (K3.depth K3_good (Fintype.card ι)))) 0 hist₀
          (fun _ => 1) →
        (∀ H : Hyp ι V, X.Consistent val H → ∀ s ∈ H.S, val (H.a s) ≤ sp X.x s) ∧
        X.queries ≤ 4 * K3.r₀ ι V (K3.depth K3_good (Fintype.card ι))
          * (2 * Fintype.card ι) ^ 66) :=
  ⟨fun oracle => K3.exists_approx_run K3_good (by norm_num) val _ (by positivity) oracle hist₀,
   fun X hX => price_search_k3_approx_const val X hist₀ hX⟩

/-- **Arity 5 with a constant tolerance, end to end.** Tolerance `2^-21`, at most
`4 r₀ (2N)^39` label queries. -/
theorem price_search_k5_approx_const_total (val : V → ℝ) (hist₀ : ℕ → ι → ℝ) :
    (∀ oracle : List ℕ → (ι → ℝ) → (ι → Bool),
      ∃ X : Exec ι (Expert ι V 5 (K5.depth K5_good (Fintype.card ι))),
        X.ValidWith (approxMarket val (1 / 2 ^ 21))
          (K5.algRoot ι V val (2 * K5.r₀ ι V (K5.depth K5_good (Fintype.card ι)))) 0 hist₀
          (fun _ => 1) ∧ X.LabelsFrom oracle []) ∧
    (∀ X : Exec ι (Expert ι V 5 (K5.depth K5_good (Fintype.card ι))),
      X.ValidWith (approxMarket val (1 / 2 ^ 21))
          (K5.algRoot ι V val (2 * K5.r₀ ι V (K5.depth K5_good (Fintype.card ι)))) 0 hist₀
          (fun _ => 1) →
        (∀ H : Hyp ι V, X.Consistent val H → ∀ s ∈ H.S, val (H.a s) ≤ sp X.x s) ∧
        X.queries ≤ 4 * K5.r₀ ι V (K5.depth K5_good (Fintype.card ι))
          * (2 * Fintype.card ι) ^ 39) :=
  ⟨fun oracle => K5.exists_approx_run K5_good (by norm_num) val _ (by positivity) oracle hist₀,
   fun X hX => price_search_k5_approx_const val X hist₀ hX⟩

/-- **Arity 6 with a constant tolerance, end to end.** Tolerance `2^-18`, at most
`4 r₀ (2N)^35` label queries. -/
theorem price_search_k6_approx_const_total (val : V → ℝ) (hist₀ : ℕ → ι → ℝ) :
    (∀ oracle : List ℕ → (ι → ℝ) → (ι → Bool),
      ∃ X : Exec ι (Expert ι V 6 (K6.depth K6_good (Fintype.card ι))),
        X.ValidWith (approxMarket val (1 / 2 ^ 18))
          (K6.algRoot ι V val (2 * K6.r₀ ι V (K6.depth K6_good (Fintype.card ι)))) 0 hist₀
          (fun _ => 1) ∧ X.LabelsFrom oracle []) ∧
    (∀ X : Exec ι (Expert ι V 6 (K6.depth K6_good (Fintype.card ι))),
      X.ValidWith (approxMarket val (1 / 2 ^ 18))
          (K6.algRoot ι V val (2 * K6.r₀ ι V (K6.depth K6_good (Fintype.card ι)))) 0 hist₀
          (fun _ => 1) →
        (∀ H : Hyp ι V, X.Consistent val H → ∀ s ∈ H.S, val (H.a s) ≤ sp X.x s) ∧
        X.queries ≤ 4 * K6.r₀ ι V (K6.depth K6_good (Fintype.card ι))
          * (2 * Fintype.card ι) ^ 35) :=
  ⟨fun oracle => K6.exists_approx_run K6_good (by norm_num) val _ (by positivity) oracle hist₀,
   fun X hX => price_search_k6_approx_const val X hist₀ hX⟩

end SPLP
