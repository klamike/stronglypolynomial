import Mathlib
import SPLP.Final

/-!
# Concrete constants

Four sets of constants, for experts guessing `k = 3`, `4`, `5` and `6` slots. Each is checked
by exact rational arithmetic. The preprint's choice (`k = 4`, `r = 2^19 + 1` probes per node,
depth `log_{5/4} 2N`) gives `(2N)^{59.02}` probes below the root; here the corresponding
exponents are `66`, `46`, `39` and `35`.
-/

namespace SPLP

/-- Arity `4` (the arity of the preprint). The algorithm uses `125800` probes per node,
investment share `c = 2^{-17}` and learning rate `η = 1/16` (the preprint: `2^19 + 1`,
`2^{-14}`, `1/16`). The remaining constants only enter the analysis: boost factor `β = 4`,
band `[γ, δ] = [2/11 - 1/200, 2/11]`, reserve masses `(25/4) · 12^{-i}`, transfer constant
`C = 1437`. -/
def K4 : Consts 4 where
  β := 4
  δ := 2 / 11
  γ := 389 / 2200
  η := 1 / 16
  θ := 1 / 12
  ω₀ := 25 / 4
  C := 1437
  a := 17
  r := 125800
  p := 40

theorem K4_good : K4.Good := by
  constructor <;>
    norm_num [K4, Consts.ρ, Consts.q, Consts.lp, Consts.lam, Consts.ε, Consts.Pm, Consts.c,
      Consts.cp, Consts.fee, Consts.ep, Consts.epp]

theorem K4_exp : ((K4.r : ℚ)) ^ 2 ≤ (K4.ρ ^ 2 / K4.β) ^ 46 := by
  norm_num [K4, Consts.ρ]

/-- Arity `3`: `β = 7/2`, `δ = 12/53`, `η = 1/25`, `c = 2^{-17}`, `121100` probes per
node. Fewer slots per expert, at the price of a larger exponent. -/
def K3 : Consts 3 where
  β := 7 / 2
  δ := 12 / 53
  γ := 3787 / 16960
  η := 1 / 25
  θ := 1 / 20
  ω₀ := 3
  C := 1191
  a := 17
  r := 121100
  p := 40

theorem K3_good : K3.Good := by
  constructor <;>
    norm_num [K3, Consts.ρ, Consts.q, Consts.lp, Consts.lam, Consts.ε, Consts.Pm, Consts.c,
      Consts.cp, Consts.fee, Consts.ep, Consts.epp]

theorem K3_exp : ((K3.r : ℚ)) ^ 2 ≤ (K3.ρ ^ 2 / K3.β) ^ 66 := by
  norm_num [K3, Consts.ρ]

/-- Arity `5`: `β = 9/2`, `δ = 2/13`, `η = 1/11`, `c = 2^{-18}`, `213700` probes per node. -/
def K5 : Consts 5 where
  β := 9 / 2
  δ := 2 / 13
  γ := 307 / 2080
  η := 1 / 11
  θ := 1 / 5
  ω₀ := 47 / 4
  C := 3132
  a := 18
  r := 213700
  p := 40

theorem K5_good : K5.Good := by
  constructor <;>
    norm_num [K5, Consts.ρ, Consts.q, Consts.lp, Consts.lam, Consts.ε, Consts.Pm, Consts.c,
      Consts.cp, Consts.fee, Consts.ep, Consts.epp]

theorem K5_exp : ((K5.r : ℚ)) ^ 2 ≤ (K5.ρ ^ 2 / K5.β) ^ 39 := by
  norm_num [K5, Consts.ρ]

/-- Arity `6`: `β = 11/2`, `δ = 1/8`, `η = 1/27`, `c = 2^{-22}`, `1352300` probes per
node. -/
def K6 : Consts 6 where
  β := 11 / 2
  δ := 1 / 8
  γ := 31 / 256
  η := 1 / 27
  θ := 1 / 4
  ω₀ := 35 / 2
  C := 27827
  a := 22
  r := 1352300
  p := 40

theorem K6_good : K6.Good := by
  constructor <;>
    norm_num [K6, Consts.ρ, Consts.q, Consts.lp, Consts.lam, Consts.ε, Consts.Pm, Consts.c,
      Consts.cp, Consts.fee, Consts.ep, Consts.epp]

theorem K6_exp : ((K6.r : ℚ)) ^ 2 ≤ (K6.ρ ^ 2 / K6.β) ^ 35 := by
  norm_num [K6, Consts.ρ]


/-! ### The resulting theorems -/

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V] [Nonempty ι]

/-- **Arity 4.** Every valid run meets all demands of every consistent hypothesis and makes at
most `2 r₀ (2N)^46` label queries. -/
theorem price_search_k4 (val : V → ℝ)
    (X : Exec ι (Expert ι V 4 (K4.depth K4_good (Fintype.card ι)))) (hist₀ : ℕ → ι → ℝ)
    (hX : X.Valid (K4.alg K4_good ι V val) 0 hist₀ (fun _ => 1)) :
    (∀ H : Hyp ι V, X.Consistent val H → ∀ s ∈ H.S, val (H.a s) ≤ sp X.x s) ∧
    X.queries ≤ 2 * K4.r₀ ι V (K4.depth K4_good (Fintype.card ι)) * (2 * Fintype.card ι) ^ 46 :=
  K4.price_search K4_good 46 K4_exp val X hist₀ hX

/-- **Arity 3.** At most `2 r₀ (2N)^66` label queries. -/
theorem price_search_k3 (val : V → ℝ)
    (X : Exec ι (Expert ι V 3 (K3.depth K3_good (Fintype.card ι)))) (hist₀ : ℕ → ι → ℝ)
    (hX : X.Valid (K3.alg K3_good ι V val) 0 hist₀ (fun _ => 1)) :
    (∀ H : Hyp ι V, X.Consistent val H → ∀ s ∈ H.S, val (H.a s) ≤ sp X.x s) ∧
    X.queries ≤ 2 * K3.r₀ ι V (K3.depth K3_good (Fintype.card ι)) * (2 * Fintype.card ι) ^ 66 :=
  K3.price_search K3_good 66 K3_exp val X hist₀ hX

/-- **Arity 5.** At most `2 r₀ (2N)^39` label queries. -/
theorem price_search_k5 (val : V → ℝ)
    (X : Exec ι (Expert ι V 5 (K5.depth K5_good (Fintype.card ι)))) (hist₀ : ℕ → ι → ℝ)
    (hX : X.Valid (K5.alg K5_good ι V val) 0 hist₀ (fun _ => 1)) :
    (∀ H : Hyp ι V, X.Consistent val H → ∀ s ∈ H.S, val (H.a s) ≤ sp X.x s) ∧
    X.queries ≤ 2 * K5.r₀ ι V (K5.depth K5_good (Fintype.card ι)) * (2 * Fintype.card ι) ^ 39 :=
  K5.price_search K5_good 39 K5_exp val X hist₀ hX

/-- **Arity 6.** At most `2 r₀ (2N)^35` label queries. -/
theorem price_search_k6 (val : V → ℝ)
    (X : Exec ι (Expert ι V 6 (K6.depth K6_good (Fintype.card ι)))) (hist₀ : ℕ → ι → ℝ)
    (hX : X.Valid (K6.alg K6_good ι V val) 0 hist₀ (fun _ => 1)) :
    (∀ H : Hyp ι V, X.Consistent val H → ∀ s ∈ H.S, val (H.a s) ≤ sp X.x s) ∧
    X.queries ≤ 2 * K6.r₀ ι V (K6.depth K6_good (Fintype.card ι)) * (2 * Fintype.card ι) ^ 35 :=
  K6.price_search K6_good 35 K6_exp val X hist₀ hX

/-! ### The preprint's constants, for comparison

The preprint uses `r = 2^19 + 1` probes per node and a depth `D` with `(5/4)^D ≈ 2N`, hence
`r^(D-1) ≈ (2N)^(log_{5/4} r)` probes below the root. The exponent lies strictly between
`59` and `60`. -/

theorem preprint_exponent : ((5 : ℚ) / 4) ^ 59 < 2 ^ 19 + 1 ∧ (2 ^ 19 + 1 : ℚ) < (5 / 4) ^ 60 := by
  constructor <;> norm_num

end SPLP
