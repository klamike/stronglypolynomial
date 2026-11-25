import Mathlib
import SPLP.Main
import SPLP.Float

/-!
# Rational constants

`Consts k` is a finite list of rational constants for experts of arity `k`; `Consts.Good` is a
list of inequalities between explicit rational expressions in them. `Consts.toParams` shows
that good constants give valid analysis parameters `Params` on every instance, with the number
of root probes chosen from the size of the expert pool. All logarithms are discharged here by
elementary bounds, so checking an instance is rational arithmetic.
-/

set_option linter.unusedSectionVars false

namespace SPLP

open Finset

/-! ### Elementary bounds on logarithms -/

theorem log_one_add_ge {η : ℝ} (h0 : 0 < η) (h1 : η < 1) :
    η - η ^ 2 / 2 + η ^ 3 / 3 - η ^ 4 / (1 - η) ≤ Real.log (1 + η) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -η)
    (by rw [abs_neg, abs_of_pos h0]; exact h1) 3
  rw [abs_neg, abs_of_pos h0] at h
  have h' := (abs_le.1 h).1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, sub_neg_eq_add] at h'
  norm_num at h'
  linarith

theorem log_one_sub_ge {η : ℝ} (h0 : 0 < η) (h1 : η < 1) :
    -(η + η ^ 2 / 2 + η ^ 3 / 3 + η ^ 4 / (1 - η)) ≤ Real.log (1 - η) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := η)
    (by rw [abs_of_pos h0]; exact h1) 3
  rw [abs_of_pos h0] at h
  have h' := (abs_le.1 h).1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h'
  norm_num at h'
  linarith

theorem log_one_sub_ge' {c : ℝ} (h1 : c < 1) :
    -(c / (1 - c)) ≤ Real.log (1 - c) := by
  have h := Real.one_sub_inv_le_log_of_pos (x := 1 - c) (by linarith)
  have hc : (1 : ℝ) - (1 - c)⁻¹ = -(c / (1 - c)) := by
    have : (1 - c) ≠ 0 := by linarith
    field_simp
    ring
  linarith

theorem geom_sum_le_inv {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (n : ℕ) :
    ∑ i ∈ range n, θ ^ i ≤ 1 / (1 - θ) := by
  have hpos : 0 < 1 - θ := by linarith
  rw [le_div_iff₀ hpos]
  have h := geom_sum_mul θ n
  have h2 : (∑ i ∈ range n, θ ^ i) * (1 - θ) = 1 - θ ^ n := by
    have : (∑ i ∈ range n, θ ^ i) * (1 - θ) = -((∑ i ∈ range n, θ ^ i) * (θ - 1)) := by ring
    rw [this, h]; ring
  rw [h2]
  linarith [pow_nonneg h0 n]

/-! ### Constants -/

/-- Rational constants for the price search with experts of arity `k`: boost factor `β`,
band `[γ, δ]`, learning rate `η`, reserve masses `ω₀ θ^i`, transfer constant `C`,
investment share `2^{-a}`, `r` probes per internal node, and rounding precision `p`. -/
structure Consts (k : ℕ) where
  β : ℚ
  δ : ℚ
  γ : ℚ
  η : ℚ
  θ : ℚ
  ω₀ : ℚ
  C : ℚ
  a : ℕ
  r : ℕ
  /-- Wealth is rounded down to `p + 1` significant bits after every update. -/
  p : ℕ

namespace Consts

variable {k : ℕ} (K : Consts k)

/-- Largest growth factor of a slot's mass in one level. -/
def ρ : ℚ := K.β / (1 + (K.β - 1) * K.δ)
/-- Probability that `k` draws hit a set of mass `γ`. -/
def q : ℚ := 1 - (1 - K.γ) ^ k
/-- Lower bound for `log (1 + η)`. -/
def lp : ℚ := K.η - K.η ^ 2 / 2 + K.η ^ 3 / 3 - K.η ^ 4 / (1 - K.η)
/-- Upper bound for `-log (1 - η)`. -/
def lam : ℚ := K.η + K.η ^ 2 / 2 + K.η ^ 3 / 3 + K.η ^ 4 / (1 - K.η)
/-- Average log gain of a heavy probe. -/
def ε : ℚ := K.q * K.lp - (1 - K.q) * K.lam
/-- Total weight of a node. -/
def Pm : ℚ := 1 + K.ω₀ / (1 - K.θ)
/-- Investment share. -/
def c : ℚ := 1 / 2 ^ K.a
/-- Upper bound for `-log (1 - c)`. -/
def cp : ℚ := K.c / (1 - K.c)
/-- Upper bound for `-log κ`, with `κ = c / (1 + η)` and `log 2 < 0.6931471808`. -/
def fee : ℚ := K.a * (6931471808 / 10000000000) + K.η
/-- Relative rounding error of the wealth updates. -/
def ep : ℚ := 1 / 2 ^ K.p
/-- Upper bound for `-log (1 - ep)`. -/
def epp : ℚ := K.ep / (1 - K.ep)
/-- Bonus per probe of a failed node. -/
def σ : ℚ := K.C * (K.ε + K.lam) / K.r

/-- The inequalities between rational expressions that make the constants usable. -/
structure Good (K : Consts k) : Prop where
  hβ : 1 < K.β
  hγ0 : 0 ≤ K.γ
  hγδ : K.γ < K.δ
  hδ1 : K.δ ≤ 1
  hη0 : 0 < K.η
  hη1 : K.η < 1
  hθ0 : 0 < K.θ
  hθ1 : K.θ < 1
  hω₀ : 0 < K.ω₀
  ha : 1 ≤ K.a
  hC1 : K.ρ ^ k ≤ K.C
  hC2 : K.ρ ^ k ≤ K.C * ((K.δ - K.γ) * K.ω₀)
  hC3 : K.ρ ^ (k + 1) ≤ K.C * K.θ
  hε : 0 < K.ε
  hmain : K.Pm * K.fee + K.C * (K.ε + K.lam) ≤ K.r * (K.ε / 2 - K.Pm * (K.cp + K.epp))
  hp : 1 ≤ K.p
  /-- The per-level growth `ρ²/β` of the boosting potential exceeds one. -/
  hb : 1 < K.ρ ^ 2 / K.β
  hr : 2 ≤ K.r

section Facts

variable {K} (hK : K.Good)
include hK

theorem den_pos : 0 < 1 + (K.β - 1) * K.δ := by
  have := hK.hβ; have := hK.hγ0; have := hK.hγδ; nlinarith

theorem ρ_pos : 0 < K.ρ := div_pos (by linarith [hK.hβ]) (den_pos hK)

theorem C_pos : 0 < K.C := lt_of_lt_of_le (pow_pos (ρ_pos hK) k) hK.hC1

theorem lam_pos : 0 < K.lam := by
  have h0 := hK.hη0; have h1 := hK.hη1
  have : 0 < K.η ^ 4 / (1 - K.η) := div_pos (by positivity) (by linarith)
  unfold lam; positivity

theorem Pm_pos : 0 < K.Pm := by
  have : 0 < K.ω₀ / (1 - K.θ) := div_pos hK.hω₀ (by linarith [hK.hθ1])
  unfold Pm; linarith

theorem c_pos : 0 < K.c := by unfold c; positivity

theorem c_lt_one : K.c < 1 := by
  unfold c
  have h2 : (1 : ℚ) < 2 ^ K.a := one_lt_pow₀ (by norm_num) (by have := hK.ha; omega)
  rw [div_lt_one (by positivity)]
  exact h2

theorem cp_nonneg : 0 ≤ K.cp :=
  div_nonneg (c_pos hK).le (by linarith [c_lt_one hK])

theorem ep_pos : 0 < K.ep := by unfold ep; positivity

theorem ep_lt_one : K.ep < 1 := by
  unfold ep
  have h2 : (1 : ℚ) < 2 ^ K.p := one_lt_pow₀ (by norm_num) (by have := hK.hp; omega)
  rw [div_lt_one (by positivity)]
  exact h2

theorem epp_nonneg : 0 ≤ K.epp :=
  div_nonneg (ep_pos hK).le (by linarith [ep_lt_one hK])

theorem fee_nonneg : 0 ≤ K.fee := by
  unfold fee
  have := hK.hη0
  positivity

theorem r_pos : 0 < (K.r : ℚ) := by
  have hmain := hK.hmain
  have h1 : 0 < K.Pm * K.fee + K.C * (K.ε + K.lam) :=
    add_pos_of_nonneg_of_pos (mul_nonneg (Pm_pos hK).le (fee_nonneg hK))
      (mul_pos (C_pos hK) (add_pos hK.hε (lam_pos hK)))
  by_contra hcon
  have hr : (K.r : ℚ) = 0 := le_antisymm (not_lt.1 hcon) (Nat.cast_nonneg _)
  rw [hr, zero_mul] at hmain
  linarith

theorem σ_pos : 0 < K.σ :=
  div_pos (mul_pos (C_pos hK) (add_pos hK.hε (lam_pos hK))) (r_pos hK)

theorem σ_mul_r : K.σ * K.r = K.C * (K.ε + K.lam) := by
  unfold σ
  exact div_mul_cancel₀ _ (r_pos hK).ne'

/-- The slack left after paying `σ` and the investment loss per probe covers the entry fee,
for every number of probes `T ≥ r`. -/
theorem slack {T : ℚ} (hT : (K.r : ℚ) ≤ T) :
    K.σ * T + K.Pm * K.fee + K.Pm * T * (K.cp + K.epp) ≤ K.ε * T / 2 := by
  have hmain := hK.hmain
  have hσr := σ_mul_r hK
  have hfee : 0 ≤ K.Pm * K.fee := mul_nonneg (Pm_pos hK).le (fee_nonneg hK)
  have hr := r_pos hK
  have hcoef : 0 ≤ K.ε / 2 - K.Pm * (K.cp + K.epp) - K.σ := by
    by_contra hcon
    rw [not_le] at hcon
    nlinarith
  nlinarith

end Facts


/-! ### From constants to parameters -/

section Real

variable {K} (hK : K.Good)
include hK

theorem η_pos_real : (0 : ℝ) < K.η := by exact_mod_cast hK.hη0
theorem η_lt_one_real : (K.η : ℝ) < 1 := by exact_mod_cast hK.hη1
theorem c_pos_real : (0 : ℝ) < K.c := by exact_mod_cast c_pos hK
theorem c_lt_one_real : (K.c : ℝ) < 1 := by exact_mod_cast c_lt_one hK
theorem σ_pos_real : (0 : ℝ) < K.σ := by exact_mod_cast σ_pos hK
theorem ep_pos_real : (0 : ℝ) < K.ep := by exact_mod_cast ep_pos hK
theorem ep_lt_one_real : (K.ep : ℝ) < 1 := by exact_mod_cast ep_lt_one hK
theorem Pm_pos_real : (0 : ℝ) < K.Pm := by exact_mod_cast Pm_pos hK

theorem hε_real : (K.ε : ℝ) ≤ (1 - (1 - (K.γ : ℝ)) ^ k) * Real.log (1 + (K.η : ℝ))
    + (1 - (K.γ : ℝ)) ^ k * Real.log (1 - (K.η : ℝ)) := by
  have hη0 := η_pos_real hK
  have hη1 := η_lt_one_real hK
  have h1 := log_one_add_ge hη0 hη1
  have h2 := log_one_sub_ge hη0 hη1
  have hγ0 : (0 : ℝ) ≤ K.γ := by exact_mod_cast hK.hγ0
  have hγ1 : (K.γ : ℝ) ≤ 1 := by exact_mod_cast (hK.hγδ.le.trans hK.hδ1)
  have hp0 : 0 ≤ (1 - (K.γ : ℝ)) ^ k := pow_nonneg (by linarith) k
  have hp1 : (1 - (K.γ : ℝ)) ^ k ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hε : (K.ε : ℝ) = (1 - (1 - (K.γ : ℝ)) ^ k)
        * ((K.η : ℝ) - (K.η : ℝ) ^ 2 / 2 + (K.η : ℝ) ^ 3 / 3 - (K.η : ℝ) ^ 4 / (1 - (K.η : ℝ)))
      - (1 - (K.γ : ℝ)) ^ k
        * ((K.η : ℝ) + (K.η : ℝ) ^ 2 / 2 + (K.η : ℝ) ^ 3 / 3
            + (K.η : ℝ) ^ 4 / (1 - (K.η : ℝ))) := by
    simp only [Consts.ε, Consts.q, Consts.lp, Consts.lam]
    push_cast
    ring
  rw [hε]
  have h3 := mul_le_mul_of_nonneg_left h1 (sub_nonneg.2 hp1)
  have h4 := mul_le_mul_of_nonneg_left h2 hp0
  linarith

theorem hlam_real : -(K.lam : ℝ) ≤ Real.log (1 - (K.η : ℝ)) := by
  have h2 := log_one_sub_ge (η_pos_real hK) (η_lt_one_real hK)
  have hl : (K.lam : ℝ) = (K.η : ℝ) + (K.η : ℝ) ^ 2 / 2 + (K.η : ℝ) ^ 3 / 3
      + (K.η : ℝ) ^ 4 / (1 - (K.η : ℝ)) := by
    simp only [Consts.lam]
    push_cast
    ring
  rw [hl]
  exact h2

end Real

/-- Bonus scale `κ = c / (1 + η)`. -/
noncomputable def κ (K : Consts k) : ℝ := (K.c : ℝ) / (1 + (K.η : ℝ))

section Kappa

variable {K} (hK : K.Good)
include hK

theorem κ_pos : 0 < K.κ :=
  div_pos (c_pos_real hK) (by linarith [η_pos_real hK])

theorem κ_le_one : K.κ ≤ 1 := by
  unfold κ
  rw [div_le_one (by linarith [η_pos_real hK])]
  linarith [c_lt_one_real hK, η_pos_real hK]

theorem κ_mul : K.κ * (1 - (K.c : ℝ)) * (1 + (K.η : ℝ)) ≤ (K.c : ℝ) := by
  have h1 : K.κ * (1 + (K.η : ℝ)) = (K.c : ℝ) :=
    div_mul_cancel₀ _ (by linarith [η_pos_real hK])
  have hc0 := c_pos_real hK
  have hc1 := c_lt_one_real hK
  calc K.κ * (1 - (K.c : ℝ)) * (1 + (K.η : ℝ))
      = (K.κ * (1 + (K.η : ℝ))) * (1 - (K.c : ℝ)) := by ring
    _ = (K.c : ℝ) * (1 - (K.c : ℝ)) := by rw [h1]
    _ ≤ (K.c : ℝ) := by nlinarith

theorem log_κ_ge : -(K.fee : ℝ) ≤ Real.log K.κ := by
  have hη0 := η_pos_real hK
  have hc : (K.c : ℝ) = 1 / 2 ^ K.a := by
    simp only [Consts.c]
    push_cast
    ring
  have hlogc : Real.log (K.c : ℝ) = -(K.a * Real.log 2) := by
    rw [hc, one_div, Real.log_inv, Real.log_pow]
  have hlog1 : Real.log (1 + (K.η : ℝ)) ≤ (K.η : ℝ) := by
    have := Real.log_le_sub_one_of_pos (x := 1 + (K.η : ℝ)) (by linarith)
    linarith
  have hκ : Real.log K.κ = Real.log (K.c : ℝ) - Real.log (1 + (K.η : ℝ)) := by
    unfold κ
    rw [Real.log_div (c_pos_real hK).ne' (by linarith)]
  have hfee : (K.fee : ℝ) = K.a * (6931471808 / 10000000000) + (K.η : ℝ) := by
    simp only [Consts.fee]
    push_cast
    ring
  have hl2 : Real.log 2 < 6931471808 / 10000000000 := by
    have := Real.log_two_lt_d9
    norm_num at this ⊢
    linarith
  have ha : (0 : ℝ) ≤ K.a := Nat.cast_nonneg _
  rw [hκ, hlogc, hfee]
  nlinarith [mul_le_mul_of_nonneg_left hl2.le ha]

theorem log_c_ge : -(K.cp : ℝ) ≤ Real.log (1 - (K.c : ℝ)) := by
  have h := log_one_sub_ge' (c_lt_one_real hK)
  have hcp : (K.cp : ℝ) = (K.c : ℝ) / (1 - (K.c : ℝ)) := by
    simp only [Consts.cp]
    push_cast
    ring
  rw [hcp]
  exact h

theorem log_ep_ge : -(K.epp : ℝ) ≤ Real.log (1 - (K.ep : ℝ)) := by
  have h := log_one_sub_ge' (ep_lt_one_real hK)
  have hepp : (K.epp : ℝ) = (K.ep : ℝ) / (1 - (K.ep : ℝ)) := by
    simp only [Consts.epp]
    push_cast
    ring
  rw [hepp]
  exact h

theorem hR2_real (T : ℕ) (hT : K.r ≤ T) :
    (K.σ : ℝ) * T ≤ (K.ε : ℝ) * T / 2
      + (K.Pm : ℝ) * (Real.log K.κ
          + T * (Real.log (1 - (K.c : ℝ)) + Real.log (1 - (K.ep : ℝ)))) := by
  have hs := slack hK (T := (T : ℚ)) (by exact_mod_cast hT)
  have hs' : (K.σ : ℝ) * T + (K.Pm : ℝ) * (K.fee : ℝ)
      + (K.Pm : ℝ) * T * ((K.cp : ℝ) + (K.epp : ℝ)) ≤ (K.ε : ℝ) * T / 2 := by
    exact_mod_cast hs
  have h1 := log_κ_ge hK
  have h2 := log_c_ge hK
  have h2' := log_ep_ge hK
  have hPm := (Pm_pos_real hK).le
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  have h3 := mul_le_mul_of_nonneg_left h1 hPm
  have h4 := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (add_le_add h2 h2') hT0) hPm
  nlinarith

end Kappa

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V]

/-- Number of probes at the root: at least `r`, and large enough that the root cannot fail
(logarithmic in the size of the expert pool). -/
noncomputable def r₀ (K : Consts k) (ι V : Type*) [Fintype ι] [DecidableEq ι] [Fintype V]
    (D : ℕ) : ℕ :=
  max K.r (⌊(K.Pm : ℝ) * Real.log (1 + K.κ * Fintype.card (Expert ι V k D)) / (K.σ : ℝ)⌋₊ + 1)

theorem hroot_real {K : Consts k} (hK : K.Good) (D : ℕ) :
    (K.Pm : ℝ) * Real.log (1 + K.κ * Fintype.card (Expert ι V k D))
      < (K.σ : ℝ) * (K.r₀ ι V D : ℝ) := by
  have hσ := σ_pos_real hK
  have h1 := Nat.lt_floor_add_one
    ((K.Pm : ℝ) * Real.log (1 + K.κ * Fintype.card (Expert ι V k D)) / (K.σ : ℝ))
  have h2 : ((⌊(K.Pm : ℝ) * Real.log (1 + K.κ * Fintype.card (Expert ι V k D))
      / (K.σ : ℝ)⌋₊ + 1 : ℕ) : ℝ) ≤ (K.r₀ ι V D : ℝ) := by
    exact_mod_cast le_max_right _ _
  push_cast at h2
  have h3 : (K.Pm : ℝ) * Real.log (1 + K.κ * Fintype.card (Expert ι V k D)) / (K.σ : ℝ)
      < (K.r₀ ι V D : ℝ) := lt_of_lt_of_le h1 h2
  rw [div_lt_iff₀ hσ] at h3
  linarith

/-- **Good constants give valid parameters**, for every index type, demand type, valuation
and every depth `D` with `(2N)² < (ρ²/β)^D`. -/
noncomputable def toParams (K : Consts k) (hK : K.Good) (val : V → ℝ) (D : ℕ)
    (hD : ((Fintype.card (Slot ι) : ℝ)) ^ 2 < ((K.ρ : ℝ) ^ 2 / (K.β : ℝ)) ^ D) :
    Params ι V k D where
  A := { val := val, r := K.r, r₀ := K.r₀ ι V D, c := (K.c : ℝ), η := (K.η : ℝ),
         rnd := fl K.p }
  β := K.β
  δ := K.δ
  γ := K.γ
  ρ := K.ρ
  ω := fun i => (K.ω₀ : ℝ) * (K.θ : ℝ) ^ i
  Pm := K.Pm
  C := K.C
  σ := K.σ
  ε := K.ε
  lam := K.lam
  κ := K.κ
  ep := K.ep
  hβ := by exact_mod_cast hK.hβ
  hγ0 := by exact_mod_cast hK.hγ0
  hγδ := by exact_mod_cast hK.hγδ
  hδ1 := by exact_mod_cast hK.hδ1
  hρ := by
    have h : K.ρ * (1 + (K.β - 1) * K.δ) = K.β := div_mul_cancel₀ _ (den_pos hK).ne'
    exact_mod_cast h
  hdepth := hD
  hc0 := c_pos_real hK
  hc1 := c_lt_one_real hK
  hη0 := η_pos_real hK
  hη1 := η_lt_one_real hK
  hω := fun i => mul_nonneg (by exact_mod_cast hK.hω₀.le)
    (pow_nonneg (by exact_mod_cast hK.hθ0.le) i)
  hPm := by
    intro n
    have hθ0 : (0 : ℝ) ≤ K.θ := by exact_mod_cast hK.hθ0.le
    have hθ1 : (K.θ : ℝ) < 1 := by exact_mod_cast hK.hθ1
    have hω : (0 : ℝ) ≤ K.ω₀ := by exact_mod_cast hK.hω₀.le
    have hg := mul_le_mul_of_nonneg_left (geom_sum_le_inv hθ0 hθ1 n) hω
    have hPm : (K.Pm : ℝ) = 1 + (K.ω₀ : ℝ) * (1 / (1 - (K.θ : ℝ))) := by
      simp only [Consts.Pm]
      push_cast
      ring
    rw [← Finset.mul_sum, hPm]
    linarith
  hC1 := by exact_mod_cast hK.hC1
  hC2 := by
    have h := hK.hC2
    simp only [pow_zero, mul_one]
    exact_mod_cast h
  hC3 := by
    intro i
    have h : (K.ρ : ℝ) ^ (k + 1) ≤ (K.C : ℝ) * (K.θ : ℝ) := by exact_mod_cast hK.hC3
    have hnn : (0 : ℝ) ≤ (K.ω₀ : ℝ) * (K.θ : ℝ) ^ i :=
      mul_nonneg (by exact_mod_cast hK.hω₀.le) (pow_nonneg (by exact_mod_cast hK.hθ0.le) i)
    calc (K.ρ : ℝ) ^ (k + 1) * ((K.ω₀ : ℝ) * (K.θ : ℝ) ^ i)
        ≤ ((K.C : ℝ) * (K.θ : ℝ)) * ((K.ω₀ : ℝ) * (K.θ : ℝ) ^ i) :=
          mul_le_mul_of_nonneg_right h hnn
      _ = (K.C : ℝ) * ((K.ω₀ : ℝ) * (K.θ : ℝ) ^ (i + 1)) := by ring
  hε0 := by exact_mod_cast hK.hε.le
  hε := hε_real hK
  hlam := hlam_real hK
  hκ0 := κ_pos hK
  hκ1 := κ_le_one hK
  hκc := κ_mul hK
  hep0 := (ep_pos_real hK).le
  hep1 := ep_lt_one_real hK
  hrnd := by
    intro x hx
    have hep : (K.ep : ℝ) = 1 / (2 : ℝ) ^ K.p := by
      simp only [Consts.ep]
      push_cast
      ring
    refine ⟨?_, fl_le K.p hx⟩
    rw [hep]
    exact fl_ge K.p hx
  hR1 := by
    have h := σ_mul_r hK
    have h' : (K.σ : ℝ) * (K.r : ℝ) = (K.C : ℝ) * ((K.ε : ℝ) + (K.lam : ℝ)) := by
      exact_mod_cast h
    exact h'.ge
  hR2 := by
    intro T hT
    rcases hT with rfl | rfl
    · exact hR2_real hK _ le_rfl
    · exact hR2_real hK _ (le_max_left _ _)
  hroot := hroot_real hK D

end Consts

end SPLP
