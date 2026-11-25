import Mathlib
import SPLP.Count

/-!
# The price-search theorem with explicit constants

For good constants `K : Consts k` and an integer `e` with `r ≤ (ρ/√β)^e`, every valid run on
`N` coordinates meets all demands of every consistent hypothesis and makes at most
`2 r₀ (2N)^e` label queries, where `r₀ ≤ r + 1 + (Pm/σ) log (1 + |E|)` and `E` is the expert
pool.
-/

set_option linter.unusedSectionVars false

namespace SPLP

open Finset

variable {k : ℕ}

namespace Consts

theorem b_real (K : Consts k) (hK : K.Good) : (1 : ℝ) < (K.ρ : ℝ) ^ 2 / (K.β : ℝ) := by
  exact_mod_cast hK.hb

/-- The depth of the recursion for `N` coordinates: the least `D` with
`(2N)² < (ρ²/β)^D`. -/
noncomputable def depth (K : Consts k) (hK : K.Good) (N : ℕ) : ℕ :=
  SPLP.depth (K.b_real hK) (2 * N)

end Consts

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V]

theorem card_slot (ι : Type*) [Fintype ι] : Fintype.card (Slot ι) = 2 * Fintype.card ι := by
  simp [Slot, Fintype.card_prod, mul_comm]

/-- Size of the expert pool. -/
theorem card_expert (ι V : Type*) [Fintype ι] [DecidableEq ι] [Fintype V] (k D : ℕ) :
    Fintype.card (Expert ι V k D)
      = (2 * Fintype.card ι) ^ k * Fintype.card V ^ k
        * (D * ((2 * Fintype.card ι) * Fintype.card V) + 1) := by
  simp [Expert, Slot, Fintype.card_prod, Fintype.card_option, mul_comm]
  ring

namespace Consts

/-- The analysis parameters attached to good constants on a given instance. -/
noncomputable def params (K : Consts k) (hK : K.Good) (ι V : Type*) [Fintype ι]
    [DecidableEq ι] [Fintype V] (val : V → ℝ) :
    Params ι V k (K.depth hK (Fintype.card ι)) :=
  K.toParams hK val _ (by
    rw [card_slot]
    exact depth_spec (K.b_real hK) (2 * Fintype.card ι))

/-- The algorithm (probe counts, investment share, learning rate) attached to good
constants on a given instance. -/
noncomputable def alg (K : Consts k) (hK : K.Good) (ι V : Type*) [Fintype ι]
    [DecidableEq ι] [Fintype V] (val : V → ℝ) : Alg V :=
  (K.params hK ι V val).A

theorem r₀_le (K : Consts k) (hK : K.Good) (ι V : Type*) [Fintype ι] [DecidableEq ι]
    [Fintype V] (D : ℕ) :
    (K.r₀ ι V D : ℝ) ≤ K.r + 1
      + ((K.Pm : ℝ) / (K.σ : ℝ)) * Real.log (1 + Fintype.card (Expert ι V k D)) := by
  have hσ := σ_pos_real hK
  have hPm := Pm_pos_real hK
  have hκ0 := κ_pos hK
  have hκ1 := κ_le_one hK
  have hE : (0 : ℝ) ≤ Fintype.card (Expert ι V k D) := Nat.cast_nonneg _
  have hlog : Real.log (1 + K.κ * Fintype.card (Expert ι V k D))
      ≤ Real.log (1 + Fintype.card (Expert ι V k D)) := by
    apply Real.log_le_log
    · nlinarith
    · nlinarith
  have hlog0 : 0 ≤ Real.log (1 + K.κ * Fintype.card (Expert ι V k D)) :=
    Real.log_nonneg (by nlinarith)
  have hx0 : 0 ≤ (K.Pm : ℝ) * Real.log (1 + K.κ * Fintype.card (Expert ι V k D))
      / (K.σ : ℝ) := div_nonneg (mul_nonneg hPm.le hlog0) hσ.le
  have hfloor := Nat.floor_le hx0
  have hmax : (K.r₀ ι V D : ℝ) ≤ K.r
      + (⌊(K.Pm : ℝ) * Real.log (1 + K.κ * Fintype.card (Expert ι V k D))
          / (K.σ : ℝ)⌋₊ + 1 : ℕ) := by
    have : K.r₀ ι V D ≤ K.r
        + (⌊(K.Pm : ℝ) * Real.log (1 + K.κ * Fintype.card (Expert ι V k D))
            / (K.σ : ℝ)⌋₊ + 1) := by
      unfold r₀
      exact max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
    exact_mod_cast this
  push_cast at hmax
  have hmono : (K.Pm : ℝ) * Real.log (1 + K.κ * Fintype.card (Expert ι V k D)) / (K.σ : ℝ)
      ≤ ((K.Pm : ℝ) / (K.σ : ℝ)) * Real.log (1 + Fintype.card (Expert ι V k D)) := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog hPm.le) hσ.le
  linarith

/-- **Price search with explicit constants.** Let `K` be good constants for arity `k` and let
`e` satisfy `r² ≤ (ρ²/β)^e`. On any instance with `N ≥ 1` coordinates, every valid run from
the root with unit wealth

* returns prices `x` that meet every demand of every hypothesis consistent with the labels
  received: `val (a s) ≤ ± x_i` for each slot `s = (i, ±)`;
* makes at most `2 · r₀ · (2N)^e` label queries. -/
theorem price_search (K : Consts k) (hK : K.Good) (e : ℕ)
    (he : ((K.r : ℚ)) ^ 2 ≤ (K.ρ ^ 2 / K.β) ^ e)
    {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V] [Nonempty ι] (val : V → ℝ)
    (X : Exec ι (Expert ι V k (K.depth hK (Fintype.card ι)))) (hist₀ : ℕ → ι → ℝ)
    (hX : X.Valid (K.alg hK ι V val) 0 hist₀ (fun _ => 1)) :
    (∀ H : Hyp ι V, X.Consistent val H → ∀ s ∈ H.S, val (H.a s) ≤ sp X.x s) ∧
    X.queries ≤ 2 * K.r₀ ι V (K.depth hK (Fintype.card ι)) * (2 * Fintype.card ι) ^ e := by
  have hN : 1 ≤ 2 * Fintype.card ι := by
    have := Fintype.card_pos (α := ι)
    omega
  constructor
  · intro H hH s hs
    have h := price_search_correct (K.params hK ι V val) X hist₀ hX H hH s hs
    simp only [Hyp.surplus] at h
    have hval : (K.params hK ι V val).A.val = val := rfl
    rw [hval] at h
    linarith
  · have hD := depth_pos (K.b_real hK) hN
    have hq := queries_root_le (K.alg hK ι V val) hK.hr X hist₀ _ hX hD
    have he' : (((K.r : ℕ) : ℝ)) ^ 2 ≤ ((K.ρ : ℝ) ^ 2 / (K.β : ℝ)) ^ e := by
      exact_mod_cast he
    have hpow : K.r ^ (K.depth hK (Fintype.card ι) - 1) ≤ (2 * Fintype.card ι) ^ e :=
      pow_depth_le (K.b_real hK) he' (depth_min (K.b_real hK) hN)
    calc X.queries
        ≤ 2 * K.r₀ ι V (K.depth hK (Fintype.card ι))
            * K.r ^ (K.depth hK (Fintype.card ι) - 1) := hq
      _ ≤ 2 * K.r₀ ι V (K.depth hK (Fintype.card ι)) * (2 * Fintype.card ι) ^ e :=
          Nat.mul_le_mul_left _ hpow

end Consts

end SPLP
