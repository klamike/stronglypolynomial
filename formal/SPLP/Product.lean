import Mathlib
import SPLP.Compat

/-!
# Product measures on tuples

Elementary identities for `k` independent draws from a weight vector `m` on a finite type:
total mass, the probability of missing a set, and pointwise domination.
-/

set_option linter.unusedSectionVars false

namespace SPLP

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem sum_prod_tuple (m : α → ℝ) (k : ℕ) :
    ∑ tup : Fin k → α, ∏ q, m (tup q) = (∑ s, m s) ^ k := by
  exact (Fintype.sum_pow m k).symm

theorem sum_prod_tuple_miss (m : α → ℝ) (A : α → Prop) [DecidablePred A] (k : ℕ) :
    ∑ tup : Fin k → α, (if ∀ q, ¬ A (tup q) then ∏ q, m (tup q) else 0)
      = (∑ s, if A s then 0 else m s) ^ k := by
  rw [← sum_prod_tuple (fun s => if A s then 0 else m s) k]
  refine Finset.sum_congr rfl fun tup _ => ?_
  by_cases hall : ∀ q, ¬ A (tup q)
  · rw [if_pos hall]
    refine Finset.prod_congr rfl fun q _ => ?_
    exact (if_neg (hall q)).symm
  · rw [if_neg hall]
    obtain ⟨q, hq⟩ := not_forall.mp hall
    have hq' : A (tup q) := not_not.mp hq
    symm
    refine Finset.prod_eq_zero (Finset.mem_univ q) ?_
    exact if_pos hq'

theorem prod_le_pow_mul_prod (m m' : α → ℝ) (ρ : ℝ) (h0 : ∀ s, 0 ≤ m' s)
    (h : ∀ s, m' s ≤ ρ * m s) {k : ℕ} (tup : Fin k → α) :
    ∏ q, m' (tup q) ≤ ρ ^ k * ∏ q, m (tup q) := by
  calc ∏ q, m' (tup q) ≤ ∏ q, (ρ * m (tup q)) :=
        prod_le_prod_real _ _ _ (fun q _ => h0 (tup q)) (fun q _ => h (tup q))
    _ = ρ ^ k * ∏ q, m (tup q) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **Hit probability.** If `A` has mass at least `γ`, then `k` independent draws hit `A`
with probability at least `1 - (1 - γ)^k`. -/
theorem hit_mass (m : α → ℝ) (hm : ∀ s, 0 ≤ m s) (hsum : ∑ s, m s = 1)
    (A : α → Prop) [DecidablePred A] (γ : ℝ) (hγ : γ ≤ ∑ s, if A s then m s else 0) (k : ℕ) :
    1 - (1 - γ) ^ k ≤ ∑ tup : Fin k → α, if ∃ q, A (tup q) then ∏ q, m (tup q) else 0 := by
  -- total mass of all tuples is `1`
  have htot : ∑ tup : Fin k → α, ∏ q, m (tup q) = 1 := by
    rw [sum_prod_tuple, hsum, one_pow]
  -- split every tuple by whether it hits `A`
  have hsplit : (∑ tup : Fin k → α, if ∃ q, A (tup q) then ∏ q, m (tup q) else 0)
      + (∑ tup : Fin k → α, if ∀ q, ¬ A (tup q) then ∏ q, m (tup q) else 0) = 1 := by
    rw [← Finset.sum_add_distrib, ← htot]
    refine Finset.sum_congr rfl fun tup _ => ?_
    by_cases hex : ∃ q, A (tup q)
    · have hall : ¬ ∀ q, ¬ A (tup q) := fun hall => hex.elim fun q hq => hall q hq
      rw [if_pos hex, if_neg hall, add_zero]
    · have hall : ∀ q, ¬ A (tup q) := fun q hq => hex ⟨q, hq⟩
      rw [if_neg hex, if_pos hall, zero_add]
  -- the mass of the complement of `A` is `1 - mass A`
  have hcompl : (∑ s, if A s then 0 else m s) = 1 - ∑ s, if A s then m s else 0 := by
    rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib, ← hsum]
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases hs : A s
    · rw [if_pos hs, if_pos hs, zero_add]
    · rw [if_neg hs, if_neg hs, add_zero]
  have hnonneg : 0 ≤ ∑ s, if A s then 0 else m s := by
    refine Finset.sum_nonneg fun s _ => ?_
    by_cases hs : A s
    · rw [if_pos hs]
    · rw [if_neg hs]
      exact hm s
  have hle : (∑ s, if A s then 0 else m s) ≤ 1 - γ := by
    rw [hcompl]
    linarith
  have hpow : (∑ s, if A s then 0 else m s) ^ k ≤ (1 - γ) ^ k :=
    pow_le_pow_left₀ hnonneg hle k
  rw [sum_prod_tuple_miss m A k] at hsplit
  linarith

end SPLP
