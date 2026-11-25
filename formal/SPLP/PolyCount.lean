import Mathlib
import SPLP.Norm1

/-!
# Counting integer polynomials of bounded degree and bounded coefficients
-/

namespace SPLP

open MvPolynomial Finset

variable {σ : Type*}

theorem norm1_eq_sum_of_subset (p : MvPolynomial σ ℤ) (s : Finset (σ →₀ ℕ))
    (h : p.support ⊆ s) : norm1 p = ∑ m ∈ s, (p.coeff m).natAbs := by
  unfold norm1
  apply Finset.sum_subset h
  intro m _ hm
  simp [MvPolynomial.notMem_support_iff.mp hm]

theorem norm1_zero : norm1 (0 : MvPolynomial σ ℤ) = 0 := by
  simp [norm1]

theorem norm1_monomial (m : σ →₀ ℕ) (c : ℤ) : norm1 (monomial m c) = c.natAbs := by
  classical
  unfold norm1
  rw [MvPolynomial.support_monomial]
  by_cases hc : c = 0
  · simp [hc]
  · simp [hc]

theorem norm1_add_le (p q : MvPolynomial σ ℤ) : norm1 (p + q) ≤ norm1 p + norm1 q := by
  classical
  rw [norm1_eq_sum_of_subset (p + q) (p.support ∪ q.support) MvPolynomial.support_add,
    norm1_eq_sum_of_subset p (p.support ∪ q.support) subset_union_left,
    norm1_eq_sum_of_subset q (p.support ∪ q.support) subset_union_right,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro m _
  rw [MvPolynomial.coeff_add]
  exact Int.natAbs_add_le _ _

theorem norm1_sum_le {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℤ) :
    norm1 (∑ i ∈ s, f i) ≤ ∑ i ∈ s, norm1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [norm1_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (norm1_add_le _ _).trans (Nat.add_le_add_left ih _)

theorem norm1_mul_le (p q : MvPolynomial σ ℤ) : norm1 (p * q) ≤ norm1 p * norm1 q := by
  classical
  have hpq : p * q = ∑ a ∈ p.support, ∑ b ∈ q.support,
      monomial (a + b) (p.coeff a * q.coeff b) := by
    rw [MvPolynomial.mul_def]
    rfl
  rw [hpq]
  refine (norm1_sum_le _ _).trans ?_
  unfold norm1
  rw [Finset.sum_mul_sum]
  apply Finset.sum_le_sum
  intro a _
  refine (norm1_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro b _
  rw [norm1_monomial, Int.natAbs_mul]

theorem norm1_prod_le {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℤ) :
    norm1 (∏ i ∈ s, f i) ≤ ∏ i ∈ s, norm1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.prod_empty]
    have : (1 : MvPolynomial σ ℤ) = monomial 0 1 := rfl
    rw [this, norm1_monomial]
    simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (norm1_mul_le _ _).trans (Nat.mul_le_mul_left _ ih)

theorem natAbs_coeff_le_norm1 (p : MvPolynomial σ ℤ) (m : σ →₀ ℕ) :
    (p.coeff m).natAbs ≤ norm1 p := by
  by_cases hm : m ∈ p.support
  · exact Finset.single_le_sum (f := fun m => (p.coeff m).natAbs) (fun _ _ => Nat.zero_le _) hm
  · simp [MvPolynomial.notMem_support_iff.mp hm]

/-- There are at most `(2B+1)^((d+1)^n)` integer polynomials in `n` variables with every
individual degree at most `d` and coefficient 1-norm at most `B`. -/
theorem card_le_of_degreeOf_norm1 [Fintype σ] {d B : ℕ} (S : Finset (MvPolynomial σ ℤ))
    (hS : ∀ p ∈ S, (∀ v, p.degreeOf v ≤ d) ∧ norm1 p ≤ B) :
    S.card ≤ (2 * B + 1) ^ ((d + 1) ^ Fintype.card σ) := by
  classical
  let f : MvPolynomial σ ℤ → ((σ → Fin (d + 1)) → ℤ) := fun p e =>
    p.coeff (Finsupp.equivFunOnFinite.symm (fun v => (e v : ℕ)))
  let T : Finset ((σ → Fin (d + 1)) → ℤ) :=
    Fintype.piFinset (fun _ : σ → Fin (d + 1) => Finset.Icc (-(B : ℤ)) B)
  have hT : T.card = (2 * B + 1) ^ ((d + 1) ^ Fintype.card σ) := by
    simp only [T, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, Finset.card_univ,
      Fintype.card_fun, Fintype.card_fin]
    congr 1
    omega
  rw [← hT]
  apply Finset.card_le_card_of_injOn f
  · intro p hp
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro e
    rw [Finset.mem_Icc]
    have h1 := natAbs_coeff_le_norm1 p (Finsupp.equivFunOnFinite.symm (fun v => (e v : ℕ)))
    have h2 := (hS p hp).2
    simp only [f]
    omega
  · intro p hp q hq hpq
    have hzero : ∀ r ∈ S, ∀ m : σ →₀ ℕ, (∃ v, d < m v) → r.coeff m = 0 := by
      intro r hr m ⟨v, hv⟩
      by_contra hne
      have hm : m ∈ r.support := MvPolynomial.mem_support_iff.mpr hne
      have := MvPolynomial.monomial_le_degreeOf v hm
      have := (hS r hr).1 v
      omega
    ext m
    by_cases hm : ∀ v, m v ≤ d
    · have h := congr_fun hpq (fun v => ⟨m v, Nat.lt_succ_of_le (hm v)⟩)
      have hmm : (Finsupp.equivFunOnFinite.symm (fun v => m v) : σ →₀ ℕ) = m := by
        ext v; simp
      simpa [f, hmm] using h
    · push Not at hm
      rw [hzero p hp m hm, hzero q hq m hm]

end SPLP
