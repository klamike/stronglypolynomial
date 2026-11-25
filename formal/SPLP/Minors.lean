import Mathlib
import SPLP.Norm1

/-!
# Minors as integer polynomials in the matrix entries

A `k × k` minor of the generic `r × c` matrix is an integer polynomial in the entries with
every individual degree at most one and coefficient 1-norm at most `k!`.
-/

namespace SPLP

open MvPolynomial Finset

variable {r c k : ℕ}

/-- The minor with rows `f` and columns `g`, as a polynomial in the matrix entries. -/
noncomputable def minorPoly (f : Fin k → Fin r) (g : Fin k → Fin c) :
    MvPolynomial (Fin r × Fin c) ℤ :=
  ((Matrix.mvPolynomialX (Fin r) (Fin c) ℤ).submatrix f g).det

theorem minorPoly_eval (f : Fin k → Fin r) (g : Fin k → Fin c) (M : Matrix (Fin r) (Fin c) ℝ) :
    aeval (fun v : Fin r × Fin c => M v.1 v.2) (minorPoly f g) = (M.submatrix f g).det := by
  unfold minorPoly
  rw [AlgHom.map_det]
  congr 1
  ext i j
  simp [Matrix.mvPolynomialX_apply]

/-- A minor is a signed sum of monomials, one for each permutation. -/
theorem minorPoly_eq_sum (f : Fin k → Fin r) (g : Fin k → Fin c) :
    minorPoly f g = ∑ τ : Equiv.Perm (Fin k),
      C ((Equiv.Perm.sign τ : ℤˣ) : ℤ) * ∏ i, X (f (τ i), g i) := by
  unfold minorPoly
  rw [Matrix.det_apply]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Units.smul_def, MvPolynomial.smul_eq_C_mul]
  simp [Matrix.mvPolynomialX_apply]

theorem minorPoly_degreeOf_le (f : Fin k → Fin r) (g : Fin k → Fin c)
    (hg : Function.Injective g) (v : Fin r × Fin c) :
    (minorPoly f g).degreeOf v ≤ 1 := by
  classical
  rw [minorPoly_eq_sum]
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun τ _ => ?_)
  refine (degreeOf_C_mul_le _ _ _).trans ((degreeOf_prod_le _ _ _).trans ?_)
  simp only [degreeOf_X]
  rw [Finset.sum_boole]
  have h : (Finset.univ.filter fun i : Fin k => v = (f (τ i), g i)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    apply hg
    have h1 := congrArg Prod.snd ha.2
    have h2 := congrArg Prod.snd hb.2
    simp only at h1 h2
    rw [← h1, ← h2]
  exact_mod_cast h

private theorem norm1_eq_sum_of_subset {σ : Type*} (p : MvPolynomial σ ℤ)
    (s : Finset (σ →₀ ℕ)) (h : p.support ⊆ s) :
    norm1 p = ∑ m ∈ s, (p.coeff m).natAbs := by
  unfold norm1
  refine Finset.sum_subset h fun m _ hm => ?_
  simp [MvPolynomial.notMem_support_iff.mp hm]

private theorem norm1_add_le_aux {σ : Type*} (p q : MvPolynomial σ ℤ) :
    norm1 (p + q) ≤ norm1 p + norm1 q := by
  classical
  rw [norm1_eq_sum_of_subset (p + q) (p.support ∪ q.support) MvPolynomial.support_add,
    norm1_eq_sum_of_subset p (p.support ∪ q.support) Finset.subset_union_left,
    norm1_eq_sum_of_subset q (p.support ∪ q.support) Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun m _ => ?_
  rw [coeff_add]
  exact Int.natAbs_add_le _ _

private theorem norm1_sum_le_aux {σ ι : Type*} (s : Finset ι) (F : ι → MvPolynomial σ ℤ) :
    norm1 (∑ i ∈ s, F i) ≤ ∑ i ∈ s, norm1 (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [norm1]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (norm1_add_le_aux _ _).trans (Nat.add_le_add_left ih _)

private theorem norm1_monomial_le {σ : Type*} (s : σ →₀ ℕ) (a : ℤ) :
    norm1 (monomial s a) ≤ a.natAbs := by
  classical
  rw [norm1_eq_sum_of_subset _ {s} support_monomial_subset]
  simp

theorem minorPoly_norm1_le (f : Fin k → Fin r) (g : Fin k → Fin c) :
    norm1 (minorPoly f g) ≤ Nat.factorial k := by
  classical
  rw [minorPoly_eq_sum]
  refine (norm1_sum_le_aux _ _).trans ?_
  have hterm : ∀ τ : Equiv.Perm (Fin k),
      norm1 (C ((Equiv.Perm.sign τ : ℤˣ) : ℤ) * ∏ i, X (f (τ i), g i)) ≤ 1 := by
    intro τ
    have hX : (∏ i, X (f (τ i), g i) : MvPolynomial (Fin r × Fin c) ℤ)
        = monomial (∑ i, Finsupp.single (f (τ i), g i) 1) 1 := by
      rw [monomial_sum_one]
      rfl
    rw [hX, C_mul_monomial, mul_one]
    refine (norm1_monomial_le _ _).trans ?_
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> simp [h]
  refine (Finset.sum_le_sum fun τ _ => hterm τ).trans ?_
  simp [Fintype.card_perm]

end SPLP
