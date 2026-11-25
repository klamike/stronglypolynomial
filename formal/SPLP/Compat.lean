import Mathlib

/-!
# Lemmas stated locally so that the library builds under more than one Mathlib revision

`Finset.prod_le_prod` names different statements in the two Mathlib revisions this library is
built against (the ordered-semiring version is `Finset.prod_le_prod₀` in the newer one).
-/

namespace SPLP

theorem prod_le_prod_real {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ g i) : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have h0' : ∀ i ∈ s, 0 ≤ f i := fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    have h1' : ∀ i ∈ s, f i ≤ g i := fun i hi => h1 i (Finset.mem_insert_of_mem hi)
    exact mul_le_mul (h1 a (Finset.mem_insert_self a s)) (ih h0' h1')
      (Finset.prod_nonneg h0') ((h0 a (Finset.mem_insert_self a s)).trans
        (h1 a (Finset.mem_insert_self a s)))

theorem prod_le_prod_nat {ι : Type*} (s : Finset ι) (f g : ι → ℕ)
    (h1 : ∀ i ∈ s, f i ≤ g i) : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact Nat.mul_le_mul (h1 a (Finset.mem_insert_self a s))
      (ih (fun i hi => h1 i (Finset.mem_insert_of_mem hi)))

end SPLP
