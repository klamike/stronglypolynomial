import Mathlib

/-!
# The coefficient 1-norm of an integer polynomial
-/

namespace SPLP

open MvPolynomial

/-- Sum of the absolute values of the coefficients of an integer polynomial. -/
def norm1 {σ : Type*} (p : MvPolynomial σ ℤ) : ℕ :=
  ∑ m ∈ p.support, (p.coeff m).natAbs

end SPLP
