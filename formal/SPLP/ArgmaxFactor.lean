import Mathlib

/-!
# A wealth factor that depends on the best option is not a product of pairwise factors

At a probe the wealth of an expert is multiplied by a factor that depends on which of its
options is best. For three options with values `x0, x1, x2` this is a function `F` of the
index of the maximum. If `F` could be written as a product of functions of the three pairwise
comparisons, the wealth measure would be a pairwise graphical model and sums over it could be
computed by dynamic programming along the comparisons. `argmax_factor_const` shows that this
is possible only when `F` is constant (for nonvanishing `F`, as here, where the factors are
`1 ± η` and `1`). So the coupling of the options through the maximum cannot be removed by
factoring.
-/

namespace SPLP

theorem argmax_factor_const (F0 F1 F2 : ℝ) (h0 : F0 ≠ 0) (h1 : F1 ≠ 0) (h2 : F2 ≠ 0)
    (g01 g02 g12 : Bool → ℝ)
    (h : ∀ (x0 x1 x2 : ℝ) (b01 b02 b12 : Bool),
      (b01 = true ↔ x0 < x1) → (b02 = true ↔ x0 < x2) → (b12 = true ↔ x2 < x1) →
      (x1 < x0 → x2 < x0 → F0 = g01 b01 * g02 b02 * g12 b12) ∧
      (x0 < x1 → x2 < x1 → F1 = g01 b01 * g02 b02 * g12 b12) ∧
      (x0 < x2 → x1 < x2 → F2 = g01 b01 * g02 b02 * g12 b12)) :
    F0 = F1 ∧ F1 = F2 := by
  have e1 : F0 = g01 false * g02 false * g12 true :=
    (h 2 1 0 false false true (by norm_num) (by norm_num) (by norm_num)).1
      (by norm_num) (by norm_num)
  have e2 : F0 = g01 false * g02 false * g12 false :=
    (h 2 0 1 false false false (by norm_num) (by norm_num) (by norm_num)).1
      (by norm_num) (by norm_num)
  have e3 : F1 = g01 true * g02 false * g12 true :=
    (h 1 2 0 true false true (by norm_num) (by norm_num) (by norm_num)).2.1
      (by norm_num) (by norm_num)
  have e4 : F1 = g01 true * g02 true * g12 true :=
    (h 0 2 1 true true true (by norm_num) (by norm_num) (by norm_num)).2.1
      (by norm_num) (by norm_num)
  have e5 : F2 = g01 false * g02 true * g12 false :=
    (h 1 0 2 false true false (by norm_num) (by norm_num) (by norm_num)).2.2
      (by norm_num) (by norm_num)
  have e6 : F2 = g01 true * g02 true * g12 false :=
    (h 0 1 2 true true false (by norm_num) (by norm_num) (by norm_num)).2.2
      (by norm_num) (by norm_num)
  have k12 : g12 true = g12 false := by
    have a1 : g01 false * g02 false ≠ 0 := by
      intro hz
      apply h0
      rw [e1, hz, zero_mul]
    exact mul_left_cancel₀ a1 (e1.symm.trans e2)
  have k02 : g02 false = g02 true := by
    have a2 : g01 true * g12 true ≠ 0 := by
      intro hz
      apply h1
      have hr : g01 true * g02 false * g12 true = (g01 true * g12 true) * g02 false := by ring
      rw [e3, hr, hz, zero_mul]
    have h34 : (g01 true * g12 true) * g02 false = (g01 true * g12 true) * g02 true := by
      have hr : (g01 true * g12 true) * g02 false = g01 true * g02 false * g12 true := by ring
      have hr' : (g01 true * g12 true) * g02 true = g01 true * g02 true * g12 true := by ring
      rw [hr, hr', ← e3, ← e4]
    exact mul_left_cancel₀ a2 h34
  have k01 : g01 false = g01 true := by
    have a3 : g02 true * g12 false ≠ 0 := by
      intro hz
      apply h2
      have hr : g01 false * g02 true * g12 false = g01 false * (g02 true * g12 false) := by ring
      rw [e5, hr, hz, mul_zero]
    have h56 : (g02 true * g12 false) * g01 false = (g02 true * g12 false) * g01 true := by
      have hr : (g02 true * g12 false) * g01 false = g01 false * g02 true * g12 false := by ring
      have hr' : (g02 true * g12 false) * g01 true = g01 true * g02 true * g12 false := by ring
      rw [hr, hr', ← e5, ← e6]
    exact mul_left_cancel₀ a3 h56
  constructor
  · rw [e1, e3, k01]
  · rw [e4, e6, k12]

end SPLP
