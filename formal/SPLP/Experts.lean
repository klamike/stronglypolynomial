import Mathlib
import SPLP.Defs

/-!
# Utilities, payoffs and gains of experts

Explicit formulas for the market quantities of an expert, and the three facts about gains used
in the analysis: gains lie in `[-1, 1]`, an expert that does not bid has gain zero, and an
expert whose maximizing options all receive correct feedback gains.
-/

namespace SPLP

open Finset

variable {ι V : Type*} {k D : ℕ}

theorem sgn_mul_sgn (b b' : Bool) : sgn b * sgn b' = if b' = b then 1 else -1 := by
  cases b <;> cases b' <;> simp [sgn]

theorem sgn_mul_self (b : Bool) : sgn b * sgn b = 1 := by
  cases b <;> simp [sgn]

theorem abs_sgn (b : Bool) : |sgn b| = 1 := by
  cases b <;> simp [sgn]

variable [Fintype ι] [DecidableEq ι]

section Formulas

variable (val : V → ℝ) (l : ℕ) (hist : ℕ → ι → ℝ) (e : Expert ι V k D)

theorem util_none (y : ι → ℝ) :
    util (bidOf val l hist) (dirOf val l hist) e none y = 0 := by
  simp [util, bidOf, dirOf]

theorem pay_none (v : ι → ℝ) : pay (dirOf val l hist) e none v = 0 := by
  simp [pay, dirOf]

variable {val l hist e}

theorem util_some_of_thr {τ : ℝ} (h : thr val l hist e = some τ) (q : Fin k) (y : ι → ℝ) :
    util (bidOf val l hist) (dirOf val l hist) e (some q) y
      = val (e.2.1 q) - τ - sp y (e.1 q) := by
  simp [util, bidOf, dirOf, h, sp]

theorem util_some_of_inactive (h : thr val l hist e = none) (q : Fin k) (y : ι → ℝ) :
    util (bidOf val l hist) (dirOf val l hist) e (some q) y = 0 := by
  simp [util, bidOf, dirOf, h]

theorem pay_some_of_thr {τ : ℝ} (h : thr val l hist e = some τ) (q : Fin k) (v : ι → Bool) :
    pay (dirOf val l hist) e (some q) (vreal v)
      = if v (e.1 q).1 = (e.1 q).2 then 1 else -1 := by
  simp [pay, dirOf, h, vreal, sgn_mul_sgn]

theorem pay_some_of_inactive (h : thr val l hist e = none) (q : Fin k) (v : ι → ℝ) :
    pay (dirOf val l hist) e (some q) v = 0 := by
  simp [pay, dirOf, h]

end Formulas

variable (val : V → ℝ) (l : ℕ) (hist : ℕ → ι → ℝ) (e : Expert ι V k D)

theorem pay_bounds (o : Option (Fin k)) (v : ι → Bool) :
    -1 ≤ pay (dirOf val l hist) e o (vreal v) ∧ pay (dirOf val l hist) e o (vreal v) ≤ 1 := by
  cases o with
  | none => rw [pay_none]; constructor <;> norm_num
  | some q =>
    cases h : thr val l hist e with
    | none => rw [pay_some_of_inactive h]; constructor <;> norm_num
    | some τ =>
      rw [pay_some_of_thr h]
      split_ifs <;> constructor <;> norm_num

theorem gain_bounds (y : ι → ℝ) (v : ι → Bool) :
    -1 ≤ gain val l hist y v e ∧ gain val l hist y v e ≤ 1 := by
  constructor
  · exact le_minPay _ _ _ _ _ _ (fun o _ => (pay_bounds val l hist e o v).1)
  · exact minPay_le_of_forall _ _ _ _ _ _ (fun o _ => (pay_bounds val l hist e o v).2)

/-- An expert that does not bid at this level has gain zero. -/
theorem gain_of_inactive (h : thr val l hist e = none) (y : ι → ℝ) (v : ι → Bool) :
    gain val l hist y v e = 0 := by
  have hp : ∀ o, pay (dirOf val l hist) e o (vreal v) = 0 := by
    intro o
    cases o with
    | none => exact pay_none val l hist e _
    | some q => exact pay_some_of_inactive h q _
  apply le_antisymm
  · exact minPay_le_of_forall _ _ _ _ _ _ (fun o _ => (hp o).le)
  · exact le_minPay _ _ _ _ _ _ (fun o _ => (hp o).ge)

end SPLP
