import Mathlib

/-!
# Rounding to a fixed number of significant bits

`fl p x` rounds a positive real `x` down to `p + 1` significant bits: it is `m · 2^j` with
`2^p ≤ m < 2^(p+1)`, and it loses at most the factor `1 - 2^{-p}`.
-/

namespace SPLP

/-- `x = m · 2^j` with a mantissa `m < 2^(p+1)`. -/
def IsFloat (p : ℕ) (x : ℝ) : Prop := ∃ (m : ℕ) (j : ℤ), x = m * (2 : ℝ) ^ j ∧ m < 2 ^ (p + 1)

theorem IsFloat.one (p : ℕ) : IsFloat p 1 :=
  ⟨1, 0, by simp, Nat.one_lt_two_pow (Nat.succ_ne_zero p)⟩

/-- Dividing by a power of two keeps the mantissa. -/
theorem IsFloat.div_two_pow {p : ℕ} {x : ℝ} (hx : IsFloat p x) (a : ℕ) :
    IsFloat p (1 / (2 : ℝ) ^ a * x) := by
  obtain ⟨m, j, rfl, hm⟩ := hx
  refine ⟨m, j - a, ?_, hm⟩
  rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]
  field_simp

/-- Round a positive real down to `p + 1` significant bits. -/
noncomputable def fl (p : ℕ) (x : ℝ) : ℝ :=
  (⌊x / (2 : ℝ) ^ (Int.log 2 x - (p : ℤ))⌋ : ℝ) * (2 : ℝ) ^ (Int.log 2 x - (p : ℤ))

theorem fl_le (p : ℕ) {x : ℝ} (_hx : 0 < x) : fl p x ≤ x := by
  unfold fl
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (Int.log 2 x - (p : ℤ)) := zpow_pos (by norm_num) _
  calc (⌊x / (2 : ℝ) ^ (Int.log 2 x - (p : ℤ))⌋ : ℝ) * (2 : ℝ) ^ (Int.log 2 x - (p : ℤ))
      ≤ x / (2 : ℝ) ^ (Int.log 2 x - (p : ℤ)) * (2 : ℝ) ^ (Int.log 2 x - (p : ℤ)) :=
        mul_le_mul_of_nonneg_right (Int.floor_le _) hpos.le
    _ = x := div_mul_cancel₀ x hpos.ne'

theorem fl_ge (p : ℕ) {x : ℝ} (hx : 0 < x) : (1 - 1 / (2 : ℝ) ^ p) * x ≤ fl p x := by
  unfold fl
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (Int.log 2 x - (p : ℤ)) := zpow_pos (by norm_num) _
  have hlog : (2 : ℝ) ^ (Int.log 2 x) ≤ x := by
    have := Int.zpow_log_le_self (b := 2) (by norm_num) hx
    simpa using this
  have hj : (2 : ℝ) ^ (Int.log 2 x - (p : ℤ)) ≤ x / (2 : ℝ) ^ p := by
    rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]
    exact div_le_div_of_nonneg_right hlog (by positivity)
  have hfloor : x / (2 : ℝ) ^ (Int.log 2 x - (p : ℤ)) - 1
      < (⌊x / (2 : ℝ) ^ (Int.log 2 x - (p : ℤ))⌋ : ℝ) := Int.sub_one_lt_floor _
  have h1 : (x / (2 : ℝ) ^ (Int.log 2 x - (p : ℤ)) - 1) * (2 : ℝ) ^ (Int.log 2 x - (p : ℤ))
      ≤ (⌊x / (2 : ℝ) ^ (Int.log 2 x - (p : ℤ))⌋ : ℝ) * (2 : ℝ) ^ (Int.log 2 x - (p : ℤ)) :=
    mul_le_mul_of_nonneg_right hfloor.le hpos.le
  have h2 : (x / (2 : ℝ) ^ (Int.log 2 x - (p : ℤ)) - 1) * (2 : ℝ) ^ (Int.log 2 x - (p : ℤ))
      = x - (2 : ℝ) ^ (Int.log 2 x - (p : ℤ)) := by
    rw [sub_mul, div_mul_cancel₀ x hpos.ne', one_mul]
  have h3 : (1 - 1 / (2 : ℝ) ^ p) * x = x - x / (2 : ℝ) ^ p := by ring
  rw [h3]
  linarith

theorem fl_isFloat (p : ℕ) {x : ℝ} (hx : 0 < x) : IsFloat p (fl p x) := by
  unfold fl
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (Int.log 2 x - (p : ℤ)) := zpow_pos (by norm_num) _
  have ha0 : 0 ≤ x / (2 : ℝ) ^ (Int.log 2 x - (p : ℤ)) := (div_pos hx hpos).le
  have hlt : x < (2 : ℝ) ^ (Int.log 2 x + 1) := by
    have := Int.lt_zpow_succ_log_self (b := 2) (by norm_num) x
    simpa using this
  have ha1 : x / (2 : ℝ) ^ (Int.log 2 x - (p : ℤ)) < (2 : ℝ) ^ (p + 1) := by
    rw [div_lt_iff₀ hpos]
    have : (2 : ℝ) ^ (p + 1) * (2 : ℝ) ^ (Int.log 2 x - (p : ℤ)) = (2 : ℝ) ^ (Int.log 2 x + 1) := by
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      congr 1
      push_cast
      ring
    rw [this]
    exact hlt
  have hfl0 : 0 ≤ ⌊x / (2 : ℝ) ^ (Int.log 2 x - (p : ℤ))⌋ := Int.floor_nonneg.2 ha0
  refine ⟨⌊x / (2 : ℝ) ^ (Int.log 2 x - (p : ℤ))⌋.toNat, Int.log 2 x - (p : ℤ), ?_, ?_⟩
  · congr 1
    have : ((⌊x / (2 : ℝ) ^ (Int.log 2 x - (p : ℤ))⌋.toNat : ℤ) : ℝ)
        = (⌊x / (2 : ℝ) ^ (Int.log 2 x - (p : ℤ))⌋ : ℝ) := by
      rw [Int.toNat_of_nonneg hfl0]
    exact_mod_cast this.symm
  · have hlt2 : (⌊x / (2 : ℝ) ^ (Int.log 2 x - (p : ℤ))⌋ : ℝ) < (2 : ℝ) ^ (p + 1) :=
      lt_of_le_of_lt (Int.floor_le _) ha1
    have hz : ⌊x / (2 : ℝ) ^ (Int.log 2 x - (p : ℤ))⌋ < (2 : ℤ) ^ (p + 1) := by
      exact_mod_cast hlt2
    have := (Int.toNat_lt hfl0).2 (by exact_mod_cast hz : ⌊x / (2 : ℝ) ^ (Int.log 2 x - (p : ℤ))⌋ < ((2 ^ (p + 1) : ℕ) : ℤ))
    exact this

end SPLP
