import Mathlib

/-!
# The counting inequality of Lemma 5.1 holds for a much smaller constant

The preprint takes `D = (d+1)^6`. Its counting argument only needs
`(2 · 2^D · (d!)^D + 1)^((D+1)^(d^2)) < 2^(2^D)`, which already holds for
`D = 12 d² ⌈log₂ (d+1)⌉`.
-/

namespace SPLP

theorem count_lt {n D δ L lam mu nu : ℕ} (hL : L ≤ 2 ^ lam) (hmu : δ * D + 1 ≤ 2 ^ mu)
    (hnu : D * (1 + lam) + 2 ≤ 2 ^ nu) (h : n * mu + nu < D) :
    (2 * (2 ^ D * L ^ D) + 1) ^ ((δ * D + 1) ^ n) < 2 ^ (2 ^ D) := by
  have hbase : 2 * (2 ^ D * L ^ D) + 1 ≤ 2 ^ (2 ^ nu) := by
    have h1 : L ^ D ≤ 2 ^ (lam * D) := by
      rw [pow_mul]; exact Nat.pow_le_pow_left hL D
    have h2 : 2 * (2 ^ D * L ^ D) + 1 ≤ 2 ^ (D * (1 + lam) + 2) := by
      have e : 2 ^ (D * (1 + lam) + 2) = 4 * (2 ^ D * 2 ^ (lam * D)) := by ring
      rw [e]
      have hpos : 1 ≤ 2 ^ D * 2 ^ (lam * D) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      have h3 := Nat.mul_le_mul_left (2 ^ D) h1
      omega
    exact h2.trans (Nat.pow_le_pow_right (by norm_num) hnu)
  have hexp : (δ * D + 1) ^ n ≤ 2 ^ (mu * n) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left hmu n
  calc (2 * (2 ^ D * L ^ D) + 1) ^ ((δ * D + 1) ^ n)
      ≤ (2 ^ (2 ^ nu)) ^ (2 ^ (mu * n)) :=
        (Nat.pow_le_pow_left hbase _).trans (Nat.pow_le_pow_right (by positivity) hexp)
    _ = 2 ^ (2 ^ (nu + mu * n)) := by rw [← pow_mul, ← pow_add]
    _ < 2 ^ (2 ^ D) :=
        Nat.pow_lt_pow_right (by norm_num)
          (Nat.pow_lt_pow_right (by norm_num) (by linarith [mul_comm n mu]))

/-- The smaller constant. -/
def Dnew (d : ℕ) : ℕ := 12 * d ^ 2 * Nat.clog 2 (d + 1)

theorem count_lt_Dnew (d : ℕ) (hd : 1 ≤ d) :
    (2 * (2 ^ Dnew d * (Nat.factorial d) ^ Dnew d) + 1) ^ ((Dnew d + 1) ^ (d ^ 2))
      < 2 ^ (2 ^ Dnew d) := by
  rcases Nat.lt_or_ge d 2 with h2 | h2
  · obtain rfl : d = 1 := by omega
    have hD : Dnew 1 = 12 := by
      have : Nat.clog 2 2 = 1 := by decide
      simp [Dnew, this]
    have := @count_lt 1 12 1 1 0 4 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    rw [hD]
    simpa only [Nat.factorial_one, one_mul, one_pow, pow_one] using this
  · have hDdef : Dnew d = 12 * d ^ 2 * Nat.clog 2 (d + 1) := rfl
    generalize hℓ : Nat.clog 2 (d + 1) = ℓ at hDdef
    have hdl : d + 1 ≤ 2 ^ ℓ := hℓ ▸ Nat.le_pow_clog (by norm_num) _
    have hℓ1 : 1 ≤ ℓ := hℓ ▸ Nat.clog_pos (by norm_num) (by omega)
    have hℓ2 : ℓ < 2 ^ ℓ := Nat.lt_two_pow_self
    have hfac : d.factorial ≤ 2 ^ (ℓ * d) := by
      calc d.factorial ≤ d ^ d := Nat.factorial_le_pow d
        _ ≤ (2 ^ ℓ) ^ d := Nat.pow_le_pow_left (by omega) d
        _ = 2 ^ (ℓ * d) := (pow_mul ..).symm
    generalize hX : 2 ^ ℓ = X at hdl hℓ2
    have hX1 : 1 ≤ X := by omega
    have hD3 : Dnew d ≤ 12 * X ^ 3 := by
      rw [hDdef]
      have : d ^ 2 * ℓ ≤ X ^ 2 * X :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) 2) hℓ2.le
      nlinarith
    have hmu : 1 * Dnew d + 1 ≤ 2 ^ (3 * ℓ + 4) := by
      have e : 2 ^ (3 * ℓ + 4) = 16 * (2 ^ ℓ) ^ 3 := by ring
      rw [e, hX]
      have : 1 ≤ X ^ 3 := Nat.one_le_pow _ _ hX1
      omega
    have hnu : Dnew d * (1 + ℓ * d) + 2 ≤ 2 ^ (5 * ℓ + 4) := by
      have e : 2 ^ (5 * ℓ + 4) = 16 * ((2 ^ ℓ) ^ 3 * ((2 ^ ℓ) * (2 ^ ℓ))) := by ring
      rw [e, hX]
      have h1 : 1 + ℓ * d ≤ X * X := by
        calc 1 + ℓ * d ≤ ℓ * (d + 1) := by nlinarith
          _ ≤ X * X := Nat.mul_le_mul hℓ2.le hdl
      have h3 : Dnew d * (1 + ℓ * d) ≤ 12 * X ^ 3 * (X * X) := Nat.mul_le_mul hD3 h1
      have h4 : 1 ≤ X ^ 3 * (X * X) :=
        Nat.one_le_iff_ne_zero.mpr (by positivity)
      nlinarith
    have hlt : d ^ 2 * (3 * ℓ + 4) + (5 * ℓ + 4) < Dnew d := by
      rw [hDdef]
      have hd2 : 4 ≤ d ^ 2 := by nlinarith
      have ha1 : d ^ 2 * 1 ≤ d ^ 2 * ℓ := Nat.mul_le_mul_left _ hℓ1
      have ha2 : 4 * ℓ ≤ d ^ 2 * ℓ := Nat.mul_le_mul_right _ hd2
      nlinarith
    have := count_lt (n := d ^ 2) (D := Dnew d) (δ := 1) hfac hmu hnu hlt
    simpa using this

theorem Dnew_lt_paper (d : ℕ) (hd : 1 ≤ d) : Dnew d < (d + 1) ^ 6 := by
  have _ := hd
  have hℓ : Nat.clog 2 (d + 1) ≤ d :=
    Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n := d))
  have h1 : Dnew d ≤ 12 * d ^ 2 * d := Nat.mul_le_mul_left _ hℓ
  have e : (d + 1) ^ 6 = d ^ 6 + 6 * d ^ 5 + 15 * d ^ 4 + 20 * d ^ 3 + 15 * d ^ 2 + 6 * d + 1 := by
    ring
  have e3 : 12 * d ^ 2 * d = 12 * d ^ 3 := by ring
  have := Nat.zero_le (d ^ 6)
  have := Nat.zero_le (d ^ 5)
  have := Nat.zero_le (d ^ 4)
  have := Nat.zero_le (d ^ 2)
  omega

end SPLP
