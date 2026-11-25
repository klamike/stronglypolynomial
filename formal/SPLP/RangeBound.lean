import Mathlib
import SPLP.CountArith

/-!
# Size of the demand bound of Section 5 as a function of its constant `D`

The preprint's Section 5 fixes a constant `D` bounding the size of dissociated sets and a
precision parameter `K`, and derives a uniform integer bound `F` for the compressed
substitutes; the range of the price search is `R = 4F`. The definitions below transcribe the
formulas of Lemmas 5.2 and 5.3 and Section 5.4 with the largest admissible parameters
(`m = p = D - 1`). The theorems say that `log₂ F` is of order `D⁴ (K + log D)`.
-/

namespace SPLP

/-- `1/η`: the least power of two at least `4 D 2^K`. -/
def etaInv (D K : ℕ) : ℕ := 2 ^ (Nat.clog 2 (4 * D) + K)

/-- `A = 2^K (D+4) / η` (Lemma 5.2). -/
def cA (D K : ℕ) : ℕ := 2 ^ K * (D + 4) * etaInv D K

/-- `M = (D+1) A^(D+1)` (Lemma 5.2). -/
def cM (D K : ℕ) : ℕ := (D + 1) * cA D K ^ (D + 1)

/-- `1/ε = 100 (m+1) M` with `m + 1 = D` (Section 5.4). -/
def epsInv (D K : ℕ) : ℕ := 100 * D * cM D K

/-- `C = 2^(m(m+1)) (2/ε)^(m+1)` with `m = D - 1` (Lemma 5.3). -/
def cC (D K : ℕ) : ℕ := 2 ^ ((D - 1) * D) * (2 * epsInv D K) ^ D

/-- `H = 100 M C` (Section 5.4). -/
def cH (D K : ℕ) : ℕ := 100 * cM D K * cC D K

/-- `B = 10 M (m H + 3)` (Section 5.4). -/
def cB (D K : ℕ) : ℕ := 10 * cM D K * ((D - 1) * cH D K + 3)

/-- `U = B^(p+2) / η` with `p = D - 1` (Section 5.4). -/
def cU (D K : ℕ) : ℕ := cB D K ^ (D + 1) * etaInv D K

/-- `F = (D+2) (A U + 1)^(D+1) U / η` (Lemma 5.2). -/
def cF (D K : ℕ) : ℕ := (D + 2) * (cA D K * cU D K + 1) ^ (D + 1) * cU D K * etaInv D K

/-! ### Auxiliary arithmetic -/

private lemma two_pow_mono {x y : ℕ} (h : x ≤ y) : (2 : ℕ) ^ x ≤ 2 ^ y :=
  Nat.pow_le_pow_right (by norm_num) h

private lemma mul_le_two_pow {a b x y : ℕ} (ha : a ≤ 2 ^ x) (hb : b ≤ 2 ^ y) :
    a * b ≤ 2 ^ (x + y) := by
  rw [pow_add]; exact Nat.mul_le_mul ha hb

private lemma pow_le_two_pow {a x : ℕ} (ha : a ≤ 2 ^ x) (n : ℕ) : a ^ n ≤ 2 ^ (x * n) := by
  rw [pow_mul]; exact Nat.pow_le_pow_left ha n

private lemma succ_le_two_pow {a x : ℕ} (ha : a ≤ 2 ^ x) : a + 1 ≤ 2 ^ (x + 1) := by
  have h1 : 1 ≤ 2 ^ x := Nat.one_le_two_pow
  have h2 : (2 : ℕ) ^ (x + 1) = 2 * 2 ^ x := by ring
  omega

/-! ### Upper bounds: `L` stands for `⌈log₂ D⌉` and `e` for `K + L + 3` -/

section Upper

variable {D K L e : ℕ}

private lemma etaInv_le (hL : D ≤ 2 ^ L) (he : K + L + 3 ≤ e) : etaInv D K ≤ 2 ^ e := by
  unfold etaInv
  apply two_pow_mono
  have h : Nat.clog 2 (4 * D) ≤ L + 2 := by
    apply Nat.clog_le_of_le_pow
    have : (2 : ℕ) ^ (L + 2) = 4 * 2 ^ L := by ring
    omega
  omega

private lemma cA_le (hD : 1 ≤ D) (hL : D ≤ 2 ^ L) (he : K + L + 3 ≤ e) :
    cA D K ≤ 2 ^ (2 * e) := by
  have h4 : D + 4 ≤ 2 ^ (L + 3) := by
    have : (2 : ℕ) ^ (L + 3) = 8 * 2 ^ L := by ring
    omega
  unfold cA
  calc 2 ^ K * (D + 4) * etaInv D K ≤ 2 ^ (K + (L + 3) + e) :=
        mul_le_two_pow (mul_le_two_pow le_rfl h4) (etaInv_le hL he)
    _ ≤ 2 ^ (2 * e) := two_pow_mono (by omega)

private lemma cM_le (hD : 1 ≤ D) (hL : D ≤ 2 ^ L) (he : K + L + 3 ≤ e) :
    cM D K ≤ 2 ^ (e * (2 * D + 3)) := by
  have h1 : D + 1 ≤ 2 ^ (L + 1) := by
    have : (2 : ℕ) ^ (L + 1) = 2 * 2 ^ L := by ring
    omega
  unfold cM
  calc (D + 1) * cA D K ^ (D + 1) ≤ 2 ^ ((L + 1) + 2 * e * (D + 1)) :=
        mul_le_two_pow h1 (pow_le_two_pow (cA_le hD hL he) _)
    _ ≤ 2 ^ (e * (2 * D + 3)) := two_pow_mono (by nlinarith)

private lemma two_epsInv_le (hD : 1 ≤ D) (hL : D ≤ 2 ^ L) (he : K + L + 3 ≤ e) :
    2 * epsInv D K ≤ 2 ^ (e * (2 * D + 6)) := by
  have h200 : 2 * (100 * D) ≤ 2 ^ (8 + L) := by
    have : (2 : ℕ) ^ (8 + L) = 256 * 2 ^ L := by ring
    omega
  unfold epsInv
  calc 2 * (100 * D * cM D K) = 2 * (100 * D) * cM D K := by ring
    _ ≤ 2 ^ (8 + L + e * (2 * D + 3)) := mul_le_two_pow h200 (cM_le hD hL he)
    _ ≤ 2 ^ (e * (2 * D + 6)) := two_pow_mono (by nlinarith)

private lemma cC_le (hD : 1 ≤ D) (hL : D ≤ 2 ^ L) (he : K + L + 3 ≤ e) :
    cC D K ≤ 2 ^ (D * D + e * (2 * D + 6) * D) := by
  unfold cC
  exact mul_le_two_pow (two_pow_mono (Nat.mul_le_mul_right D (Nat.sub_le D 1)))
    (pow_le_two_pow (two_epsInv_le hD hL he) D)

private lemma cH_le (hD : 1 ≤ D) (hL : D ≤ 2 ^ L) (he : K + L + 3 ≤ e) :
    cH D K ≤ 2 ^ (7 + e * (2 * D + 3) + (D * D + e * (2 * D + 6) * D)) := by
  unfold cH
  exact mul_le_two_pow (mul_le_two_pow (by norm_num) (cM_le hD hL he)) (cC_le hD hL he)

private lemma cB_le_of_cH (hD : 1 ≤ D) (hL : D ≤ 2 ^ L) (he : K + L + 3 ≤ e) {h : ℕ}
    (hH : cH D K ≤ 2 ^ h) : cB D K ≤ 2 ^ (4 + e * (2 * D + 3) + (L + 2 + h)) := by
  have h3 : (D - 1) * cH D K + 3 ≤ 2 ^ (L + 2 + h) := by
    have h1 : (D - 1) * cH D K ≤ 2 ^ L * 2 ^ h := Nat.mul_le_mul (by omega) hH
    have h2 : 1 ≤ 2 ^ L * 2 ^ h := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have : (2 : ℕ) ^ (L + 2 + h) = 4 * (2 ^ L * 2 ^ h) := by ring
    omega
  unfold cB
  exact mul_le_two_pow (mul_le_two_pow (by norm_num) (cM_le hD hL he)) h3

private lemma cB_le (hD : 1 ≤ D) (hL : D ≤ 2 ^ L) (he : K + L + 3 ≤ e) :
    cB D K ≤ 2 ^ (e * (3 * D ^ 2 + 10 * D + 11)) := by
  refine (cB_le_of_cH hD hL he (cH_le hD hL he)).trans (two_pow_mono ?_)
  have h1 : 1 * (D * D) ≤ e * (D * D) := Nat.mul_le_mul_right _ (by omega)
  nlinarith

private lemma cB_one_le {L e K : ℕ} (hL : 1 ≤ 2 ^ L) (he : K + L + 3 ≤ e) :
    cB 1 K ≤ 2 ^ (5 + e * (2 * 1 + 3)) := by
  unfold cB
  calc 10 * cM 1 K * ((1 - 1) * cH 1 K + 3) = 30 * cM 1 K := by
        rw [Nat.sub_self, Nat.zero_mul]; ring
    _ ≤ 2 ^ (5 + e * (2 * 1 + 3)) := mul_le_two_pow (by norm_num) (cM_le le_rfl hL he)

private lemma cU_le (hL : D ≤ 2 ^ L) (he : K + L + 3 ≤ e) {b : ℕ} (hb : cB D K ≤ 2 ^ b) :
    cU D K ≤ 2 ^ (b * (D + 1) + e) := by
  unfold cU
  exact mul_le_two_pow (pow_le_two_pow hb _) (etaInv_le hL he)

private lemma cF_le_of_cB (hD : 1 ≤ D) (hL : D ≤ 2 ^ L) (he : K + L + 3 ≤ e) {b : ℕ}
    (hb : cB D K ≤ 2 ^ b) :
    cF D K ≤ 2 ^ (L + 2 + (2 * e + (b * (D + 1) + e) + 1) * (D + 1) + (b * (D + 1) + e) + e) := by
  have h2 : D + 2 ≤ 2 ^ (L + 2) := by
    have : (2 : ℕ) ^ (L + 2) = 4 * 2 ^ L := by ring
    omega
  have hU := cU_le hL he hb
  unfold cF
  exact mul_le_two_pow (mul_le_two_pow (mul_le_two_pow h2
    (pow_le_two_pow (succ_le_two_pow (mul_le_two_pow (cA_le hD hL he) hU)) _)) hU)
    (etaInv_le hL he)

end Upper

/-- Upper bound: `log₂ F ≤ c D⁴ (K + ⌈log₂ D⌉ + 3)`. -/
theorem cF_le (D K : ℕ) (hD : 1 ≤ D) :
    cF D K ≤ 2 ^ (64 * D ^ 4 * (K + Nat.clog 2 D + 3)) := by
  have hL : D ≤ 2 ^ Nat.clog 2 D := Nat.le_pow_clog (by norm_num) D
  generalize Nat.clog 2 D = L at hL ⊢
  obtain ⟨e, he⟩ : ∃ e, e = K + L + 3 := ⟨_, rfl⟩
  rw [← he]
  have he' : K + L + 3 ≤ e := he.ge
  rcases Nat.lt_or_ge D 2 with h | hD2
  · obtain rfl : D = 1 := by omega
    refine (cF_le_of_cB hD hL he' (cB_one_le hL he')).trans (two_pow_mono ?_)
    norm_num
    omega
  · refine (cF_le_of_cB hD hL he' (cB_le hD hL he')).trans (two_pow_mono ?_)
    have h1 : 1 * (D + 1) ≤ e * (D + 1) := Nat.mul_le_mul_right _ (by omega)
    have h2 : 3 * D ^ 4 + 19 * D ^ 3 + 47 * D ^ 2 + 57 * D + 29 ≤ 64 * D ^ 4 := by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hD2
      ring_nf
      nlinarith [Nat.zero_le (d ^ 2), Nat.zero_le (d ^ 3), Nat.zero_le (d ^ 4)]
    have h3 := Nat.mul_le_mul_left e h2
    nlinarith

/-! ### Lower bounds -/

section Lower

variable {D K : ℕ}

private lemma etaInv_ge : 2 ^ K ≤ etaInv D K := two_pow_mono (Nat.le_add_left _ _)

private lemma etaInv_pos : 1 ≤ etaInv D K := Nat.one_le_two_pow

private lemma cA_ge : 2 ^ K ≤ cA D K := by
  unfold cA
  calc 2 ^ K = 2 ^ K * 1 * 1 := by ring
    _ ≤ 2 ^ K * (D + 4) * etaInv D K :=
        Nat.mul_le_mul (Nat.mul_le_mul le_rfl (by omega)) etaInv_pos

private lemma cA_pos : 1 ≤ cA D K := le_trans Nat.one_le_two_pow cA_ge

private lemma cM_ge : 2 ^ (K * D) ≤ cM D K := by
  unfold cM
  calc 2 ^ (K * D) = (2 ^ K) ^ D := pow_mul _ _ _
    _ ≤ cA D K ^ D := Nat.pow_le_pow_left cA_ge D
    _ ≤ cA D K ^ (D + 1) := Nat.pow_le_pow_right cA_pos (Nat.le_succ D)
    _ ≤ (D + 1) * cA D K ^ (D + 1) := Nat.le_mul_of_pos_left _ (by omega)

private lemma cM_pos : 1 ≤ cM D K := le_trans Nat.one_le_two_pow cM_ge

private lemma cC_ge (hD : 1 ≤ D) : 2 ^ (K * D * D) ≤ cC D K := by
  have h : 2 ^ (K * D) ≤ 2 * epsInv D K := by
    unfold epsInv
    have h1 : cM D K ≤ 100 * D * cM D K := Nat.le_mul_of_pos_left _ (by omega)
    have h2 := cM_ge (D := D) (K := K)
    omega
  unfold cC
  calc 2 ^ (K * D * D) = (2 ^ (K * D)) ^ D := pow_mul _ _ _
    _ ≤ (2 * epsInv D K) ^ D := Nat.pow_le_pow_left h D
    _ ≤ 2 ^ ((D - 1) * D) * (2 * epsInv D K) ^ D := Nat.le_mul_of_pos_left _ (by positivity)

private lemma cC_le_cH : cC D K ≤ cH D K := by
  unfold cH
  exact Nat.le_mul_of_pos_left _ (Nat.mul_pos (by norm_num) cM_pos)

private lemma cB_pos : 1 ≤ cB D K := by
  unfold cB
  exact Nat.mul_pos (Nat.mul_pos (by norm_num) cM_pos) (by omega)

private lemma cH_le_cB (hD : 2 ≤ D) : cH D K ≤ cB D K := by
  unfold cB
  calc cH D K ≤ (D - 1) * cH D K := Nat.le_mul_of_pos_left _ (by omega)
    _ ≤ (D - 1) * cH D K + 3 := Nat.le_add_right _ _
    _ ≤ 10 * cM D K * ((D - 1) * cH D K + 3) :=
        Nat.le_mul_of_pos_left _ (Nat.mul_pos (by norm_num) cM_pos)

private lemma cU_pos : 1 ≤ cU D K := by
  unfold cU
  exact Nat.mul_pos (pow_pos cB_pos _) etaInv_pos

private lemma cU_ge (hD : 2 ≤ D) : 2 ^ (K * D * D * D) ≤ cU D K := by
  have hB : 2 ^ (K * D * D) ≤ cB D K :=
    (cC_ge (by omega)).trans (cC_le_cH.trans (cH_le_cB hD))
  unfold cU
  calc 2 ^ (K * D * D * D) = (2 ^ (K * D * D)) ^ D := pow_mul _ _ _
    _ ≤ cB D K ^ D := Nat.pow_le_pow_left hB D
    _ ≤ cB D K ^ (D + 1) := Nat.pow_le_pow_right cB_pos (Nat.le_succ D)
    _ ≤ cB D K ^ (D + 1) * etaInv D K := Nat.le_mul_of_pos_right _ etaInv_pos

private lemma cU_pow_le_cF : cU D K ^ (D + 1) ≤ cF D K := by
  have h : cU D K ≤ cA D K * cU D K + 1 :=
    (Nat.le_mul_of_pos_left _ cA_pos).trans (Nat.le_add_right _ _)
  unfold cF
  calc cU D K ^ (D + 1) ≤ (cA D K * cU D K + 1) ^ (D + 1) := Nat.pow_le_pow_left h _
    _ = 1 * (cA D K * cU D K + 1) ^ (D + 1) * 1 * 1 := by ring
    _ ≤ (D + 2) * (cA D K * cU D K + 1) ^ (D + 1) * cU D K * etaInv D K :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (by omega) le_rfl) cU_pos) etaInv_pos

end Lower

/-- Lower bound: `log₂ F ≥ D⁴ K`. -/
theorem le_cF (D K : ℕ) (hD : 1 ≤ D) : 2 ^ (D ^ 4 * K) ≤ cF D K := by
  refine le_trans ?_ cU_pow_le_cF
  rcases Nat.lt_or_ge D 2 with h | hD2
  · obtain rfl : D = 1 := by omega
    calc 2 ^ (1 ^ 4 * K) = 2 ^ K := by norm_num
      _ ≤ etaInv 1 K := etaInv_ge
      _ ≤ cU 1 K := by
          unfold cU
          exact Nat.le_mul_of_pos_left _ (pow_pos cB_pos _)
      _ ≤ cU 1 K ^ (1 + 1) := Nat.le_self_pow (by norm_num) _
  · calc 2 ^ (D ^ 4 * K) = (2 ^ (K * D * D * D)) ^ D := by
          rw [← pow_mul]; congr 1; ring
      _ ≤ cU D K ^ D := Nat.pow_le_pow_left (cU_ge hD2) D
      _ ≤ cU D K ^ (D + 1) := Nat.pow_le_pow_right cU_pos (Nat.le_succ D)

/-- With the preprint's constant `D = (d+1)^6`, `log₂ F ≥ (d+1)^24 K`. -/
theorem cF_paper_ge (d K : ℕ) : 2 ^ ((d + 1) ^ 24 * K) ≤ cF ((d + 1) ^ 6) K := by
  have h := le_cF ((d + 1) ^ 6) K (Nat.one_le_pow _ _ (Nat.succ_pos d))
  rwa [← pow_mul] at h

/-- With the constant `Dnew d = 12 d² ⌈log₂ (d+1)⌉` of `minors_dissociated_card_lt`,
`log₂ F ≤ 64 (Dnew d)⁴ (K + ⌈log₂ (Dnew d)⌉ + 3)`. -/
theorem cF_new_le (d K : ℕ) (hd : 1 ≤ d) :
    cF (Dnew d) K ≤ 2 ^ (64 * Dnew d ^ 4 * (K + Nat.clog 2 (Dnew d) + 3)) := by
  refine cF_le (Dnew d) K ?_
  have h1 : 1 ≤ Nat.clog 2 (d + 1) := Nat.clog_pos (by norm_num) (by omega)
  have h2 : 1 ≤ d ^ 2 := Nat.one_le_pow _ _ hd
  unfold Dnew
  nlinarith [Nat.mul_le_mul h2 h1]

end SPLP
