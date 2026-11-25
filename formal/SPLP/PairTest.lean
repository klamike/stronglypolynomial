import Mathlib

/-!
# Lemma 3.1 of the preprint with explicit constants

Vectors on paired slots are pairs `(a, b)` with `a` on the positive and `b` on the negative
slots, and `Q (a, b) = ∑ i, a i * b i`. If a convex set of such vectors has all entries in
`[-ε, 2]` and `Q ≤ q` throughout, then for each coordinate at most one of its two slots reaches
the threshold `θ` anywhere in the set, as soon as `q < ((θ - ε)/2)² - 2 ε (N - 1)`.

The preprint takes `ε = H^-10` and `q = H^-1` with `H = 2^(100 N²)`. The lemma only needs `ε` of
order `1/N` and a constant `q` (`opposing_slots_quarter`).
-/

namespace SPLP

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem opposing_slots (K : Set ((ι → ℝ) × (ι → ℝ))) (hconv : Convex ℝ K) {ε θ q : ℝ}
    (hε : 0 ≤ ε) (hεθ : ε ≤ θ)
    (hbox : ∀ y ∈ K, ∀ i, (-ε ≤ y.1 i ∧ y.1 i ≤ 2) ∧ (-ε ≤ y.2 i ∧ y.2 i ≤ 2))
    (hQ : ∀ y ∈ K, ∑ i, y.1 i * y.2 i ≤ q)
    (hgap : q < ((θ - ε) / 2) ^ 2 - 2 * ε * ((Fintype.card ι : ℝ) - 1)) (i : ι) :
    ¬ ((∃ y ∈ K, θ ≤ y.1 i) ∧ (∃ y ∈ K, θ ≤ y.2 i)) := by
  rintro ⟨⟨y, hy, hyi⟩, ⟨y', hy', hyi'⟩⟩
  set m : (ι → ℝ) × (ι → ℝ) := (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • y' with hm
  have hmK : m ∈ K := hconv hy hy' (by norm_num) (by norm_num) (by norm_num)
  have hm1 : ∀ j, m.1 j = (y.1 j + y'.1 j) / 2 := fun j => by
    simp [hm]; ring
  have hm2 : ∀ j, m.2 j = (y.2 j + y'.2 j) / 2 := fun j => by
    simp [hm]; ring
  have hi : ((θ - ε) / 2) ^ 2 ≤ m.1 i * m.2 i := by
    have h1 : (θ - ε) / 2 ≤ m.1 i := by
      rw [hm1]; linarith [(hbox y' hy' i).1.1]
    have h2 : (θ - ε) / 2 ≤ m.2 i := by
      rw [hm2]; linarith [(hbox y hy i).2.1]
    have h0 : 0 ≤ (θ - ε) / 2 := by linarith
    rw [sq]
    exact mul_le_mul h1 h2 h0 (h0.trans h1)
  have hj : ∀ j, -(2 * ε) ≤ m.1 j * m.2 j := by
    intro j
    obtain ⟨⟨ha, ha'⟩, ⟨hb, hb'⟩⟩ := hbox m hmK j
    rcases le_total 0 (m.1 j) with h1 | h1 <;> rcases le_total 0 (m.2 j) with h2 | h2
    · nlinarith [mul_nonneg h1 h2]
    · nlinarith [mul_nonneg h1 (sub_nonneg.2 h2), mul_nonneg (sub_nonneg.2 ha') (add_nonneg (by linarith : (0:ℝ) ≤ m.2 j + ε) (le_refl 0))]
    · nlinarith [mul_nonneg (sub_nonneg.2 hb') (by linarith : (0:ℝ) ≤ m.1 j + ε)]
    · nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)]
  have hsum : ((θ - ε) / 2) ^ 2 - 2 * ε * ((Fintype.card ι : ℝ) - 1) ≤ ∑ j, m.1 j * m.2 j := by
    rw [← Finset.add_sum_erase univ _ (mem_univ i)]
    have : -(2 * ε) * ((Fintype.card ι : ℝ) - 1) ≤ ∑ j ∈ univ.erase i, m.1 j * m.2 j := by
      calc -(2 * ε) * ((Fintype.card ι : ℝ) - 1)
          = ∑ _j ∈ univ.erase i, -(2 * ε) := by
            rw [Finset.sum_const, Finset.card_erase_of_mem (mem_univ i), Finset.card_univ,
              nsmul_eq_mul, Nat.cast_sub (Fintype.card_pos_iff.2 ⟨i⟩), Nat.cast_one]
            ring
        _ ≤ _ := Finset.sum_le_sum (fun j _ => hj j)
    linarith
  linarith [hQ m hmK]

/-- The threshold `1/4` with tolerance `1/(400 N)` and `Q ≤ 1/100`. -/
theorem opposing_slots_quarter (K : Set ((ι → ℝ) × (ι → ℝ))) (hconv : Convex ℝ K) {ε : ℝ}
    (hε : 0 ≤ ε) (hεN : ε * (400 * (Fintype.card ι : ℝ)) ≤ 1)
    (hbox : ∀ y ∈ K, ∀ i, (-ε ≤ y.1 i ∧ y.1 i ≤ 2) ∧ (-ε ≤ y.2 i ∧ y.2 i ≤ 2))
    (hQ : ∀ y ∈ K, ∑ i, y.1 i * y.2 i ≤ 1 / 100) (i : ι) :
    ¬ ((∃ y ∈ K, (1 / 4 : ℝ) ≤ y.1 i) ∧ (∃ y ∈ K, (1 / 4 : ℝ) ≤ y.2 i)) := by
  have hN : (1 : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast Fintype.card_pos_iff.2 ⟨i⟩
  have hε' : ε ≤ 1 / 400 := by nlinarith
  refine opposing_slots K hconv hε (by linarith) hbox hQ ?_ i
  nlinarith [sq_nonneg (1 / 400 - ε)]

end SPLP
