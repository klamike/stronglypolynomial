import Mathlib
import SPLP.PairTest

/-!
# How much precision the label test needs

The preprint runs its label test (Section 3.2) on a matrix `B` that approximates a true scaled
basis `B*` within `2^-P`, with `H = 2^(100 N²)` bounding the coefficients of vectors of sup
norm one, `ε = H^-10` and `2^-P = H^-100`. Three facts, with explicit constants:

* `coeff_bound`: for rows in the echelon form produced by calibration (pivot entries of
  magnitude one, zeros at earlier pivots, entries at most two), a combination of sup norm at
  most one has `j`th coefficient at most `3^j` (rows counted from zero). This is the bound
  `3^(j-1)` in the preprint's proof of Theorem 3; so `H = 3^(r-1)` serves for `r` rows.
* `Qf_le_of_close`: the quadratic form `Q` of a vector within `δ` of one on which `Q`
  vanishes is at most `N δ (4 + δ)`.
* `label_test_sound`: if `δ = r H η` (rows × coefficient bound × entrywise error) satisfies
  `δ ≤ ε ≤ 1/(400 N)` and `δ ≤ 1/(500 N)`, then opposing slots never both pass the test at
  threshold `1/4`, and every true vector with coefficients at most `H`, entries in `[0, 1]`
  and an entry at least `1/3` makes the test pass at that slot.

So `2^-P` of order `1 / (N r H)` is enough, with `H = 3^(r-1)`: precision linear in `N`.
-/

namespace SPLP

open Finset

private lemma geom_aux (n : ℕ) : ∑ i ∈ range n, (2 : ℝ) * 3 ^ i = 3 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih, pow_succ]; ring

private lemma geom_aux' (r n : ℕ) :
    ∑ i : Fin r, (if (i : ℕ) < n then (2 : ℝ) * 3 ^ (i : ℕ) else 0) ≤ 3 ^ n - 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < n then (2 : ℝ) * 3 ^ i else 0) r, ← geom_aux n,
    ← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    simp only [mem_filter, mem_range] at hi ⊢
    exact hi.2
  · intros; positivity

theorem coeff_bound {S : Type*} {r : ℕ} (b : Fin r → S → ℝ) (t : Fin r → S)
    (hpiv : ∀ j, |b j (t j)| = 1) (hzero : ∀ i j, i < j → b j (t i) = 0)
    (hnorm : ∀ j s, |b j s| ≤ 2) (ξ : Fin r → ℝ)
    (hv : ∀ s, |∑ j, ξ j * b j s| ≤ 1) : ∀ j, |ξ j| ≤ 3 ^ (j : ℕ) := by
  suffices h : ∀ n, ∀ j : Fin r, (j : ℕ) = n → |ξ j| ≤ 3 ^ n from fun j => h j j rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro j hjn
    subst hjn
    have hsplit : ∑ i, ξ i * b i (t j)
        = ∑ i, (if i < j then ξ i * b i (t j) else 0) + ξ j * b j (t j) := by
      have hpt : ∀ i, ξ i * b i (t j) = (if i < j then ξ i * b i (t j) else 0)
          + (if i = j then ξ j * b j (t j) else 0) := by
        intro i
        rcases lt_trichotomy i j with h | h | h
        · simp [h, h.ne]
        · subst h; simp
        · simp [not_lt.2 h.le, h.ne', hzero j i h]
      rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_add_distrib, Finset.sum_ite_eq']
      simp
    have hgb : ∀ i : Fin r, |if i < j then ξ i * b i (t j) else 0|
        ≤ if (i : ℕ) < (j : ℕ) then (2 : ℝ) * 3 ^ (i : ℕ) else 0 := by
      intro i
      by_cases h : i < j
      · have h' : (i : ℕ) < (j : ℕ) := h
        rw [if_pos h, if_pos h', abs_mul, mul_comm (2 : ℝ)]
        exact mul_le_mul (ih i h' i rfl) (hnorm i (t j)) (abs_nonneg _) (by positivity)
      · have h' : ¬ (i : ℕ) < (j : ℕ) := h
        rw [if_neg h, if_neg h', abs_zero]
    have h1 : |∑ i, (if i < j then ξ i * b i (t j) else 0)| ≤ 3 ^ (j : ℕ) - 1 :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        ((Finset.sum_le_sum fun i _ => hgb i).trans (geom_aux' r j))
    have h2 := hv (t j)
    have h3 : |ξ j| = |ξ j * b j (t j)| := by rw [abs_mul, hpiv j, mul_one]
    rw [h3]
    rw [hsplit] at h2
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

/-- The combination of the rows `B` with coefficients `ξ`; vectors on paired slots are pairs. -/
def comb (ξ : Fin r → ℝ) (B : Fin r → (ι → ℝ) × (ι → ℝ)) : (ι → ℝ) × (ι → ℝ) :=
  ∑ j, ξ j • B j

/-- The quadratic form `Q(y) = ∑ i, y_{i+} y_{i-}`. -/
def Qf (y : (ι → ℝ) × (ι → ℝ)) : ℝ := ∑ i, y.1 i * y.2 i

/-- The convex set of the label test: bounded combinations of the rows with entries in
`[-ε, 2]`. -/
def testBox (B : Fin r → (ι → ℝ) × (ι → ℝ)) (H ε : ℝ) : Set ((ι → ℝ) × (ι → ℝ)) :=
  {y | ∃ ξ : Fin r → ℝ, (∀ j, |ξ j| ≤ H) ∧ y = comb ξ B ∧
    ∀ i, (-ε ≤ y.1 i ∧ y.1 i ≤ 2) ∧ (-ε ≤ y.2 i ∧ y.2 i ≤ 2)}

omit [Fintype ι] [DecidableEq ι] in
theorem comb_fst (ξ : Fin r → ℝ) (B : Fin r → (ι → ℝ) × (ι → ℝ)) (i : ι) :
    (comb ξ B).1 i = ∑ j, ξ j * (B j).1 i := by
  simp [comb, Prod.fst_sum, Finset.sum_apply]

omit [Fintype ι] [DecidableEq ι] in
theorem comb_snd (ξ : Fin r → ℝ) (B : Fin r → (ι → ℝ) × (ι → ℝ)) (i : ι) :
    (comb ξ B).2 i = ∑ j, ξ j * (B j).2 i := by
  simp [comb, Prod.snd_sum, Finset.sum_apply]

private lemma convex_aux {a b u u' lo hi : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (h1 : lo ≤ u ∧ u ≤ hi) (h2 : lo ≤ u' ∧ u' ≤ hi) :
    lo ≤ a * u + b * u' ∧ a * u + b * u' ≤ hi := by
  have e1 : (a + b) * lo = lo := by rw [hab, one_mul]
  have e2 : (a + b) * hi = hi := by rw [hab, one_mul]
  constructor
  · linarith [mul_nonneg ha (sub_nonneg.2 h1.1), mul_nonneg hb (sub_nonneg.2 h2.1)]
  · linarith [mul_nonneg ha (sub_nonneg.2 h1.2), mul_nonneg hb (sub_nonneg.2 h2.2)]

private lemma close_aux (ξ u us : Fin r → ℝ) {H η : ℝ} (hξ : ∀ j, |ξ j| ≤ H)
    (hu : ∀ j, |u j - us j| ≤ η) :
    |∑ j, ξ j * u j - ∑ j, ξ j * us j| ≤ r * H * η := by
  rw [← Finset.sum_sub_distrib]
  calc |∑ j, (ξ j * u j - ξ j * us j)| ≤ ∑ j, |ξ j * u j - ξ j * us j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin r, H * η := by
        apply Finset.sum_le_sum
        intro j _
        rw [← mul_sub, abs_mul]
        exact mul_le_mul (hξ j) (hu j) (abs_nonneg _) ((abs_nonneg _).trans (hξ j))
    _ = r * H * η := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

omit [Fintype ι] [DecidableEq ι] in
theorem testBox_convex (B : Fin r → (ι → ℝ) × (ι → ℝ)) (H ε : ℝ) :
    Convex ℝ (testBox B H ε) := by
  rintro y ⟨ξ, hξ, rfl, hy⟩ y' ⟨ξ', hξ', rfl, hy'⟩ a b ha hb hab
  refine ⟨fun j => a * ξ j + b * ξ' j, ?_, ?_, ?_⟩
  · intro j
    calc |a * ξ j + b * ξ' j| ≤ |a * ξ j| + |b * ξ' j| := abs_add_le _ _
      _ = a * |ξ j| + b * |ξ' j| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * H + b * H :=
          add_le_add (mul_le_mul_of_nonneg_left (hξ j) ha) (mul_le_mul_of_nonneg_left (hξ' j) hb)
      _ = H := by rw [← add_mul, hab, one_mul]
  · simp only [comb, Finset.smul_sum, ← Finset.sum_add_distrib, smul_smul, add_smul]
  · intro i
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    exact ⟨convex_aux ha hb hab (hy i).1 (hy' i).1, convex_aux ha hb hab (hy i).2 (hy' i).2⟩

omit [Fintype ι] [DecidableEq ι] in
theorem comb_close (B Bs : Fin r → (ι → ℝ) × (ι → ℝ)) {H η : ℝ}
    (hclose : ∀ j i, |(B j).1 i - (Bs j).1 i| ≤ η ∧ |(B j).2 i - (Bs j).2 i| ≤ η)
    (ξ : Fin r → ℝ) (hξ : ∀ j, |ξ j| ≤ H) (i : ι) :
    |(comb ξ B).1 i - (comb ξ Bs).1 i| ≤ r * H * η ∧
      |(comb ξ B).2 i - (comb ξ Bs).2 i| ≤ r * H * η := by
  constructor
  · rw [comb_fst, comb_fst]
    exact close_aux ξ _ _ hξ (fun j => (hclose j i).1)
  · rw [comb_snd, comb_snd]
    exact close_aux ξ _ _ hξ (fun j => (hclose j i).2)

omit [DecidableEq ι] in
theorem Qf_le_of_close (y ys : (ι → ℝ) × (ι → ℝ)) {δ : ℝ} (hQ : Qf ys = 0)
    (hclose : ∀ i, |y.1 i - ys.1 i| ≤ δ ∧ |y.2 i - ys.2 i| ≤ δ)
    (hbox : ∀ i, |y.1 i| ≤ 2 ∧ |y.2 i| ≤ 2) :
    Qf y ≤ Fintype.card ι * (δ * (4 + δ)) := by
  have hterm : ∀ i, y.1 i * y.2 i ≤ ys.1 i * ys.2 i + δ * (4 + δ) := by
    intro i
    obtain ⟨h1, h2⟩ := hclose i
    obtain ⟨h3, h4⟩ := hbox i
    have hδ : 0 ≤ δ := (abs_nonneg _).trans h1
    have hb' : |ys.2 i| ≤ 2 + δ := by
      rw [abs_le] at h2 h4 ⊢
      constructor <;> linarith [h2.1, h2.2, h4.1, h4.2]
    have e1 : y.1 i * (y.2 i - ys.2 i) ≤ 2 * δ :=
      (le_abs_self _).trans (by
        rw [abs_mul]
        exact mul_le_mul h3 h2 (abs_nonneg _) (by norm_num))
    have e2 : ys.2 i * (y.1 i - ys.1 i) ≤ (2 + δ) * δ :=
      (le_abs_self _).trans (by
        rw [abs_mul]
        exact mul_le_mul hb' h1 (abs_nonneg _) (by linarith))
    have e3 : y.1 i * y.2 i
        = ys.1 i * ys.2 i + y.1 i * (y.2 i - ys.2 i) + ys.2 i * (y.1 i - ys.1 i) := by ring
    rw [e3]
    linarith
  have hQ' : ∑ i, ys.1 i * ys.2 i = 0 := hQ
  calc Qf y = ∑ i, y.1 i * y.2 i := rfl
    _ ≤ ∑ i, (ys.1 i * ys.2 i + δ * (4 + δ)) := Finset.sum_le_sum fun i _ => hterm i
    _ = Fintype.card ι * (δ * (4 + δ)) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hQ',
          zero_add]

/-- **The label test with explicit precision.** -/
theorem label_test_sound (B Bs : Fin r → (ι → ℝ) × (ι → ℝ)) {H ε η : ℝ}
    (hH : 0 ≤ H) (hη : 0 ≤ η)
    (hclose : ∀ j i, |(B j).1 i - (Bs j).1 i| ≤ η ∧ |(B j).2 i - (Bs j).2 i| ≤ η)
    (hQ : ∀ ξ : Fin r → ℝ, Qf (comb ξ Bs) = 0)
    (hδε : r * H * η ≤ ε) (hεN : ε * (400 * (Fintype.card ι : ℝ)) ≤ 1)
    (hδN : r * H * η * (500 * (Fintype.card ι : ℝ)) ≤ 1) :
    (∀ i, ¬ ((∃ y ∈ testBox B H ε, (1 / 4 : ℝ) ≤ y.1 i) ∧
        (∃ y ∈ testBox B H ε, (1 / 4 : ℝ) ≤ y.2 i))) ∧
    (∀ ξ : Fin r → ℝ, (∀ j, |ξ j| ≤ H) →
      (∀ i, (0 ≤ (comb ξ Bs).1 i ∧ (comb ξ Bs).1 i ≤ 1) ∧
        (0 ≤ (comb ξ Bs).2 i ∧ (comb ξ Bs).2 i ≤ 1)) →
      ∀ i, ((1 / 3 : ℝ) ≤ (comb ξ Bs).1 i → ∃ y ∈ testBox B H ε, (1 / 4 : ℝ) ≤ y.1 i) ∧
        ((1 / 3 : ℝ) ≤ (comb ξ Bs).2 i → ∃ y ∈ testBox B H ε, (1 / 4 : ℝ) ≤ y.2 i)) := by
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = r * H * η := ⟨_, rfl⟩
  rw [← hδ] at hδε hδN
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hε : 0 ≤ ε := hδ0.trans hδε
  have hcc : ∀ ξ : Fin r → ℝ, (∀ j, |ξ j| ≤ H) → ∀ i,
      |(comb ξ B).1 i - (comb ξ Bs).1 i| ≤ δ ∧ |(comb ξ B).2 i - (comb ξ Bs).2 i| ≤ δ := by
    intro ξ hξ i
    rw [hδ]
    exact comb_close B Bs hclose ξ hξ i
  have hN : ι → (1 : ℝ) ≤ Fintype.card ι := fun i => by
    exact_mod_cast Fintype.card_pos_iff.2 ⟨i⟩
  have hδs : ι → δ ≤ 1 / 500 := fun i => by
    nlinarith [mul_nonneg hδ0 (sub_nonneg.2 (hN i))]
  have hεs : ι → ε ≤ 1 / 400 := fun i => by
    nlinarith [mul_nonneg hε (sub_nonneg.2 (hN i))]
  constructor
  · intro i
    have hbox : ∀ y ∈ testBox B H ε, ∀ i,
        (-ε ≤ y.1 i ∧ y.1 i ≤ 2) ∧ (-ε ≤ y.2 i ∧ y.2 i ≤ 2) := by
      rintro y ⟨ξ, _, _, hy⟩
      exact hy
    have hQ' : ∀ y ∈ testBox B H ε, ∑ i, y.1 i * y.2 i ≤ 1 / 100 := by
      rintro y ⟨ξ, hξ, rfl, hy⟩
      have hle := Qf_le_of_close (comb ξ B) (comb ξ Bs) (hQ ξ) (hcc ξ hξ)
        (fun k => ⟨abs_le.2 ⟨by linarith [(hy k).1.1, hεs i], (hy k).1.2⟩,
          abs_le.2 ⟨by linarith [(hy k).2.1, hεs i], (hy k).2.2⟩⟩)
      have hNδ : (Fintype.card ι : ℝ) * δ ≤ 1 / 500 := by linarith
      have hprod : (Fintype.card ι : ℝ) * δ * (4 + δ) ≤ 1 / 500 * (4 + 1 / 500) :=
        mul_le_mul hNδ (by linarith [hδs i]) (by linarith) (by norm_num)
      show Qf (comb ξ B) ≤ 1 / 100
      calc Qf (comb ξ B) ≤ Fintype.card ι * (δ * (4 + δ)) := hle
        _ = (Fintype.card ι : ℝ) * δ * (4 + δ) := by ring
        _ ≤ 1 / 500 * (4 + 1 / 500) := hprod
        _ ≤ 1 / 100 := by norm_num
    exact opposing_slots_quarter (testBox B H ε) (testBox_convex B H ε) hε hεN hbox hQ' i
  · intro ξ hξ hbnd i
    have hmem : comb ξ B ∈ testBox B H ε := by
      refine ⟨ξ, hξ, rfl, fun k => ?_⟩
      obtain ⟨c1, c2⟩ := hcc ξ hξ k
      obtain ⟨⟨b1, b2⟩, b3, b4⟩ := hbnd k
      rw [abs_le] at c1 c2
      have := hδs i
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [c1.1, c1.2, c2.1, c2.2]
    obtain ⟨c1, c2⟩ := hcc ξ hξ i
    rw [abs_le] at c1 c2
    have := hδs i
    exact ⟨fun h => ⟨_, hmem, by linarith [c1.1]⟩, fun h => ⟨_, hmem, by linarith [c2.1]⟩⟩

end SPLP
