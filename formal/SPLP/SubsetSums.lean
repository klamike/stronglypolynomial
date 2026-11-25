import Mathlib

/-!
# Subset sums of numbers whose magnitudes are separated by more than a factor of two

If nonzero reals have base-two log-magnitudes pairwise more than one apart, then in increasing
order of magnitude each exceeds the sum of all smaller ones, so two different subsets have
different sums: they differ at a largest element, whose contribution survives cancellation.
This is the first step of the proof of Lemma 5.1 of the preprint.
-/

namespace SPLP

open Finset

/-- Separation of log-magnitudes by more than one gives a factor of more than two. -/
lemma two_mul_abs_lt_of_sep {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hsep : 1 < |Real.logb 2 (abs a) - Real.logb 2 (abs b)|) (hle : |b| ≤ |a|) : 2 * |b| < |a| := by
  have hapos : 0 < |a| := abs_pos.mpr ha
  have hbpos : 0 < |b| := abs_pos.mpr hb
  have hmono : Real.logb 2 |b| ≤ Real.logb 2 |a| :=
    Real.logb_le_logb_of_le (by norm_num) hbpos hle
  rw [abs_of_nonneg (sub_nonneg.mpr hmono)] at hsep
  have h2 : Real.logb 2 (2 * |b|) = 1 + Real.logb 2 |b| := by
    rw [Real.logb_mul (by norm_num) hbpos.ne', Real.logb_self_eq_one (by norm_num)]
  have h3 : Real.logb 2 (2 * |b|) < Real.logb 2 |a| := by rw [h2]; linarith
  exact (Real.logb_lt_logb_iff (by norm_num) (by positivity) hapos).mp h3

/-- With magnitudes separated by factors of more than two, any finite family of magnitudes
each at most half of `c` sums to less than `c`. -/
lemma sum_abs_lt_of_sep {I : Type*} [DecidableEq I] (y : I → ℝ)
    (hy : ∀ i, y i ≠ 0)
    (hsep : ∀ i j, i ≠ j → 1 < |Real.logb 2 (abs (y i)) - Real.logb 2 (abs (y j))|)
    (S : Finset I) : ∀ c : ℝ, 0 < c → (∀ j ∈ S, 2 * |y j| ≤ c) → ∑ j ∈ S, |y j| < c := by
  induction S using Finset.induction_on_max_value (fun i => |y i|) with
  | empty => intro c hc _; simpa using hc
  | insert m s hm hmax ih =>
    intro c hc hall
    rw [Finset.sum_insert hm]
    have h1 : ∑ j ∈ s, |y j| < |y m| := by
      refine ih _ (abs_pos.mpr (hy m)) ?_
      intro j hj
      have hne : m ≠ j := fun h => hm (h ▸ hj)
      exact (two_mul_abs_lt_of_sep (hy m) (hy j) (hsep m j hne) (hmax j hj)).le
    have h2 := hall m (Finset.mem_insert_self m s)
    linarith

/-- Two disjoint index sets whose union has a largest-magnitude element in the first set have
different sums. -/
lemma sum_ne_sum_of_max {I : Type*} [DecidableEq I] (y : I → ℝ)
    (hy : ∀ i, y i ≠ 0)
    (hsep : ∀ i j, i ≠ j → 1 < |Real.logb 2 (abs (y i)) - Real.logb 2 (abs (y j))|)
    (A B : Finset I) (hAB : Disjoint A B) (i : I) (hiA : i ∈ A)
    (hmax : ∀ j ∈ A ∪ B, |y j| ≤ |y i|) : ∑ j ∈ A, y j ≠ ∑ j ∈ B, y j := by
  intro heq
  have hiB : i ∉ B := Finset.disjoint_left.mp hAB hiA
  have hdisj : Disjoint (A.erase i) B := hAB.mono_left (Finset.erase_subset _ _)
  have hlt : ∑ j ∈ A.erase i ∪ B, |y j| < |y i| := by
    refine sum_abs_lt_of_sep y hy hsep _ _ (abs_pos.mpr (hy i)) ?_
    intro j hj
    have hne : i ≠ j := by
      rintro rfl
      rcases Finset.mem_union.mp hj with h | h
      · exact Finset.notMem_erase _ _ h
      · exact hiB h
    have hj' : j ∈ A ∪ B := by
      rcases Finset.mem_union.mp hj with h | h
      · exact Finset.mem_union_left _ (Finset.mem_of_mem_erase h)
      · exact Finset.mem_union_right _ h
    exact (two_mul_abs_lt_of_sep (hy i) (hy j) (hsep i j hne) (hmax j hj')).le
  rw [Finset.sum_union hdisj] at hlt
  have hsplit : ∑ j ∈ A, y j = y i + ∑ j ∈ A.erase i, y j :=
    (Finset.add_sum_erase A y hiA).symm
  have hyi : y i = ∑ j ∈ B, y j - ∑ j ∈ A.erase i, y j := by linarith
  have habs : |y i| ≤ ∑ j ∈ B, |y j| + ∑ j ∈ A.erase i, |y j| := by
    rw [hyi]
    calc |∑ j ∈ B, y j - ∑ j ∈ A.erase i, y j|
        ≤ |∑ j ∈ B, y j| + |∑ j ∈ A.erase i, y j| := abs_sub _ _
      _ ≤ _ := add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _)
  linarith

theorem subsetSum_injective_of_sep {I : Type*} [Fintype I] [DecidableEq I] (y : I → ℝ)
    (hy : ∀ i, y i ≠ 0)
    (hsep : ∀ i j, i ≠ j → 1 < |Real.logb 2 (abs (y i)) - Real.logb 2 (abs (y j))|) :
    Function.Injective (fun T : Finset I => ∑ i ∈ T, y i) := by
  intro T T' hsum
  simp only at hsum
  by_contra hne
  have hD : ((T \ T') ∪ (T' \ T)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [Finset.union_eq_empty, Finset.sdiff_eq_empty_iff_subset,
      Finset.sdiff_eq_empty_iff_subset] at h
    exact hne (Finset.Subset.antisymm h.1 h.2)
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image _ (fun j => |y j|) hD
  have hdiff : ∑ j ∈ T \ T', y j = ∑ j ∈ T' \ T, y j := by
    have := Finset.sum_sdiff_sub_sum_sdiff (s₁ := T) (s₂ := T') (f := y)
    linarith
  have hdisj : Disjoint (T \ T') (T' \ T) := disjoint_sdiff_sdiff
  rcases Finset.mem_union.mp hi with h | h
  · exact sum_ne_sum_of_max y hy hsep _ _ hdisj i h hmax hdiff
  · refine sum_ne_sum_of_max y hy hsep _ _ hdisj.symm i h ?_ hdiff.symm
    intro j hj
    exact hmax j (by rwa [Finset.union_comm])

end SPLP
