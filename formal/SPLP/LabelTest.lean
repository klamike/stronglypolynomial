import Mathlib

/-!
# The label test has a margin governed by its tolerance

In the preprint the label of a coordinate `i` at prices `p` comes from a feasibility test
(its Section 3): give `i` the label `+` if the scaled space contains a vector with all entries
at least `-ε` and `i`th entry at least `θ`. The test cannot tell entries in `[-ε, 0)` from
zero, so it may pass on the wrong side.

`falsePositive_bound` quantifies this. Let `c` lie in a subspace and `u ≥ 0` in its orthogonal
complement, and let `d` be the positive scaling of the first space, so that the second is
scaled by `1 / d`. If the scaled `c` passes the test at `i`, the scaled entry of `u` at `i` is
at most `ε / θ` times the sum of its other scaled entries. So a wrong `+` can occur only when
the true witness is far from visible at `i`: the test is correct on every slot whose scaled
entry is within a factor `θ / ((N - 1) ε)` of the largest one (`falsePositive_bound_max`).
In the logarithmic units of the price search this is a margin of `log₂ (θ / ((N - 1) ε))`,
which grows linearly with the number of bits of precision spent on the test.
-/

namespace SPLP

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A vector passing the tolerant test at `i` bounds the scaled entry at `i` of every
nonnegative vector orthogonal to it. -/
theorem falsePositive_bound (c u d : ι → ℝ) (i : ι) {ε θ : ℝ}
    (hd : ∀ j, 0 < d j) (hu : ∀ j, 0 ≤ u j) (horth : ∑ j, c j * u j = 0)
    (hneg : ∀ j, -ε ≤ c j * d j) (hi : θ ≤ c i * d i) :
    θ * (u i / d i) ≤ ε * ∑ j ∈ univ.erase i, u j / d j := by
  have h1 : c i * u i = ∑ j ∈ univ.erase i, -(c j * u j) := by
    have := Finset.add_sum_erase univ (fun j => c j * u j) (mem_univ i)
    rw [Finset.sum_neg_distrib]
    linarith
  have h2 : ∀ j, -(c j * u j) ≤ ε * (u j / d j) := by
    intro j
    have hc : -(c j) ≤ ε / d j := by
      rw [le_div_iff₀ (hd j)]
      linarith [hneg j]
    calc -(c j * u j) = -(c j) * u j := by ring
      _ ≤ ε / d j * u j := mul_le_mul_of_nonneg_right hc (hu j)
      _ = ε * (u j / d j) := by ring
  have h3 : θ * (u i / d i) ≤ c i * u i := by
    have hc : θ / d i ≤ c i := by
      rw [div_le_iff₀ (hd i)]
      exact hi
    calc θ * (u i / d i) = θ / d i * u i := by ring
      _ ≤ c i * u i := mul_le_mul_of_nonneg_right hc (hu i)
  calc θ * (u i / d i) ≤ c i * u i := h3
    _ = ∑ j ∈ univ.erase i, -(c j * u j) := h1
    _ ≤ ∑ j ∈ univ.erase i, ε * (u j / d j) := Finset.sum_le_sum (fun j _ => h2 j)
    _ = ε * ∑ j ∈ univ.erase i, u j / d j := by rw [Finset.mul_sum]

/-- The same bound against the largest scaled entry `M` of `u`. -/
theorem falsePositive_bound_max (c u d : ι → ℝ) (i : ι) {ε θ M : ℝ} (hε : 0 ≤ ε)
    (hd : ∀ j, 0 < d j) (hu : ∀ j, 0 ≤ u j) (horth : ∑ j, c j * u j = 0)
    (hneg : ∀ j, -ε ≤ c j * d j) (hi : θ ≤ c i * d i) (hM : ∀ j, u j / d j ≤ M) :
    θ * (u i / d i) ≤ ε * ((Fintype.card ι - 1 : ℕ) * M) := by
  refine (falsePositive_bound c u d i hd hu horth hneg hi).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hε
  calc ∑ j ∈ univ.erase i, u j / d j ≤ ∑ _j ∈ univ.erase i, M :=
        Finset.sum_le_sum (fun j _ => hM j)
    _ = ((Fintype.card ι - 1 : ℕ) : ℝ) * M := by
        rw [Finset.sum_const, Finset.card_erase_of_mem (mem_univ i), Finset.card_univ,
          nsmul_eq_mul]

/-- With no tolerance the test is never wrong: if a nonnegative vector of the space has a
positive `i`th entry, every nonnegative vector orthogonal to it vanishes at `i`. All errors of
the label test come from its tolerance. -/
theorem exact_test_sound (c u : ι → ℝ) (i : ι) (hc : ∀ j, 0 ≤ c j) (hu : ∀ j, 0 ≤ u j)
    (horth : ∑ j, c j * u j = 0) (hi : 0 < c i) : u i = 0 := by
  have h := falsePositive_bound c u (fun _ => 1) i (ε := 0) (θ := c i)
    (fun _ => one_pos) hu horth (fun j => by simpa using hc j) (by simp)
  simp only [div_one, zero_mul] at h
  have h2 : u i ≤ 0 := by
    by_contra hcon
    have := mul_pos hi (not_le.1 hcon)
    linarith
  exact le_antisymm h2 (hu i)

end SPLP
