import Mathlib

/-!
# Weak medians of finite families

A parity-free notion of median, sufficient for the coordinatewise-median steps of the
price search (Section 6 of the preprint).
-/

namespace SPLP

open Finset

/-- `x` is a (weak) median of the finite family `f`: at least half of the entries are `≤ x`
and at least half are `≥ x`. No parity assumption on `n` is needed. -/
def IsMedian {n : ℕ} (f : Fin n → ℝ) (x : ℝ) : Prop :=
  n ≤ 2 * (univ.filter (fun j => f j ≤ x)).card ∧
  n ≤ 2 * (univ.filter (fun j => x ≤ f j)).card

/-- The entries strictly below `x` and the entries at least `x` partition the index set. -/
private theorem card_lt_add_card_ge {n : ℕ} (f : Fin n → ℝ) (x : ℝ) :
    (univ.filter (fun j => f j < x)).card + (univ.filter (fun j => x ≤ f j)).card = n := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
    (fun j => f j < x)
  have h2 : (univ.filter (fun j => ¬ f j < x)) = (univ.filter (fun j => x ≤ f j)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
  rw [h2, Finset.card_univ, Fintype.card_fin] at h
  exact h

theorem exists_isMedian {n : ℕ} (f : Fin n → ℝ) : ∃ x, IsMedian f x := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- `n = 0`: every real number is a median of the empty family.
    exact ⟨0, by omega, by omega⟩
  · -- `n ≥ 1`: take the least value `f i` such that at least half of the entries are `≤ f i`.
    have hne : (univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    -- The largest value qualifies, since every entry is `≤` it.
    obtain ⟨iM, -, hiM⟩ := Finset.exists_max_image (univ : Finset (Fin n)) f hne
    have hSne : (univ.filter
        (fun i : Fin n => n ≤ 2 * (univ.filter (fun j => f j ≤ f i)).card)).Nonempty := by
      refine ⟨iM, ?_⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hall : (univ.filter (fun j => f j ≤ f iM)) = univ :=
        Finset.filter_true_of_mem (fun j hj => hiM j hj)
      rw [hall, Finset.card_univ, Fintype.card_fin]
      omega
    -- Take the least qualifying value.
    obtain ⟨i₀, hi₀S, hi₀min⟩ := Finset.exists_min_image _ f hSne
    rw [Finset.mem_filter] at hi₀S
    refine ⟨f i₀, hi₀S.2, ?_⟩
    by_contra hcon
    rw [not_le] at hcon
    have hsum := card_lt_add_card_ge f (f i₀)
    -- Otherwise more than half of the entries are strictly below `f i₀` ...
    have hpos : 0 < (univ.filter (fun j => f j < f i₀)).card := by omega
    -- ... and the largest of those values would be a smaller qualifying value.
    obtain ⟨i₁, hi₁mem, hi₁max⟩ := Finset.exists_max_image _ f (Finset.card_pos.mp hpos)
    have hi₁lt : f i₁ < f i₀ := (Finset.mem_filter.mp hi₁mem).2
    have hsub : (univ.filter (fun j => f j < f i₀)) ⊆ (univ.filter (fun j => f j ≤ f i₁)) := by
      intro j hj
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hi₁max j hj⟩
    have hcard := Finset.card_le_card hsub
    have hi₁S : i₁ ∈ univ.filter
        (fun i : Fin n => n ≤ 2 * (univ.filter (fun j => f j ≤ f i)).card) := by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      omega
    exact absurd hi₁lt (not_lt.mpr (hi₀min i₁ hi₁S))

theorem IsMedian.le_of_majority_ge {n : ℕ} {f : Fin n → ℝ} {x c : ℝ} (hx : IsMedian f x)
    (h : n < 2 * (univ.filter (fun j => c ≤ f j)).card) : c ≤ x := by
  obtain ⟨h1, -⟩ := hx
  -- The two sets have more than `n` elements in total, so they share an index.
  have hcard : (univ : Finset (Fin n)).card <
      (univ.filter (fun j => c ≤ f j)).card + (univ.filter (fun j => f j ≤ x)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  have hne : ((univ.filter (fun j => c ≤ f j)) ∩ (univ.filter (fun j => f j ≤ x))).Nonempty :=
    Finset.inter_nonempty_of_card_lt_card_add_card
      (Finset.filter_subset _ _) (Finset.filter_subset _ _) hcard
  obtain ⟨j, hj⟩ := hne
  rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at hj
  exact hj.1.2.trans hj.2.2

theorem IsMedian.ge_of_majority_le {n : ℕ} {f : Fin n → ℝ} {x c : ℝ} (hx : IsMedian f x)
    (h : n < 2 * (univ.filter (fun j => f j ≤ c)).card) : x ≤ c := by
  obtain ⟨-, h2⟩ := hx
  -- The two sets have more than `n` elements in total, so they share an index.
  have hcard : (univ : Finset (Fin n)).card <
      (univ.filter (fun j => x ≤ f j)).card + (univ.filter (fun j => f j ≤ c)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  have hne : ((univ.filter (fun j => x ≤ f j)) ∩ (univ.filter (fun j => f j ≤ c))).Nonempty :=
    Finset.inter_nonempty_of_card_lt_card_add_card
      (Finset.filter_subset _ _) (Finset.filter_subset _ _) hcard
  obtain ⟨j, hj⟩ := hne
  rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at hj
  exact hj.1.2.trans hj.2.2

theorem IsMedian.half_lt_of_lt {n : ℕ} {f : Fin n → ℝ} {x c : ℝ} (hx : IsMedian f x)
    (h : x < c) : n ≤ 2 * (univ.filter (fun j => f j < c)).card := by
  obtain ⟨h1, -⟩ := hx
  have hsub : (univ.filter (fun j => f j ≤ x)) ⊆ (univ.filter (fun j => f j < c)) := by
    intro j hj
    rw [Finset.mem_filter] at hj ⊢
    exact ⟨hj.1, lt_of_le_of_lt hj.2 h⟩
  have hcard := Finset.card_le_card hsub
  omega

theorem IsMedian.half_gt_of_gt {n : ℕ} {f : Fin n → ℝ} {x c : ℝ} (hx : IsMedian f x)
    (h : c < x) : n ≤ 2 * (univ.filter (fun j => c < f j)).card := by
  obtain ⟨-, h2⟩ := hx
  have hsub : (univ.filter (fun j => x ≤ f j)) ⊆ (univ.filter (fun j => c < f j)) := by
    intro j hj
    rw [Finset.mem_filter] at hj ⊢
    exact ⟨hj.1, lt_of_lt_of_le h hj.2⟩
  have hcard := Finset.card_le_card hsub
  omega

end SPLP
