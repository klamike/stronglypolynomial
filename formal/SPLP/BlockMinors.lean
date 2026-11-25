import Mathlib

/-!
# Cofactor vectors of a block-diagonal basis are one-sided

The preprint calibrates a row basis `B0` of `W = C × C⊥`, whose columns are the slots: the
positive slots carry `C`, the negative slots carry `C⊥`. For a block-diagonal basis (rows of
`C` vanish on negative slots, rows of `C⊥` on positive slots), a square minor can be nonzero
only if it uses as many positive columns as rows of `C`. Hence a cofactor vector
`c_s = det B0[rows, (T, s)]` cannot be nonzero both at a positive and at a negative slot `s`:
its support lies on one side.
-/

namespace SPLP

open Finset

/-- A square matrix with a block structure (rows marked by `R`, columns by `Cc`, zero off the
two diagonal blocks) is singular unless the two markings have the same number of indices. -/
theorem det_eq_zero_of_block_card {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (R Cc : Fin n → Prop) [DecidablePred R] [DecidablePred Cc]
    (h0 : ∀ a b, (R a ∧ ¬ Cc b) ∨ (¬ R a ∧ Cc b) → M a b = 0)
    (hcard : (univ.filter R).card ≠ (univ.filter Cc).card) : M.det = 0 := by
  rw [Matrix.det_apply]
  apply Finset.sum_eq_zero
  intro σ _
  have hex : ∃ i, (R (σ i) ∧ ¬ Cc i) ∨ (¬ R (σ i) ∧ Cc i) := by
    by_contra hne
    apply hcard
    have hiff : ∀ i, R (σ i) ↔ Cc i := by
      intro i
      have := fun h => hne ⟨i, h⟩
      tauto
    have hmap : (univ.filter Cc).map σ.toEmbedding = univ.filter R := by
      ext a
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Equiv.toEmbedding_apply]
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact (hiff i).2 hi
      · intro ha
        refine ⟨σ.symm a, (hiff _).1 ?_, by simp⟩
        simpa using ha
    rw [← hmap, Finset.card_map]
  obtain ⟨i, hi⟩ := hex
  have hprod : ∏ j, M (σ j) j = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (h0 _ _ hi)
  rw [hprod, smul_zero]

/-- **One-sidedness.** Let `B` vanish off its two diagonal blocks (rows marked by `R`, columns
by `Cc`). Two square minors with the same rows `f` and with columns `g₁`, `g₂` that agree
except at one position `i₀`, where `g₁` picks a marked and `g₂` an unmarked column, cannot
both be nonzero. -/
theorem block_minors_one_sided {ρ κ : Type*} {n : ℕ} (B : Matrix ρ κ ℝ)
    (R : ρ → Prop) (Cc : κ → Prop) [DecidablePred R] [DecidablePred Cc]
    (h0 : ∀ a b, (R a ∧ ¬ Cc b) ∨ (¬ R a ∧ Cc b) → B a b = 0)
    (f : Fin n → ρ) (g₁ g₂ : Fin n → κ) (i₀ : Fin n)
    (hagree : ∀ i, i ≠ i₀ → g₁ i = g₂ i) (h1 : Cc (g₁ i₀)) (h2 : ¬ Cc (g₂ i₀)) :
    ¬ ((B.submatrix f g₁).det ≠ 0 ∧ (B.submatrix f g₂).det ≠ 0) := by
  rintro ⟨hd1, hd2⟩
  have e1 : (univ.filter fun a => R (f a)).card = (univ.filter fun b => Cc (g₁ b)).card := by
    by_contra h
    exact hd1 (det_eq_zero_of_block_card (B.submatrix f g₁) (fun a => R (f a))
      (fun b => Cc (g₁ b)) (fun a b h => h0 _ _ h) h)
  have e2 : (univ.filter fun a => R (f a)).card = (univ.filter fun b => Cc (g₂ b)).card := by
    by_contra h
    exact hd2 (det_eq_zero_of_block_card (B.submatrix f g₂) (fun a => R (f a))
      (fun b => Cc (g₂ b)) (fun a b h => h0 _ _ h) h)
  have hins : (univ.filter fun b => Cc (g₁ b)) = insert i₀ (univ.filter fun b => Cc (g₂ b)) := by
    ext b
    simp only [mem_filter, mem_univ, true_and, mem_insert]
    by_cases hb : b = i₀
    · subst hb
      simp [h1]
    · rw [hagree b hb]
      simp [hb]
  have hnot : i₀ ∉ univ.filter fun b => Cc (g₂ b) := by simp [h2]
  rw [hins, card_insert_of_notMem hnot] at e1
  omega

end SPLP
