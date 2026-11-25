import Mathlib
import SPLP.Norm1
import SPLP.Compat
import SPLP.SubsetSums
import SPLP.PolyCount
import SPLP.CountArith
import SPLP.Minors

/-!
# Lemma 5.1 of the preprint with a much smaller constant

Section 5 of the preprint compresses the logarithms of the minors of the input matrix. Its
constant `D = (d+1)^6` bounds the size of a *dissociated* set of minors: one whose
log-magnitudes have subset sums pairwise far apart. The constant bounds the number of restarts
of the price search and enters the bit length of the demands, hence `log R`, polynomially.

The counting argument behind Lemma 5.1 is formalized here for general integer polynomials
(`dissociated_count`). It gives `2^(2^D) ≤ (2 · 2^D · L^D + 1)^((δ D + 1)^n)` for a dissociated
family of `D` polynomials in `n` variables with individual degrees at most `δ` and coefficient
1-norms at most `L`. For minors of a matrix with at most `d` rows and columns this fails
already at `D = 12 d² ⌈log₂ (d+1)⌉` (`minors_dissociated_card_lt`), far below `(d+1)^6`
(`Dnew_lt_paper`).
-/

namespace SPLP

open MvPolynomial Finset

/-- Subset sums pairwise more than one apart. -/
def LogDissociated {I : Type*} [DecidableEq I] (ℓ : I → ℝ) : Prop :=
  ∀ A B : Finset I, A ≠ B → 1 < |∑ u ∈ A, ℓ u - ∑ u ∈ B, ℓ u|

/-- The preprint states dissociation for proxies `v` within `η` of the logarithms, with subset
sums more than two apart. If `D η ≤ 1` the logarithms themselves are dissociated. -/
theorem logDissociated_of_proxy {I : Type*} [Fintype I] [DecidableEq I] (v ℓ : I → ℝ) {η : ℝ}
    (hη : Fintype.card I * η ≤ 1) (hv : ∀ u, |v u - ℓ u| ≤ η)
    (hdiss : ∀ A B : Finset I, A ≠ B → 2 < |∑ u ∈ A, v u - ∑ u ∈ B, v u|) :
    LogDissociated ℓ := by
  intro A B hAB
  have h2 := hdiss A B hAB
  rcases isEmpty_or_nonempty I with hI | ⟨⟨u₀⟩⟩
  · exact absurd (Subsingleton.elim A B) hAB
  have hη0 : 0 ≤ η := (abs_nonneg _).trans (hv u₀)
  have herr : |∑ u ∈ A, (v u - ℓ u) - ∑ u ∈ B, (v u - ℓ u)| ≤ 1 := by
    rw [← Finset.sum_sdiff_sub_sum_sdiff]
    have hdisj : Disjoint (A \ B) (B \ A) := disjoint_sdiff_sdiff
    calc |∑ u ∈ A \ B, (v u - ℓ u) - ∑ u ∈ B \ A, (v u - ℓ u)|
        ≤ |∑ u ∈ A \ B, (v u - ℓ u)| + |∑ u ∈ B \ A, (v u - ℓ u)| := abs_sub _ _
      _ ≤ ∑ u ∈ A \ B, |v u - ℓ u| + ∑ u ∈ B \ A, |v u - ℓ u| :=
          add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _)
      _ = ∑ u ∈ (A \ B) ∪ (B \ A), |v u - ℓ u| := (Finset.sum_union hdisj).symm
      _ ≤ ∑ _u ∈ (A \ B) ∪ (B \ A), η := Finset.sum_le_sum (fun u _ => hv u)
      _ = (((A \ B) ∪ (B \ A)).card : ℝ) * η := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Fintype.card I * η :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ _) hη0
      _ ≤ 1 := hη
  have hsplit : ∑ u ∈ A, ℓ u - ∑ u ∈ B, ℓ u
      = (∑ u ∈ A, v u - ∑ u ∈ B, v u)
        - (∑ u ∈ A, (v u - ℓ u) - ∑ u ∈ B, (v u - ℓ u)) := by
    simp only [Finset.sum_sub_distrib]
    ring
  rw [hsplit]
  have := abs_sub_abs_le_abs_sub (∑ u ∈ A, v u - ∑ u ∈ B, v u)
    (∑ u ∈ A, (v u - ℓ u) - ∑ u ∈ B, (v u - ℓ u))
  linarith

/-- **The counting argument of Lemma 5.1.** A dissociated family of integer polynomials,
evaluated at a real point, is small: all subset sums of subset products are distinct
polynomials of bounded degree and coefficient size. -/
theorem dissociated_count {σ : Type*} [Fintype σ] {I : Type*} [Fintype I] [DecidableEq I]
    (x : σ → ℝ) (q : I → MvPolynomial σ ℤ) (δ L : ℕ) (hL : 1 ≤ L)
    (hdeg : ∀ u v, (q u).degreeOf v ≤ δ) (hnorm : ∀ u, norm1 (q u) ≤ L)
    (hne : ∀ u, aeval x (q u) ≠ 0)
    (hdiss : LogDissociated (fun u => Real.logb 2 |aeval x (q u)|)) :
    2 ^ (2 ^ Fintype.card I) ≤
      (2 * (2 ^ Fintype.card I * L ^ Fintype.card I) + 1)
        ^ ((δ * Fintype.card I + 1) ^ Fintype.card σ) := by
  classical
  let y : Finset I → ℝ := fun A => ∏ u ∈ A, aeval x (q u)
  have hy : ∀ A, y A ≠ 0 := fun A => Finset.prod_ne_zero_iff.2 (fun u _ => hne u)
  have hlog : ∀ A, Real.logb 2 (abs (y A)) = ∑ u ∈ A, Real.logb 2 |aeval x (q u)| := by
    intro A
    simp only [y]
    rw [Finset.abs_prod, Real.logb_prod]
    intro u _
    exact abs_ne_zero.2 (hne u)
  have hinj := subsetSum_injective_of_sep y hy (by
    intro A B hAB
    rw [hlog, hlog]
    exact hdiss A B hAB)
  let P : Finset (Finset I) → MvPolynomial σ ℤ := fun T => ∑ A ∈ T, ∏ u ∈ A, q u
  have hP : ∀ T, aeval x (P T) = ∑ A ∈ T, y A := by
    intro T
    simp [P, y, map_sum, map_prod]
  have hPinj : Function.Injective P := by
    intro T T' h
    apply hinj
    show ∑ A ∈ T, y A = ∑ A ∈ T', y A
    rw [← hP, ← hP, h]
  have hbox : ∀ p ∈ (Finset.univ.image P),
      (∀ v, p.degreeOf v ≤ δ * Fintype.card I) ∧
        norm1 p ≤ 2 ^ Fintype.card I * L ^ Fintype.card I := by
    intro p hp
    obtain ⟨T, -, rfl⟩ := Finset.mem_image.1 hp
    constructor
    · intro v
      refine (degreeOf_sum_le v T _).trans ?_
      refine Finset.sup_le ?_
      intro A _
      refine (degreeOf_prod_le v A _).trans ?_
      calc ∑ u ∈ A, (q u).degreeOf v ≤ ∑ _u ∈ A, δ := Finset.sum_le_sum (fun u _ => hdeg u v)
        _ = A.card * δ := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ Fintype.card I * δ := Nat.mul_le_mul_right _ (Finset.card_le_univ A)
        _ = δ * Fintype.card I := Nat.mul_comm _ _
    · refine (norm1_sum_le T _).trans ?_
      calc ∑ A ∈ T, norm1 (∏ u ∈ A, q u) ≤ ∑ _A ∈ T, L ^ Fintype.card I := by
            refine Finset.sum_le_sum (fun A _ => ?_)
            refine (norm1_prod_le A _).trans ?_
            calc ∏ u ∈ A, norm1 (q u) ≤ ∏ _u ∈ A, L :=
                  prod_le_prod_nat _ _ _ (fun u _ => hnorm u)
              _ = L ^ A.card := by rw [Finset.prod_const]
              _ ≤ L ^ Fintype.card I := Nat.pow_le_pow_right hL (Finset.card_le_univ A)
        _ = T.card * L ^ Fintype.card I := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ 2 ^ Fintype.card I * L ^ Fintype.card I := by
            refine Nat.mul_le_mul_right _ ?_
            calc T.card ≤ Fintype.card (Finset I) := Finset.card_le_univ T
              _ = 2 ^ Fintype.card I := Fintype.card_finset
  have hcard := card_le_of_degreeOf_norm1 (Finset.univ.image P) hbox
  rw [Finset.card_image_of_injective _ hPinj, Finset.card_univ, Fintype.card_finset,
    Fintype.card_finset] at hcard
  exact hcard

/-- **Lemma 5.1 with the smaller constant.** Let `M` be a real matrix with at most `d` rows and
`d` columns. Every family of nonzero minors of `M` whose log-magnitudes are dissociated has
fewer than `12 d² ⌈log₂ (d+1)⌉` members. The preprint uses the bound `(d+1)^6`. -/
theorem minors_dissociated_card_lt {r c d : ℕ} (hr : r ≤ d) (hc : c ≤ d) (hd : 1 ≤ d)
    (M : Matrix (Fin r) (Fin c) ℝ) {I : Type*} [Fintype I] [DecidableEq I]
    (k : I → ℕ) (f : ∀ u, Fin (k u) → Fin r) (g : ∀ u, Fin (k u) → Fin c)
    (hg : ∀ u, Function.Injective (g u))
    (hne : ∀ u, (M.submatrix (f u) (g u)).det ≠ 0)
    (hdiss : LogDissociated (fun u => Real.logb 2 |(M.submatrix (f u) (g u)).det|)) :
    Fintype.card I < Dnew d := by
  classical
  by_contra hcon
  rw [not_lt] at hcon
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset I))
    (by simpa using hcon)
  have hk : ∀ u, k u ≤ d := fun u => by
    have := Fintype.card_le_of_injective _ (hg u)
    simp only [Fintype.card_fin] at this
    omega
  have key := dissociated_count (σ := Fin r × Fin c) (I := {u // u ∈ s})
    (fun v => M v.1 v.2) (fun u => minorPoly (f u) (g u)) 1 (Nat.factorial d)
    (Nat.factorial_pos d)
    (fun u v => minorPoly_degreeOf_le _ _ (hg u) v)
    (fun u => (minorPoly_norm1_le _ _).trans (Nat.factorial_le (hk u)))
    (fun u => by rw [minorPoly_eval]; exact hne u)
    (by
      intro A B hAB
      simp only [minorPoly_eval]
      have := hdiss (A.map (Function.Embedding.subtype _)) (B.map (Function.Embedding.subtype _))
        (fun h => hAB (Finset.map_injective _ h))
      rw [Finset.sum_map, Finset.sum_map] at this
      exact this)
  rw [Fintype.card_coe, hs, one_mul] at key
  have hrc : Fintype.card (Fin r × Fin c) ≤ d ^ 2 := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    calc r * c ≤ d * d := Nat.mul_le_mul hr hc
      _ = d ^ 2 := (sq d).symm
  have hmono : (2 * (2 ^ Dnew d * (Nat.factorial d) ^ Dnew d) + 1)
        ^ ((Dnew d + 1) ^ Fintype.card (Fin r × Fin c))
      ≤ (2 * (2 ^ Dnew d * (Nat.factorial d) ^ Dnew d) + 1) ^ ((Dnew d + 1) ^ (d ^ 2)) :=
    Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by omega) hrc)
  exact absurd (key.trans hmono) (not_le.2 (count_lt_Dnew d hd))

/-- The same statement in the preprint's form: dissociation is assumed for proxies `v` within
`η` of the logarithms, with tolerance two, and `η` is small against the new constant (the
preprint takes `η⁻¹ ≥ 4 D 2^K`). -/
theorem minors_proxy_dissociated_card_lt {r c d : ℕ} (hr : r ≤ d) (hc : c ≤ d) (hd : 1 ≤ d)
    (M : Matrix (Fin r) (Fin c) ℝ) {I : Type*} [Fintype I] [DecidableEq I]
    (k : I → ℕ) (f : ∀ u, Fin (k u) → Fin r) (g : ∀ u, Fin (k u) → Fin c)
    (hg : ∀ u, Function.Injective (g u))
    (hne : ∀ u, (M.submatrix (f u) (g u)).det ≠ 0)
    (v : I → ℝ) {η : ℝ} (hη : (Dnew d : ℝ) * η ≤ 1)
    (hv : ∀ u, |v u - Real.logb 2 (abs (M.submatrix (f u) (g u)).det)| ≤ η)
    (hdiss : ∀ A B : Finset I, A ≠ B → 2 < |∑ u ∈ A, v u - ∑ u ∈ B, v u|) :
    Fintype.card I < Dnew d := by
  classical
  by_contra hcon
  rw [not_lt] at hcon
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset I))
    (by simpa using hcon)
  have hcard : Fintype.card {u // u ∈ s} = Dnew d := by rw [Fintype.card_coe, hs]
  have hlog : LogDissociated (fun u : {u // u ∈ s} =>
      Real.logb 2 |(M.submatrix (f u) (g u)).det|) := by
    refine logDissociated_of_proxy (fun u : {u // u ∈ s} => v u) _ (η := η)
      (by rw [hcard]; exact hη) (fun u => hv u) ?_
    intro A B hAB
    have := hdiss (A.map (Function.Embedding.subtype _)) (B.map (Function.Embedding.subtype _))
      (fun h => hAB (Finset.map_injective _ h))
    rw [Finset.sum_map, Finset.sum_map] at this
    exact this
  have := minors_dissociated_card_lt hr hc hd M (I := {u // u ∈ s}) (fun u => k u)
    (fun u => f u) (fun u => g u) (fun u => hg u) (fun u => hne u) hlog
  omega

end SPLP
