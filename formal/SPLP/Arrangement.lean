import Mathlib

/-!
# Sign vectors of affine forms

`n` affine forms on a real vector space of dimension at most `k` realize at most
`∑_{i ≤ k} 2^i (n choose i)` sign vectors in `{-1, 0, 1}^n` (the number of faces of `n`
hyperplanes in general position). This is the counting fact behind the bound on the number of
expert cells in the market step.
-/

namespace SPLP

open Finset

/-- `∑_{i ≤ k} 2^i (n choose i)`. -/
def faceBound (n k : ℕ) : ℕ := ∑ i ∈ range (k + 1), 2 ^ i * n.choose i

theorem faceBound_mono_left {n n' : ℕ} (h : n ≤ n') (k : ℕ) :
    faceBound n k ≤ faceBound n' k := by
  unfold faceBound
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (Nat.choose_le_choose i h)

theorem faceBound_mono_right (n : ℕ) {k k' : ℕ} (h : k ≤ k') :
    faceBound n k ≤ faceBound n k' := by
  unfold faceBound
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_succ h))

theorem faceBound_le_pow (n k : ℕ) : faceBound n k ≤ (2 * n + 1) ^ k := by
  unfold faceBound
  -- compare termwise with the binomial expansion of `(2 * n + 1) ^ k`
  rw [add_pow]
  refine Finset.sum_le_sum fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have h1 : n.choose i ≤ n ^ i := Nat.choose_le_pow n i
  have h2 : 1 ≤ k.choose i := Nat.choose_pos hik
  calc 2 ^ i * n.choose i ≤ 2 ^ i * n ^ i * 1 := by
        rw [mul_one]; exact Nat.mul_le_mul_left _ h1
    _ ≤ 2 ^ i * n ^ i * k.choose i := Nat.mul_le_mul_left _ h2
    _ = (2 * n) ^ i * 1 ^ (k - i) * k.choose i := by rw [mul_pow, one_pow, mul_one]

/-- `faceBound 0 k = 1`: only the term `i = 0` survives. -/
private theorem faceBound_zero_left (k : ℕ) : faceBound 0 k = 1 := by
  unfold faceBound
  rw [Finset.sum_range_succ']
  simp

/-- Pascal-type recursion for `faceBound`, matching deletion–restriction. -/
private theorem faceBound_succ_succ (n k : ℕ) :
    faceBound (n + 1) (k + 1) = faceBound n (k + 1) + 2 * faceBound n k := by
  unfold faceBound
  rw [Finset.sum_range_succ' _ (k + 1), Finset.sum_range_succ' _ (k + 1), Finset.mul_sum]
  simp only [Nat.choose_succ_succ, pow_zero, Nat.choose_zero_right, mul_one]
  rw [add_right_comm, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- A positive combination of two reals with the same sign has that sign. -/
private theorem sign_convex_comb {u w s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (h : SignType.sign u = SignType.sign w) :
    SignType.sign (s * u + t * w) = SignType.sign u := by
  rcases lt_trichotomy u 0 with hu | hu | hu
  · have hw : w < 0 := by rw [← sign_eq_neg_one_iff, ← h, sign_neg hu]
    rw [sign_neg hu, sign_neg]
    exact add_neg (mul_neg_of_pos_of_neg hs hu) (mul_neg_of_pos_of_neg ht hw)
  · subst hu
    have hw : w = 0 := by rw [← sign_eq_zero_iff, ← h, sign_zero]
    subst hw
    simp
  · have hw : 0 < w := by rw [← sign_eq_one_iff, ← h, sign_pos hu]
    rw [sign_pos hu, sign_pos]
    exact add_pos (mul_pos hs hu) (mul_pos ht hw)

/-- Core of `card_signVectors_le`, for forms indexed by `Fin n`: deletion–restriction induction
on `n`, generalizing over the dimension bound `k` and the space `E`.

In the step, split the sign vectors by the sign `s` of the first form and let `T s` be the set of
tails occurring with first sign `s`. The tails in `T 1 ∪ T (-1)` are sign vectors of the remaining
`n` forms on `E`, while those in `T 0` and (by convexity) those in `T 1 ∩ T (-1)` are sign vectors
of the remaining `n` forms restricted to the hyperplane where the first form vanishes, a space of
dimension one less. Hence
`|S| = |T 0| + |T 1 ∪ T (-1)| + |T 1 ∩ T (-1)| ≤ faceBound n (k + 1) + 2 * faceBound n k`. -/
private theorem card_signVectors_fin_le.{u} (n : ℕ) :
    ∀ (k : ℕ) (E : Type u) [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
      (L : Fin n → (E →ₗ[ℝ] ℝ)) (c : Fin n → ℝ), Module.finrank ℝ E ≤ k →
      ∀ S : Finset (Fin n → SignType),
        (∀ σ ∈ S, ∃ x : E, ∀ j, σ j = SignType.sign (L j x - c j)) →
        S.card ≤ faceBound n k := by
  induction n with
  | zero =>
    intro k E _ _ _ L c _ S _
    rw [faceBound_zero_left]
    exact Finset.card_le_one_of_subsingleton S
  | succ n ih =>
    intro k E _ _ _ L c hk S hS
    -- tails of realized sign vectors are realized by the tail forms
    have htail : ∀ T : Finset (Fin n → SignType), T ⊆ S.image Fin.tail →
        ∀ τ ∈ T, ∃ x : E, ∀ j, τ j = SignType.sign (L j.succ x - c j.succ) := by
      intro T hT τ hτ
      obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp (hT hτ)
      obtain ⟨x, hx⟩ := hS σ hσ
      exact ⟨x, fun j => hx j.succ⟩
    -- the tail map is injective on each fiber of the head map
    have hinj : ∀ s : SignType,
        Set.InjOn (Fin.tail : (Fin (n + 1) → SignType) → (Fin n → SignType))
          ((S.filter fun σ => σ 0 = s : Finset (Fin (n + 1) → SignType)) :
            Set (Fin (n + 1) → SignType)) := by
      intro s σ₁ h₁ σ₂ h₂ h
      have e₁ : σ₁ 0 = s := (Finset.mem_filter.mp (Finset.mem_coe.mp h₁)).2
      have e₂ : σ₂ 0 = s := (Finset.mem_filter.mp (Finset.mem_coe.mp h₂)).2
      funext j
      refine Fin.cases ?_ (fun i => ?_) j
      · rw [e₁, e₂]
      · exact congrFun h i
    by_cases hφ : L 0 = 0
    · -- the first form is zero: its sign is constant, so the tail map is injective on `S`
      have hS0 : S.filter (fun σ => σ 0 = SignType.sign (0 - c 0)) = S := by
        refine Finset.filter_true_of_mem fun σ hσ => ?_
        obtain ⟨x, hx⟩ := hS σ hσ
        rw [hx 0, hφ]
        simp
      have h1 : S.card = (S.image Fin.tail).card := by
        have := Finset.card_image_of_injOn (hinj (SignType.sign (0 - c 0)))
        rw [hS0] at this
        exact this.symm
      calc S.card = (S.image Fin.tail).card := h1
        _ ≤ faceBound n k :=
            ih k E (fun j => L j.succ) (fun j => c j.succ) hk _ (htail _ (Finset.Subset.refl _))
        _ ≤ faceBound (n + 1) k := faceBound_mono_left (Nat.le_succ n) k
    · -- the first form is nonzero: restrict to the hyperplane `L 0 x = c 0`
      obtain ⟨v, hv⟩ : ∃ v, L 0 v ≠ 0 := by
        by_contra hcon
        refine hφ (LinearMap.ext fun v => ?_)
        by_contra hv
        exact hcon ⟨v, by simpa using hv⟩
      obtain ⟨x₀, hx₀⟩ : ∃ x₀ : E, L 0 x₀ = c 0 :=
        ⟨(c 0 / L 0 v) • v, by simp [div_mul_cancel₀ _ hv]⟩
      obtain ⟨K, hKdef⟩ : ∃ K : Submodule ℝ E, K = LinearMap.ker (L 0) := ⟨_, rfl⟩
      have hKrank : Module.finrank ℝ K + 1 = Module.finrank ℝ E := by
        rw [hKdef]
        exact Module.Dual.finrank_ker_add_one_of_ne_zero hφ
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hK' : Module.finrank ℝ K ≤ k' := by omega
      -- sign vectors of the tail forms realized on the hyperplane `L 0 x = c 0` are sign vectors
      -- of `n` affine forms on `K` (translate by `x₀`), so the induction hypothesis applies
      have hKbound : ∀ T : Finset (Fin n → SignType),
          (∀ τ ∈ T, ∃ x : E, L 0 x = c 0 ∧
            ∀ j, τ j = SignType.sign (L j.succ x - c j.succ)) →
          T.card ≤ faceBound n k' := by
        intro T hT
        refine ih k' K (fun j => (L j.succ).comp K.subtype)
          (fun j => c j.succ - L j.succ x₀) hK' T ?_
        intro τ hτ
        obtain ⟨x, hx, hxτ⟩ := hT τ hτ
        refine ⟨⟨x - x₀, by rw [hKdef, LinearMap.mem_ker, map_sub, hx, hx₀, sub_self]⟩,
          fun j => ?_⟩
        rw [hxτ j]
        congr 1
        simp only [LinearMap.comp_apply, Submodule.subtype_apply, map_sub]
        ring
      -- `T s`: the tails of the sign vectors in `S` whose first sign is `s`
      obtain ⟨T, hT⟩ : ∃ T : SignType → Finset (Fin n → SignType),
          ∀ s, T s = (S.filter fun σ => σ 0 = s).image Fin.tail := ⟨_, fun _ => rfl⟩
      have hTcard : ∀ s, (T s).card = (S.filter fun σ => σ 0 = s).card := fun s => by
        rw [hT s]
        exact Finset.card_image_of_injOn (hinj s)
      have hTsub : ∀ s, T s ⊆ S.image Fin.tail := fun s => by
        rw [hT s]
        exact Finset.image_subset_image (Finset.filter_subset _ _)
      have hTmem : ∀ s τ, τ ∈ T s → ∃ x : E, s = SignType.sign (L 0 x - c 0) ∧
          ∀ j, τ j = SignType.sign (L j.succ x - c j.succ) := by
        intro s τ hτ
        rw [hT s] at hτ
        obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hτ
        obtain ⟨hσS, hσ0⟩ := Finset.mem_filter.mp hσ
        obtain ⟨x, hx⟩ := hS σ hσS
        exact ⟨x, by rw [← hσ0, hx 0], fun j => hx j.succ⟩
      -- Claim A: a tail occurring with first sign `0` is realized on the hyperplane
      have hA : (T 0).card ≤ faceBound n k' := by
        refine hKbound _ fun τ hτ => ?_
        obtain ⟨x, hx0, hx⟩ := hTmem 0 τ hτ
        exact ⟨x, sub_eq_zero.mp (sign_eq_zero_iff.mp hx0.symm), hx⟩
      -- Claim B (convexity): a tail occurring with both first signs `1` and `-1` is realized on
      -- the hyperplane, at the point where the segment between the two witnesses crosses it
      have hB : (T 1 ∩ T (-1)).card ≤ faceBound n k' := by
        refine hKbound _ fun τ hτ => ?_
        obtain ⟨hτ₁, hτ₂⟩ := Finset.mem_inter.mp hτ
        obtain ⟨x₁, h₁0, h₁⟩ := hTmem 1 τ hτ₁
        obtain ⟨x₂, h₂0, h₂⟩ := hTmem (-1) τ hτ₂
        obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = L 0 x₁ - c 0 := ⟨_, rfl⟩
        obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = c 0 - L 0 x₂ := ⟨_, rfl⟩
        have ha : 0 < a := by
          rw [hadef]
          exact sign_eq_one_iff.mp h₁0.symm
        have hb : 0 < b := by
          have := sign_eq_neg_one_iff.mp h₂0.symm
          rw [hbdef]
          linarith
        have hab : 0 < a + b := add_pos ha hb
        have hab' : a + b ≠ 0 := hab.ne'
        have hx₁ : L 0 x₁ = a + c 0 := by rw [hadef]; ring
        have hx₂ : L 0 x₂ = c 0 - b := by rw [hbdef]; ring
        refine ⟨(b / (a + b)) • x₁ + (a / (a + b)) • x₂, ?_, fun j => ?_⟩
        · simp only [map_add, map_smul, smul_eq_mul]
          rw [hx₁, hx₂]
          field_simp
          ring
        · have key : L j.succ ((b / (a + b)) • x₁ + (a / (a + b)) • x₂) - c j.succ
              = (b / (a + b)) * (L j.succ x₁ - c j.succ)
                + (a / (a + b)) * (L j.succ x₂ - c j.succ) := by
            simp only [map_add, map_smul, smul_eq_mul]
            field_simp
            ring
          rw [key, sign_convex_comb (div_pos hb hab) (div_pos ha hab)
            ((h₁ j).symm.trans (h₂ j))]
          exact h₁ j
      -- the tails with first sign `1` or `-1` are sign vectors of the tail forms on `E`
      have hU : (T 1 ∪ T (-1)).card ≤ faceBound n (k' + 1) :=
        ih (k' + 1) E (fun j => L j.succ) (fun j => c j.succ) hk _
          (htail _ (Finset.union_subset (hTsub 1) (hTsub (-1))))
      -- count `S` by the first sign
      have hsplit : S.card = (T 0).card + (T (-1)).card + (T 1).card := by
        rw [Finset.card_eq_sum_card_fiberwise (f := fun σ : Fin (n + 1) → SignType => σ 0)
          (s := S) (t := Finset.univ) (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)),
          SignType.univ_eq]
        rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
          hTcard, hTcard, hTcard, add_assoc]
      have hUI := Finset.card_union_add_card_inter (T 1) (T (-1))
      rw [faceBound_succ_succ]
      omega

/-- **Sign vectors of an arrangement.** Any finite set of sign vectors realized by the affine
forms `x ↦ L j x - c j`, `j : J`, on a space of dimension at most `k` has at most
`faceBound |J| k` elements. -/
theorem card_signVectors_le {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    {J : Type*} [Fintype J] (L : J → (E →ₗ[ℝ] ℝ)) (c : J → ℝ) (k : ℕ)
    (hk : Module.finrank ℝ E ≤ k) (S : Finset (J → SignType))
    (hS : ∀ σ ∈ S, ∃ x : E, ∀ j, σ j = SignType.sign (L j x - c j)) :
    S.card ≤ faceBound (Fintype.card J) k := by
  -- transport along an enumeration `J ≃ Fin (Fintype.card J)`
  obtain ⟨e⟩ : Nonempty (J ≃ Fin (Fintype.card J)) := ⟨Fintype.equivFin J⟩
  have hinj : Function.Injective
      (fun (σ : J → SignType) (i : Fin (Fintype.card J)) => σ (e.symm i)) := by
    intro σ₁ σ₂ h
    funext j
    have := congrFun h (e j)
    simpa using this
  rw [← Finset.card_image_of_injective S hinj]
  refine card_signVectors_fin_le _ k E (fun i => L (e.symm i)) (fun i => c (e.symm i)) hk _ ?_
  intro τ hτ
  obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hτ
  obtain ⟨x, hx⟩ := hS σ hσ
  exact ⟨x, fun i => hx (e.symm i)⟩

end SPLP
