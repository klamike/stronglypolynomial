import Mathlib
import SPLP.Defs
import SPLP.Product

/-!
# Expert weights attached to a hypothesis

For a fixed hypothesis, the analysis weighs the experts that guess its true demands.
`cur` is the weight of the experts with a given threshold description and `k` slots drawn
independently from a distribution `m`; `res` reserves weight for a future pivot level, with the
pivot slot drawn from `m` as well; `Psi` combines the current description with all reserves
(the weights `π` of Section 6.5 of the preprint, with general reserve masses `ω`).
-/

set_option linter.unusedSectionVars false

namespace SPLP

open Finset

variable {ι V : Type*} {k D : ℕ}

/-- The expert that guesses the true demands of `H` on the slots `tup`, with threshold
description `d` (`none`, or a pivot level and slot with its true demand). -/
def trueExp (H : Hyp ι V) (tup : Fin k → Slot ι) (d : Option (Fin D × Slot ι)) :
    Expert ι V k D :=
  (tup, fun q => H.a (tup q), d.map (fun jp => (jp.1, jp.2, H.a jp.2)))

variable [Fintype ι] [DecidableEq ι]

/-- Weighted sum of `F` over true-demand experts with description `d` and slots drawn from
`m`. -/
noncomputable def cur (H : Hyp ι V) (m : Slot ι → ℝ) (d : Option (Fin D × Slot ι))
    (F : Expert ι V k D → ℝ) : ℝ :=
  ∑ tup : Fin k → Slot ι, (∏ q, m (tup q)) * F (trueExp H tup d)

/-- The same with a pivot at level `j` whose slot is also drawn from `m`. -/
noncomputable def res (H : Hyp ι V) (m : Slot ι → ℝ) (j : Fin D) (F : Expert ι V k D → ℝ) : ℝ :=
  ∑ p : Slot ι, m p * cur H m (some (j, p)) F

/-- The weights of a node at level `l` with distribution `m` and description `d₀`: the current
description, plus mass `ω (j - l)` reserved for each pivot level `j ≥ l`. -/
noncomputable def Psi (H : Hyp ι V) (ω : ℕ → ℝ) (l : ℕ) (m : Slot ι → ℝ)
    (d₀ : Option (Fin D × Slot ι)) (F : Expert ι V k D → ℝ) : ℝ :=
  cur H m d₀ F + ∑ j : Fin D, if l ≤ (j : ℕ) then ω (j - l) * res H m j F else 0

section Linear

variable (H : Hyp ι V) (m : Slot ι → ℝ)

theorem prod_nonneg_of (hm : ∀ s, 0 ≤ m s) (tup : Fin k → Slot ι) : 0 ≤ ∏ q, m (tup q) :=
  Finset.prod_nonneg (fun q _ => hm (tup q))

theorem cur_mono (hm : ∀ s, 0 ≤ m s) (d : Option (Fin D × Slot ι))
    {F G : Expert ι V k D → ℝ} (h : ∀ e, F e ≤ G e) : cur H m d F ≤ cur H m d G :=
  Finset.sum_le_sum (fun tup _ => mul_le_mul_of_nonneg_left (h _) (prod_nonneg_of m hm tup))

theorem cur_nonneg (hm : ∀ s, 0 ≤ m s) (d : Option (Fin D × Slot ι))
    {F : Expert ι V k D → ℝ} (h : ∀ e, 0 ≤ F e) : 0 ≤ cur H m d F :=
  Finset.sum_nonneg (fun tup _ => mul_nonneg (prod_nonneg_of m hm tup) (h _))

theorem cur_add (d : Option (Fin D × Slot ι)) (F G : Expert ι V k D → ℝ) :
    cur H m d (fun e => F e + G e) = cur H m d F + cur H m d G := by
  simp only [cur, mul_add, Finset.sum_add_distrib]

theorem cur_const (hsum : ∑ s, m s = 1) (d : Option (Fin D × Slot ι)) (a : ℝ) :
    cur H m d (fun _ : Expert ι V k D => a) = a := by
  simp only [cur]
  rw [← Finset.sum_mul, sum_prod_tuple, hsum, one_pow, one_mul]

theorem cur_sum {κ : Type*} (s : Finset κ) (d : Option (Fin D × Slot ι))
    (F : κ → Expert ι V k D → ℝ) :
    cur H m d (fun e => ∑ τ ∈ s, F τ e) = ∑ τ ∈ s, cur H m d (F τ) := by
  simp only [cur, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem res_mono (hm : ∀ s, 0 ≤ m s) (j : Fin D)
    {F G : Expert ι V k D → ℝ} (h : ∀ e, F e ≤ G e) : res H m j F ≤ res H m j G :=
  Finset.sum_le_sum (fun p _ => mul_le_mul_of_nonneg_left (cur_mono H m hm _ h) (hm p))

theorem res_nonneg (hm : ∀ s, 0 ≤ m s) (j : Fin D)
    {F : Expert ι V k D → ℝ} (h : ∀ e, 0 ≤ F e) : 0 ≤ res H m j F :=
  Finset.sum_nonneg (fun p _ => mul_nonneg (hm p) (cur_nonneg H m hm _ h))

theorem res_add (j : Fin D) (F G : Expert ι V k D → ℝ) :
    res H m j (fun e => F e + G e) = res H m j F + res H m j G := by
  simp only [res, cur_add, mul_add, Finset.sum_add_distrib]

theorem res_const (hsum : ∑ s, m s = 1) (j : Fin D) (a : ℝ) :
    res H m j (fun _ : Expert ι V k D => a) = a := by
  simp only [res, cur_const H m hsum]
  rw [← Finset.sum_mul, hsum, one_mul]

theorem res_sum {κ : Type*} (s : Finset κ) (j : Fin D) (F : κ → Expert ι V k D → ℝ) :
    res H m j (fun e => ∑ τ ∈ s, F τ e) = ∑ τ ∈ s, res H m j (F τ) := by
  simp only [res, cur_sum, Finset.mul_sum]
  rw [Finset.sum_comm]

variable (ω : ℕ → ℝ) (l : ℕ) (d₀ : Option (Fin D × Slot ι))

theorem Psi_mono (hm : ∀ s, 0 ≤ m s) (hω : ∀ i, 0 ≤ ω i)
    {F G : Expert ι V k D → ℝ} (h : ∀ e, F e ≤ G e) : Psi H ω l m d₀ F ≤ Psi H ω l m d₀ G := by
  unfold Psi
  refine add_le_add (cur_mono H m hm _ h) (Finset.sum_le_sum (fun j _ => ?_))
  split_ifs
  · exact mul_le_mul_of_nonneg_left (res_mono H m hm j h) (hω _)
  · exact le_rfl

theorem Psi_nonneg (hm : ∀ s, 0 ≤ m s) (hω : ∀ i, 0 ≤ ω i)
    {F : Expert ι V k D → ℝ} (h : ∀ e, 0 ≤ F e) : 0 ≤ Psi H ω l m d₀ F := by
  unfold Psi
  refine add_nonneg (cur_nonneg H m hm _ h) (Finset.sum_nonneg (fun j _ => ?_))
  split_ifs
  · exact mul_nonneg (hω _) (res_nonneg H m hm j h)
  · exact le_rfl

theorem Psi_add (F G : Expert ι V k D → ℝ) :
    Psi H ω l m d₀ (fun e => F e + G e) = Psi H ω l m d₀ F + Psi H ω l m d₀ G := by
  unfold Psi
  rw [cur_add, add_add_add_comm, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs
  · rw [res_add, mul_add]
  · simp

theorem Psi_sum {κ : Type*} (s : Finset κ) (F : κ → Expert ι V k D → ℝ) :
    Psi H ω l m d₀ (fun e => ∑ τ ∈ s, F τ e) = ∑ τ ∈ s, Psi H ω l m d₀ (F τ) := by
  unfold Psi
  rw [cur_sum, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs
  · rw [res_sum, Finset.mul_sum]
  · simp

/-- Total reserved mass seen from level `l`. -/
noncomputable def reserve (D : ℕ) (ω : ℕ → ℝ) (l : ℕ) : ℝ :=
  ∑ j : Fin D, if l ≤ (j : ℕ) then ω (j - l) else 0

theorem Psi_const (hsum : ∑ s, m s = 1) (a : ℝ) :
    Psi H ω l m d₀ (fun _ : Expert ι V k D => a) = a * (1 + reserve D ω l) := by
  unfold Psi reserve
  rw [cur_const H m hsum, mul_add, mul_one, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs
  · rw [res_const H m hsum, mul_comm]
  · simp

theorem reserve_nonneg (hω : ∀ i, 0 ≤ ω i) : 0 ≤ reserve D ω l :=
  Finset.sum_nonneg (fun j _ => by split_ifs <;> [exact hω _; exact le_rfl])

theorem reserve_le (hω : ∀ i, 0 ≤ ω i) : reserve D ω l ≤ ∑ i ∈ range D, ω i := by
  unfold reserve
  rw [Fin.sum_univ_eq_sum_range (fun j => if l ≤ j then ω (j - l) else 0) D]
  rw [← Finset.sum_filter]
  have hinj : Set.InjOn (fun j => j - l) ((range D).filter (fun j => l ≤ j) : Finset ℕ) := by
    intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha hb
    simp only at hab
    omega
  rw [← Finset.sum_image (f := fun i => ω i) hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => hω i)
  intro i hi
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hi ⊢
  obtain ⟨j, ⟨hj, _⟩, rfl⟩ := hi
  omega

end Linear

/-! ### Transfer from a child to its parent -/

section Transfer

variable (H : Hyp ι V) (m m' : Slot ι → ℝ) (ω : ℕ → ℝ) (l : ℕ)

theorem cur_le_pow_mul (ρ : ℝ) (hm'0 : ∀ s, 0 ≤ m' s) (hm' : ∀ s, m' s ≤ ρ * m s)
    (d : Option (Fin D × Slot ι)) {F : Expert ι V k D → ℝ} (hF : ∀ e, 0 ≤ F e) :
    cur H m' d F ≤ ρ ^ k * cur H m d F := by
  unfold cur
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun tup _ => ?_)
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (prod_le_pow_mul_prod m m' ρ hm'0 hm' tup) (hF _)

theorem res_le_pow_mul (ρ : ℝ) (hρ : 0 ≤ ρ) (hm0 : ∀ s, 0 ≤ m s) (hm'0 : ∀ s, 0 ≤ m' s)
    (hm' : ∀ s, m' s ≤ ρ * m s) (j : Fin D) {F : Expert ι V k D → ℝ} (hF : ∀ e, 0 ≤ F e) :
    res H m' j F ≤ ρ ^ (k + 1) * res H m j F := by
  unfold res
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun p _ => ?_)
  have h1 := cur_le_pow_mul H m m' ρ hm'0 hm' (some (j, p)) hF
  have h2 : 0 ≤ cur H m (some (j, p)) F := cur_nonneg H m hm0 _ hF
  calc m' p * cur H m' (some (j, p)) F
      ≤ m' p * (ρ ^ k * cur H m (some (j, p)) F) := mul_le_mul_of_nonneg_left h1 (hm'0 p)
    _ ≤ (ρ * m p) * (ρ ^ k * cur H m (some (j, p)) F) :=
        mul_le_mul_of_nonneg_right (hm' p) (mul_nonneg (pow_nonneg hρ k) h2)
    _ = ρ ^ (k + 1) * (m p * cur H m (some (j, p)) F) := by ring

/-- Reserve terms of the child are dominated by those of the parent. -/
theorem reserve_term_le (ρ C : ℝ) (hρ : 0 ≤ ρ) (hC : 0 ≤ C) (hm0 : ∀ s, 0 ≤ m s)
    (hm'0 : ∀ s, 0 ≤ m' s) (hm' : ∀ s, m' s ≤ ρ * m s) (hω : ∀ i, 0 ≤ ω i)
    (hC3 : ∀ i, ρ ^ (k + 1) * ω i ≤ C * ω (i + 1))
    {F : Expert ι V k D → ℝ} (hF : ∀ e, 0 ≤ F e) (j : Fin D) :
    (if l + 1 ≤ (j : ℕ) then ω (j - (l + 1)) * res H m' j F else 0)
      ≤ C * (if l ≤ (j : ℕ) then ω (j - l) * res H m j F else 0) := by
  have hres : 0 ≤ res H m j F := res_nonneg H m hm0 j hF
  by_cases h1 : l + 1 ≤ (j : ℕ)
  · have h2 : l ≤ (j : ℕ) := by omega
    rw [if_pos h1, if_pos h2]
    have h3 : (j : ℕ) - l = ((j : ℕ) - (l + 1)) + 1 := by omega
    rw [h3]
    calc ω (j - (l + 1)) * res H m' j F
        ≤ ω (j - (l + 1)) * (ρ ^ (k + 1) * res H m j F) :=
          mul_le_mul_of_nonneg_left (res_le_pow_mul H m m' ρ hρ hm0 hm'0 hm' j hF) (hω _)
      _ = (ρ ^ (k + 1) * ω (j - (l + 1))) * res H m j F := by ring
      _ ≤ (C * ω (j - (l + 1) + 1)) * res H m j F :=
          mul_le_mul_of_nonneg_right (hC3 _) hres
      _ = C * (ω (j - (l + 1) + 1) * res H m j F) := by ring
  · rw [if_neg h1]
    split_ifs
    · exact mul_nonneg hC (mul_nonneg (hω _) hres)
    · simp

/-- **Transfer, light probe.** The child keeps the description of its parent. -/
theorem transfer_light (ρ C : ℝ) (hρ : 0 ≤ ρ) (hm0 : ∀ s, 0 ≤ m s)
    (hm'0 : ∀ s, 0 ≤ m' s) (hm' : ∀ s, m' s ≤ ρ * m s) (hω : ∀ i, 0 ≤ ω i)
    (hC1 : ρ ^ k ≤ C) (hC3 : ∀ i, ρ ^ (k + 1) * ω i ≤ C * ω (i + 1))
    (d₀ : Option (Fin D × Slot ι)) {F : Expert ι V k D → ℝ} (hF : ∀ e, 0 ≤ F e) :
    Psi H ω (l + 1) m' d₀ F ≤ C * Psi H ω l m d₀ F := by
  have hC : 0 ≤ C := (pow_nonneg hρ k).trans hC1
  unfold Psi
  rw [mul_add, Finset.mul_sum]
  refine add_le_add ?_ (Finset.sum_le_sum (fun j _ =>
    reserve_term_le H m m' ω l ρ C hρ hC hm0 hm'0 hm' hω hC3 hF j))
  calc cur H m' d₀ F ≤ ρ ^ k * cur H m d₀ F := cur_le_pow_mul H m m' ρ hm'0 hm' d₀ hF
    _ ≤ C * cur H m d₀ F := mul_le_mul_of_nonneg_right hC1 (cur_nonneg H m hm0 _ hF)

/-- **Transfer, heavy probe.** The child's description is the new pivot at level `l`, chosen
so that its score is at most the `m`-average over pivots divided by the band width `δ - γ`. -/
theorem transfer_heavy (ρ C γ δ : ℝ) (hρ : 0 ≤ ρ) (hm0 : ∀ s, 0 ≤ m s)
    (hm'0 : ∀ s, 0 ≤ m' s) (hm' : ∀ s, m' s ≤ ρ * m s) (hω : ∀ i, 0 ≤ ω i)
    (hγδ : γ < δ) (hC1 : ρ ^ k ≤ C) (hC2 : ρ ^ k ≤ C * ((δ - γ) * ω 0))
    (hC3 : ∀ i, ρ ^ (k + 1) * ω i ≤ C * ω (i + 1))
    (d₀ : Option (Fin D × Slot ι)) {F : Expert ι V k D → ℝ} (hF : ∀ e, 0 ≤ F e)
    (hl : l < D) (pstar : Slot ι)
    (hpiv : (δ - γ) * cur H m' (some (⟨l, hl⟩, pstar)) F
      ≤ ∑ s, m s * cur H m' (some (⟨l, hl⟩, s)) F) :
    Psi H ω (l + 1) m' (some (⟨l, hl⟩, pstar)) F ≤ C * Psi H ω l m d₀ F := by
  have hC : 0 ≤ C := (pow_nonneg hρ k).trans hC1
  have hδγ : 0 < δ - γ := sub_pos.2 hγδ
  have hresl : 0 ≤ res H m ⟨l, hl⟩ F := res_nonneg H m hm0 _ hF
  -- the new description is paid by the parent's reserve for level `l`
  have hcur : cur H m' (some (⟨l, hl⟩, pstar)) F ≤ C * (ω 0 * res H m ⟨l, hl⟩ F) := by
    have h1 : ∑ s, m s * cur H m' (some (⟨l, hl⟩, s)) F ≤ ρ ^ k * res H m ⟨l, hl⟩ F := by
      unfold res
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun s _ => ?_)
      calc m s * cur H m' (some (⟨l, hl⟩, s)) F
          ≤ m s * (ρ ^ k * cur H m (some (⟨l, hl⟩, s)) F) :=
            mul_le_mul_of_nonneg_left (cur_le_pow_mul H m m' ρ hm'0 hm' _ hF) (hm0 s)
        _ = ρ ^ k * (m s * cur H m (some (⟨l, hl⟩, s)) F) := by ring
    have h2 : (δ - γ) * cur H m' (some (⟨l, hl⟩, pstar)) F
        ≤ (δ - γ) * (C * (ω 0 * res H m ⟨l, hl⟩ F)) := by
      calc (δ - γ) * cur H m' (some (⟨l, hl⟩, pstar)) F
          ≤ ρ ^ k * res H m ⟨l, hl⟩ F := hpiv.trans h1
        _ ≤ (C * ((δ - γ) * ω 0)) * res H m ⟨l, hl⟩ F :=
            mul_le_mul_of_nonneg_right hC2 hresl
        _ = (δ - γ) * (C * (ω 0 * res H m ⟨l, hl⟩ F)) := by ring
    exact le_of_mul_le_mul_left h2 hδγ
  unfold Psi
  rw [mul_add, Finset.mul_sum]
  have hcur0 : 0 ≤ C * cur H m d₀ F := mul_nonneg hC (cur_nonneg H m hm0 _ hF)
  have key : cur H m' (some (⟨l, hl⟩, pstar)) F
      + ∑ j : Fin D, (if l + 1 ≤ (j : ℕ) then ω (j - (l + 1)) * res H m' j F else 0)
      ≤ ∑ j : Fin D, C * (if l ≤ (j : ℕ) then ω (j - l) * res H m j F else 0) := by
    have hsplit : cur H m' (some (⟨l, hl⟩, pstar)) F
        = ∑ j : Fin D, (if j = ⟨l, hl⟩ then cur H m' (some (⟨l, hl⟩, pstar)) F else 0) := by
      simp
    rw [hsplit, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun j _ => ?_)
    by_cases hj : j = ⟨l, hl⟩
    · subst hj
      simp only [if_true, le_refl]
      rw [if_neg (by simp), add_zero]
      simpa using hcur
    · rw [if_neg hj, zero_add]
      exact reserve_term_le H m m' ω l ρ C hρ hC hm0 hm'0 hm' hω hC3 hF j
  linarith

end Transfer

end SPLP
