import Mathlib

/-!
# Boost profiles and pivots

Combinatorics of a probability vector `m` on a finite set of slots ordered by a real "surplus"
`d`: the fractional boost of the top `δ` of the mass, and the existence of a pivot whose level
lies in the band `[γ, δ]` of the surplus distribution (Section 6.2 and Lemma 6.3 of the
preprint, in a tie-symmetric form that needs no sorting).
-/

namespace SPLP

open Finset

variable {α : Type*} [Fintype α]

/-- Mass of the slots whose surplus is strictly above `θ`. -/
noncomputable def massGT (m d : α → ℝ) (θ : ℝ) : ℝ := ∑ s, if θ < d s then m s else 0

/-- Mass of the slots whose surplus is at least `θ`. -/
noncomputable def massGE (m d : α → ℝ) (θ : ℝ) : ℝ := ∑ s, if θ ≤ d s then m s else 0

/-- Termwise monotonicity of an indicator-weighted nonnegative term; the implication is only
needed when the weight is positive. -/
private lemma ite_le_ite_of_pos_imp {P Q : Prop} [Decidable P] [Decidable Q] {x : ℝ}
    (hx : 0 ≤ x) (h : 0 < x → P → Q) :
    (if P then x else 0) ≤ (if Q then x else 0) := by
  rcases hx.eq_or_lt with hx0 | hxpos
  · subst hx0
    simp
  · by_cases hP : P
    · rw [if_pos hP, if_pos (h hxpos hP)]
    · rw [if_neg hP]
      exact ite_nonneg hx le_rfl

theorem massGT_antitone (m d : α → ℝ) (hm : ∀ s, 0 ≤ m s) {θ θ' : ℝ} (h : θ ≤ θ') :
    massGT m d θ' ≤ massGT m d θ := by
  unfold massGT
  exact Finset.sum_le_sum fun s _ =>
    ite_le_ite_of_pos_imp (hm s) (fun _ h1 => lt_of_le_of_lt h h1)

/-- A level set at or above `θ'` is contained in the strict upper level set of any `θ < θ'`. -/
private lemma massGE_le_massGT (m d : α → ℝ) (hm : ∀ s, 0 ≤ m s) {θ θ' : ℝ} (h : θ < θ') :
    massGE m d θ' ≤ massGT m d θ := by
  unfold massGT massGE
  exact Finset.sum_le_sum fun s _ =>
    ite_le_ite_of_pos_imp (hm s) (fun _ h1 => lt_of_lt_of_le h h1)

/-- The slot `t` itself sits at level `d t`, on top of everything strictly above. -/
private lemma massGT_add_le_massGE (m d : α → ℝ) (hm : ∀ s, 0 ≤ m s) (t : α) :
    massGT m d (d t) + m t ≤ massGE m d (d t) := by
  classical
  have ht : (∑ s, if s = t then m s else 0) = m t := by simp
  unfold massGT massGE
  rw [← ht, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro s _
  by_cases hs : s = t
  · subst hs
    rw [if_neg (lt_irrefl _), if_pos rfl, if_pos le_rfl, zero_add]
  · rw [if_neg hs, add_zero]
    exact ite_le_ite_of_pos_imp (hm s) (fun _ h1 => le_of_lt h1)

/-- A slot strictly between the levels `θ` and `θ'` adds its mass to the mass at or above `θ'`. -/
private lemma add_massGE_le_massGT (m d : α → ℝ) (hm : ∀ s, 0 ≤ m s) {θ θ' : ℝ} (t : α)
    (h1 : θ < d t) (h2 : d t < θ') :
    m t + massGE m d θ' ≤ massGT m d θ := by
  classical
  have ht : (∑ s, if s = t then m s else 0) = m t := by simp
  unfold massGT massGE
  rw [← ht, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro s _
  by_cases hs : s = t
  · subst hs
    rw [if_pos rfl, if_neg (not_le.mpr h2), if_pos h1, add_zero]
  · rw [if_neg hs, zero_add]
    exact ite_le_ite_of_pos_imp (hm s) (fun _ h3 => lt_of_lt_of_le (lt_trans h1 h2) h3)

/-- A positive indicator-weighted sum has a positive-mass slot in the indicated set. -/
private lemma exists_pos_of_sum_ite_pos (m : α → ℝ) (hm : ∀ s, 0 ≤ m s) (P : α → Prop)
    [DecidablePred P] (hpos : 0 < ∑ s, if P s then m s else 0) : ∃ s, P s ∧ 0 < m s := by
  by_contra hne
  have hzero : (∑ s, if P s then m s else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro s _
    by_cases hs : P s
    · rw [if_pos hs]
      exact le_antisymm (not_lt.mp fun h => hne ⟨s, hs, h⟩) (hm s)
    · rw [if_neg hs]
  rw [hzero] at hpos
  exact lt_irrefl _ hpos

/-- The mass of a set of positive mass is dominated by the mass at or above the level of its
lowest positive-mass slot. -/
private lemma exists_pos_le_massGE (m d : α → ℝ) (hm : ∀ s, 0 ≤ m s) (P : α → Prop)
    [DecidablePred P] (hpos : 0 < ∑ s, if P s then m s else 0) :
    ∃ p, P p ∧ 0 < m p ∧ (∑ s, if P s then m s else 0) ≤ massGE m d (d p) := by
  obtain ⟨s₀, hs₀⟩ := exists_pos_of_sum_ite_pos m hm P hpos
  obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image
    (Finset.univ.filter (fun s => P s ∧ 0 < m s)) d
    ⟨s₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs₀⟩⟩
  have hp' : P p ∧ 0 < m p := (Finset.mem_filter.mp hp).2
  refine ⟨p, hp'.1, hp'.2, ?_⟩
  unfold massGE
  exact Finset.sum_le_sum fun s _ =>
    ite_le_ite_of_pos_imp (hm s)
      (fun h0 hs => hmin s (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs, h0⟩))

/-- The mass of a nonempty set and the mass strictly above the level of its highest slot are
disjoint parts of the total mass. -/
private lemma exists_add_massGT_le (m d : α → ℝ) (hm : ∀ s, 0 ≤ m s) (P : α → Prop)
    [DecidablePred P] (hP : ∃ s, P s) :
    ∃ p, P p ∧ (∑ s, if P s then m s else 0) + massGT m d (d p) ≤ ∑ s, m s := by
  obtain ⟨s₀, hs₀⟩ := hP
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image (Finset.univ.filter P) d
    ⟨s₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs₀⟩⟩
  refine ⟨p, (Finset.mem_filter.mp hp).2, ?_⟩
  unfold massGT
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro s _
  by_cases hs : P s
  · have h1 : d s ≤ d p := hmax s (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩)
    rw [if_pos hs, if_neg (not_lt.mpr h1), add_zero]
  · rw [if_neg hs, zero_add]
    split_ifs
    · exact le_rfl
    · exact hm s

/-- **Boost profile.** There is a fractional indicator `φ` of "the top `δ` of the mass": it has
total weighted mass exactly `δ`, and it is identically one on every strict upper level set of
mass at most `δ`. -/
theorem exists_boost (m d : α → ℝ) (hm : ∀ s, 0 ≤ m s) (hsum : ∑ s, m s = 1)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    ∃ φ : α → ℝ, (∀ s, 0 ≤ φ s ∧ φ s ≤ 1) ∧ ∑ s, m s * φ s = δ ∧
      ∀ θ, massGT m d θ ≤ δ → ∀ s, θ < d s → 0 < m s → φ s = 1 := by
  classical
  -- a positive-mass slot at whose level the mass at or above is everything
  obtain ⟨s₀, -, hs₀pos, hs₀⟩ :=
    exists_pos_le_massGE m d hm (fun _ => True) (by simp [hsum])
  have hs₀' : (1 : ℝ) ≤ massGE m d (d s₀) := by simpa [hsum] using hs₀
  -- the highest positive-mass slot `t` with `δ ≤ massGE (d t)`
  obtain ⟨t, ht, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter (fun s => 0 < m s ∧ δ ≤ massGE m d (d s))) d
    ⟨s₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs₀pos, le_trans hδ1 hs₀'⟩⟩
  obtain ⟨htpos, htδ⟩ : 0 < m t ∧ δ ≤ massGE m d (d t) := (Finset.mem_filter.mp ht).2
  -- the mass strictly above `d t` is at most `δ`, by maximality of `t`
  have hAδ : massGT m d (d t) ≤ δ := by
    by_contra hcon
    have hcon' : δ < massGT m d (d t) := not_le.mp hcon
    obtain ⟨p, hp1, hp2, hp3⟩ :=
      exists_pos_le_massGE m d hm (fun s => d t < d s) (lt_of_le_of_lt hδ0 hcon')
    have hp1' : d t < d p := hp1
    have hp3' : massGT m d (d t) ≤ massGE m d (d p) := hp3
    have hle : d p ≤ d t :=
      hmax p (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp2, le_trans hcon'.le hp3'⟩)
    exact absurd hp1' (not_lt.mpr hle)
  have hBA : 0 < massGE m d (d t) - massGT m d (d t) := by
    have := massGT_add_le_massGE m d hm t
    linarith
  -- the fractional weight on the level `d t`
  obtain ⟨c, hc0, hc1, hcmul⟩ : ∃ c : ℝ, 0 ≤ c ∧ c ≤ 1 ∧
      c * (massGE m d (d t) - massGT m d (d t)) = δ - massGT m d (d t) := by
    refine ⟨(δ - massGT m d (d t)) / (massGE m d (d t) - massGT m d (d t)), ?_, ?_, ?_⟩
    · exact div_nonneg (by linarith) hBA.le
    · rw [div_le_one hBA]
      linarith
    · exact div_mul_cancel₀ _ hBA.ne'
  refine ⟨fun s => if d t < d s then 1 else if d s = d t then c else 0, ?_, ?_, ?_⟩
  · intro s
    dsimp only
    split_ifs
    · exact ⟨zero_le_one, le_rfl⟩
    · exact ⟨hc0, hc1⟩
    · exact ⟨le_rfl, zero_le_one⟩
  · have hterm : ∀ s, m s * (if d t < d s then 1 else if d s = d t then c else 0)
        = (if d t < d s then m s else 0)
          + c * ((if d t ≤ d s then m s else 0) - (if d t < d s then m s else 0)) := by
      intro s
      rcases lt_trichotomy (d t) (d s) with h | h | h
      · rw [if_pos h, if_pos h, if_pos h.le]
        ring
      · have h1 : ¬ d t < d s := by rw [h]; exact lt_irrefl _
        rw [if_neg h1, if_pos h.symm, if_neg h1, if_pos h.le]
        ring
      · have h1 : ¬ d t < d s := not_lt.mpr h.le
        rw [if_neg h1, if_neg h.ne, if_neg h1, if_neg (not_le.mpr h)]
        ring
    calc ∑ s, m s * (if d t < d s then 1 else if d s = d t then c else 0)
        = ∑ s, ((if d t < d s then m s else 0)
            + c * ((if d t ≤ d s then m s else 0) - (if d t < d s then m s else 0))) :=
          Finset.sum_congr rfl (fun s _ => hterm s)
      _ = massGT m d (d t) + c * (massGE m d (d t) - massGT m d (d t)) := by
          unfold massGT massGE
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
      _ = δ := by rw [hcmul]; ring
  · intro θ hθ s hs hms
    dsimp only
    rcases lt_trichotomy (d t) (d s) with h | h | h
    · rw [if_pos h]
    · -- `s` lies on the level `d t`: then that whole level is within the top `δ`, so `c = 1`
      have hθt : θ < d t := by rw [h]; exact hs
      have h1 : massGE m d (d t) ≤ massGT m d θ := massGE_le_massGT m d hm hθt
      have hBδ : massGE m d (d t) = δ := le_antisymm (le_trans h1 hθ) htδ
      have hc : c = 1 := by
        have h2 : c * (massGE m d (d t) - massGT m d (d t))
            = 1 * (massGE m d (d t) - massGT m d (d t)) := by
          rw [hcmul, hBδ, one_mul]
        exact mul_right_cancel₀ hBA.ne' h2
      have h3 : ¬ d t < d s := by rw [h]; exact lt_irrefl _
      rw [if_neg h3, if_pos h.symm, hc]
    · -- `s` lies strictly below the level `d t`: impossible
      exfalso
      have h1 := add_massGE_le_massGT m d hm s hs h
      linarith

/-- **Pivot selection.** Slots `p` whose level satisfies `massGT (d p) ≤ δ` and
`γ ≤ massGE (d p)` carry mass at least `δ - γ`; hence for any nonnegative score `F` one of
them has score at most the `m`-average divided by `δ - γ`. -/
theorem exists_pivot (m d : α → ℝ) (hm : ∀ s, 0 ≤ m s) (hsum : ∑ s, m s = 1)
    (γ δ : ℝ) (hγ0 : 0 ≤ γ) (hγδ : γ < δ) (hδ1 : δ ≤ 1)
    (F : α → ℝ) (hF : ∀ p, 0 ≤ F p) :
    ∃ p, massGT m d (d p) ≤ δ ∧ γ ≤ massGE m d (d p) ∧ 0 < m p ∧
      (δ - γ) * F p ≤ ∑ s, m s * F s := by
  classical
  -- the slots that are too high carry mass at most `γ`
  have hH : (∑ s, if massGE m d (d s) < γ then m s else 0) ≤ γ := by
    by_contra hcon
    have hcon' : γ < ∑ s, if massGE m d (d s) < γ then m s else 0 := not_le.mp hcon
    obtain ⟨p, hp, -, hle⟩ := exists_pos_le_massGE m d hm
      (fun s => massGE m d (d s) < γ) (lt_of_le_of_lt hγ0 hcon')
    have hp' : massGE m d (d p) < γ := hp
    linarith
  -- the slots that are too low carry mass at most `1 - δ`
  have hL : (∑ s, if δ < massGT m d (d s) then m s else 0) ≤ 1 - δ := by
    by_contra hcon
    have hcon' : 1 - δ < ∑ s, if δ < massGT m d (d s) then m s else 0 := not_le.mp hcon
    have hpos : 0 < ∑ s, if δ < massGT m d (d s) then m s else 0 := by linarith
    obtain ⟨s₀, hs₀, -⟩ :=
      exists_pos_of_sum_ite_pos m hm (fun s => δ < massGT m d (d s)) hpos
    obtain ⟨p, hp, hle⟩ :=
      exists_add_massGT_le m d hm (fun s => δ < massGT m d (d s)) ⟨s₀, hs₀⟩
    have hp' : δ < massGT m d (d p) := hp
    rw [hsum] at hle
    linarith
  -- every slot is a pivot candidate, too high, or too low
  have hcover : (∑ s, m s)
      ≤ (∑ s, if massGT m d (d s) ≤ δ ∧ γ ≤ massGE m d (d s) then m s else 0)
        + (∑ s, if massGE m d (d s) < γ then m s else 0)
        + (∑ s, if δ < massGT m d (d s) then m s else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro s _
    have h1 : 0 ≤ (if massGT m d (d s) ≤ δ ∧ γ ≤ massGE m d (d s) then m s else 0) :=
      ite_nonneg (hm s) le_rfl
    have h2 : 0 ≤ (if massGE m d (d s) < γ then m s else 0) := ite_nonneg (hm s) le_rfl
    have h3 : 0 ≤ (if δ < massGT m d (d s) then m s else 0) := ite_nonneg (hm s) le_rfl
    by_cases hQ : massGE m d (d s) < γ
    · rw [if_pos hQ] at h2 ⊢
      linarith
    · by_cases hR : δ < massGT m d (d s)
      · rw [if_pos hR] at h3 ⊢
        linarith
      · have hP : massGT m d (d s) ≤ δ ∧ γ ≤ massGE m d (d s) :=
          ⟨not_lt.mp hR, not_lt.mp hQ⟩
        rw [if_pos hP] at h1 ⊢
        linarith
  have hV : δ - γ ≤ ∑ s, if massGT m d (d s) ≤ δ ∧ γ ≤ massGE m d (d s) then m s else 0 := by
    rw [hsum] at hcover
    linarith
  -- a positive-mass candidate of least score
  obtain ⟨s₀, hs₀⟩ := exists_pos_of_sum_ite_pos m hm
    (fun s => massGT m d (d s) ≤ δ ∧ γ ≤ massGE m d (d s)) (by linarith)
  obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image
    (Finset.univ.filter
      (fun s => (massGT m d (d s) ≤ δ ∧ γ ≤ massGE m d (d s)) ∧ 0 < m s)) F
    ⟨s₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs₀⟩⟩
  obtain ⟨⟨hp1, hp2⟩, hp3⟩ :
      (massGT m d (d p) ≤ δ ∧ γ ≤ massGE m d (d p)) ∧ 0 < m p := (Finset.mem_filter.mp hp).2
  refine ⟨p, hp1, hp2, hp3, ?_⟩
  calc (δ - γ) * F p
      ≤ (∑ s, if massGT m d (d s) ≤ δ ∧ γ ≤ massGE m d (d s) then m s else 0) * F p :=
        mul_le_mul_of_nonneg_right hV (hF p)
    _ = ∑ s, (if massGT m d (d s) ≤ δ ∧ γ ≤ massGE m d (d s) then m s else 0) * F p :=
        Finset.sum_mul _ _ _
    _ ≤ ∑ s, m s * F s := by
        apply Finset.sum_le_sum
        intro s _
        by_cases hs : massGT m d (d s) ≤ δ ∧ γ ≤ massGE m d (d s)
        · rw [if_pos hs]
          rcases (hm s).eq_or_lt with h0 | hpos
          · rw [← h0, zero_mul, zero_mul]
          · exact mul_le_mul_of_nonneg_left
              (hmin s (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs, hpos⟩)) (hm s)
        · rw [if_neg hs, zero_mul]
          exact mul_nonneg (hm s) (hF s)

end SPLP
