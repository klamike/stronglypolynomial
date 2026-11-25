import Mathlib
import SPLP.Defs
import SPLP.Experts
import SPLP.Weights
import SPLP.Boost
import SPLP.Product
import SPLP.Median

/-!
# Node invariants for a fixed hypothesis

The analysis attaches to every node of a run, for a fixed consistent hypothesis, a threshold
`t`, a threshold description `d₀` and a probability distribution `m` on the slots of the
hypothesis. `NodeInv` collects what the proofs need: `m` is a distribution, the description
really evaluates to `t`, and every slot has been boosted whenever it exceeded the threshold.
-/

set_option linter.unusedSectionVars false

namespace SPLP

open Finset

variable {ι V : Type*} {k D : ℕ} [Fintype ι] [DecidableEq ι]

/-- Number of proposals on the path at which slot `s` has surplus at most `t`. -/
noncomputable def lowCount (val : V → ℝ) (H : Hyp ι V) (l : ℕ) (hist : ℕ → ι → ℝ)
    (s : Slot ι) (t : ℝ) : ℕ :=
  ((range l).filter (fun j => H.surplus val (hist j) s ≤ t)).card

/-- The invariant carried by a node of level `l` for the hypothesis `H`. -/
structure NodeInv (val : V → ℝ) (H : Hyp ι V) (ρ β : ℝ) (l : ℕ) (hist : ℕ → ι → ℝ)
    (m : Slot ι → ℝ) (t : ℝ) (d₀ : Option (Fin D × Slot ι)) : Prop where
  nonneg : ∀ s, 0 ≤ m s
  supp : ∀ s, s ∉ H.S → m s = 0
  sum_one : ∑ s, m s = 1
  boost : ∀ s ∈ H.S, ρ ^ l ≤ m s * H.S.card * β ^ lowCount val H l hist s t
  thr_nonneg : 0 ≤ t
  desc : (d₀ = none ∧ t = 0) ∨
    ∃ j p, d₀ = some (j, p) ∧ (j : ℕ) < l ∧ t = H.surplus val (hist j) p

theorem card_filter_fin_eq_range (l : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (univ.filter (fun j : Fin l => P j)).card = ((range l).filter P).card := by
  rw [Finset.card_filter, Finset.card_filter]
  exact Fin.sum_univ_eq_sum_range (fun j => if P j then 1 else 0) l

section Basic

variable {val : V → ℝ} {H : Hyp ι V} {ρ β : ℝ} {l : ℕ} {hist : ℕ → ι → ℝ}
  {m : Slot ι → ℝ} {t : ℝ} {d₀ : Option (Fin D × Slot ι)}

theorem NodeInv.le_one (inv : NodeInv val H ρ β l hist m t d₀) (s : Slot ι) : m s ≤ 1 := by
  rw [← inv.sum_one]
  exact Finset.single_le_sum (fun i _ => inv.nonneg i) (Finset.mem_univ s)

/-- A true-demand expert carrying the node's description has the node's threshold. -/
theorem thr_trueExp_cur (inv : NodeInv val H ρ β l hist m t d₀) (tup : Fin k → Slot ι) :
    thr val l hist (trueExp H tup d₀) = some t := by
  rcases inv.desc with ⟨hd, ht⟩ | ⟨j, p, hd, hj, ht⟩
  · subst hd; subst ht
    simp [thr, trueExp]
  · subst hd
    simp [thr, trueExp, hj, ht, Hyp.surplus]

/-- A true-demand expert reserved for a pivot level `j ≥ l` does not bid at level `l`. -/
theorem thr_trueExp_reserve (val : V → ℝ) (H : Hyp ι V) (hist : ℕ → ι → ℝ)
    (tup : Fin k → Slot ι) (j : Fin D) (p : Slot ι) (h : l ≤ (j : ℕ)) :
    thr val l hist (trueExp H tup (some (j, p))) = none := by
  simp [thr, trueExp, Nat.not_lt.2 h]

theorem util_trueExp (inv : NodeInv val H ρ β l hist m t d₀) (tup : Fin k → Slot ι)
    (q : Fin k) (y : ι → ℝ) :
    util (bidOf val l hist) (dirOf val l hist) (trueExp H tup d₀) (some q) y
      = H.surplus val y (tup q) - t := by
  rw [util_some_of_thr (thr_trueExp_cur inv tup)]
  simp [trueExp, Hyp.surplus]
  ring

theorem pay_trueExp (inv : NodeInv val H ρ β l hist m t d₀) (tup : Fin k → Slot ι)
    (q : Fin k) (v : ι → Bool) :
    pay (dirOf val l hist) (trueExp H tup d₀) (some q) (vreal v)
      = if v (tup q).1 = (tup q).2 then 1 else -1 := by
  rw [pay_some_of_thr (thr_trueExp_cur inv tup)]
  rfl

/-- Light probes: if feedback is correct on every slot of surplus at least the node's
threshold, an aligned expert never loses. -/
theorem gain_trueExp_nonneg (inv : NodeInv val H ρ β l hist m t d₀) (y : ι → ℝ)
    (v : ι → Bool) (hv : ∀ s ∈ H.S, t ≤ H.surplus val y s → v s.1 = s.2)
    (tup : Fin k → Slot ι) (htup : ∀ q, tup q ∈ H.S) :
    0 ≤ gain val l hist y v (trueExp H tup d₀) := by
  refine le_minPay _ _ _ _ _ _ (fun o ho => ?_)
  cases o with
  | none => rw [pay_none]
  | some q =>
    have h0 : (0 : ℝ) ≤ H.surplus val y (tup q) - t := by
      rw [← util_trueExp inv tup q y, ho, ← util_none val l hist (trueExp H tup d₀) y]
      exact util_le_best _ _ _ _ _
    rw [pay_trueExp inv, if_pos (hv _ (htup q) (by linarith))]
    norm_num

/-- Heavy probes: if feedback is correct on every slot of surplus at least `t' > t` and the
expert holds such a slot, it wins. -/
theorem gain_trueExp_eq_one (inv : NodeInv val H ρ β l hist m t d₀) (y : ι → ℝ)
    (v : ι → Bool) (t' : ℝ) (htt' : t < t')
    (hv : ∀ s ∈ H.S, t' ≤ H.surplus val y s → v s.1 = s.2)
    (tup : Fin k → Slot ι) (htup : ∀ q, tup q ∈ H.S)
    (hhit : ∃ q, t' ≤ H.surplus val y (tup q)) :
    gain val l hist y v (trueExp H tup d₀) = 1 := by
  obtain ⟨q₀, hq₀⟩ := hhit
  have hbest : t' - t ≤ best (bidOf val l hist) (dirOf val l hist) (trueExp H tup d₀) y := by
    have := util_le_best (bidOf val l hist) (dirOf val l hist) (trueExp H tup d₀) (some q₀) y
    rw [util_trueExp inv] at this
    linarith
  refine le_antisymm (gain_bounds val l hist _ y v).2 ?_
  refine le_minPay _ _ _ _ _ _ (fun o ho => ?_)
  cases o with
  | none =>
    rw [util_none] at ho
    linarith
  | some q =>
    rw [util_trueExp inv] at ho
    rw [pay_trueExp inv, if_pos (hv _ (htup q) (by linarith))]

end Basic

/-- If the child brought every surplus down to `t' ≥ 0`, the feedback is correct on every slot
whose surplus at the proposal is at least `t'` (implication (5.3) of the preprint). -/
theorem feedback_correct (val : V → ℝ) (H : Hyp ι V) (y x : ι → ℝ) (z : ι → Bool) (t' : ℝ)
    (ht' : 0 ≤ t') (hsucc : ∀ s ∈ H.S, H.surplus val x s ≤ t')
    (hcons : H.ConsistentAt val x z) :
    ∀ s ∈ H.S, t' ≤ H.surplus val y s → feedback y x z s.1 = s.2 := by
  rintro ⟨i, h⟩ hs hy
  have hx := hsucc _ hs
  have htie : x i = y i → z i = h := by
    intro hxy
    have heq : H.surplus val x (i, h) = t' := by
      apply le_antisymm hx
      have : H.surplus val x (i, h) = H.surplus val y (i, h) := by
        simp [Hyp.surplus, sp, hxy]
      rw [this]; exact hy
    exact hcons (i, h) hs (fun u hu => by rw [heq]; exact hsucc u hu) (by rw [heq]; exact ht')
  have hsp : sp y (i, h) ≤ sp x (i, h) := by
    simp only [Hyp.surplus] at hx hy
    linarith
  cases h with
  | true =>
    have hle : y i ≤ x i := by simpa [sp, sgn] using hsp
    simp only [feedback]
    by_cases h1 : y i < x i
    · simp [h1]
    · have hxy : x i = y i := le_antisymm (not_lt.1 h1) hle
      simp [hxy, htie hxy]
  | false =>
    have hle : x i ≤ y i := by simpa [sp, sgn] using hsp
    simp only [feedback]
    by_cases h1 : x i < y i
    · simp [h1, not_lt.2 hle]
    · have hxy : x i = y i := le_antisymm hle (not_lt.1 h1)
      simp [hxy, htie hxy]


/-! ### The child's distribution -/

section Child

variable {val : V → ℝ} {H : Hyp ι V} {ρ β δ : ℝ} {l : ℕ} {hist : ℕ → ι → ℝ}
  {m : Slot ι → ℝ} {t : ℝ} {d₀ : Option (Fin D × Slot ι)}

theorem lowCount_succ (val : V → ℝ) (H : Hyp ι V) (l : ℕ) (hist : ℕ → ι → ℝ) (y : ι → ℝ)
    (s : Slot ι) (t' : ℝ) :
    lowCount val H (l + 1) (Function.update hist l y) s t'
      = lowCount val H l hist s t' + (if H.surplus val y s ≤ t' then 1 else 0) := by
  unfold lowCount
  rw [Finset.range_add_one, Finset.filter_insert]
  have hcongr : (range l).filter (fun j => H.surplus val (Function.update hist l y j) s ≤ t')
      = (range l).filter (fun j => H.surplus val (hist j) s ≤ t') := by
    apply Finset.filter_congr
    intro j hj
    have hne : j ≠ l := (Finset.mem_range.1 hj).ne
    rw [Function.update_of_ne hne]
  rw [Function.update_self, hcongr]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

theorem lowCount_mono (val : V → ℝ) (H : Hyp ι V) (l : ℕ) (hist : ℕ → ι → ℝ) (s : Slot ι)
    {t t' : ℝ} (h : t ≤ t') : lowCount val H l hist s t ≤ lowCount val H l hist s t' := by
  unfold lowCount
  apply Finset.card_le_card
  intro j hj
  simp only [Finset.mem_filter] at hj ⊢
  exact ⟨hj.1, hj.2.trans h⟩

/-- **Boosted distribution of a child.** It depends only on the parent's distribution and the
proposal, is dominated by `ρ` times the parent's distribution, and maintains the invariant for
every child threshold `t' ≥ t` whose strict violators carry mass at most `δ`. -/
theorem exists_child_dist (hβ : 1 < β) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hρ : ρ * (1 + (β - 1) * δ) = β)
    (inv : NodeInv val H ρ β l hist m t d₀) (y : ι → ℝ) :
    ∃ m' : Slot ι → ℝ, (∀ s, 0 ≤ m' s) ∧ (∀ s, m' s ≤ ρ * m s) ∧
      ∀ (t' : ℝ) (d₀' : Option (Fin D × Slot ι)), t ≤ t' →
        massGT m (H.surplus val y) t' ≤ δ →
        ((d₀' = none ∧ t' = 0) ∨ ∃ j p, d₀' = some (j, p) ∧ (j : ℕ) < l + 1 ∧
            t' = H.surplus val (Function.update hist l y j) p) →
        NodeInv val H ρ β (l + 1) (Function.update hist l y) m' t' d₀' := by
  obtain ⟨φ, hφ, hφsum, hφtop⟩ :=
    exists_boost m (H.surplus val y) inv.nonneg inv.sum_one δ hδ0 hδ1
  have hden : 0 < 1 + (β - 1) * δ := by nlinarith
  have hρeq : ρ = β / (1 + (β - 1) * δ) := eq_div_of_mul_eq hden.ne' hρ
  have hρpos : 0 < ρ := by rw [hρeq]; exact div_pos (by linarith) hden
  have hnum : ∀ s, 1 ≤ 1 + (β - 1) * φ s := fun s => by nlinarith [(hφ s).1]
  have hnum' : ∀ s, 1 + (β - 1) * φ s ≤ β := fun s => by nlinarith [(hφ s).2]
  refine ⟨fun s => m s * (1 + (β - 1) * φ s) / (1 + (β - 1) * δ), ?_, ?_, ?_⟩
  · intro s
    exact div_nonneg (mul_nonneg (inv.nonneg s) (by linarith [hnum s])) hden.le
  · intro s
    rw [hρeq, div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hden.le
    rw [mul_comm β (m s)]
    exact mul_le_mul_of_nonneg_left (hnum' s) (inv.nonneg s)
  · intro t' d₀' htt' hmass hdesc
    refine ⟨?_, ?_, ?_, ?_, inv.thr_nonneg.trans htt', hdesc⟩
    · intro s
      exact div_nonneg (mul_nonneg (inv.nonneg s) (by linarith [hnum s])) hden.le
    · intro s hs
      simp [inv.supp s hs]
    · rw [← Finset.sum_div]
      have hsum : ∑ s, m s * (1 + (β - 1) * φ s) = 1 + (β - 1) * δ := by
        simp only [mul_add, mul_one]
        rw [Finset.sum_add_distrib, inv.sum_one, ← hφsum, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl (fun s _ => by ring)
      rw [hsum, div_self hden.ne']
    · intro s hs
      have hb := inv.boost s hs
      have hms : 0 < m s := by
        by_contra h
        have h0 : m s = 0 := le_antisymm (not_lt.1 h) (inv.nonneg s)
        rw [h0, zero_mul, zero_mul] at hb
        exact absurd hb (not_le.2 (pow_pos hρpos l))
      have hmono := lowCount_mono val H l hist s htt'
      rw [lowCount_succ]
      have hS : (0 : ℝ) ≤ H.S.card := Nat.cast_nonneg _
      have hβn : β ^ lowCount val H l hist s t ≤ β ^ lowCount val H l hist s t' :=
        pow_le_pow_right₀ hβ.le hmono
      have hstep : ρ ^ (l + 1) ≤ ρ * (m s * H.S.card * β ^ lowCount val H l hist s t') := by
        rw [pow_succ, mul_comm]
        apply mul_le_mul_of_nonneg_left _ hρpos.le
        exact hb.trans (mul_le_mul_of_nonneg_left hβn (mul_nonneg hms.le hS))
      by_cases hys : H.surplus val y s ≤ t'
      · rw [if_pos hys]
        have h1 : m s / (1 + (β - 1) * δ) ≤ m s * (1 + (β - 1) * φ s) / (1 + (β - 1) * δ) := by
          apply div_le_div_of_nonneg_right _ hden.le
          nlinarith [hnum s, hms.le]
        have hβpos : 0 < β := by linarith
        calc ρ ^ (l + 1) ≤ ρ * (m s * H.S.card * β ^ lowCount val H l hist s t') := hstep
          _ = m s / (1 + (β - 1) * δ) * H.S.card * β ^ (lowCount val H l hist s t' + 1) := by
              rw [hρeq, pow_succ]; field_simp
          _ ≤ m s * (1 + (β - 1) * φ s) / (1 + (β - 1) * δ) * H.S.card
                * β ^ (lowCount val H l hist s t' + 1) := by
              apply mul_le_mul_of_nonneg_right _ (pow_nonneg hβpos.le _)
              exact mul_le_mul_of_nonneg_right h1 hS
      · rw [if_neg hys, add_zero]
        have hφ1 : φ s = 1 := hφtop t' hmass s (not_le.1 hys) hms
        have hm' : m s * (1 + (β - 1) * φ s) / (1 + (β - 1) * δ) = ρ * m s := by
          rw [hφ1, hρeq]; field_simp; ring
        rw [hm']
        calc ρ ^ (l + 1) ≤ ρ * (m s * H.S.card * β ^ lowCount val H l hist s t') := hstep
          _ = ρ * m s * H.S.card * β ^ lowCount val H l hist s t' := by ring

/-- **Leaves succeed** (Lemma 5.1 of the preprint, with the depth condition
`(2N)² < (ρ²/β)^D`). -/
theorem leaf_success (hβ : 1 < β) (hρ0 : 0 < ρ)
    (hdepth : ((Fintype.card (Slot ι) : ℝ)) ^ 2 < (ρ ^ 2 / β) ^ l)
    (inv : NodeInv val H ρ β l hist m t d₀) (x : ι → ℝ)
    (hx : ∀ i, IsMedian (fun j : Fin l => hist j i) (x i)) :
    ∀ s ∈ H.S, H.surplus val x s ≤ t := by
  intro s hs
  by_contra hcon
  rw [not_le] at hcon
  have hhalf : l ≤ 2 * (univ.filter (fun j : Fin l => t < H.surplus val (hist j) s)).card := by
    obtain ⟨i, h⟩ := s
    cases h with
    | true =>
      have h1 : x i < val (H.a (i, true)) - t := by
        simp only [Hyp.surplus, sp, sgn, if_true, one_mul] at hcon
        linarith
      have h2 := (hx i).half_lt_of_lt h1
      have hset : (univ.filter (fun j : Fin l => t < H.surplus val (hist j) (i, true)))
          = univ.filter (fun j : Fin l => hist j i < val (H.a (i, true)) - t) := by
        apply Finset.filter_congr
        intro j _
        simp only [Hyp.surplus, sp, sgn, if_true, one_mul]
        constructor <;> intro h <;> linarith
      rw [hset]; exact h2
    | false =>
      have h1 : t - val (H.a (i, false)) < x i := by
        simp only [Hyp.surplus, sp, sgn] at hcon
        simp at hcon
        linarith
      have h2 := (hx i).half_gt_of_gt h1
      have hset : (univ.filter (fun j : Fin l => t < H.surplus val (hist j) (i, false)))
          = univ.filter (fun j : Fin l => t - val (H.a (i, false)) < hist j i) := by
        apply Finset.filter_congr
        intro j _
        simp only [Hyp.surplus, sp, sgn]
        simp
        constructor <;> intro h <;> linarith
      rw [hset]; exact h2
  have hlow : 2 * lowCount val H l hist s t ≤ l := by
    have hsplit : (univ.filter (fun j : Fin l => t < H.surplus val (hist j) s)).card
        + lowCount val H l hist s t = l := by
      unfold lowCount
      rw [← card_filter_fin_eq_range l (fun j => H.surplus val (hist j) s ≤ t)]
      have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin l)))
        (fun j => t < H.surplus val (hist j) s)
      simp only [not_lt, Finset.card_univ, Fintype.card_fin] at h
      exact h
    omega
  have hb := inv.boost s hs
  have hβpos : 0 < β := by linarith
  have hN : (H.S.card : ℝ) ≤ Fintype.card (Slot ι) := by
    exact_mod_cast Finset.card_le_univ H.S
  have hcard0 : (0 : ℝ) ≤ Fintype.card (Slot ι) := Nat.cast_nonneg _
  have h1 : ρ ^ l ≤ (Fintype.card (Slot ι) : ℝ) * β ^ lowCount val H l hist s t := by
    have hpow : 0 ≤ β ^ lowCount val H l hist s t := pow_nonneg hβpos.le _
    calc ρ ^ l ≤ m s * H.S.card * β ^ lowCount val H l hist s t := hb
      _ ≤ 1 * (Fintype.card (Slot ι) : ℝ) * β ^ lowCount val H l hist s t := by
          apply mul_le_mul_of_nonneg_right _ hpow
          exact mul_le_mul (inv.le_one s) hN (Nat.cast_nonneg _) zero_le_one
      _ = (Fintype.card (Slot ι) : ℝ) * β ^ lowCount val H l hist s t := by ring
  have h2 : (ρ ^ l) ^ 2 ≤ (Fintype.card (Slot ι) : ℝ) ^ 2 * β ^ l := by
    calc (ρ ^ l) ^ 2 ≤ ((Fintype.card (Slot ι) : ℝ) * β ^ lowCount val H l hist s t) ^ 2 :=
          pow_le_pow_left₀ (pow_nonneg hρ0.le l) h1 2
      _ = (Fintype.card (Slot ι) : ℝ) ^ 2 * β ^ (2 * lowCount val H l hist s t) := by ring
      _ ≤ (Fintype.card (Slot ι) : ℝ) ^ 2 * β ^ l :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hβ.le hlow) (sq_nonneg _)
  have h3 : (ρ ^ 2 / β) ^ l ≤ (Fintype.card (Slot ι) : ℝ) ^ 2 := by
    rw [div_pow, div_le_iff₀ (pow_pos hβpos l)]
    calc (ρ ^ 2) ^ l = (ρ ^ l) ^ 2 := by ring
      _ ≤ _ := h2
  linarith

end Child

/-! ### Market gains of the aligned experts -/

section GainSums

variable {val : V → ℝ} {H : Hyp ι V} {ρ β : ℝ} {l : ℕ} {hist : ℕ → ι → ℝ}
  {m : Slot ι → ℝ} {t : ℝ} {d₀ : Option (Fin D × Slot ι)}

theorem prod_eq_zero_of_not_mem (inv : NodeInv val H ρ β l hist m t d₀) (tup : Fin k → Slot ι)
    (h : ¬ ∀ q, tup q ∈ H.S) : ∏ q, m (tup q) = 0 := by
  rw [not_forall] at h
  obtain ⟨q, hq⟩ := h
  exact Finset.prod_eq_zero (Finset.mem_univ q) (inv.supp _ hq)

/-- Light probe with a successful child: aligned experts do not lose. -/
theorem cur_gain_light (inv : NodeInv val H ρ β l hist m t d₀) {η : ℝ} (hη0 : 0 < η)
    (y : ι → ℝ) (v : ι → Bool) (hv : ∀ s ∈ H.S, t ≤ H.surplus val y s → v s.1 = s.2) :
    0 ≤ cur H m d₀ (fun e : Expert ι V k D => Real.log (1 + η * gain val l hist y v e)) := by
  unfold cur
  refine Finset.sum_nonneg (fun tup _ => ?_)
  by_cases htup : ∀ q, tup q ∈ H.S
  · refine mul_nonneg (prod_nonneg_of m inv.nonneg tup) (Real.log_nonneg ?_)
    have := gain_trueExp_nonneg inv y v hv tup htup
    nlinarith
  · rw [prod_eq_zero_of_not_mem inv tup htup, zero_mul]

/-- Any probe: aligned experts lose at most `-log (1 - η)` on average. -/
theorem cur_gain_any (inv : NodeInv val H ρ β l hist m t d₀) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η < 1) (y : ι → ℝ) (v : ι → Bool) :
    Real.log (1 - η)
      ≤ cur H m d₀ (fun e : Expert ι V k D => Real.log (1 + η * gain val l hist y v e)) := by
  have hpt : ∀ e : Expert ι V k D,
      Real.log (1 - η) ≤ Real.log (1 + η * gain val l hist y v e) := by
    intro e
    apply Real.log_le_log (by linarith)
    have := (gain_bounds val l hist e y v).1
    nlinarith
  have h := cur_mono H m inv.nonneg d₀ hpt
  rwa [cur_const H m inv.sum_one] at h

/-- Heavy probe with a successful child: aligned experts hit the correctly labelled slots with
probability at least `1 - (1 - γ)^k`, and gain on average. -/
theorem cur_gain_heavy (inv : NodeInv val H ρ β l hist m t d₀) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η < 1) (y : ι → ℝ) (v : ι → Bool) (t' : ℝ) (htt' : t < t')
    (hv : ∀ s ∈ H.S, t' ≤ H.surplus val y s → v s.1 = s.2)
    (γ : ℝ) (hγ : γ ≤ massGE m (H.surplus val y) t') :
    (1 - (1 - γ) ^ k) * Real.log (1 + η) + (1 - γ) ^ k * Real.log (1 - η)
      ≤ cur H m d₀ (fun e : Expert ι V k D => Real.log (1 + η * gain val l hist y v e)) := by
  classical
  have hhit := hit_mass m inv.nonneg inv.sum_one (fun s => t' ≤ H.surplus val y s) γ
    (by simpa [massGE] using hγ) k
  have hlog : Real.log (1 - η) ≤ Real.log (1 + η) :=
    Real.log_le_log (by linarith) (by linarith)
  have hterm : ∀ tup : Fin k → Slot ι,
      (if ∃ q, t' ≤ H.surplus val y (tup q) then ∏ q, m (tup q) else 0) * Real.log (1 + η)
        + (∏ q, m (tup q)
            - (if ∃ q, t' ≤ H.surplus val y (tup q) then ∏ q, m (tup q) else 0))
          * Real.log (1 - η)
      ≤ (∏ q, m (tup q))
          * Real.log (1 + η * gain val l hist y v (trueExp H tup d₀ : Expert ι V k D)) := by
    intro tup
    by_cases htup : ∀ q, tup q ∈ H.S
    · by_cases hh : ∃ q, t' ≤ H.surplus val y (tup q)
      · rw [if_pos hh, gain_trueExp_eq_one inv y v t' htt' hv tup htup hh]
        simp
      · rw [if_neg hh]
        simp only [zero_mul, zero_add, sub_zero]
        apply mul_le_mul_of_nonneg_left _ (prod_nonneg_of m inv.nonneg tup)
        apply Real.log_le_log (by linarith)
        have := (gain_bounds val l hist (trueExp H tup d₀ : Expert ι V k D) y v).1
        nlinarith
    · rw [prod_eq_zero_of_not_mem inv tup htup]
      simp
  have hsum := Finset.sum_le_sum (fun tup (_ : tup ∈ (univ : Finset (Fin k → Slot ι))) => hterm tup)
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, Finset.sum_sub_distrib,
    sum_prod_tuple, inv.sum_one, one_pow] at hsum
  unfold cur
  nlinarith [hhit, hlog, hsum]

/-- Experts reserved for future pivot levels do not bid, so only the current description
contributes market gains. -/
theorem Psi_gain_eq_cur (val : V → ℝ) (H : Hyp ι V) (ω : ℕ → ℝ) (l : ℕ) (hist : ℕ → ι → ℝ)
    (m : Slot ι → ℝ) (d₀ : Option (Fin D × Slot ι)) (η : ℝ) (y : ι → ℝ) (v : ι → Bool) :
    Psi H ω l m d₀ (fun e : Expert ι V k D => Real.log (1 + η * gain val l hist y v e))
      = cur H m d₀ (fun e : Expert ι V k D => Real.log (1 + η * gain val l hist y v e)) := by
  unfold Psi
  have hz : ∑ j : Fin D, (if l ≤ (j : ℕ) then ω (j - l)
      * res H m j (fun e : Expert ι V k D => Real.log (1 + η * gain val l hist y v e)) else 0)
      = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    split_ifs with hj
    · have hres : res H m j
          (fun e : Expert ι V k D => Real.log (1 + η * gain val l hist y v e)) = 0 := by
        unfold res cur
        apply Finset.sum_eq_zero
        intro p _
        rw [Finset.sum_eq_zero, mul_zero]
        intro tup _
        beta_reduce
        rw [gain_of_inactive val l hist _ (thr_trueExp_reserve val H hist tup j p hj)]
        simp
      rw [hres, mul_zero]
    · rfl
  rw [hz, add_zero]

end GainSums

end SPLP
