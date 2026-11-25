import Mathlib

/-!
# The market lemma

Agents `e : E` choose among finitely many options `o : O`. Option `o` of agent `e` has
utility `b e o - ∑ i, u e o i * y i` at prices `y`, and pays `∑ i, u e o i * v i` when the
feedback direction is `v`. If `y` minimizes the wealth-weighted sum of best utilities, then no
feedback direction lets the agents make an aggregate profit, even when every agent is paid the
*least* payoff among its maximizing options (equation (5.1) of the preprint).
-/

namespace SPLP

open Finset

variable {ι E O : Type*} [Fintype ι] [Fintype E] [Fintype O] [Nonempty O]

/-- Utility of option `o` of agent `e` at prices `y`. -/
def util (b : E → O → ℝ) (u : E → O → ι → ℝ) (e : E) (o : O) (y : ι → ℝ) : ℝ :=
  b e o - ∑ i, u e o i * y i

/-- Best utility available to agent `e` at prices `y`. -/
noncomputable def best (b : E → O → ℝ) (u : E → O → ι → ℝ) (e : E) (y : ι → ℝ) : ℝ :=
  univ.sup' univ_nonempty (fun o => util b u e o y)

/-- Payoff of option `o` of agent `e` under feedback direction `v`. -/
def pay (u : E → O → ι → ℝ) (e : E) (o : O) (v : ι → ℝ) : ℝ :=
  ∑ i, u e o i * v i

/-- Wealth-weighted sum of best utilities. -/
noncomputable def potential (b : E → O → ℝ) (u : E → O → ι → ℝ) (w : E → ℝ) (y : ι → ℝ) : ℝ :=
  ∑ e, w e * best b u e y

omit [Fintype E] in
/-- Every option's utility is at most the best utility. -/
private lemma util_le_best (b : E → O → ℝ) (u : E → O → ι → ℝ) (e : E) (o : O) (y : ι → ℝ) :
    util b u e o y ≤ best b u e y :=
  Finset.le_sup' (fun o => util b u e o y) (mem_univ o)

omit [Fintype E] in
/-- A common upper bound on the utilities of all options bounds the best utility. -/
private lemma best_le (b : E → O → ℝ) (u : E → O → ι → ℝ) (e : E) (y : ι → ℝ) (a : ℝ)
    (h : ∀ o, util b u e o y ≤ a) : best b u e y ≤ a :=
  Finset.sup'_le _ _ fun o _ => h o

omit [Fintype E] [Fintype O] [Nonempty O] in
/-- Moving the prices by `t` times `v` lowers the utility of an option by `t` times its
payoff. -/
private lemma util_shift (b : E → O → ℝ) (u : E → O → ι → ℝ) (e : E) (o : O) (y v : ι → ℝ)
    (t : ℝ) : util b u e o (fun i => y i + t * v i) = util b u e o y - t * pay u e o v := by
  unfold util pay
  have h : ∑ i, u e o i * (y i + t * v i) = ∑ i, u e o i * y i + t * ∑ i, u e o i * v i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [h]
  ring

/-- A finite family of positive reals has a positive lower bound. -/
private lemma exists_pos_le {α : Type*} [Fintype α] (c : α → ℝ) (hc : ∀ a, 0 < c a) :
    ∃ t : ℝ, 0 < t ∧ ∀ a, t ≤ c a := by
  rcases isEmpty_or_nonempty α with hα | hα
  · exact ⟨1, one_pos, fun a => isEmptyElim a⟩
  · obtain ⟨a₀, -, ha₀⟩ :=
      Finset.exists_min_image (Finset.univ : Finset α) c Finset.univ_nonempty
    exact ⟨c a₀, hc a₀, fun a => ha₀ a (Finset.mem_univ a)⟩

/-- For a small enough step `t > 0` in direction `v`, every option of every agent `e` ends up
at most `t * g e` below the old best utility of `e`. -/
private lemma exists_step (b : E → O → ℝ) (u : E → O → ι → ℝ) (y v : ι → ℝ) (g : E → ℝ)
    (hg : ∀ e o, util b u e o y = best b u e y → g e ≤ pay u e o v) :
    ∃ t : ℝ, 0 < t ∧ ∀ e o, util b u e o y - t * pay u e o v ≤ best b u e y - t * g e := by
  classical
  have hc : ∀ p : E × O, 0 < (if util b u p.1 p.2 y = best b u p.1 y then (1 : ℝ)
      else (best b u p.1 y - util b u p.1 p.2 y) / (|g p.1| + |pay u p.1 p.2 v| + 1)) := by
    intro p
    split_ifs with h
    · exact one_pos
    · have h1 : util b u p.1 p.2 y < best b u p.1 y :=
        lt_of_le_of_ne (util_le_best b u p.1 p.2 y) h
      have h2 : 0 < |g p.1| + |pay u p.1 p.2 v| + 1 := by positivity
      exact div_pos (sub_pos.mpr h1) h2
  obtain ⟨t, ht, htc⟩ := exists_pos_le _ hc
  refine ⟨t, ht, fun e o => ?_⟩
  have hte : t ≤ (if util b u e o y = best b u e y then (1 : ℝ)
      else (best b u e y - util b u e o y) / (|g e| + |pay u e o v| + 1)) := htc (e, o)
  by_cases h : util b u e o y = best b u e y
  · have h1 : t * g e ≤ t * pay u e o v := mul_le_mul_of_nonneg_left (hg e o h) ht.le
    rw [h]
    linarith
  · have hD : 0 < |g e| + |pay u e o v| + 1 := by positivity
    rw [if_neg h] at hte
    have h2 : t * (|g e| + |pay u e o v| + 1) ≤ best b u e y - util b u e o y :=
      (le_div_iff₀ hD).mp hte
    have h3 : t * (g e - pay u e o v) ≤ t * (|g e| + |pay u e o v| + 1) := by
      refine mul_le_mul_of_nonneg_left ?_ ht.le
      have h4 := le_abs_self (g e)
      have h5 := neg_abs_le (pay u e o v)
      linarith
    have h6 : t * (g e - pay u e o v) = t * g e - t * pay u e o v := mul_sub _ _ _
    linarith

/-- **Market lemma.** At a minimizer of the potential, paying every agent at most the least
payoff among its maximizing options never yields positive aggregate gain. -/
theorem market_no_profit (b : E → O → ℝ) (u : E → O → ι → ℝ) (w : E → ℝ)
    (hw : ∀ e, 0 ≤ w e) (y : ι → ℝ)
    (hmin : ∀ y', potential b u w y ≤ potential b u w y') (v : ι → ℝ) (g : E → ℝ)
    (hg : ∀ e o, util b u e o y = best b u e y → g e ≤ pay u e o v) :
    ∑ e, w e * g e ≤ 0 := by
  -- a small step `t > 0` in direction `v` lowers every agent's best utility by `t * g e`
  obtain ⟨t, ht, hstep⟩ := exists_step b u y v g hg
  have hbest : ∀ e, best b u e (fun i => y i + t * v i) ≤ best b u e y - t * g e := by
    intro e
    refine best_le b u e _ _ fun o => ?_
    rw [util_shift]
    exact hstep e o
  -- hence the potential drops by at least `t * ∑ e, w e * g e`
  have hpot : potential b u w (fun i => y i + t * v i)
      ≤ potential b u w y - t * ∑ e, w e * g e := by
    have h1 : potential b u w y - t * ∑ e, w e * g e
        = ∑ e, w e * (best b u e y - t * g e) := by
      unfold potential
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun e _ => ?_
      ring
    rw [h1]
    unfold potential
    exact Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left (hbest e) (hw e)
  -- but `y` minimizes the potential
  have hmin' := hmin (fun i => y i + t * v i)
  have hle : t * ∑ e, w e * g e ≤ 0 := by linarith
  by_contra hcon
  have hpos : 0 < ∑ e, w e * g e := not_le.mp hcon
  have := mul_pos ht hpos
  linarith

end SPLP
