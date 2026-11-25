import Mathlib
import SPLP.Total

/-!
# Vertex minimizers of the market potential

A direction `d` *preserves the ties* at `y` if any two options of any expert that have equal
utility at `y` keep equal utility along `y + s d`. A minimizer is a *vertex* if only `d = 0`
preserves its ties. Vertex minimizers exist; they are the proposals an implementation uses
(the preprint's "prices at vertices").
-/

set_option linter.unusedSectionVars false

namespace SPLP

open Finset Filter

variable {ι V : Type*} {k D : ℕ} [Fintype ι] [DecidableEq ι] [Fintype V]

/-- `d` preserves every tie between two options of an expert at the prices `y`. -/
def TieHom (val : V → ℝ) (l : ℕ) (hist : ℕ → ι → ℝ) (y d : ι → ℝ) : Prop :=
  ∀ (e : Expert ι V k D) (o o' : Option (Fin k)),
    util (bidOf val l hist) (dirOf val l hist) e o y
        = util (bidOf val l hist) (dirOf val l hist) e o' y →
      pay (dirOf val l hist) e o d = pay (dirOf val l hist) e o' d

/-- `y` is a vertex: only the zero direction preserves all ties at `y`. -/
def IsVertex (val : V → ℝ) (l : ℕ) (hist : ℕ → ι → ℝ) (y : ι → ℝ) : Prop :=
  ∀ d : ι → ℝ, TieHom (k := k) (D := D) val l hist y d → d = 0

/-- Moving the prices by `t` times `v` lowers the utility of an option by `t` times its
payoff. -/
private lemma vtx_util_shift {E O : Type*} (b : E → O → ℝ) (u : E → O → ι → ℝ) (e : E) (o : O)
    (y v : ι → ℝ) (t : ℝ) :
    util b u e o (fun i => y i + t * v i) = util b u e o y - t * pay u e o v := by
  unfold util pay
  have h : ∑ i, u e o i * (y i + t * v i) = ∑ i, u e o i * y i + t * ∑ i, u e o i * v i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [h]
  ring

/-- Along a tie-preserving direction `d` from a minimizer `y` of the potential, either the whole
ray `y + s d`, `s ≥ 0`, consists of minimizers, or some point of the ray is a minimizer at
which two options that were not tied at `y` are tied. -/
private lemma vtx_ray {E O : Type*} [Fintype E] [Fintype O] [Nonempty O]
    (b : E → O → ℝ) (u : E → O → ι → ℝ) (w : E → ℝ) (hw : ∀ e, 0 ≤ w e) (y d : ι → ℝ)
    (hmin : ∀ y', potential b u w y ≤ potential b u w y')
    (hd : ∀ e o o', util b u e o y = util b u e o' y → pay u e o d = pay u e o' d) :
    (∀ s : ℝ, 0 ≤ s → potential b u w (fun i => y i + s * d i) ≤ potential b u w y) ∨
    ∃ s : ℝ, potential b u w (fun i => y i + s * d i) ≤ potential b u w y ∧
      ∃ e o o', util b u e o y ≠ util b u e o' y ∧
        util b u e o (fun i => y i + s * d i) = util b u e o' (fun i => y i + s * d i) := by
  classical
  -- a maximizing option of every agent at `y`
  have hex : ∀ e, ∃ o, util b u e o y = best b u e y := fun e => by
    obtain ⟨o, ho⟩ := bestSet_nonempty b u e y
    exact ⟨o, by simpa using ho⟩
  choose o₀ ho₀ using hex
  -- the slope of the potential along `d` is nonnegative, by minimality in direction `-d`
  have hc₀ : 0 ≤ ∑ e, w e * pay u e (o₀ e) d := by
    have h := market_no_profit b u w hw y hmin (fun i => -d i) (fun e => -pay u e (o₀ e) d)
      (by
        intro e o ho
        have h1 : pay u e o d = pay u e (o₀ e) d := hd e o (o₀ e) (ho.trans (ho₀ e).symm)
        have h2 : pay u e o (fun i => -d i) = -pay u e o d := by
          simp [pay]
        rw [h2, h1])
    simp only [mul_neg, Finset.sum_neg_distrib] at h
    linarith
  -- as long as strict preferences at `y` do not reverse, the potential is affine
  have key : ∀ s : ℝ, (∀ e o o', util b u e o y < util b u e o' y →
        util b u e o (fun i => y i + s * d i) ≤ util b u e o' (fun i => y i + s * d i)) →
      potential b u w (fun i => y i + s * d i)
        = potential b u w y - s * ∑ e, w e * pay u e (o₀ e) d := by
    intro s hs
    have hbest : ∀ e, best b u e (fun i => y i + s * d i)
        = best b u e y - s * pay u e (o₀ e) d := by
      intro e
      rw [← ho₀ e, ← vtx_util_shift]
      apply le_antisymm
      · refine Finset.sup'_le _ _ fun o _ => ?_
        rcases (util_le_best b u e o y).lt_or_eq with h | h
        · exact hs e o (o₀ e) (by rw [ho₀ e]; exact h)
        · have h' : util b u e o y = util b u e (o₀ e) y := h.trans (ho₀ e).symm
          have hp := hd e o (o₀ e) h'
          exact le_of_eq (by rw [vtx_util_shift, vtx_util_shift, h', hp])
      · exact util_le_best b u e (o₀ e) _
    unfold potential
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hbest e]
    ring
  -- the positive times at which a strict preference at `y` could become a tie
  set A : E × O × O → ℝ := fun t => util b u t.1 t.2.2 y - util b u t.1 t.2.1 y with hA
  set C : E × O × O → ℝ := fun t => pay u t.1 t.2.2 d - pay u t.1 t.2.1 d with hC
  set R : Finset ℝ := (univ.image (fun t : E × O × O => A t / C t)).filter (fun r => 0 < r)
    with hR
  have hgood : ∀ s : ℝ, 0 ≤ s → (∀ r ∈ R, s ≤ r) → ∀ e o o',
      util b u e o y < util b u e o' y →
        util b u e o (fun i => y i + s * d i) ≤ util b u e o' (fun i => y i + s * d i) := by
    intro s hs0 hsR e o o' hlt
    by_contra hcon
    rw [not_le, vtx_util_shift, vtx_util_shift] at hcon
    have ha : 0 < A (e, o, o') := sub_pos.2 hlt
    have hsc : A (e, o, o') < s * C (e, o, o') := by
      simp only [hA, hC]
      linarith
    have hcpos : 0 < C (e, o, o') := by
      by_contra hc
      have : s * C (e, o, o') ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs0 (not_lt.1 hc)
      linarith
    have hr : A (e, o, o') / C (e, o, o') ∈ R := by
      simp only [hR, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨⟨(e, o, o'), rfl⟩, div_pos ha hcpos⟩
    have h1 := hsR _ hr
    rw [le_div_iff₀ hcpos] at h1
    linarith
  rcases R.eq_empty_or_nonempty with hRe | hRne
  · left
    intro s hs
    rw [key s (hgood s hs (by simp [hRe]))]
    have := mul_nonneg hs hc₀
    linarith
  · right
    have hmem := Finset.min'_mem R hRne
    have hle : ∀ r ∈ R, R.min' hRne ≤ r := fun r hr => Finset.min'_le R r hr
    set s := R.min' hRne
    simp only [hR, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] at hmem
    obtain ⟨⟨t, ht⟩, hpos⟩ := hmem
    have hCt : C t ≠ 0 := by
      intro h0
      rw [h0, div_zero] at ht
      linarith
    have hAt : A t ≠ 0 := by
      intro h0
      rw [h0, zero_div] at ht
      linarith
    have hst : s * C t = A t := by
      rw [← ht]
      exact div_mul_cancel₀ _ hCt
    refine ⟨s, ?_, t.1, t.2.1, t.2.2, ?_, ?_⟩
    · rw [key s (hgood s hpos.le hle)]
      have := mul_nonneg hpos.le hc₀
      linarith
    · intro h0
      exact hAt (by simp only [hA]; linarith)
    · rw [vtx_util_shift, vtx_util_shift]
      simp only [hA, hC] at hst
      linarith

/-- **Vertex minimizers exist.** For positive wealth the potential has a minimizer that is a
vertex. -/
theorem exists_vertex_min [Nonempty V] (hk : 0 < k) (val : V → ℝ) (l : ℕ) (hist : ℕ → ι → ℝ)
    (w : Expert ι V k D → ℝ) (hw : ∀ e, 0 < w e) :
    ∃ y : ι → ℝ, (∀ y', Phi val l hist w y ≤ Phi val l hist w y') ∧
      IsVertex (k := k) (D := D) val l hist y := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · obtain ⟨y, hy⟩ := exists_Phi_min hk val l hist w hw
    exact ⟨y, hy, fun d _ => Subsingleton.elim _ _⟩
  -- the ties at given prices
  obtain ⟨ties, hties⟩ : ∃ ties : (ι → ℝ) →
      Finset (Expert ι V k D × Option (Fin k) × Option (Fin k)), ∀ y t, t ∈ ties y ↔
        util (bidOf val l hist) (dirOf val l hist) t.1 t.2.1 y
          = util (bidOf val l hist) (dirOf val l hist) t.1 t.2.2 y :=
    ⟨fun y => univ.filter fun t => util (bidOf val l hist) (dirOf val l hist) t.1 t.2.1 y
      = util (bidOf val l hist) (dirOf val l hist) t.1 t.2.2 y, fun y t => by simp⟩
  -- a minimizer with the largest number of ties
  set S : Set ℕ := (fun y => (ties y).card) ''
    {y | ∀ y', Phi val l hist w y ≤ Phi val l hist w y'}
  have hSne : S.Nonempty := by
    obtain ⟨y, hy⟩ := exists_Phi_min hk val l hist w hw
    exact ⟨_, y, hy, rfl⟩
  have hSbdd : BddAbove S :=
    ⟨Fintype.card (Expert ι V k D × Option (Fin k) × Option (Fin k)), by
      rintro _ ⟨y, -, rfl⟩
      exact Finset.card_le_univ _⟩
  obtain ⟨y, hy, hcard⟩ := Nat.sSup_mem hSne hSbdd
  have hmax : ∀ y', (∀ y'', Phi val l hist w y' ≤ Phi val l hist w y'') →
      (ties y').card ≤ (ties y).card := by
    intro y' hy'
    exact (le_csSup hSbdd ⟨y', hy', rfl⟩).trans hcard.ge
  refine ⟨y, hy, fun d hd => ?_⟩
  by_contra hd0
  rcases vtx_ray (bidOf val l hist) (dirOf val l hist) w (fun e => (hw e).le) y d hy hd with
    h | ⟨s, hs, e, o, o', hne, heq⟩
  · -- the potential is bounded along a ray, against coercivity
    obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := Function.ne_iff.1 hd0
    have h1 : Tendsto (fun s : ℝ => fun j => y j + s * d j) atTop (cocompact (ι → ℝ)) := by
      rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
      have h2 : Tendsto (fun s : ℝ => s * |d i| + -|y i|) atTop atTop :=
        tendsto_atTop_add_const_right _ _ (tendsto_id.atTop_mul_const (abs_pos.2 hi))
      refine tendsto_atTop_mono' atTop ?_ h2
      filter_upwards [eventually_ge_atTop 0] with s hs
      have h3 : |s * d i| = s * |d i| := by rw [abs_mul, abs_of_nonneg hs]
      have h4 : |s * d i| ≤ |y i + s * d i| + |y i| := by
        have := abs_sub (y i + s * d i) (y i)
        simpa using this
      have h5 : ‖y i + s * d i‖ ≤ ‖fun j => y j + s * d j‖ :=
        norm_le_pi_norm (fun j => y j + s * d j) i
      rw [Real.norm_eq_abs] at h5
      linarith
    have h3 := (Phi_coercive hk val l hist w hw).comp h1
    obtain ⟨s, hs1, hs2⟩ := ((h3.eventually (eventually_gt_atTop (Phi val l hist w y))).and
      (eventually_ge_atTop 0)).exists
    exact absurd (h s hs2) (not_le.2 hs1)
  · -- a minimizer with more ties
    have hmin' : ∀ y'', Phi val l hist w (fun i => y i + s * d i) ≤ Phi val l hist w y'' :=
      fun y'' => hs.trans (hy y'')
    have hle := hmax _ hmin'
    have hlt : (ties y).card < (ties (fun i => y i + s * d i)).card := by
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · exact ⟨(e, o, o'), (hties _ _).2 heq, fun hmem => hne ((hties _ _).1 hmem)⟩
      · intro t ht
        rw [hties] at ht ⊢
        rw [vtx_util_shift, vtx_util_shift, ht, hd _ _ _ ht]
    omega

end SPLP
