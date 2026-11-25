import Mathlib
import SPLP.Main

/-!
# Valid runs exist

`Exec.Valid` is a specification; this file shows it is never vacuous. For any rule that
answers label queries (it may depend on the position of the probe in the recursion tree, hence
on everything that happened before), the algorithm has a run: the market potential attains its
minimum, weak medians exist, and wealth stays positive.
-/

set_option linter.unusedSectionVars false

namespace SPLP

open Finset Filter

variable {ι V : Type*} {k D : ℕ} [Fintype ι] [DecidableEq ι] [Fintype V]

/-- The market potential is continuous in the prices. -/
theorem continuous_Phi (val : V → ℝ) (l : ℕ) (hist : ℕ → ι → ℝ) (w : Expert ι V k D → ℝ) :
    Continuous (Phi val l hist w) := by
  unfold Phi potential
  refine continuous_finsetSum _ (fun e _ => ?_)
  refine continuous_const.mul ?_
  unfold best
  refine Continuous.finset_sup'_apply _ (fun o _ => ?_)
  unfold util
  refine continuous_const.sub ?_
  refine continuous_finsetSum _ (fun i _ => ?_)
  exact continuous_const.mul (continuous_apply i)

/-- The zero-threshold expert that bids `v₀` on the single slot `s`. -/
def anchor (s : Slot ι) (v₀ : V) : Expert ι V k D := (fun _ => s, fun _ => v₀, none)

theorem best_nonneg (val : V → ℝ) (l : ℕ) (hist : ℕ → ι → ℝ) (e : Expert ι V k D)
    (y : ι → ℝ) : 0 ≤ best (bidOf val l hist) (dirOf val l hist) e y := by
  have h := util_le_best (bidOf val l hist) (dirOf val l hist) e none y
  rwa [util_none] at h

theorem best_anchor_ge (val : V → ℝ) (l : ℕ) (hist : ℕ → ι → ℝ) (hk : 0 < k) (s : Slot ι)
    (v₀ : V) (y : ι → ℝ) :
    val v₀ - sp y s
      ≤ best (bidOf val l hist) (dirOf val l hist) (anchor s v₀ : Expert ι V k D) y := by
  have hthr : thr val l hist (anchor s v₀ : Expert ι V k D) = some 0 := rfl
  have h := util_le_best (bidOf val l hist) (dirOf val l hist) (anchor s v₀ : Expert ι V k D)
    (some ⟨0, hk⟩) y
  rw [util_some_of_thr hthr] at h
  simpa [anchor] using h

/-- **The potential is coercive**: it tends to infinity at infinity, because for each slot
some zero-threshold expert bids on that slot alone. -/
theorem Phi_coercive [Nonempty V] [Nonempty ι] (hk : 0 < k) (val : V → ℝ) (l : ℕ)
    (hist : ℕ → ι → ℝ) (w : Expert ι V k D → ℝ) (hw : ∀ e, 0 < w e) :
    Tendsto (Phi val l hist w) (cocompact (ι → ℝ)) atTop := by
  classical
  obtain ⟨v₀⟩ := ‹Nonempty V›
  -- least wealth among the anchors
  obtain ⟨s₀, -, hs₀⟩ := Finset.exists_min_image (univ : Finset (Slot ι))
    (fun s => w (anchor s v₀ : Expert ι V k D)) univ_nonempty
  set μ := w (anchor s₀ v₀ : Expert ι V k D) with hμ
  have hμpos : 0 < μ := hw _
  have hlow : ∀ (y : ι → ℝ) (s : Slot ι), μ * (val v₀ - sp y s) ≤ Phi val l hist w y := by
    intro y s
    have hterm : w (anchor s v₀ : Expert ι V k D)
        * best (bidOf val l hist) (dirOf val l hist) (anchor s v₀ : Expert ι V k D) y
        ≤ Phi val l hist w y := by
      unfold Phi potential
      exact Finset.single_le_sum
        (f := fun e => w e * best (bidOf val l hist) (dirOf val l hist) e y)
        (fun e _ => mul_nonneg (hw e).le (best_nonneg val l hist e y)) (Finset.mem_univ _)
    have hb := best_anchor_ge (D := D) val l hist hk s v₀ y
    have hb0 := best_nonneg val l hist (anchor s v₀ : Expert ι V k D) y
    have hμs : μ ≤ w (anchor s v₀ : Expert ι V k D) := hs₀ s (Finset.mem_univ s)
    by_cases hsign : 0 ≤ val v₀ - sp y s
    · calc μ * (val v₀ - sp y s)
          ≤ w (anchor s v₀ : Expert ι V k D) * (val v₀ - sp y s) :=
            mul_le_mul_of_nonneg_right hμs hsign
        _ ≤ w (anchor s v₀ : Expert ι V k D)
              * best (bidOf val l hist) (dirOf val l hist) (anchor s v₀ : Expert ι V k D) y :=
            mul_le_mul_of_nonneg_left hb (hw _).le
        _ ≤ _ := hterm
    · have h1 : μ * (val v₀ - sp y s) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hμpos.le (not_le.1 hsign).le
      have h2 : 0 ≤ Phi val l hist w y :=
        (mul_nonneg (hw _).le hb0).trans hterm
      linarith
  have hnorm : ∀ y : ι → ℝ, μ * (‖y‖ + val v₀) ≤ Phi val l hist w y := by
    intro y
    have habs : ∀ i, |y i| ≤ Phi val l hist w y / μ - val v₀ := by
      intro i
      have h1 := hlow y (i, true)
      have h2 := hlow y (i, false)
      simp only [sp, sgn, if_true, one_mul] at h1
      simp only [sp, sgn] at h2
      norm_num at h2
      have h1' : val v₀ - y i ≤ Phi val l hist w y / μ := by
        rw [le_div_iff₀ hμpos]; linarith
      have h2' : val v₀ + y i ≤ Phi val l hist w y / μ := by
        rw [le_div_iff₀ hμpos]; linarith
      rw [abs_le]
      constructor <;> linarith
    have hR : 0 ≤ Phi val l hist w y / μ - val v₀ :=
      (abs_nonneg _).trans (habs (Classical.arbitrary ι))
    have hn : ‖y‖ ≤ Phi val l hist w y / μ - val v₀ := by
      rw [pi_norm_le_iff_of_nonneg hR]
      intro i
      rw [Real.norm_eq_abs]
      exact habs i
    have : ‖y‖ + val v₀ ≤ Phi val l hist w y / μ := by linarith
    rw [le_div_iff₀ hμpos] at this
    linarith
  refine tendsto_atTop_mono hnorm ?_
  refine Tendsto.const_mul_atTop hμpos ?_
  exact tendsto_atTop_add_const_right _ _ tendsto_norm_cocompact_atTop

/-- **The market clears.** For positive wealth the potential attains its minimum. -/
theorem exists_Phi_min [Nonempty V] (hk : 0 < k) (val : V → ℝ) (l : ℕ) (hist : ℕ → ι → ℝ)
    (w : Expert ι V k D → ℝ) (hw : ∀ e, 0 < w e) :
    ∃ y : ι → ℝ, ∀ y', Phi val l hist w y ≤ Phi val l hist w y' := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨fun i => (hι.false i).elim, fun y' => ?_⟩
    have : y' = fun i => (hι.false i).elim := Subsingleton.elim _ _
    rw [this]
  · exact (continuous_Phi val l hist w).exists_forall_le (Phi_coercive hk val l hist w hw)

/-! ### Runs against an arbitrary labelling rule -/

/-- The labels recorded in a run are produced by the rule `oracle`: the probe reached from
this node by the path `pos` receives `oracle pos x` when it queries at `x`. Since the path
determines everything that happened before the query, this covers adaptive label oracles. -/
def Exec.LabelsFrom {E : Type*} (oracle : List ℕ → (ι → ℝ) → (ι → Bool)) :
    Exec ι E → List ℕ → Prop
  | .leaf _ _, _ => True
  | .node T _ z child _ _, pos =>
      ∀ τ : Fin T, z τ = oracle (pos ++ [(τ : ℕ)]) (child τ).x ∧
        (child τ).LabelsFrom oracle (pos ++ [(τ : ℕ)])

theorem exists_valid_aux [Nonempty V] (hk : 0 < k) (A : Alg V) (hc0 : 0 < A.c)
    (hc1 : A.c < 1) (hη0 : 0 < A.η) (hη1 : A.η < 1) {ep : ℝ} (hep1 : ep < 1)
    (hrnd : ∀ x : ℝ, 0 < x → (1 - ep) * x ≤ A.rnd x ∧ A.rnd x ≤ x)
    (oracle : List ℕ → (ι → ℝ) → (ι → Bool)) :
    ∀ (d l : ℕ), l + d = D → ∀ (hist : ℕ → ι → ℝ) (wIn : Expert ι V k D → ℝ) (pos : List ℕ),
      (∀ e, 0 < wIn e) →
      ∃ X : Exec ι (Expert ι V k D), X.Valid A l hist wIn ∧ X.LabelsFrom oracle pos := by
  intro d
  induction d with
  | zero =>
    intro l hl hist wIn pos _
    choose x hx using fun i => exists_isMedian (fun j : Fin l => hist j i)
    exact ⟨.leaf x wIn, ⟨by omega, rfl, hx⟩, trivial⟩
  | succ d ih =>
    intro l hl hist wIn pos hpos
    have hlD : l < D := by omega
    -- one probe, as a function of its index and of the wealth before it
    have hstep : ∀ (n : ℕ) (w : Expert ι V k D → ℝ),
        ∃ (y : ι → ℝ) (c : Exec ι (Expert ι V k D)), (∀ e, 0 < w e) →
          (∀ y', Phi A.val l hist (fun e => (1 - A.c) * w e) y
              ≤ Phi A.val l hist (fun e => (1 - A.c) * w e) y') ∧
          c.Valid A (l + 1) (Function.update hist l y) (fun e => A.c * w e) ∧
          c.LabelsFrom oracle (pos ++ [n]) := by
      intro n w
      by_cases hw : ∀ e, 0 < w e
      · obtain ⟨y, hy⟩ := exists_Phi_min hk A.val l hist (fun e => (1 - A.c) * w e)
          (fun e => mul_pos (by linarith) (hw e))
        obtain ⟨c, hcv, hcl⟩ := ih (l + 1) (by omega) (Function.update hist l y)
          (fun e => A.c * w e) (pos ++ [n]) (fun e => mul_pos hc0 (hw e))
        exact ⟨y, c, fun _ => ⟨hy, hcv, hcl⟩⟩
      · exact ⟨0, .leaf 0 0, fun h => absurd h hw⟩
    choose ystep cstep hspec using hstep
    -- the wealth before each probe
    let next : ℕ → (Expert ι V k D → ℝ) → (Expert ι V k D → ℝ) := fun n w e =>
      A.rnd ((1 - A.c) * w e * (1 + A.η * gain A.val l hist (ystep n w)
          (feedback (ystep n w) (cstep n w).x (oracle (pos ++ [n]) (cstep n w).x)) e)
        + (cstep n w).wOut e)
    let W : ℕ → Expert ι V k D → ℝ := fun n =>
      Nat.rec (motive := fun _ => Expert ι V k D → ℝ) wIn (fun n w => next n w) n
    have hWs : ∀ n, W (n + 1) = next n (W n) := fun n => rfl
    have hWpos : ∀ n, ∀ e, 0 < W n e := by
      intro n
      induction n with
      | zero => exact hpos
      | succ n ihn =>
        intro e
        rw [hWs n]
        obtain ⟨-, hcv, -⟩ := hspec n (W n) ihn
        have hcout := (Exec.wealth A hc0 hc1 hη0 hη1 hep1 hrnd (cstep n (W n)) _ _ _ hcv
          (fun e => mul_pos hc0 (ihn e))).1 e
        have hg := (gain_bounds A.val l hist e (ystep n (W n))
          (feedback (ystep n (W n)) (cstep n (W n)).x
            (oracle (pos ++ [n]) (cstep n (W n)).x))).1
        have h1 : 0 < 1 + A.η * gain A.val l hist (ystep n (W n))
            (feedback (ystep n (W n)) (cstep n (W n)).x
              (oracle (pos ++ [n]) (cstep n (W n)).x)) e := by nlinarith
        have hX := add_pos (mul_pos (mul_pos (by linarith : 0 < 1 - A.c) (ihn e)) h1) hcout
        exact lt_of_lt_of_le (mul_pos (by linarith) hX) (hrnd _ hX).1
    choose x hx using fun i => exists_isMedian
      (fun τ : Fin (if l = 0 then A.r₀ else A.r) => (cstep τ (W τ)).x i)
    refine ⟨.node (if l = 0 then A.r₀ else A.r) (fun τ => ystep τ (W τ))
      (fun τ => oracle (pos ++ [(τ : ℕ)]) (cstep τ (W τ)).x) (fun τ => cstep τ (W τ)) W x,
      ?_, ?_⟩
    · refine ⟨hlD, rfl, rfl, fun τ => ?_, hx⟩
      obtain ⟨hmin, hcv, -⟩ := hspec τ (W τ) (hWpos τ)
      exact ⟨hmin, hcv, fun e => by rw [hWs τ]⟩
    · intro τ
      exact ⟨rfl, (hspec τ (W τ) (hWpos τ)).2.2⟩

/-- **Valid runs exist** against every labelling rule, from the root with unit wealth. -/
theorem exists_valid [Nonempty V] (hk : 0 < k) (A : Alg V) (hc0 : 0 < A.c) (hc1 : A.c < 1)
    (hη0 : 0 < A.η) (hη1 : A.η < 1) {ep : ℝ} (hep1 : ep < 1)
    (hrnd : ∀ x : ℝ, 0 < x → (1 - ep) * x ≤ A.rnd x ∧ A.rnd x ≤ x)
    (oracle : List ℕ → (ι → ℝ) → (ι → Bool)) (hist₀ : ℕ → ι → ℝ) :
    ∃ X : Exec ι (Expert ι V k D),
      X.Valid A 0 hist₀ (fun _ => 1) ∧ X.LabelsFrom oracle [] :=
  exists_valid_aux hk A hc0 hc1 hη0 hη1 hep1 hrnd oracle D 0 (by omega) hist₀ _ []
    (fun _ => one_pos)

end SPLP
