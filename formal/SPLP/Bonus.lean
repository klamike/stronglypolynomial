import Mathlib

/-!
# The bonus inequality

One expert's wealth through the probes of a node. In each probe a share `c` of the current
wealth is invested in a child, which returns `w' τ`, while the remaining share is multiplied by
`1 + η * g τ`. The logarithmic bonus `log (1 + κ * (returned / input))` of the node dominates
the sum of the log market gains and the children's bonuses, up to an entry fee `log κ` and a
per-probe investment loss `log (1 - c)` (inequality (5.8) of the preprint, with `κ` in place of
`c / 2`).
-/

namespace SPLP

open Finset

/-- Along the same recursion all wealths stay positive. -/
theorem wealth_pos (T : ℕ) (c η : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (hη0 : 0 < η) (hη1 : η < 1)
    (w : ℕ → ℝ) (g w' : Fin T → ℝ)
    (hw0 : 0 < w 0) (hg : ∀ τ, -1 ≤ g τ ∧ g τ ≤ 1) (hw' : ∀ τ, 0 < w' τ)
    (hstep : ∀ τ : Fin T, w (τ + 1) = (1 - c) * w τ * (1 + η * g τ) + w' τ) :
    ∀ τ ≤ T, 0 < w τ := by
  -- `0 < c` is not needed for positivity (the hypotheses are those of `bonus_bound`);
  -- this line only references it, to keep the unused-variable linter quiet.
  have _ := hc0
  intro τ
  induction τ with
  | zero =>
    intro _
    exact hw0
  | succ n ih =>
    intro hn
    have hn' : n < T := hn
    have ihn : 0 < w n := ih hn'.le
    have hs : w (n + 1) = (1 - c) * w n * (1 + η * g ⟨n, hn'⟩) + w' ⟨n, hn'⟩ :=
      hstep ⟨n, hn'⟩
    have h1 : 0 < 1 - c := by linarith
    have h2 : 0 < 1 + η * g ⟨n, hn'⟩ := by
      have h : 0 ≤ η * (g ⟨n, hn'⟩ + 1) := mul_nonneg hη0.le (by linarith [(hg ⟨n, hn'⟩).1])
      linarith
    rw [hs]
    exact add_pos (mul_pos (mul_pos h1 ihn) h2) (hw' ⟨n, hn'⟩)

/-- One probe: the log wealth grows at least by the investment loss `log (1 - c)`, the log market
gain and the child's bonus. Here `x` is the wealth before the probe, `y` the wealth returned by
the child and `γ` the market gain. -/
private lemma step_log (c η κ : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (hη0 : 0 < η) (hη1 : η < 1)
    (hκ : 0 < κ) (hκc : κ * (1 - c) * (1 + η) ≤ c) (x y γ : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hγ : -1 ≤ γ ∧ γ ≤ 1) :
    Real.log (1 - c) + (Real.log (1 + η * γ) + Real.log (1 + κ * (y / (c * x)))) + Real.log x
      ≤ Real.log ((1 - c) * x * (1 + η * γ) + y) := by
  have h1 : 0 < 1 - c := by linarith
  have h2 : 0 < 1 + η * γ := by
    have h : 0 ≤ η * (γ + 1) := mul_nonneg hη0.le (by linarith [hγ.1])
    linarith
  have hμ : 0 < y / (c * x) := div_pos hy (mul_pos hc0 hx)
  have h3 : 0 < 1 + κ * (y / (c * x)) := by
    have h := mul_pos hκ hμ
    linarith
  -- the product form of the left-hand side
  have hprod : Real.log (1 - c) + (Real.log (1 + η * γ) + Real.log (1 + κ * (y / (c * x))))
        + Real.log x
      = Real.log ((1 - c) * ((1 + η * γ) * (1 + κ * (y / (c * x)))) * x) := by
    rw [Real.log_mul (mul_pos h1 (mul_pos h2 h3)).ne' hx.ne',
      Real.log_mul h1.ne' (mul_pos h2 h3).ne', Real.log_mul h2.ne' h3.ne']
  rw [hprod]
  apply Real.log_le_log (mul_pos (mul_pos h1 (mul_pos h2 h3)) hx)
  -- `y = μ * (c * x)` with `μ = y / (c * x)`
  have hy' : y / (c * x) * (c * x) = y := div_mul_cancel₀ y (mul_pos hc0 hx).ne'
  -- `κ * (1 - c) * (1 + η * γ) ≤ κ * (1 - c) * (1 + η) ≤ c`
  have hle : 1 + η * γ ≤ 1 + η := by
    have h : 0 ≤ η * (1 - γ) := mul_nonneg hη0.le (by linarith [hγ.2])
    linarith
  have hAκ : κ * (1 - c) * (1 + η * γ) ≤ c :=
    le_trans (mul_le_mul_of_nonneg_left hle (mul_pos hκ h1).le) hκc
  have hmain : κ * (1 - c) * (1 + η * γ) * (y / (c * x) * x) ≤ c * (y / (c * x) * x) :=
    mul_le_mul_of_nonneg_right hAκ (mul_pos hμ hx).le
  linarith

/-- Telescoping the one-probe inequality over all `T` probes. -/
private lemma telescope (c η κ : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (hη0 : 0 < η) (hη1 : η < 1)
    (hκ : 0 < κ) (hκc : κ * (1 - c) * (1 + η) ≤ c) (w : ℕ → ℝ) (hw0 : 0 < w 0) :
    ∀ (T : ℕ) (g w' : Fin T → ℝ), (∀ τ, -1 ≤ g τ ∧ g τ ≤ 1) → (∀ τ, 0 < w' τ) →
      (∀ τ : Fin T, w (τ + 1) = (1 - c) * w τ * (1 + η * g τ) + w' τ) →
      (T : ℝ) * Real.log (1 - c)
          + ∑ τ : Fin T, (Real.log (1 + η * g τ) + Real.log (1 + κ * (w' τ / (c * w τ))))
          + Real.log (w 0) ≤ Real.log (w T) := by
  intro T
  induction T with
  | zero =>
    intro g w' _ _ _
    simp
  | succ n ih =>
    intro g w' hg hw' hstep
    have hwn : 0 < w n :=
      wealth_pos (n + 1) c η hc0 hc1 hη0 hη1 w g w' hw0 hg hw' hstep n (Nat.le_succ n)
    have ih' : (n : ℝ) * Real.log (1 - c)
          + ∑ τ : Fin n, (Real.log (1 + η * g τ.castSucc)
              + Real.log (1 + κ * (w' τ.castSucc / (c * w τ))))
          + Real.log (w 0) ≤ Real.log (w n) :=
      ih (fun τ => g τ.castSucc) (fun τ => w' τ.castSucc)
        (fun τ => hg τ.castSucc) (fun τ => hw' τ.castSucc) (fun τ => hstep τ.castSucc)
    have hlast : w (n + 1) = (1 - c) * w n * (1 + η * g (Fin.last n)) + w' (Fin.last n) :=
      hstep (Fin.last n)
    have hs := step_log c η κ hc0 hc1 hη0 hη1 hκ hκc (w n) (w' (Fin.last n)) (g (Fin.last n))
      hwn (hw' _) (hg _)
    rw [← hlast] at hs
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    push_cast
    linarith

theorem bonus_bound (T : ℕ) (c η κ : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (hη0 : 0 < η) (hη1 : η < 1)
    (hκ : 0 < κ) (hκc : κ * (1 - c) * (1 + η) ≤ c)
    (w : ℕ → ℝ) (g w' : Fin T → ℝ)
    (hw0 : 0 < w 0) (hg : ∀ τ, -1 ≤ g τ ∧ g τ ≤ 1) (hw' : ∀ τ, 0 < w' τ)
    (hstep : ∀ τ : Fin T, w (τ + 1) = (1 - c) * w τ * (1 + η * g τ) + w' τ) :
    Real.log κ + T * Real.log (1 - c)
        + ∑ τ : Fin T, (Real.log (1 + η * g τ) + Real.log (1 + κ * (w' τ / (c * w τ))))
      ≤ Real.log (1 + κ * (w T / w 0)) := by
  have hT : 0 < w T := wealth_pos T c η hc0 hc1 hη0 hη1 w g w' hw0 hg hw' hstep T le_rfl
  have key := telescope c η κ hc0 hc1 hη0 hη1 hκ hκc w hw0 T g w' hg hw' hstep
  have hratio : 0 < κ * (w T / w 0) := mul_pos hκ (div_pos hT hw0)
  have hlog : Real.log (κ * (w T / w 0))
      = Real.log κ + (Real.log (w T) - Real.log (w 0)) := by
    rw [Real.log_mul hκ.ne' (div_pos hT hw0).ne', Real.log_div hT.ne' hw0.ne']
  have hle : Real.log (κ * (w T / w 0)) ≤ Real.log (1 + κ * (w T / w 0)) :=
    Real.log_le_log hratio (by linarith)
  linarith

/-! ### With rounding

The same statements when every updated wealth is rounded down by a factor at most `1 - ep`:
the only change is an extra loss `log (1 - ep)` per probe. -/

theorem wealth_pos_rnd (T : ℕ) (c η ep : ℝ) (hc1 : c < 1) (hη0 : 0 < η) (hη1 : η < 1)
    (hep1 : ep < 1) (w : ℕ → ℝ) (g w' : Fin T → ℝ)
    (hw0 : 0 < w 0) (hg : ∀ τ, -1 ≤ g τ ∧ g τ ≤ 1) (hw' : ∀ τ, 0 < w' τ)
    (hstep : ∀ τ : Fin T, (1 - ep) * ((1 - c) * w τ * (1 + η * g τ) + w' τ) ≤ w (τ + 1)) :
    ∀ τ ≤ T, 0 < w τ := by
  intro τ
  induction τ with
  | zero =>
    intro _
    exact hw0
  | succ n ih =>
    intro hn
    have hn' : n < T := hn
    have ihn : 0 < w n := ih hn'.le
    have hs := hstep ⟨n, hn'⟩
    simp only at hs
    have h1 : 0 < 1 - c := by linarith
    have h2 : 0 < 1 + η * g ⟨n, hn'⟩ := by
      have h : 0 ≤ η * (g ⟨n, hn'⟩ + 1) := mul_nonneg hη0.le (by linarith [(hg ⟨n, hn'⟩).1])
      linarith
    have h3 : 0 < (1 - c) * w n * (1 + η * g ⟨n, hn'⟩) + w' ⟨n, hn'⟩ :=
      add_pos (mul_pos (mul_pos h1 ihn) h2) (hw' _)
    exact lt_of_lt_of_le (mul_pos (by linarith) h3) hs

private lemma telescope_rnd (c η κ ep : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (hη0 : 0 < η)
    (hη1 : η < 1) (hκ : 0 < κ) (hκc : κ * (1 - c) * (1 + η) ≤ c) (hep1 : ep < 1)
    (w : ℕ → ℝ) (hw0 : 0 < w 0) :
    ∀ (T : ℕ) (g w' : Fin T → ℝ), (∀ τ, -1 ≤ g τ ∧ g τ ≤ 1) → (∀ τ, 0 < w' τ) →
      (∀ τ : Fin T, (1 - ep) * ((1 - c) * w τ * (1 + η * g τ) + w' τ) ≤ w (τ + 1)) →
      (T : ℝ) * (Real.log (1 - c) + Real.log (1 - ep))
          + ∑ τ : Fin T, (Real.log (1 + η * g τ) + Real.log (1 + κ * (w' τ / (c * w τ))))
          + Real.log (w 0) ≤ Real.log (w T) := by
  intro T
  induction T with
  | zero =>
    intro g w' _ _ _
    simp
  | succ n ih =>
    intro g w' hg hw' hstep
    have hwn : 0 < w n :=
      wealth_pos_rnd (n + 1) c η ep hc1 hη0 hη1 hep1 w g w' hw0 hg hw' hstep n (Nat.le_succ n)
    have ih' : (n : ℝ) * (Real.log (1 - c) + Real.log (1 - ep))
          + ∑ τ : Fin n, (Real.log (1 + η * g τ.castSucc)
              + Real.log (1 + κ * (w' τ.castSucc / (c * w τ))))
          + Real.log (w 0) ≤ Real.log (w n) :=
      ih (fun τ => g τ.castSucc) (fun τ => w' τ.castSucc)
        (fun τ => hg τ.castSucc) (fun τ => hw' τ.castSucc) (fun τ => hstep τ.castSucc)
    have hlast : (1 - ep) * ((1 - c) * w n * (1 + η * g (Fin.last n)) + w' (Fin.last n))
        ≤ w (n + 1) := hstep (Fin.last n)
    have hs := step_log c η κ hc0 hc1 hη0 hη1 hκ hκc (w n) (w' (Fin.last n)) (g (Fin.last n))
      hwn (hw' _) (hg _)
    have h1 : 0 < 1 - c := by linarith
    have h2 : 0 < 1 + η * g (Fin.last n) := by
      have h : 0 ≤ η * (g (Fin.last n) + 1) := mul_nonneg hη0.le (by linarith [(hg (Fin.last n)).1])
      linarith
    have hX : 0 < (1 - c) * w n * (1 + η * g (Fin.last n)) + w' (Fin.last n) :=
      add_pos (mul_pos (mul_pos h1 hwn) h2) (hw' _)
    have hep : 0 < 1 - ep := by linarith
    have hround : Real.log (1 - ep)
        + Real.log ((1 - c) * w n * (1 + η * g (Fin.last n)) + w' (Fin.last n))
        ≤ Real.log (w (n + 1)) := by
      rw [← Real.log_mul hep.ne' hX.ne']
      exact Real.log_le_log (mul_pos hep hX) hlast
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    push_cast
    linarith

/-- The bonus inequality with rounding. -/
theorem bonus_bound_rnd (T : ℕ) (c η κ ep : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (hη0 : 0 < η)
    (hη1 : η < 1) (hκ : 0 < κ) (hκc : κ * (1 - c) * (1 + η) ≤ c) (hep1 : ep < 1)
    (w : ℕ → ℝ) (g w' : Fin T → ℝ)
    (hw0 : 0 < w 0) (hg : ∀ τ, -1 ≤ g τ ∧ g τ ≤ 1) (hw' : ∀ τ, 0 < w' τ)
    (hstep : ∀ τ : Fin T, (1 - ep) * ((1 - c) * w τ * (1 + η * g τ) + w' τ) ≤ w (τ + 1)) :
    Real.log κ + T * (Real.log (1 - c) + Real.log (1 - ep))
        + ∑ τ : Fin T, (Real.log (1 + η * g τ) + Real.log (1 + κ * (w' τ / (c * w τ))))
      ≤ Real.log (1 + κ * (w T / w 0)) := by
  have hT : 0 < w T :=
    wealth_pos_rnd T c η ep hc1 hη0 hη1 hep1 w g w' hw0 hg hw' hstep T le_rfl
  have key := telescope_rnd c η κ ep hc0 hc1 hη0 hη1 hκ hκc hep1 w hw0 T g w' hg hw' hstep
  have hratio : 0 < κ * (w T / w 0) := mul_pos hκ (div_pos hT hw0)
  have hlog : Real.log (κ * (w T / w 0))
      = Real.log κ + (Real.log (w T) - Real.log (w 0)) := by
    rw [Real.log_mul hκ.ne' (div_pos hT hw0).ne', Real.log_div hT.ne' hw0.ne']
  have hle : Real.log (κ * (w T / w 0)) ≤ Real.log (1 + κ * (w T / w 0)) :=
    Real.log_le_log hratio (by linarith)
  linarith

end SPLP
