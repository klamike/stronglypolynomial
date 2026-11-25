import Mathlib
import SPLP.GainMarket

/-!
# What the proof needs from a child's returned wealth

In the search a node invests the share `c` of every expert's wealth in a child and adds the
child's output back: `w' = (1 - c) w (1 + η g) + out`. Because of this, an expert's wealth
depends on every probe below the node, which is where the cost of the market step comes from.
This file determines how much of the individual returns the correctness proof uses.

* Scalar returns do not work (`scalar_return_cannot_pay`): if the child returns the same
  multiple `G` of every expert's input, a failed child can never pay for its probe, because
  its weighted bonus is at most `Pm · κ G`, far below the `C (ε + λ)` the charging step needs.
* Thresholded returns do work. Call `R = out / (c w)` the child's return ratio. The proof goes
  through for every update between `(1 - ep) (1 - c) w (1 + η g) · max 1 (κ R)` and
  `(1 - c) w (1 + η g) + out` (`Exec.ValidThr`, `price_search_correct_thr`). So an expert's
  individual return may be dropped unless it multiplied its wealth by at least `1/κ` inside
  the child, and the experts for which it may not be dropped carry at most the fraction
  `κ · (child's growth)` of the child's input wealth (`boosted_mass_le`).
-/

namespace SPLP

open Finset

/-! ### One expert -/

/-- The thresholded product update never exceeds the additive one. -/
theorem thr_factor_le {c η κ g M : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hη0 : 0 < η) (hη1 : η < 1)
    (hκ0 : 0 < κ) (hκc : κ * (1 - c) * (1 + η) ≤ c) (hg : -1 ≤ g ∧ g ≤ 1) (hM : 0 ≤ M) :
    (1 - c) * (1 + η * g) * max 1 (κ * M) ≤ (1 - c) * (1 + η * g) + c * M := by
  have h1 : 0 < 1 - c := by linarith
  have h2 : 0 < 1 + η * g := by nlinarith [hg.1]
  have h3 : 1 + η * g ≤ 1 + η := by nlinarith [hg.2]
  rcases le_total (κ * M) 1 with h | h
  · rw [max_eq_left h]
    nlinarith [mul_nonneg hc0.le hM]
  · rw [max_eq_right h]
    have h4 : (1 - c) * (1 + η * g) * (κ * M) ≤ (1 - c) * (1 + η) * (κ * M) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 h1.le) (mul_nonneg hκ0.le hM)
    have h5 : (1 - c) * (1 + η) * (κ * M) = (κ * (1 - c) * (1 + η)) * M := by ring
    have h6 : (κ * (1 - c) * (1 + η)) * M ≤ c * M := mul_le_mul_of_nonneg_right hκc hM
    have h7 : 0 ≤ (1 - c) * (1 + η * g) := (mul_pos h1 h2).le
    linarith

/-- The thresholded bonus: `log max(1, κ · returned / input)`. -/
noncomputable def bonusT {E : Type*} (κ : ℝ) (wIn wOut : E → ℝ) (e : E) : ℝ :=
  Real.log (max 1 (κ * (wOut e / wIn e)))

theorem bonusT_nonneg {E : Type*} (κ : ℝ) (wIn wOut : E → ℝ) (e : E) :
    0 ≤ bonusT κ wIn wOut e :=
  Real.log_nonneg (le_max_left _ _)

theorem bonusT_le_bonus {E : Type*} {κ : ℝ} (hκ : 0 ≤ κ) {wIn wOut : E → ℝ}
    (h1 : ∀ e, 0 < wIn e) (h2 : ∀ e, 0 < wOut e) (e : E) :
    bonusT κ wIn wOut e ≤ bonus κ wIn wOut e := by
  unfold bonusT bonus
  have hx : 0 ≤ κ * (wOut e / wIn e) := mul_nonneg hκ (div_pos (h2 e) (h1 e)).le
  exact Real.log_le_log (lt_of_lt_of_le one_pos (le_max_left _ _))
    (max_le (by linarith) (by linarith))

theorem wealth_pos_thr (T : ℕ) (c η κ ep : ℝ) (hc1 : c < 1) (hη0 : 0 < η) (hη1 : η < 1)
    (hep1 : ep < 1) (w : ℕ → ℝ) (g w' : Fin T → ℝ)
    (hw0 : 0 < w 0) (hg : ∀ τ, -1 ≤ g τ ∧ g τ ≤ 1)
    (hstep : ∀ τ : Fin T, (1 - ep) * ((1 - c) * w τ * (1 + η * g τ)
        * max 1 (κ * (w' τ / (c * w τ)))) ≤ w (τ + 1)) :
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
    have h2 : 0 < 1 + η * g ⟨n, hn'⟩ := by nlinarith [(hg ⟨n, hn'⟩).1]
    have h3 : 0 < max 1 (κ * (w' ⟨n, hn'⟩ / (c * w n))) :=
      lt_of_lt_of_le one_pos (le_max_left _ _)
    exact lt_of_lt_of_le
      (mul_pos (by linarith) (mul_pos (mul_pos (mul_pos h1 ihn) h2) h3)) hs

private lemma telescope_thr (c η κ ep : ℝ) (hc1 : c < 1) (hη0 : 0 < η)
    (hη1 : η < 1) (hep1 : ep < 1) (w : ℕ → ℝ) (hw0 : 0 < w 0) :
    ∀ (T : ℕ) (g w' : Fin T → ℝ), (∀ τ, -1 ≤ g τ ∧ g τ ≤ 1) →
      (∀ τ : Fin T, (1 - ep) * ((1 - c) * w τ * (1 + η * g τ)
          * max 1 (κ * (w' τ / (c * w τ)))) ≤ w (τ + 1)) →
      (T : ℝ) * (Real.log (1 - c) + Real.log (1 - ep))
          + ∑ τ : Fin T, (Real.log (1 + η * g τ)
              + Real.log (max 1 (κ * (w' τ / (c * w τ)))))
          + Real.log (w 0) ≤ Real.log (w T) := by
  intro T
  induction T with
  | zero =>
    intro g w' _ _
    simp
  | succ n ih =>
    intro g w' hg hstep
    have hwn : 0 < w n :=
      wealth_pos_thr (n + 1) c η κ ep hc1 hη0 hη1 hep1 w g w' hw0 hg hstep n (Nat.le_succ n)
    have ih' := ih (fun τ => g τ.castSucc) (fun τ => w' τ.castSucc)
      (fun τ => hg τ.castSucc) (fun τ => hstep τ.castSucc)
    have hlast : (1 - ep) * ((1 - c) * w n * (1 + η * g (Fin.last n))
        * max 1 (κ * (w' (Fin.last n) / (c * w n)))) ≤ w (n + 1) := hstep (Fin.last n)
    have h1 : 0 < 1 - c := by linarith
    have h2 : 0 < 1 + η * g (Fin.last n) := by nlinarith [(hg (Fin.last n)).1]
    have h3 : 0 < max 1 (κ * (w' (Fin.last n) / (c * w n))) :=
      lt_of_lt_of_le one_pos (le_max_left _ _)
    have hep : 0 < 1 - ep := by linarith
    have hX : 0 < (1 - ep) * ((1 - c) * w n * (1 + η * g (Fin.last n))
        * max 1 (κ * (w' (Fin.last n) / (c * w n)))) :=
      mul_pos hep (mul_pos (mul_pos (mul_pos h1 hwn) h2) h3)
    have hlog : Real.log ((1 - ep) * ((1 - c) * w n * (1 + η * g (Fin.last n))
        * max 1 (κ * (w' (Fin.last n) / (c * w n)))))
        = Real.log (1 - ep) + (Real.log (1 - c) + Real.log (w n)
          + Real.log (1 + η * g (Fin.last n))
          + Real.log (max 1 (κ * (w' (Fin.last n) / (c * w n))))) := by
      rw [Real.log_mul hep.ne' (mul_pos (mul_pos (mul_pos h1 hwn) h2) h3).ne',
        Real.log_mul (mul_pos (mul_pos h1 hwn) h2).ne' h3.ne',
        Real.log_mul (mul_pos h1 hwn).ne' h2.ne', Real.log_mul h1.ne' hwn.ne']
    have hround := Real.log_le_log hX hlast
    rw [hlog] at hround
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last] at ih' ⊢
    push_cast
    linarith

/-- The bonus inequality for the thresholded update. -/
theorem bonusT_bound (T : ℕ) (c η κ ep : ℝ) (hc1 : c < 1) (hη0 : 0 < η)
    (hη1 : η < 1) (hκ : 0 < κ) (hep1 : ep < 1)
    (w : ℕ → ℝ) (g w' : Fin T → ℝ)
    (hw0 : 0 < w 0) (hg : ∀ τ, -1 ≤ g τ ∧ g τ ≤ 1)
    (hstep : ∀ τ : Fin T, (1 - ep) * ((1 - c) * w τ * (1 + η * g τ)
        * max 1 (κ * (w' τ / (c * w τ)))) ≤ w (τ + 1)) :
    Real.log κ + T * (Real.log (1 - c) + Real.log (1 - ep))
        + ∑ τ : Fin T, (Real.log (1 + η * g τ) + Real.log (max 1 (κ * (w' τ / (c * w τ)))))
      ≤ Real.log (max 1 (κ * (w T / w 0))) := by
  have hT : 0 < w T :=
    wealth_pos_thr T c η κ ep hc1 hη0 hη1 hep1 w g w' hw0 hg hstep T le_rfl
  have key := telescope_thr c η κ ep hc1 hη0 hη1 hep1 w hw0 T g w' hg hstep
  have hratio : 0 < κ * (w T / w 0) := mul_pos hκ (div_pos hT hw0)
  have hlog : Real.log (κ * (w T / w 0))
      = Real.log κ + (Real.log (w T) - Real.log (w 0)) := by
    rw [Real.log_mul hκ.ne' (div_pos hT hw0).ne', Real.log_div hT.ne' hw0.ne']
  have hle : Real.log (κ * (w T / w 0)) ≤ Real.log (max 1 (κ * (w T / w 0))) :=
    Real.log_le_log hratio (le_max_right _ _)
  linarith

open Classical in
/-- **Few experts need an individual return.** The experts whose return ratio exceeds `1/κ`
hold at most `κ` times the child's total output, measured in input wealth. -/
theorem boosted_mass_le {E : Type*} [Fintype E] {κ : ℝ} (hκ : 0 ≤ κ) (wc cOut : E → ℝ)
    (hwc : ∀ e, 0 < wc e) (hco : ∀ e, 0 ≤ cOut e) :
    ∑ e ∈ univ.filter (fun e => 1 < κ * (cOut e / wc e)), wc e ≤ κ * ∑ e, cOut e := by
  calc ∑ e ∈ univ.filter (fun e => 1 < κ * (cOut e / wc e)), wc e
      ≤ ∑ e ∈ univ.filter (fun e => 1 < κ * (cOut e / wc e)), κ * cOut e := by
        refine Finset.sum_le_sum (fun e he => ?_)
        have h := (Finset.mem_filter.1 he).2
        have h' : 1 < κ * cOut e / wc e := by rwa [mul_div_assoc]
        rw [lt_div_iff₀ (hwc e)] at h'
        linarith
    _ ≤ ∑ e, κ * cOut e :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun e _ _ => mul_nonneg hκ (hco e))
    _ = κ * ∑ e, cOut e := by rw [Finset.mul_sum]

/-! ### Scalar returns cannot pay -/

theorem bonus_scalar {E : Type*} (κ G : ℝ) (wc cOut : E → ℝ) (hwc : ∀ e, 0 < wc e)
    (h : ∀ e, cOut e = G * wc e) (e : E) : bonus κ wc cOut e = Real.log (1 + κ * G) := by
  unfold bonus
  rw [h e, mul_div_assoc, div_self (hwc e).ne', mul_one]

variable {ι V : Type*} {k D : ℕ} [Fintype ι] [DecidableEq ι] [Fintype V]

/-- **Scalar returns cannot pay for a failed child.** If a child returns the same multiple `G`
of every expert's input wealth, its weighted bonus is at most `Pm · κ G`. The charging step of
the proof (`probe_step`) needs a failed child's weighted bonus to be at least `σ r`, which is
at least `C (ε + λ)`. For the arity-4 constants `Pm κ ≈ 5.6 · 10^-5` and `C (ε + λ) ≈ 97`, so
this would need a growth factor `G` above `10^6`, while the market keeps `G` near one. -/
theorem scalar_return_cannot_pay (P : Params ι V k D) (H : Hyp ι V) (l : ℕ)
    (m : Slot ι → ℝ) (hm : ∑ s, m s = 1) (d₀ : Option (Fin D × Slot ι)) {G : ℝ} (hG0 : 0 ≤ G)
    (wc cOut : Expert ι V k D → ℝ) (hwc : ∀ e, 0 < wc e) (h : ∀ e, cOut e = G * wc e)
    (hsmall : P.Pm * (P.κ * G) < P.C * (P.ε + P.lam)) :
    Psi H P.ω l m d₀ (bonus P.κ wc cOut) < P.σ * P.A.r := by
  have hfun : bonus P.κ wc cOut = fun _ => Real.log (1 + P.κ * G) :=
    funext (bonus_scalar P.κ G wc cOut hwc h)
  rw [hfun, Psi_const H m P.ω l d₀ hm]
  have hκG : 0 ≤ P.κ * G := mul_nonneg P.hκ0.le hG0
  have hlog : Real.log (1 + P.κ * G) ≤ P.κ * G := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + P.κ * G by linarith)
    linarith
  have hlog0 : 0 ≤ Real.log (1 + P.κ * G) := Real.log_nonneg (by linarith)
  have hres := P.reserve_bound (k := k) l
  have hres0 := reserve_nonneg (D := D) P.ω l P.hω
  have hR1 := P.hR1
  have h1 : Real.log (1 + P.κ * G) * (1 + reserve D P.ω l) ≤ P.κ * G * P.Pm :=
    mul_le_mul hlog hres (by linarith) hκG
  linarith

/-! ### Runs with thresholded returns -/

/-- A run in which every updated wealth lies between the thresholded product update (up to a
rounding factor `1 - ep`) and the additive update of `Exec.ValidWith`. The child's output
`(child τ).wOut e` enters the lower bound only through `max 1 (κ · ratio)`. -/
def Exec.ValidThr (M : MarketCond ι V k D) (A : Alg V) (κ ep : ℝ) :
    Exec ι (Expert ι V k D) → ℕ → (ℕ → ι → ℝ) → (Expert ι V k D → ℝ) → Prop
  | .leaf x wOut, l, hist, wIn =>
      l = D ∧ wOut = wIn ∧ ∀ i, IsMedian (fun j : Fin l => hist j i) (x i)
  | .node T y z child w x, l, hist, wIn =>
      l < D ∧ T = (if l = 0 then A.r₀ else A.r) ∧ w 0 = wIn ∧
      (∀ τ : Fin T,
        M l hist (fun e => (1 - A.c) * w τ e) (y τ) ∧
        (child τ).ValidThr M A κ ep (l + 1) (Function.update hist l (y τ))
          (fun e => A.c * w τ e) ∧
        (∀ e, (1 - ep) * ((1 - A.c) * w τ e
              * (1 + A.η * gain A.val l hist (y τ) (feedback (y τ) (child τ).x (z τ)) e)
              * max 1 (κ * ((child τ).wOut e / (A.c * w τ e)))) ≤ w (τ + 1) e ∧
            w (τ + 1) e ≤ (1 - A.c) * w τ e
              * (1 + A.η * gain A.val l hist (y τ) (feedback (y τ) (child τ).x (z τ)) e)
              + (child τ).wOut e)) ∧
      (∀ i, IsMedian (fun τ : Fin T => (child τ).x i) (x i))

omit [Fintype V] in
theorem thr_node_pos (M : MarketCond ι V k D) (A : Alg V) {κ ep : ℝ} (hc1 : A.c < 1)
    (hη0 : 0 < A.η) (hη1 : A.η < 1) (hep1 : ep < 1) {T : ℕ}
    {y : Fin T → ι → ℝ} {z : Fin T → ι → Bool}
    {child : Fin T → Exec ι (Expert ι V k D)} {w : ℕ → Expert ι V k D → ℝ} {x : ι → ℝ}
    {l : ℕ} {hist : ℕ → ι → ℝ} {wIn : Expert ι V k D → ℝ}
    (hv : (Exec.node T y z child w x).ValidThr M A κ ep l hist wIn)
    (hpos : ∀ e, 0 < wIn e) : ∀ n, n ≤ T → ∀ e, 0 < w n e := by
  obtain ⟨-, -, hw0, hprobe, -⟩ := hv
  intro n
  induction n with
  | zero =>
    intro _ e
    rw [hw0]
    exact hpos e
  | succ n ih =>
    intro hn e
    have hn' : n < T := hn
    have hposn := ih (Nat.le_of_lt hn') e
    have hs := ((hprobe ⟨n, hn'⟩).2.2 e).1
    have hg := (gain_bounds A.val l hist e (y ⟨n, hn'⟩)
      (feedback (y ⟨n, hn'⟩) (child ⟨n, hn'⟩).x (z ⟨n, hn'⟩))).1
    have h1 : 0 < 1 + A.η * gain A.val l hist (y ⟨n, hn'⟩)
        (feedback (y ⟨n, hn'⟩) (child ⟨n, hn'⟩).x (z ⟨n, hn'⟩)) e := by
      nlinarith
    have h3 : 0 < max 1 (κ * ((child ⟨n, hn'⟩).wOut e / (A.c * w n e))) :=
      lt_of_lt_of_le one_pos (le_max_left _ _)
    exact lt_of_lt_of_le (mul_pos (by linarith)
      (mul_pos (mul_pos (mul_pos (by linarith) hposn) h1) h3)) hs

omit [Fintype V] in
/-- Every node of a run with thresholded returns outputs positive wealth. -/
theorem Exec.thr_pos (M : MarketCond ι V k D) (A : Alg V) {κ ep : ℝ} (hc1 : A.c < 1)
    (hη0 : 0 < A.η) (hη1 : A.η < 1) (hep1 : ep < 1) (X : Exec ι (Expert ι V k D))
    (l : ℕ) (hist : ℕ → ι → ℝ) (wIn : Expert ι V k D → ℝ)
    (hv : X.ValidThr M A κ ep l hist wIn) (hpos : ∀ e, 0 < wIn e) : ∀ e, 0 < X.wOut e := by
  cases X with
  | leaf x wOut =>
    obtain ⟨-, hw, -⟩ := hv
    simp only [Exec.wOut, hw]
    exact hpos
  | node T y z child w x =>
    exact thr_node_pos M A hc1 hη0 hη1 hep1 hv hpos T le_rfl

/-! ### Total wealth -/

theorem thr_node_wealth_aux (A : Alg V) {ζ : ℝ} (hζ : 0 ≤ ζ) (hc0 : 0 < A.c)
    (hc1 : A.c < 1) (hη0 : 0 < A.η) (hη1 : A.η < 1) {κ ep : ℝ} (hep1 : ep < 1) {T : ℕ}
    {y : Fin T → ι → ℝ} {z : Fin T → ι → Bool}
    {child : Fin T → Exec ι (Expert ι V k D)} {w : ℕ → Expert ι V k D → ℝ} {x : ι → ℝ}
    {l : ℕ} {hist : ℕ → ι → ℝ} {wIn : Expert ι V k D → ℝ}
    (hv : (Exec.node T y z child w x).ValidThr (gainMarket A.val ζ) A κ ep l hist wIn)
    (hpos : ∀ e, 0 < wIn e) {g : ℝ} (hg : 1 ≤ g)
    (hch : ∀ τ : Fin T, ∀ (hist : ℕ → ι → ℝ) (wIn : Expert ι V k D → ℝ),
        (child τ).ValidThr (gainMarket A.val ζ) A κ ep (l + 1) hist wIn → (∀ e, 0 < wIn e) →
        ∑ e, (child τ).wOut e ≤ g * ∑ e, wIn e) :
    ∀ n, n ≤ T → ∑ e, w n e
      ≤ ((1 - A.c) * (1 + A.η * ζ) + A.c * g) ^ n * ∑ e, wIn e := by
  have hwpos := thr_node_pos (gainMarket A.val ζ) A hc1 hη0 hη1 hep1 hv hpos
  obtain ⟨-, -, hw0, hprobe, -⟩ := hv
  have hb1 := one_le_base A hζ hc0 hc1 hη0 hg
  intro n
  induction n with
  | zero =>
    intro _
    rw [hw0]
    simp
  | succ n ihn =>
    intro hn
    have hn' : n < T := hn
    have hsumn := ihn (Nat.le_of_lt hn')
    have hposn := hwpos n (Nat.le_of_lt hn')
    obtain ⟨hmk, hchild, hstep⟩ := hprobe ⟨n, hn'⟩
    have hcpos : ∀ e, 0 < A.c * w n e := fun e => mul_pos hc0 (hposn e)
    have hcout := Exec.thr_pos (gainMarket A.val ζ) A hc1 hη0 hη1 hep1
      (child ⟨n, hn'⟩) _ _ _ hchild hcpos
    have hcsum := hch ⟨n, hn'⟩ _ _ hchild hcpos
    have hgb : ∀ e : Expert ι V k D, -1 ≤ gain A.val l hist (y ⟨n, hn'⟩)
          (feedback (y ⟨n, hn'⟩) (child ⟨n, hn'⟩).x (z ⟨n, hn'⟩)) e :=
      fun e => (gain_bounds _ _ _ e _ _).1
    have hmarket : ∑ e, ((1 - A.c) * w n e) * gain A.val l hist (y ⟨n, hn'⟩)
        (feedback (y ⟨n, hn'⟩) (child ⟨n, hn'⟩).x (z ⟨n, hn'⟩)) e
        ≤ ζ * ∑ e, (1 - A.c) * w n e :=
      hmk _
    have hrew : ∀ e, w (n + 1) e ≤ (1 - A.c) * w n e
        + A.η * (((1 - A.c) * w n e) * gain A.val l hist (y ⟨n, hn'⟩)
            (feedback (y ⟨n, hn'⟩) (child ⟨n, hn'⟩).x (z ⟨n, hn'⟩)) e)
        + (child ⟨n, hn'⟩).wOut e := fun e => by
      refine ((hstep e).2).trans (le_of_eq ?_)
      ring
    have hcs : ∑ e, (child ⟨n, hn'⟩).wOut e ≤ g * (A.c * ∑ e, w n e) := by
      rw [Finset.mul_sum]; exact hcsum
    have hmk' : ∑ e, ((1 - A.c) * w n e) * gain A.val l hist (y ⟨n, hn'⟩)
        (feedback (y ⟨n, hn'⟩) (child ⟨n, hn'⟩).x (z ⟨n, hn'⟩)) e
        ≤ ζ * ((1 - A.c) * ∑ e, w n e) := by
      rw [Finset.mul_sum]; exact hmarket
    have e3 : A.η * ∑ e, ((1 - A.c) * w n e) * gain A.val l hist (y ⟨n, hn'⟩)
        (feedback (y ⟨n, hn'⟩) (child ⟨n, hn'⟩).x (z ⟨n, hn'⟩)) e
        ≤ A.η * (ζ * ((1 - A.c) * ∑ e, w n e)) :=
      mul_le_mul_of_nonneg_left hmk' hη0.le
    have hstepsum : ∑ e, w (n + 1) e
        ≤ ((1 - A.c) * (1 + A.η * ζ) + A.c * g) * ∑ e, w n e := by
      calc ∑ e, w (n + 1) e
          ≤ ∑ e, ((1 - A.c) * w n e
            + A.η * (((1 - A.c) * w n e) * gain A.val l hist (y ⟨n, hn'⟩)
                (feedback (y ⟨n, hn'⟩) (child ⟨n, hn'⟩).x (z ⟨n, hn'⟩)) e)
            + (child ⟨n, hn'⟩).wOut e) := Finset.sum_le_sum (fun e _ => hrew e)
        _ = (1 - A.c) * ∑ e, w n e
            + A.η * ∑ e, ((1 - A.c) * w n e) * gain A.val l hist (y ⟨n, hn'⟩)
                (feedback (y ⟨n, hn'⟩) (child ⟨n, hn'⟩).x (z ⟨n, hn'⟩)) e
            + ∑ e, (child ⟨n, hn'⟩).wOut e := by
            rw [Finset.sum_add_distrib,
              Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        _ ≤ ((1 - A.c) * (1 + A.η * ζ) + A.c * g) * ∑ e, w n e := by
            linarith [e3, hcs]
    calc ∑ e, w (n + 1) e
        ≤ ((1 - A.c) * (1 + A.η * ζ) + A.c * g) * ∑ e, w n e := hstepsum
      _ ≤ ((1 - A.c) * (1 + A.η * ζ) + A.c * g)
          * (((1 - A.c) * (1 + A.η * ζ) + A.c * g) ^ n * ∑ e, wIn e) :=
          mul_le_mul_of_nonneg_left hsumn (by linarith)
      _ = ((1 - A.c) * (1 + A.η * ζ) + A.c * g) ^ (n + 1) * ∑ e, wIn e := by ring


/-- **Wealth with thresholded returns, by level.** A node at level `l` returns total wealth
at most `growthAt A ζ D l` times its input total. -/
theorem Exec.thr_wealth_level (A : Alg V) {ζ : ℝ} (hζ : 0 ≤ ζ) (hc0 : 0 < A.c)
    (hc1 : A.c < 1) (hη0 : 0 < A.η) (hη1 : A.η < 1) {κ ep : ℝ} (hep1 : ep < 1)
    (X : Exec ι (Expert ι V k D)) :
    ∀ (l : ℕ) (hist : ℕ → ι → ℝ) (wIn : Expert ι V k D → ℝ),
      X.ValidThr (gainMarket A.val ζ) A κ ep l hist wIn → (∀ e, 0 < wIn e) →
      ∑ e, X.wOut e ≤ growthAt A ζ D l * ∑ e, wIn e := by
  induction X with
  | leaf x wOut =>
    intro l hist wIn hv hpos
    obtain ⟨hl, hw, -⟩ := hv
    have hG : growthAt A ζ D l = 1 := by
      unfold growthAt
      rw [hl]
      by_cases h0 : D = 0
      · simp [h0]
      · simp [h0, growthH]
    simp [Exec.wOut, hw, hG]
  | node T y z child w x ih =>
    intro l hist wIn hv hpos
    have hl : l < D := hv.1
    have hT : T = (if l = 0 then A.r₀ else A.r) := hv.2.1
    have hchild : ∀ τ : Fin T, ∀ (hist : ℕ → ι → ℝ) (wIn : Expert ι V k D → ℝ),
        (child τ).ValidThr (gainMarket A.val ζ) A κ ep (l + 1) hist wIn → (∀ e, 0 < wIn e) →
        ∑ e, (child τ).wOut e ≤ growthH A ζ (D - (l + 1)) * ∑ e, wIn e := by
      intro τ hist' wIn' hv' hpos'
      have h := ih τ (l + 1) hist' wIn' hv' hpos'
      have hG : growthAt A ζ D (l + 1) = growthH A ζ (D - (l + 1)) := by
        unfold growthAt
        rw [if_neg (Nat.succ_ne_zero l)]
      rw [hG] at h
      exact h
    have h := thr_node_wealth_aux A hζ hc0 hc1 hη0 hη1 hep1 hv hpos
      (one_le_growthH A hζ hc0 hc1 hη0 _) hchild T le_rfl
    have hG : ((1 - A.c) * (1 + A.η * ζ) + A.c * growthH A ζ (D - (l + 1))) ^ T
        = growthAt A ζ D l := by
      unfold growthAt
      by_cases h0 : l = 0
      · subst h0
        have hD : D ≠ 0 := by omega
        rw [if_pos rfl, if_neg hD, hT, if_pos rfl]
      · rw [if_neg h0, hT, if_neg h0]
        have hD : D - l = (D - (l + 1)) + 1 := by omega
        rw [hD]
        rfl
    rw [hG] at h
    exact h


/-! ### Charging -/

/-- `probe_step` for an arbitrary nonnegative bonus function of the child. The contribution of one probe to the parent's weighted bonus: nonnegative when the probe is
light and its child succeeded at the parent's threshold, and at least `ε` otherwise. -/
theorem probe_step_gen (P : Params ι V k D) (H : Hyp ι V) {l : ℕ} (hl : l < D)
    {hist : ℕ → ι → ℝ} {m : Slot ι → ℝ} {t : ℝ} {d₀ : Option (Fin D × Slot ι)}
    (inv : NodeInv P.A.val H P.ρ P.β l hist m t d₀)
    (y : ι → ℝ) (z : ι → Bool) (c : Exec ι (Expert ι V k D)) (L : Expert ι V k D → ℝ)
    (hL' : ∀ e, 0 ≤ L e)
    (hcons : H.ConsistentAt P.A.val c.x z)
    (ih : ∀ (m' : Slot ι → ℝ) (t' : ℝ) (d₀' : Option (Fin D × Slot ι)),
        NodeInv P.A.val H P.ρ P.β (l + 1) (Function.update hist l y) m' t' d₀' →
        (∀ s ∈ H.S, H.surplus P.A.val c.x s ≤ t') ∨
        (P.σ * P.A.r ≤ Psi H P.ω (l + 1) m' d₀' L)) :
    ((∀ s ∈ H.S, H.surplus P.A.val c.x s ≤ t) ∧
        0 ≤ cur H m d₀ (fun e : Expert ι V k D =>
              Real.log (1 + P.A.η * gain P.A.val l hist y (feedback y c.x z) e))
            + Psi H P.ω l m d₀ L) ∨
      P.ε ≤ cur H m d₀ (fun e : Expert ι V k D =>
              Real.log (1 + P.A.η * gain P.A.val l hist y (feedback y c.x z) e))
            + Psi H P.ω l m d₀ L := by
  have hPsiL' : 0 ≤ Psi H P.ω l m d₀ L :=
    Psi_nonneg H m P.ω l d₀ inv.nonneg P.hω hL'
  obtain ⟨m', hm'0, hm'ρ, hchild⟩ :=
    exists_child_dist P.hβ P.δ_pos.le P.hδ1 P.hρ inv y
  -- a failed child pays for the probe
  have hfail : ∀ (d₀' : Option (Fin D × Slot ι)),
      Psi H P.ω (l + 1) m' d₀' L
        ≤ P.C * Psi H P.ω l m d₀ L →
      P.σ * P.A.r ≤ Psi H P.ω (l + 1) m' d₀' L →
      P.ε ≤ cur H m d₀ (fun e : Expert ι V k D =>
              Real.log (1 + P.A.η * gain P.A.val l hist y (feedback y c.x z) e))
            + Psi H P.ω l m d₀ L := by
    intro d₀' htr hf
    have h1 : P.C * (P.ε + P.lam) ≤ P.C * Psi H P.ω l m d₀ L :=
      P.hR1.trans (hf.trans htr)
    have h2 := le_of_mul_le_mul_left h1 P.C_pos
    have h3 := cur_gain_any (k := k) inv P.hη0 P.hη1 y (feedback y c.x z)
    have h4 := P.hlam
    linarith
  by_cases hlight : massGT m (H.surplus P.A.val y) t ≤ P.δ
  · -- light probe: the child keeps threshold and description
    have hdesc : (d₀ = none ∧ t = 0) ∨ ∃ j p, d₀ = some (j, p) ∧ (j : ℕ) < l + 1 ∧
        t = H.surplus P.A.val (Function.update hist l y j) p := by
      rcases inv.desc with ⟨hd, ht⟩ | ⟨j, p, hd, hj, ht⟩
      · exact Or.inl ⟨hd, ht⟩
      · refine Or.inr ⟨j, p, hd, Nat.lt_succ_of_lt hj, ?_⟩
        rw [Function.update_of_ne (Nat.ne_of_lt hj)]
        exact ht
    have inv' := hchild t d₀ le_rfl hlight hdesc
    rcases ih m' t d₀ inv' with hs | hf
    · left
      refine ⟨hs, ?_⟩
      have hv := feedback_correct P.A.val H y c.x z t inv.thr_nonneg hs hcons
      have := cur_gain_light (k := k) inv P.hη0 y (feedback y c.x z) hv
      linarith
    · right
      exact hfail d₀ (transfer_light H m m' P.ω l P.ρ P.C P.ρ_pos.le inv.nonneg hm'0 hm'ρ P.hω
        P.hC1 P.hC3 d₀ hL') hf
  · -- heavy probe: raise the threshold to a pivot in the band
    rw [not_le] at hlight
    obtain ⟨p, hp1, hp2, -, hp4⟩ := exists_pivot m (H.surplus P.A.val y) inv.nonneg inv.sum_one
      P.γ P.δ P.hγ0 P.hγδ P.hδ1
      (fun p => cur H m' (some (⟨l, hl⟩, p)) L)
      (fun p => cur_nonneg H m' hm'0 _ hL')
    have htt' : t < H.surplus P.A.val y p := by
      by_contra hcon
      have := massGT_antitone m (H.surplus P.A.val y) inv.nonneg (not_lt.1 hcon)
      linarith
    have hdesc : ((some ((⟨l, hl⟩ : Fin D), p) : Option (Fin D × Slot ι)) = none ∧
          H.surplus P.A.val y p = 0) ∨
        ∃ j q, (some ((⟨l, hl⟩ : Fin D), p) : Option (Fin D × Slot ι)) = some (j, q) ∧
          (j : ℕ) < l + 1 ∧
          H.surplus P.A.val y p = H.surplus P.A.val (Function.update hist l y j) q :=
      Or.inr ⟨⟨l, hl⟩, p, rfl, Nat.lt_succ_self l, by simp⟩
    have inv' := hchild (H.surplus P.A.val y p) (some (⟨l, hl⟩, p)) htt'.le hp1 hdesc
    rcases ih m' _ _ inv' with hs | hf
    · right
      have hv := feedback_correct P.A.val H y c.x z (H.surplus P.A.val y p)
        (inv.thr_nonneg.trans htt'.le) hs hcons
      have h1 := cur_gain_heavy (k := k) inv P.hη0 P.hη1 y (feedback y c.x z)
        (H.surplus P.A.val y p) htt' hv P.γ hp2
      have := P.hε
      linarith
    · right
      exact hfail _ (transfer_heavy H m m' P.ω l P.ρ P.C P.γ P.δ P.ρ_pos.le inv.nonneg hm'0
        hm'ρ P.hω P.hγδ P.hC1 P.hC2 P.hC3 d₀ hL' hl p hp4) hf


/-- **Charging.** For a hypothesis consistent with the run and any node invariant, a node
either succeeds (its prices bring every surplus down to its threshold), or it is internal and
its weighted thresholded bonus is at least `σ` per probe. This is `node_claim_with` for runs
with thresholded returns. -/
theorem node_claim_thr (M : MarketCond ι V k D) (P : Params ι V k D) (H : Hyp ι V)
    (X : Exec ι (Expert ι V k D)) :
    ∀ (l : ℕ) (hist : ℕ → ι → ℝ) (wIn : Expert ι V k D → ℝ),
      X.ValidThr M P.A P.κ P.ep l hist wIn → (∀ e, 0 < wIn e) → X.Consistent P.A.val H →
      ∀ (m : Slot ι → ℝ) (t : ℝ) (d₀ : Option (Fin D × Slot ι)),
        NodeInv P.A.val H P.ρ P.β l hist m t d₀ →
        (∀ s ∈ H.S, H.surplus P.A.val X.x s ≤ t) ∨
        (l < D ∧ P.σ * ((if l = 0 then P.A.r₀ else P.A.r : ℕ) : ℝ)
            ≤ Psi H P.ω l m d₀ (bonusT P.κ wIn X.wOut)) := by
  induction X with
  | leaf x wOut =>
    intro l hist wIn hv _ _ m t d₀ inv
    obtain ⟨hlD, -, hmed⟩ := hv
    left
    exact leaf_success P.hβ P.ρ_pos (by rw [hlD]; exact P.hdepth) inv x hmed
  | node T y z child w x ih =>
    intro l hist wIn hv hpos hcons m t d₀ inv
    have hv' := hv
    obtain ⟨hl, hT, hw0, hprobe, hmed⟩ := hv
    -- wealth is positive throughout the node
    have hwealth := thr_node_pos M P.A P.hc1 P.hη0 P.hη1 P.hep1 hv' hpos
    have hwpos : ∀ (τ : Fin T) (e : Expert ι V k D), 0 < w τ e :=
      fun τ e => hwealth τ (Nat.le_of_lt τ.2) e
    have hwcpos : ∀ (τ : Fin T) (e : Expert ι V k D), 0 < P.A.c * w τ e :=
      fun τ e => mul_pos P.hc0 (hwpos τ e)
    have hcout : ∀ (τ : Fin T) (e : Expert ι V k D), 0 < (child τ).wOut e :=
      fun τ => Exec.thr_pos M P.A P.hc1 P.hη0 P.hη1 P.hep1 (child τ) _ _ _
        (hprobe τ).2.1 (hwcpos τ)
    -- every probe contributes
    have hstepA : ∀ τ : Fin T,
        ((∀ s ∈ H.S, H.surplus P.A.val (child τ).x s ≤ t) ∧
          0 ≤ cur H m d₀ (fun e : Expert ι V k D => Real.log (1 + P.A.η
                * gain P.A.val l hist (y τ) (feedback (y τ) (child τ).x (z τ)) e))
              + Psi H P.ω l m d₀ (bonusT P.κ (fun e => P.A.c * w τ e) (child τ).wOut)) ∨
        P.ε ≤ cur H m d₀ (fun e : Expert ι V k D => Real.log (1 + P.A.η
                * gain P.A.val l hist (y τ) (feedback (y τ) (child τ).x (z τ)) e))
              + Psi H P.ω l m d₀ (bonusT P.κ (fun e => P.A.c * w τ e) (child τ).wOut) := by
      intro τ
      refine probe_step_gen P H hl inv (y τ) (z τ) (child τ)
        (bonusT P.κ (fun e => P.A.c * w τ e) (child τ).wOut) (bonusT_nonneg _ _ _)
        (hcons τ).1 ?_
      intro m' t' d₀' inv'
      rcases ih τ (l + 1) _ _ (hprobe τ).2.1 (hwcpos τ) (hcons τ).2 m' t' d₀' inv' with
        hs | ⟨-, hf⟩
      · exact Or.inl hs
      · right
        simpa using hf
    by_cases hmaj : T < 2 * (univ.filter
        (fun τ : Fin T => ∀ s ∈ H.S, H.surplus P.A.val (child τ).x s ≤ t)).card
    · left
      exact median_success P.A.val H (fun τ => (child τ).x) x t hmed hmaj
    · right
      refine ⟨hl, ?_⟩
      rw [← hT]
      classical
      -- bonus of each expert
      have hbonus : ∀ e : Expert ι V k D,
          (Real.log P.κ + T * (Real.log (1 - P.A.c) + Real.log (1 - P.ep)))
            + ∑ τ : Fin T, (Real.log (1 + P.A.η
                  * gain P.A.val l hist (y τ) (feedback (y τ) (child τ).x (z τ)) e)
                + bonusT P.κ (fun e => P.A.c * w τ e) (child τ).wOut e)
          ≤ bonusT P.κ wIn (w T) e := by
        intro e
        have hb := bonusT_bound T P.A.c P.A.η P.κ P.ep P.hc1 P.hη0 P.hη1 P.hκ0 P.hep1
          (fun n => w n e)
          (fun τ => gain P.A.val l hist (y τ) (feedback (y τ) (child τ).x (z τ)) e)
          (fun τ => (child τ).wOut e)
          (by rw [hw0]; exact hpos e)
          (fun τ => gain_bounds _ _ _ e _ _)
          (fun τ => ((hprobe τ).2.2 e).1)
        simp only [bonusT]
        rw [← hw0]
        exact hb
      have hPsi := Psi_mono H m P.ω l d₀ inv.nonneg P.hω hbonus
      rw [Psi_add H m P.ω l d₀ (fun _ => Real.log P.κ + T * (Real.log (1 - P.A.c) + Real.log (1 - P.ep)))
          (fun e => ∑ τ : Fin T, (Real.log (1 + P.A.η
                  * gain P.A.val l hist (y τ) (feedback (y τ) (child τ).x (z τ)) e)
                + bonusT P.κ (fun e => P.A.c * w τ e) (child τ).wOut e)),
        Psi_const H m P.ω l d₀ inv.sum_one, Psi_sum] at hPsi
      have hsumA : ∑ τ : Fin T, Psi H P.ω l m d₀ (fun e : Expert ι V k D =>
            Real.log (1 + P.A.η
                  * gain P.A.val l hist (y τ) (feedback (y τ) (child τ).x (z τ)) e)
                + bonusT P.κ (fun e => P.A.c * w τ e) (child τ).wOut e)
          = ∑ τ : Fin T, (cur H m d₀ (fun e : Expert ι V k D => Real.log (1 + P.A.η
                * gain P.A.val l hist (y τ) (feedback (y τ) (child τ).x (z τ)) e))
              + Psi H P.ω l m d₀ (bonusT P.κ (fun e => P.A.c * w τ e) (child τ).wOut)) := by
        refine Finset.sum_congr rfl (fun τ _ => ?_)
        rw [Psi_add, Psi_gain_eq_cur]
      rw [hsumA] at hPsi
      have hA := sum_ge_half _ _ P.ε P.hε0 hstepA (not_lt.1 hmaj)
      have hres := P.reserve_bound l
      have hres0 := reserve_nonneg (D := D) P.ω l P.hω
      have ha₀ : Real.log P.κ + T * (Real.log (1 - P.A.c) + Real.log (1 - P.ep)) ≤ 0 :=
        add_nonpos (Real.log_nonpos P.hκ0.le P.hκ1)
          (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg T)
            (add_nonpos (Real.log_nonpos (by linarith [P.hc1]) (by linarith [P.hc0]))
              (Real.log_nonpos (by linarith [P.hep1]) (by linarith [P.hep0]))))
      have hR2 := P.hR2 T (by rw [hT]; split_ifs <;> simp)
      have hmul : P.Pm * (Real.log P.κ + T * (Real.log (1 - P.A.c) + Real.log (1 - P.ep)))
          ≤ (Real.log P.κ + T * (Real.log (1 - P.A.c) + Real.log (1 - P.ep)))
            * (1 + reserve D P.ω l) := by
        nlinarith
      show P.σ * (T : ℝ) ≤ Psi H P.ω l m d₀ (bonusT P.κ wIn (w T))
      linarith


/-! ### Correctness -/

/-- **Price search with thresholded returns.** Generic in the market condition; see
`price_search_correct_of_growth`. -/
theorem price_search_correct_thr_of_growth (M : MarketCond ι V k D) (P : Params ι V k D)
    (X : Exec ι (Expert ι V k D)) (hist₀ : ℕ → ι → ℝ)
    (hX : X.ValidThr M P.A P.κ P.ep 0 hist₀ (fun _ => 1)) {G Γ : ℝ} (hG1 : 1 ≤ G)
    (hsum : ∑ e, X.wOut e ≤ G * Fintype.card (Expert ι V k D))
    (hlogG : Real.log G ≤ Γ)
    (hroot : P.Pm * (Real.log (1 + P.κ * Fintype.card (Expert ι V k D)) + Γ)
      < P.σ * P.A.r₀)
    (H : Hyp ι V) (hH : X.Consistent P.A.val H) :
    ∀ s ∈ H.S, H.surplus P.A.val X.x s ≤ 0 := by
  classical
  have hcard : 0 < (H.S.card : ℝ) := by exact_mod_cast Finset.card_pos.2 H.ne
  have inv : NodeInv P.A.val H P.ρ P.β 0 hist₀
      (fun s => if s ∈ H.S then 1 / (H.S.card : ℝ) else 0) 0
      (none : Option (Fin D × Slot ι)) := by
    refine ⟨?_, ?_, ?_, ?_, le_rfl, Or.inl ⟨rfl, rfl⟩⟩
    · intro s
      split_ifs
      · positivity
      · exact le_rfl
    · intro s hs
      simp [hs]
    · rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
      field_simp
    · intro s hs
      simp only [if_pos hs, lowCount, Finset.range_zero, Finset.filter_empty, Finset.card_empty,
        pow_zero, mul_one]
      rw [one_div, inv_mul_cancel₀ hcard.ne']
  rcases node_claim_thr M P H X 0 hist₀ _ hX (fun _ => one_pos) hH
      _ 0 none inv with h | ⟨-, hf⟩
  · exact h
  · exfalso
    simp only [if_true] at hf
    have hout := Exec.thr_pos M P.A P.hc1 P.hη0 P.hη1 P.hep1 X 0 hist₀ _ hX
      (fun _ => one_pos)
    have hcardE : (0 : ℝ) ≤ Fintype.card (Expert ι V k D) := Nat.cast_nonneg _
    have hGpos : 0 < G := by linarith
    have hκ0 := P.hκ0
    have hκE : 0 ≤ P.κ * Fintype.card (Expert ι V k D) := mul_nonneg hκ0.le hcardE
    have hΓ0 : 0 ≤ Γ := (Real.log_nonneg hG1).trans hlogG
    have hb : ∀ e : Expert ι V k D, bonus P.κ (fun _ => 1) X.wOut e
        ≤ Real.log (1 + P.κ * Fintype.card (Expert ι V k D)) + Γ := by
      intro e
      have h1 : X.wOut e ≤ ∑ e, X.wOut e :=
        Finset.single_le_sum (fun i _ => (hout i).le) (Finset.mem_univ e)
      have h2 : X.wOut e ≤ G * Fintype.card (Expert ι V k D) := h1.trans hsum
      have h3 : 1 + P.κ * (X.wOut e / 1)
          ≤ G * (1 + P.κ * Fintype.card (Expert ι V k D)) := by
        rw [div_one]
        have := mul_le_mul_of_nonneg_left h2 hκ0.le
        nlinarith
      unfold bonus
      calc Real.log (1 + P.κ * (X.wOut e / 1))
          ≤ Real.log (G * (1 + P.κ * Fintype.card (Expert ι V k D))) := by
            apply Real.log_le_log _ h3
            have := hout e
            rw [div_one]
            nlinarith
        _ = Real.log G + Real.log (1 + P.κ * Fintype.card (Expert ι V k D)) :=
            Real.log_mul hGpos.ne' (by linarith : (1 + P.κ * Fintype.card (Expert ι V k D)) ≠ 0)
        _ ≤ Real.log (1 + P.κ * Fintype.card (Expert ι V k D)) + Γ := by linarith
    have hb' : ∀ e : Expert ι V k D, bonusT P.κ (fun _ => 1) X.wOut e
        ≤ Real.log (1 + P.κ * Fintype.card (Expert ι V k D)) + Γ :=
      fun e => (bonusT_le_bonus hκ0.le (fun _ => one_pos) hout e).trans (hb e)
    have hPsi := Psi_mono H _ P.ω 0 none inv.nonneg P.hω hb'
    rw [Psi_const H _ P.ω 0 none inv.sum_one] at hPsi
    have hres := P.reserve_bound (k := k) 0
    have hres0 := reserve_nonneg (D := D) P.ω 0 P.hω
    have hB0 : 0 ≤ Real.log (1 + P.κ * Fintype.card (Expert ι V k D)) + Γ :=
      add_nonneg (Real.log_nonneg (by linarith)) hΓ0
    nlinarith


/-! ### Query count -/

omit [Fintype V] in
theorem queries_of_validThr (M : MarketCond ι V k D) (A : Alg V) (κ ep : ℝ)
    (X : Exec ι (Expert ι V k D)) :
    ∀ (l : ℕ) (hist : ℕ → ι → ℝ) (wIn : Expert ι V k D → ℝ), X.ValidThr M A κ ep l hist wIn →
      0 < l → X.queries = below A.r (D - l) := by
  induction X with
  | leaf x wOut =>
    intro l hist wIn hv _
    obtain ⟨hl, -, -⟩ := hv
    simp [Exec.queries, hl, below]
  | node T y z child w x ih =>
    intro l hist wIn hv hl0
    obtain ⟨hl, hT, -, hprobe, -⟩ := hv
    have hT' : T = A.r := by rw [hT, if_neg (Nat.pos_iff_ne_zero.1 hl0)]
    have hch : ∀ τ : Fin T, (child τ).queries = below A.r (D - (l + 1)) :=
      fun τ => ih τ (l + 1) _ _ (hprobe τ).2.1 (Nat.succ_pos l)
    have hD : D - l = (D - (l + 1)) + 1 := by omega
    simp only [Exec.queries, hch, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
    rw [hD, hT']
    rfl

omit [Fintype V] in
theorem queries_root_thr (M : MarketCond ι V k D) (A : Alg V) (κ ep : ℝ) (X : Exec ι (Expert ι V k D))
    (hist : ℕ → ι → ℝ) (wIn : Expert ι V k D → ℝ) (hX : X.ValidThr M A κ ep 0 hist wIn)
    (hD : 0 < D) : X.queries = A.r₀ * (1 + below A.r (D - 1)) := by
  cases X with
  | leaf x wOut =>
    obtain ⟨hl, -, -⟩ := hX
    omega
  | node T y z child w x =>
    obtain ⟨-, hT, -, hprobe, -⟩ := hX
    have hT' : T = A.r₀ := by rw [hT, if_pos rfl]
    have hch : ∀ τ : Fin T, (child τ).queries = below A.r (D - 1) :=
      fun τ => queries_of_validThr M A κ ep (child τ) 1 _ _ (hprobe τ).2.1 Nat.one_pos
    simp only [Exec.queries, hch, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
    rw [hT']

omit [Fintype V] in
theorem queries_root_le_thr (M : MarketCond ι V k D) (A : Alg V) (κ ep : ℝ) (hr : 2 ≤ A.r)
    (X : Exec ι (Expert ι V k D)) (hist : ℕ → ι → ℝ) (wIn : Expert ι V k D → ℝ)
    (hX : X.ValidThr M A κ ep 0 hist wIn) (hD : 0 < D) :
    X.queries ≤ 2 * A.r₀ * A.r ^ (D - 1) := by
  rw [queries_root_thr M A κ ep X hist wIn hX hD]
  have := below_le A.r hr (D - 1)
  calc A.r₀ * (1 + below A.r (D - 1)) ≤ A.r₀ * (2 * A.r ^ (D - 1)) :=
        Nat.mul_le_mul_left _ (by omega)
    _ = 2 * A.r₀ * A.r ^ (D - 1) := by ring

/-! ### How much wealth needs an individual return -/

open Classical in
/-- **The experts that need an individual return are light.** In a run with thresholded
returns under the gain condition, the experts whose return ratio at a node exceeds `1/κ`
(the only ones whose individual return enters the lower bound of the update) hold at most
`κ · growthAt` of the node's input wealth. -/
theorem Exec.thr_boosted_mass (A : Alg V) {ζ : ℝ} (hζ : 0 ≤ ζ) (hc0 : 0 < A.c)
    (hc1 : A.c < 1) (hη0 : 0 < A.η) (hη1 : A.η < 1) {κ ep : ℝ} (hκ : 0 ≤ κ) (hep1 : ep < 1)
    (X : Exec ι (Expert ι V k D)) (l : ℕ) (hist : ℕ → ι → ℝ) (wIn : Expert ι V k D → ℝ)
    (hv : X.ValidThr (gainMarket A.val ζ) A κ ep l hist wIn) (hpos : ∀ e, 0 < wIn e) :
    ∑ e ∈ univ.filter (fun e => 1 < κ * (X.wOut e / wIn e)), wIn e
      ≤ κ * (growthAt A ζ D l * ∑ e, wIn e) := by
  have hout := Exec.thr_pos (gainMarket A.val ζ) A hc1 hη0 hη1 hep1 X l hist wIn hv hpos
  have h1 := boosted_mass_le hκ wIn X.wOut hpos (fun e => (hout e).le)
  have h2 := Exec.thr_wealth_level A hζ hc0 hc1 hη0 hη1 hep1 X l hist wIn hv hpos
  exact h1.trans (mul_le_mul_of_nonneg_left h2 hκ)

/-! ### The exact update is a special case -/

/-- Every run of `Exec.ValidWith` (additive returns, rounded down by at most `1 - ep`) is a
run with thresholded returns. -/
theorem Exec.validThr_of_validWith (M : MarketCond ι V k D) (A : Alg V) {κ ep : ℝ} (hc0 : 0 < A.c)
    (hc1 : A.c < 1) (hη0 : 0 < A.η) (hη1 : A.η < 1) (hκ0 : 0 < κ)
    (hκc : κ * (1 - A.c) * (1 + A.η) ≤ A.c) (hep1 : ep < 1)
    (hrnd : ∀ x : ℝ, 0 < x → (1 - ep) * x ≤ A.rnd x ∧ A.rnd x ≤ x)
    (X : Exec ι (Expert ι V k D)) :
    ∀ (l : ℕ) (hist : ℕ → ι → ℝ) (wIn : Expert ι V k D → ℝ), X.ValidWith M A l hist wIn →
      (∀ e, 0 < wIn e) → X.ValidThr M A κ ep l hist wIn := by
  induction X with
  | leaf x wOut =>
    intro l hist wIn hv _
    exact hv
  | node T y z child w x ih =>
    intro l hist wIn hv hpos
    have hwpos := node_pos_aux M A hc0 hc1 hη0 hη1 hep1 hrnd hv hpos
      (fun τ => Exec.wealth_pos M A hc0 hc1 hη0 hη1 hep1 hrnd (child τ))
    obtain ⟨hl, hT, hw0, hprobe, hmed⟩ := hv
    refine ⟨hl, hT, hw0, fun τ => ?_, hmed⟩
    obtain ⟨hmk, hchild, hstep⟩ := hprobe τ
    have hwτ : ∀ e, 0 < w τ e := fun e => hwpos τ (Nat.le_of_lt τ.2) e
    have hcpos : ∀ e, 0 < A.c * w τ e := fun e => mul_pos hc0 (hwτ e)
    have hcout := Exec.wealth_pos M A hc0 hc1 hη0 hη1 hep1 hrnd (child τ) _ _ _ hchild hcpos
    refine ⟨hmk, ih τ _ _ _ hchild hcpos, fun e => ?_⟩
    have hg := gain_bounds A.val l hist e (y τ) (feedback (y τ) (child τ).x (z τ))
    have hM : 0 ≤ (child τ).wOut e / (A.c * w τ e) := (div_pos (hcout e) (hcpos e)).le
    have hfac := thr_factor_le hc0 hc1 hη0 hη1 hκ0 hκc hg hM
    have hc' := hc0.ne'
    have hW' := (hwτ e).ne'
    have hcancel : w τ e * (A.c * ((child τ).wOut e / (A.c * w τ e))) = (child τ).wOut e := by
      field_simp
    have hmul : (1 - A.c) * w τ e
          * (1 + A.η * gain A.val l hist (y τ) (feedback (y τ) (child τ).x (z τ)) e)
          * max 1 (κ * ((child τ).wOut e / (A.c * w τ e)))
        ≤ (1 - A.c) * w τ e
          * (1 + A.η * gain A.val l hist (y τ) (feedback (y τ) (child τ).x (z τ)) e)
          + (child τ).wOut e := by
      have h := mul_le_mul_of_nonneg_left hfac (hwτ e).le
      linarith [h, hcancel, show w τ e * ((1 - A.c)
          * (1 + A.η * gain A.val l hist (y τ) (feedback (y τ) (child τ).x (z τ)) e)
          * max 1 (κ * ((child τ).wOut e / (A.c * w τ e))))
        = (1 - A.c) * w τ e
          * (1 + A.η * gain A.val l hist (y τ) (feedback (y τ) (child τ).x (z τ)) e)
          * max 1 (κ * ((child τ).wOut e / (A.c * w τ e))) by ring,
        show w τ e * ((1 - A.c)
          * (1 + A.η * gain A.val l hist (y τ) (feedback (y τ) (child τ).x (z τ)) e)
          + A.c * ((child τ).wOut e / (A.c * w τ e)))
        = (1 - A.c) * w τ e
          * (1 + A.η * gain A.val l hist (y τ) (feedback (y τ) (child τ).x (z τ)) e)
          + w τ e * (A.c * ((child τ).wOut e / (A.c * w τ e))) by ring]
    have h1 : 0 < 1 + A.η * gain A.val l hist (y τ)
        (feedback (y τ) (child τ).x (z τ)) e := by nlinarith [hg.1]
    have hX : 0 < (1 - A.c) * w τ e
        * (1 + A.η * gain A.val l hist (y τ) (feedback (y τ) (child τ).x (z τ)) e)
        + (child τ).wOut e :=
      add_pos (mul_pos (mul_pos (by linarith) (hwτ e)) h1) (hcout e)
    have hr := hrnd _ hX
    rw [hstep e]
    exact ⟨(mul_le_mul_of_nonneg_left hmul (by linarith)).trans hr.1, hr.2⟩

/-! ### Correctness under the gain condition -/

/-- **Price search with thresholded returns under the gain condition.** -/
theorem price_search_correct_thr_level (P : Params ι V k D) {ζ : ℝ} (hζ : 0 ≤ ζ)
    (X : Exec ι (Expert ι V k D)) (hist₀ : ℕ → ι → ℝ)
    (hX : X.ValidThr (gainMarket P.A.val ζ) P.A P.κ P.ep 0 hist₀ (fun _ => 1))
    (hroot : P.Pm * (Real.log (1 + P.κ * Fintype.card (Expert ι V k D))
        + Real.log (growthAt P.A ζ D 0)) < P.σ * P.A.r₀)
    (H : Hyp ι V) (hH : X.Consistent P.A.val H) :
    ∀ s ∈ H.S, H.surplus P.A.val X.x s ≤ 0 := by
  have hsum := Exec.thr_wealth_level P.A hζ P.hc0 P.hc1 P.hη0 P.hη1 P.hep1 X 0
    hist₀ _ hX (fun _ => one_pos)
  have hE : ∑ _e : Expert ι V k D, (1 : ℝ) = Fintype.card (Expert ι V k D) := by simp
  rw [hE] at hsum
  exact price_search_correct_thr_of_growth (gainMarket P.A.val ζ) P X hist₀ hX
    (one_le_growthAt P.A hζ P.hc0 P.hc1 P.hη0 D 0) hsum le_rfl hroot H hH

/-! ### Explicit constants -/

namespace Consts

variable {k : ℕ}

/-- **Thresholded returns with a constant tolerance.** As `price_search_gain_level`, for runs
with thresholded returns. Let `c r (1 + α) ≤ u < 1` for some
`α ≤ 1`. With `r₀' ≥ r₀` probes at the root and a tolerance `ζ ≥ 0` satisfying
`r η ζ ≤ α (1 - u)` and `Pm · r₀' η ζ / (1 - u) ≤ σ (r₀' - r₀)`, every run whose proposals
satisfy the gain condition (with rounded wealth) meets all demands of every consistent
hypothesis and makes at most `2 r₀' (2N)^e` label queries. -/
theorem price_search_thr_level (K : Consts k) (hK : K.Good) (e : ℕ)
    (he : ((K.r : ℚ)) ^ 2 ≤ (K.ρ ^ 2 / K.β) ^ e)
    {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V] [Nonempty ι] (val : V → ℝ)
    (r₀' : ℕ) (hr₀ : K.r₀ ι V (K.depth hK (Fintype.card ι)) ≤ r₀') {ζ α u : ℝ}
    (hζ0 : 0 ≤ ζ) (hα1 : α ≤ 1)
    (hu : (K.c : ℝ) * (K.r : ℝ) * (1 + α) ≤ u) (hu1 : u < 1)
    (hζα : (K.r : ℝ) * ((K.η : ℝ) * ζ) ≤ α * (1 - u))
    (hζ : (K.Pm : ℝ) * ((r₀' : ℝ) * ((K.η : ℝ) * ζ) / (1 - u))
      ≤ (K.σ : ℝ) * ((r₀' : ℝ) - K.r₀ ι V (K.depth hK (Fintype.card ι))))
    (X : Exec ι (Expert ι V k (K.depth hK (Fintype.card ι)))) (hist₀ : ℕ → ι → ℝ)
    (hX : X.ValidThr (gainMarket val ζ) (K.algRoot ι V val r₀') K.κ (K.ep : ℝ) 0 hist₀
      (fun _ => 1)) :
    (∀ H : Hyp ι V, X.Consistent val H → ∀ s ∈ H.S, val (H.a s) ≤ sp X.x s) ∧
    X.queries ≤ 2 * r₀' * (2 * Fintype.card ι) ^ e := by
  have hN : 1 ≤ 2 * Fintype.card ι := by
    have := Fintype.card_pos (α := ι)
    omega
  have hD := depth_pos (K.b_real hK) hN
  have hq : X.queries ≤ 2 * r₀' * (2 * Fintype.card ι) ^ e := by
    have hq := queries_root_le_thr (gainMarket val ζ) (K.algRoot ι V val r₀') K.κ (K.ep : ℝ) hK.hr X
      hist₀ _ hX hD
    have he' : (((K.r : ℕ) : ℝ)) ^ 2 ≤ ((K.ρ : ℝ) ^ 2 / (K.β : ℝ)) ^ e := by
      exact_mod_cast he
    have hpow : K.r ^ (K.depth hK (Fintype.card ι) - 1) ≤ (2 * Fintype.card ι) ^ e :=
      pow_depth_le (K.b_real hK) he' (depth_min (K.b_real hK) hN)
    calc X.queries
        ≤ 2 * r₀' * K.r ^ (K.depth hK (Fintype.card ι) - 1) := hq
      _ ≤ 2 * r₀' * (2 * Fintype.card ι) ^ e := Nat.mul_le_mul_left _ hpow
  refine ⟨?_, hq⟩
  intro H hH s hs
  have hroot0 := hroot_real (ι := ι) (V := V) hK (K.depth hK (Fintype.card ι))
  let P := K.paramsRoot hK ι V val r₀' hr₀
  have hG : growthAt P.A ζ (K.depth hK (Fintype.card ι)) 0
      ≤ Real.exp ((r₀' : ℝ) * ((K.η : ℝ) * ζ) / (1 - u)) :=
    growthAt_zero_le_exp P.A hζ0 P.hc0 P.hc1 P.hη0 hα1 hu hu1 hζα _
  have hG1 := one_le_growthAt P.A hζ0 P.hc0 P.hc1 P.hη0 (K.depth hK (Fintype.card ι)) 0
  have hlog : Real.log (growthAt P.A ζ (K.depth hK (Fintype.card ι)) 0)
      ≤ (r₀' : ℝ) * ((K.η : ℝ) * ζ) / (1 - u) := by
    have := Real.log_le_log (by linarith) hG
    rwa [Real.log_exp] at this
  have hsum := Exec.thr_wealth_level P.A hζ0 P.hc0 P.hc1 P.hη0 P.hη1 P.hep1 X 0
    hist₀ _ hX (fun _ => one_pos)
  have hE : ∑ _e : Expert ι V k (K.depth hK (Fintype.card ι)), (1 : ℝ)
      = Fintype.card (Expert ι V k (K.depth hK (Fintype.card ι))) := by simp
  rw [hE] at hsum
  have h := price_search_correct_thr_of_growth (gainMarket val ζ) P X hist₀ hX hG1 hsum hlog
    (by
      show (K.Pm : ℝ) * (Real.log (1 + K.κ * Fintype.card (Expert ι V k _))
        + (r₀' : ℝ) * ((K.η : ℝ) * ζ) / (1 - u)) < (K.σ : ℝ) * (r₀' : ℝ)
      nlinarith) H hH s hs
  simp only [Hyp.surplus] at h
  have hval : P.A.val = val := rfl
  rw [hval] at h
  linarith

end Consts

/-! ### Arity 4 -/

variable [Nonempty ι]

/-- **Arity 4 with thresholded returns.** The update of every expert's wealth may be anything
between `(1 - ep) (1 - c) w (1 + η g) · max 1 (κ · out / (c w))` and `(1 - c) w (1 + η g) + out`.
Original statement for additive returns: With `2 r₀` probes at the root, every run in which
at each proposal no feedback gives the market an aggregate gain above `2^-25` times its
wealth, and whose wealth is rounded to 41 significant bits after every update, meets all
demands of every consistent hypothesis and makes at most `4 r₀ (2N)^46` label queries. -/
theorem price_search_k4_thr_const (val : V → ℝ)
    (X : Exec ι (Expert ι V 4 (K4.depth K4_good (Fintype.card ι)))) (hist₀ : ℕ → ι → ℝ)
    (hX : X.ValidThr (gainMarket val (1 / 2 ^ 25))
      (K4.algRoot ι V val (2 * K4.r₀ ι V (K4.depth K4_good (Fintype.card ι))))
      K4.κ (K4.ep : ℝ) 0 hist₀ (fun _ => 1)) :
    (∀ H : Hyp ι V, X.Consistent val H → ∀ s ∈ H.S, val (H.a s) ≤ sp X.x s) ∧
    X.queries ≤ 4 * K4.r₀ ι V (K4.depth K4_good (Fintype.card ι))
      * (2 * Fintype.card ι) ^ 46 := by
  have hσ : (1 : ℝ) / 4096 ≤ (K4.σ : ℝ) / (4 * (K4.Pm : ℝ) * (K4.η : ℝ)) := by
    have hq : (1 : ℚ) / 4096 ≤ K4.σ / (4 * K4.Pm * K4.η) := by
      norm_num [K4, Consts.σ, Consts.ε, Consts.q, Consts.lp, Consts.lam, Consts.Pm]
    have hr : ((1 / 4096 : ℚ) : ℝ) ≤ ((K4.σ / (4 * K4.Pm * K4.η) : ℚ) : ℝ) := by
      exact_mod_cast hq
    push_cast at hr
    exact hr
  have hPm := Consts.Pm_pos_real K4_good
  have hη := Consts.η_pos_real K4_good
  have hσ0 := Consts.σ_pos_real K4_good
  have hσ' : 4 * (K4.Pm : ℝ) * (K4.η : ℝ) ≤ 4096 * (K4.σ : ℝ) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)] at hσ
    linarith
  have hcr : ((K4.c : ℚ) : ℝ) * ((K4.r : ℕ) : ℝ) * (1 + 1 / 50) ≤ 979 / 1000 := by
    have hq : (K4.c : ℚ) * (K4.r : ℚ) * (1 + 1 / 50) ≤ 979 / 1000 := by
      norm_num [K4, Consts.c]
    have hr : (((K4.c : ℚ) * (K4.r : ℚ) * (1 + 1 / 50) : ℚ) : ℝ) ≤ ((979 / 1000 : ℚ) : ℝ) := by
      exact_mod_cast hq
    push_cast at hr
    exact hr
  have hηv : (K4.η : ℝ) = 1 / 16 := by norm_num [K4]
  have hrv : ((K4.r : ℕ) : ℝ) = 125800 := by norm_num [K4]
  have h := K4.price_search_thr_level K4_good 46 K4_exp val
    (2 * K4.r₀ ι V (K4.depth K4_good (Fintype.card ι))) (by omega)
    (ζ := 1 / 2 ^ 25) (α := 1 / 50) (u := 979 / 1000) (by positivity)
    (by norm_num) hcr (by norm_num)
    (by rw [hηv, hrv]; norm_num)
    (by
      have hr0 : (0 : ℝ) ≤ (K4.r₀ ι V (K4.depth K4_good (Fintype.card ι)) : ℝ) :=
        Nat.cast_nonneg _
      push_cast
      have h1 : (K4.Pm : ℝ) * (K4.η : ℝ) * (1 / 2 ^ 25) / (1 - 979 / 1000) * 2
          ≤ (K4.σ : ℝ) := by
        norm_num
        nlinarith
      have h2 := mul_le_mul_of_nonneg_right h1 hr0
      calc (K4.Pm : ℝ) * (2 * (K4.r₀ ι V (K4.depth K4_good (Fintype.card ι)) : ℝ)
            * ((K4.η : ℝ) * (1 / 2 ^ 25)) / (1 - 979 / 1000))
          = (K4.Pm : ℝ) * (K4.η : ℝ) * (1 / 2 ^ 25) / (1 - 979 / 1000) * 2
            * (K4.r₀ ι V (K4.depth K4_good (Fintype.card ι)) : ℝ) := by ring
        _ ≤ (K4.σ : ℝ) * (K4.r₀ ι V (K4.depth K4_good (Fintype.card ι)) : ℝ) := h2
        _ = (K4.σ : ℝ) * (2 * (K4.r₀ ι V (K4.depth K4_good (Fintype.card ι)) : ℝ)
            - K4.r₀ ι V (K4.depth K4_good (Fintype.card ι))) := by ring)
    X hist₀ hX
  refine ⟨h.1, h.2.trans (le_of_eq ?_)⟩
  ring

end SPLP
