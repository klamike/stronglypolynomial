import Mathlib
import SPLP.Defs
import SPLP.Experts
import SPLP.Weights
import SPLP.Invariant
import SPLP.Bonus
import SPLP.Market
import SPLP.Median
import SPLP.Boost

/-!
# Correctness of the recursive price search

`Params` collects the numerical conditions under which the analysis goes through, for general
boost factor `β`, band `[γ, δ]`, expert arity `k`, learning rate `η`, investment share `c` and
reserve masses `ω`. `price_search_correct` then states that every valid run of the algorithm
returns prices meeting all demands of every hypothesis consistent with the labels it received.
-/

set_option linter.unusedSectionVars false

namespace SPLP

open Finset

variable {ι V : Type*} {k D : ℕ} [Fintype ι] [DecidableEq ι] [Fintype V]

/-! ### Wealth stays positive and never grows in total -/

theorem node_wealth_aux (A : Alg V) (hc0 : 0 < A.c) (hc1 : A.c < 1) (hη0 : 0 < A.η)
    (hη1 : A.η < 1) {ep : ℝ} (hep1 : ep < 1)
    (hrnd : ∀ x : ℝ, 0 < x → (1 - ep) * x ≤ A.rnd x ∧ A.rnd x ≤ x) {T : ℕ} {y : Fin T → ι → ℝ} {z : Fin T → ι → Bool}
    {child : Fin T → Exec ι (Expert ι V k D)} {w : ℕ → Expert ι V k D → ℝ} {x : ι → ℝ}
    {l : ℕ} {hist : ℕ → ι → ℝ} {wIn : Expert ι V k D → ℝ}
    (hv : (Exec.node T y z child w x).Valid A l hist wIn) (hpos : ∀ e, 0 < wIn e)
    (hch : ∀ τ : Fin T, ∀ (l : ℕ) (hist : ℕ → ι → ℝ) (wIn : Expert ι V k D → ℝ),
        (child τ).Valid A l hist wIn → (∀ e, 0 < wIn e) →
        (∀ e, 0 < (child τ).wOut e) ∧ ∑ e, (child τ).wOut e ≤ ∑ e, wIn e) :
    ∀ n, n ≤ T → (∀ e, 0 < w n e) ∧ ∑ e, w n e ≤ ∑ e, wIn e := by
  obtain ⟨-, -, hw0, hprobe, -⟩ := hv
  intro n
  induction n with
  | zero =>
    intro _
    rw [hw0]
    exact ⟨hpos, le_rfl⟩
  | succ n ihn =>
    intro hn
    have hn' : n < T := hn
    obtain ⟨hposn, hsumn⟩ := ihn (Nat.le_of_lt hn')
    obtain ⟨hmin, hchild, hstep⟩ := hprobe ⟨n, hn'⟩
    have hcpos : ∀ e, 0 < A.c * w n e := fun e => mul_pos hc0 (hposn e)
    obtain ⟨hcout, hcsum⟩ := hch ⟨n, hn'⟩ _ _ _ hchild hcpos
    have hgb : ∀ e : Expert ι V k D, -1 ≤ gain A.val l hist (y ⟨n, hn'⟩)
          (feedback (y ⟨n, hn'⟩) (child ⟨n, hn'⟩).x (z ⟨n, hn'⟩)) e ∧
        gain A.val l hist (y ⟨n, hn'⟩)
          (feedback (y ⟨n, hn'⟩) (child ⟨n, hn'⟩).x (z ⟨n, hn'⟩)) e ≤ 1 :=
      fun e => gain_bounds _ _ _ e _ _
    have hs : ∀ e, w (n + 1) e = A.rnd ((1 - A.c) * w n e
        * (1 + A.η * gain A.val l hist (y ⟨n, hn'⟩)
            (feedback (y ⟨n, hn'⟩) (child ⟨n, hn'⟩).x (z ⟨n, hn'⟩)) e)
        + (child ⟨n, hn'⟩).wOut e) := fun e => hstep e
    have hXpos : ∀ e, 0 < (1 - A.c) * w n e
        * (1 + A.η * gain A.val l hist (y ⟨n, hn'⟩)
            (feedback (y ⟨n, hn'⟩) (child ⟨n, hn'⟩).x (z ⟨n, hn'⟩)) e)
        + (child ⟨n, hn'⟩).wOut e := by
      intro e
      have h1 : 0 < 1 + A.η * gain A.val l hist (y ⟨n, hn'⟩)
          (feedback (y ⟨n, hn'⟩) (child ⟨n, hn'⟩).x (z ⟨n, hn'⟩)) e := by
        nlinarith [(hgb e).1]
      exact add_pos (mul_pos (mul_pos (by linarith) (hposn e)) h1) (hcout e)
    have hmarket : ∑ e, ((1 - A.c) * w n e) * gain A.val l hist (y ⟨n, hn'⟩)
        (feedback (y ⟨n, hn'⟩) (child ⟨n, hn'⟩).x (z ⟨n, hn'⟩)) e ≤ 0 :=
      market_no_profit (bidOf A.val l hist) (dirOf A.val l hist)
        (fun e => (1 - A.c) * w n e)
        (fun e => mul_nonneg (by linarith) (hposn e).le) (y ⟨n, hn'⟩) hmin
        (vreal (feedback (y ⟨n, hn'⟩) (child ⟨n, hn'⟩).x (z ⟨n, hn'⟩))) _
        (fun e o ho => minPay_le _ _ _ _ _ o ho)
    constructor
    · intro e
      rw [hs e]
      exact lt_of_lt_of_le (mul_pos (by linarith) (hXpos e)) (hrnd _ (hXpos e)).1
    · have hrew : ∀ e, w (n + 1) e ≤ (1 - A.c) * w n e
          + A.η * (((1 - A.c) * w n e) * gain A.val l hist (y ⟨n, hn'⟩)
              (feedback (y ⟨n, hn'⟩) (child ⟨n, hn'⟩).x (z ⟨n, hn'⟩)) e)
          + (child ⟨n, hn'⟩).wOut e := fun e => by
        rw [hs e]
        refine (hrnd _ (hXpos e)).2.trans (le_of_eq ?_)
        ring
      have hcs : ∑ e, (child ⟨n, hn'⟩).wOut e ≤ A.c * ∑ e, w n e := by
        rw [Finset.mul_sum]; exact hcsum
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
        _ ≤ ∑ e, w n e := by nlinarith [hmarket, hcs, hη0]
        _ ≤ ∑ e, wIn e := hsumn

/-- Every node returns positive wealth, of total at most its input total. -/
theorem Exec.wealth (A : Alg V) (hc0 : 0 < A.c) (hc1 : A.c < 1) (hη0 : 0 < A.η)
    (hη1 : A.η < 1) {ep : ℝ} (hep1 : ep < 1)
    (hrnd : ∀ x : ℝ, 0 < x → (1 - ep) * x ≤ A.rnd x ∧ A.rnd x ≤ x)
    (X : Exec ι (Expert ι V k D)) :
    ∀ (l : ℕ) (hist : ℕ → ι → ℝ) (wIn : Expert ι V k D → ℝ), X.Valid A l hist wIn →
      (∀ e, 0 < wIn e) → (∀ e, 0 < X.wOut e) ∧ ∑ e, X.wOut e ≤ ∑ e, wIn e := by
  induction X with
  | leaf x wOut =>
    intro l hist wIn hv hpos
    obtain ⟨-, hw, -⟩ := hv
    simp only [Exec.wOut, hw]
    exact ⟨hpos, le_rfl⟩
  | node T y z child w x ih =>
    intro l hist wIn hv hpos
    exact node_wealth_aux A hc0 hc1 hη0 hη1 hep1 hrnd hv hpos ih T le_rfl

/-! ### Positivity for a general market condition -/

/-- Wealth stays positive at a node whatever the proposals are. -/
theorem node_pos_aux (M : MarketCond ι V k D) (A : Alg V) (hc0 : 0 < A.c) (hc1 : A.c < 1)
    (hη0 : 0 < A.η) (hη1 : A.η < 1) {ep : ℝ} (hep1 : ep < 1)
    (hrnd : ∀ x : ℝ, 0 < x → (1 - ep) * x ≤ A.rnd x ∧ A.rnd x ≤ x) {T : ℕ}
    {y : Fin T → ι → ℝ} {z : Fin T → ι → Bool}
    {child : Fin T → Exec ι (Expert ι V k D)} {w : ℕ → Expert ι V k D → ℝ} {x : ι → ℝ}
    {l : ℕ} {hist : ℕ → ι → ℝ} {wIn : Expert ι V k D → ℝ}
    (hv : (Exec.node T y z child w x).ValidWith M A l hist wIn) (hpos : ∀ e, 0 < wIn e)
    (hch : ∀ τ : Fin T, ∀ (l : ℕ) (hist : ℕ → ι → ℝ) (wIn : Expert ι V k D → ℝ),
        (child τ).ValidWith M A l hist wIn → (∀ e, 0 < wIn e) → ∀ e, 0 < (child τ).wOut e) :
    ∀ n, n ≤ T → ∀ e, 0 < w n e := by
  obtain ⟨-, -, hw0, hprobe, -⟩ := hv
  intro n
  induction n with
  | zero =>
    intro _
    rw [hw0]
    exact hpos
  | succ n ihn =>
    intro hn e
    have hn' : n < T := hn
    have hposn := ihn (Nat.le_of_lt hn')
    obtain ⟨-, hchild, hstep⟩ := hprobe ⟨n, hn'⟩
    have hcout := hch ⟨n, hn'⟩ _ _ _ hchild (fun e => mul_pos hc0 (hposn e))
    have hg := (gain_bounds A.val l hist e (y ⟨n, hn'⟩)
      (feedback (y ⟨n, hn'⟩) (child ⟨n, hn'⟩).x (z ⟨n, hn'⟩))).1
    have h1 : 0 < 1 + A.η * gain A.val l hist (y ⟨n, hn'⟩)
        (feedback (y ⟨n, hn'⟩) (child ⟨n, hn'⟩).x (z ⟨n, hn'⟩)) e := by
      nlinarith
    have hX : 0 < (1 - A.c) * w n e
        * (1 + A.η * gain A.val l hist (y ⟨n, hn'⟩)
            (feedback (y ⟨n, hn'⟩) (child ⟨n, hn'⟩).x (z ⟨n, hn'⟩)) e)
        + (child ⟨n, hn'⟩).wOut e :=
      add_pos (mul_pos (mul_pos (by linarith) (hposn e)) h1) (hcout e)
    have hs : w (n + 1) e = A.rnd ((1 - A.c) * w n e
        * (1 + A.η * gain A.val l hist (y ⟨n, hn'⟩)
            (feedback (y ⟨n, hn'⟩) (child ⟨n, hn'⟩).x (z ⟨n, hn'⟩)) e)
        + (child ⟨n, hn'⟩).wOut e) := hstep e
    rw [hs]
    exact lt_of_lt_of_le (mul_pos (by linarith) hX) (hrnd _ hX).1

/-- Every node returns positive wealth, whatever the proposals are. -/
theorem Exec.wealth_pos (M : MarketCond ι V k D) (A : Alg V) (hc0 : 0 < A.c) (hc1 : A.c < 1)
    (hη0 : 0 < A.η) (hη1 : A.η < 1) {ep : ℝ} (hep1 : ep < 1)
    (hrnd : ∀ x : ℝ, 0 < x → (1 - ep) * x ≤ A.rnd x ∧ A.rnd x ≤ x)
    (X : Exec ι (Expert ι V k D)) :
    ∀ (l : ℕ) (hist : ℕ → ι → ℝ) (wIn : Expert ι V k D → ℝ), X.ValidWith M A l hist wIn →
      (∀ e, 0 < wIn e) → ∀ e, 0 < X.wOut e := by
  induction X with
  | leaf x wOut =>
    intro l hist wIn hv hpos
    obtain ⟨-, hw, -⟩ := hv
    simp only [Exec.wOut, hw]
    exact hpos
  | node T y z child w x ih =>
    intro l hist wIn hv hpos
    exact node_pos_aux M A hc0 hc1 hη0 hη1 hep1 hrnd hv hpos ih T le_rfl

/-! ### Bonuses -/

/-- The logarithmic bonus of an expert at a node: `log (1 + κ · returned / input)`. -/
noncomputable def bonus {E : Type*} (κ : ℝ) (wIn wOut : E → ℝ) (e : E) : ℝ :=
  Real.log (1 + κ * (wOut e / wIn e))

theorem bonus_nonneg {E : Type*} {κ : ℝ} (hκ : 0 ≤ κ) {wIn wOut : E → ℝ}
    (h1 : ∀ e, 0 < wIn e) (h2 : ∀ e, 0 < wOut e) (e : E) : 0 ≤ bonus κ wIn wOut e := by
  apply Real.log_nonneg
  have := div_pos (h2 e) (h1 e)
  nlinarith

/-! ### Parameters -/

/-- Numerical parameters of the algorithm and of its analysis, with the conditions under which
the analysis is valid. Here `ρ = β / (1 + (β - 1) δ)` is the largest factor by which a slot's
mass can grow in one level, `ω` are the reserve masses for future pivot levels with total mass
at most `Pm - 1`, `C` is the transfer constant, `ε` the average log gain of a heavy probe,
`lam` the worst average log loss of a probe, and `κ` the bonus scale. -/
structure Params (ι V : Type*) [Fintype ι] [DecidableEq ι] [Fintype V] (k D : ℕ) where
  A : Alg V
  β : ℝ
  δ : ℝ
  γ : ℝ
  ρ : ℝ
  ω : ℕ → ℝ
  Pm : ℝ
  C : ℝ
  σ : ℝ
  ε : ℝ
  lam : ℝ
  κ : ℝ
  /-- Relative rounding error of the wealth updates (`0` for exact arithmetic). -/
  ep : ℝ
  hβ : 1 < β
  hγ0 : 0 ≤ γ
  hγδ : γ < δ
  hδ1 : δ ≤ 1
  hρ : ρ * (1 + (β - 1) * δ) = β
  /-- Depth: `(2N)² < (ρ²/β)^D`. -/
  hdepth : ((Fintype.card (Slot ι) : ℝ)) ^ 2 < (ρ ^ 2 / β) ^ D
  hc0 : 0 < A.c
  hc1 : A.c < 1
  hη0 : 0 < A.η
  hη1 : A.η < 1
  hω : ∀ i, 0 ≤ ω i
  hPm : ∀ n, 1 + ∑ i ∈ range n, ω i ≤ Pm
  hC1 : ρ ^ k ≤ C
  hC2 : ρ ^ k ≤ C * ((δ - γ) * ω 0)
  hC3 : ∀ i, ρ ^ (k + 1) * ω i ≤ C * ω (i + 1)
  hε0 : 0 ≤ ε
  hε : ε ≤ (1 - (1 - γ) ^ k) * Real.log (1 + A.η) + (1 - γ) ^ k * Real.log (1 - A.η)
  hlam : -lam ≤ Real.log (1 - A.η)
  hκ0 : 0 < κ
  hκ1 : κ ≤ 1
  hκc : κ * (1 - A.c) * (1 + A.η) ≤ A.c
  hep0 : 0 ≤ ep
  hep1 : ep < 1
  /-- Rounding only loses, and at most the factor `1 - ep`. -/
  hrnd : ∀ x : ℝ, 0 < x → (1 - ep) * x ≤ A.rnd x ∧ A.rnd x ≤ x
  /-- A failed child pays for the feedback it supplied. -/
  hR1 : C * (ε + lam) ≤ σ * A.r
  /-- A failed node returns bonus `σ` per probe. -/
  hR2 : ∀ T : ℕ, (T = A.r ∨ T = A.r₀) →
    σ * T ≤ ε * T / 2 + Pm * (Real.log κ + T * (Real.log (1 - A.c) + Real.log (1 - ep)))
  /-- The root cannot fail. -/
  hroot : Pm * Real.log (1 + κ * Fintype.card (Expert ι V k D)) < σ * A.r₀

namespace Params

variable (P : Params ι V k D)

theorem δ_pos : 0 < P.δ := lt_of_le_of_lt P.hγ0 P.hγδ

theorem den_pos : 0 < 1 + (P.β - 1) * P.δ := by
  have := P.hβ; have := P.δ_pos; nlinarith

theorem ρ_pos : 0 < P.ρ := by
  have h := P.hρ
  have hden := P.den_pos
  by_contra hcon
  have : P.ρ * (1 + (P.β - 1) * P.δ) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hcon) hden.le
  linarith [P.hβ]

theorem C_pos : 0 < P.C := lt_of_lt_of_le (pow_pos P.ρ_pos k) P.hC1

theorem reserve_bound (l : ℕ) : 1 + reserve D P.ω l ≤ P.Pm := by
  have h1 := reserve_le (D := D) P.ω l P.hω
  have h2 := P.hPm D
  linarith

end Params

/-! ### One probe -/

/-- The contribution of one probe to the parent's weighted bonus: nonnegative when the probe is
light and its child succeeded at the parent's threshold, and at least `ε` otherwise. -/
theorem probe_step (P : Params ι V k D) (H : Hyp ι V) {l : ℕ} (hl : l < D)
    {hist : ℕ → ι → ℝ} {m : Slot ι → ℝ} {t : ℝ} {d₀ : Option (Fin D × Slot ι)}
    (inv : NodeInv P.A.val H P.ρ P.β l hist m t d₀)
    (y : ι → ℝ) (z : ι → Bool) (c : Exec ι (Expert ι V k D)) (wc : Expert ι V k D → ℝ)
    (hwc : ∀ e, 0 < wc e) (hcout : ∀ e, 0 < c.wOut e)
    (hcons : H.ConsistentAt P.A.val c.x z)
    (ih : ∀ (m' : Slot ι → ℝ) (t' : ℝ) (d₀' : Option (Fin D × Slot ι)),
        NodeInv P.A.val H P.ρ P.β (l + 1) (Function.update hist l y) m' t' d₀' →
        (∀ s ∈ H.S, H.surplus P.A.val c.x s ≤ t') ∨
        (P.σ * P.A.r ≤ Psi H P.ω (l + 1) m' d₀' (bonus P.κ wc c.wOut))) :
    ((∀ s ∈ H.S, H.surplus P.A.val c.x s ≤ t) ∧
        0 ≤ cur H m d₀ (fun e : Expert ι V k D =>
              Real.log (1 + P.A.η * gain P.A.val l hist y (feedback y c.x z) e))
            + Psi H P.ω l m d₀ (bonus P.κ wc c.wOut)) ∨
      P.ε ≤ cur H m d₀ (fun e : Expert ι V k D =>
              Real.log (1 + P.A.η * gain P.A.val l hist y (feedback y c.x z) e))
            + Psi H P.ω l m d₀ (bonus P.κ wc c.wOut) := by
  have hL' : ∀ e, 0 ≤ bonus P.κ wc c.wOut e := bonus_nonneg P.hκ0.le hwc hcout
  have hPsiL' : 0 ≤ Psi H P.ω l m d₀ (bonus P.κ wc c.wOut) :=
    Psi_nonneg H m P.ω l d₀ inv.nonneg P.hω hL'
  obtain ⟨m', hm'0, hm'ρ, hchild⟩ :=
    exists_child_dist P.hβ P.δ_pos.le P.hδ1 P.hρ inv y
  -- a failed child pays for the probe
  have hfail : ∀ (d₀' : Option (Fin D × Slot ι)),
      Psi H P.ω (l + 1) m' d₀' (bonus P.κ wc c.wOut)
        ≤ P.C * Psi H P.ω l m d₀ (bonus P.κ wc c.wOut) →
      P.σ * P.A.r ≤ Psi H P.ω (l + 1) m' d₀' (bonus P.κ wc c.wOut) →
      P.ε ≤ cur H m d₀ (fun e : Expert ι V k D =>
              Real.log (1 + P.A.η * gain P.A.val l hist y (feedback y c.x z) e))
            + Psi H P.ω l m d₀ (bonus P.κ wc c.wOut) := by
    intro d₀' htr hf
    have h1 : P.C * (P.ε + P.lam) ≤ P.C * Psi H P.ω l m d₀ (bonus P.κ wc c.wOut) :=
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
      (fun p => cur H m' (some (⟨l, hl⟩, p)) (bonus P.κ wc c.wOut))
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

/-! ### Medians and counting -/

theorem median_success (val : V → ℝ) (H : Hyp ι V) {T : ℕ} (xs : Fin T → ι → ℝ) (x : ι → ℝ)
    (t : ℝ) (hmed : ∀ i, IsMedian (fun τ => xs τ i) (x i))
    (hmaj : T < 2 * (univ.filter
      (fun τ : Fin T => ∀ s ∈ H.S, H.surplus val (xs τ) s ≤ t)).card) :
    ∀ s ∈ H.S, H.surplus val x s ≤ t := by
  rintro ⟨i, h⟩ hs
  cases h with
  | true =>
    have hc : val (H.a (i, true)) - t ≤ x i := by
      apply (hmed i).le_of_majority_ge
      refine lt_of_lt_of_le hmaj (Nat.mul_le_mul_left 2 (Finset.card_le_card ?_))
      intro τ hτ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
      have := hτ _ hs
      simp only [Hyp.surplus, sp, sgn, if_true, one_mul] at this
      linarith
    simp only [Hyp.surplus, sp, sgn, if_true, one_mul]
    linarith
  | false =>
    have hc : x i ≤ t - val (H.a (i, false)) := by
      apply (hmed i).ge_of_majority_le
      refine lt_of_lt_of_le hmaj (Nat.mul_le_mul_left 2 (Finset.card_le_card ?_))
      intro τ hτ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
      have := hτ _ hs
      simp only [Hyp.surplus, sp, sgn] at this
      simp at this
      linarith
    simp only [Hyp.surplus, sp, sgn]
    simp
    linarith

theorem sum_ge_half {T : ℕ} (a : Fin T → ℝ) (good : Fin T → Prop) [DecidablePred good]
    (ε : ℝ) (hε : 0 ≤ ε) (h : ∀ τ, (good τ ∧ 0 ≤ a τ) ∨ ε ≤ a τ)
    (hmaj : 2 * (univ.filter good).card ≤ T) : ε * T / 2 ≤ ∑ τ, a τ := by
  have h1 : ∀ τ, (if good τ then (0 : ℝ) else ε) ≤ a τ := by
    intro τ
    rcases h τ with ⟨hg, h0⟩ | h1
    · simp [hg, h0]
    · split_ifs
      · exact hε.trans h1
      · exact h1
  have h2 : ∑ τ : Fin T, (if good τ then (0 : ℝ) else ε)
      = ε * (univ.filter (fun τ => ¬ good τ)).card := by
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul,
      mul_comm]
  have h3 := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin T))) good
  simp only [Finset.card_univ, Fintype.card_fin] at h3
  have h4 : (T : ℝ) ≤ 2 * ((univ.filter (fun τ => ¬ good τ)).card : ℝ) := by
    have : T ≤ 2 * (univ.filter (fun τ => ¬ good τ)).card := by omega
    exact_mod_cast this
  calc ε * T / 2 ≤ ε * (univ.filter (fun τ => ¬ good τ)).card := by nlinarith
    _ = ∑ τ : Fin T, (if good τ then (0 : ℝ) else ε) := h2.symm
    _ ≤ ∑ τ, a τ := Finset.sum_le_sum (fun τ _ => h1 τ)


/-! ### The main induction -/

/-- **Charging.** For a hypothesis consistent with the run and any node invariant, a node
either succeeds (its prices bring every surplus down to its threshold), or it is internal and
its weighted bonus is at least `σ` per probe (Lemma 5.4 of the preprint). The proposals may be
arbitrary: the market condition `M` is not used here, it only enters through the bound on the
total wealth at the root. -/
theorem node_claim_with (M : MarketCond ι V k D) (P : Params ι V k D) (H : Hyp ι V)
    (X : Exec ι (Expert ι V k D)) :
    ∀ (l : ℕ) (hist : ℕ → ι → ℝ) (wIn : Expert ι V k D → ℝ),
      X.ValidWith M P.A l hist wIn → (∀ e, 0 < wIn e) → X.Consistent P.A.val H →
      ∀ (m : Slot ι → ℝ) (t : ℝ) (d₀ : Option (Fin D × Slot ι)),
        NodeInv P.A.val H P.ρ P.β l hist m t d₀ →
        (∀ s ∈ H.S, H.surplus P.A.val X.x s ≤ t) ∨
        (l < D ∧ P.σ * ((if l = 0 then P.A.r₀ else P.A.r : ℕ) : ℝ)
            ≤ Psi H P.ω l m d₀ (bonus P.κ wIn X.wOut)) := by
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
    have hwealth := node_pos_aux M P.A P.hc0 P.hc1 P.hη0 P.hη1 P.hep1 P.hrnd hv' hpos
      (fun τ => Exec.wealth_pos M P.A P.hc0 P.hc1 P.hη0 P.hη1 P.hep1 P.hrnd (child τ))
    have hwpos : ∀ (τ : Fin T) (e : Expert ι V k D), 0 < w τ e :=
      fun τ e => hwealth τ (Nat.le_of_lt τ.2) e
    have hwcpos : ∀ (τ : Fin T) (e : Expert ι V k D), 0 < P.A.c * w τ e :=
      fun τ e => mul_pos P.hc0 (hwpos τ e)
    have hcout : ∀ (τ : Fin T) (e : Expert ι V k D), 0 < (child τ).wOut e :=
      fun τ => Exec.wealth_pos M P.A P.hc0 P.hc1 P.hη0 P.hη1 P.hep1 P.hrnd (child τ) _ _ _
        (hprobe τ).2.1 (hwcpos τ)
    -- every probe contributes
    have hstepA : ∀ τ : Fin T,
        ((∀ s ∈ H.S, H.surplus P.A.val (child τ).x s ≤ t) ∧
          0 ≤ cur H m d₀ (fun e : Expert ι V k D => Real.log (1 + P.A.η
                * gain P.A.val l hist (y τ) (feedback (y τ) (child τ).x (z τ)) e))
              + Psi H P.ω l m d₀ (bonus P.κ (fun e => P.A.c * w τ e) (child τ).wOut)) ∨
        P.ε ≤ cur H m d₀ (fun e : Expert ι V k D => Real.log (1 + P.A.η
                * gain P.A.val l hist (y τ) (feedback (y τ) (child τ).x (z τ)) e))
              + Psi H P.ω l m d₀ (bonus P.κ (fun e => P.A.c * w τ e) (child τ).wOut) := by
      intro τ
      refine probe_step P H hl inv (y τ) (z τ) (child τ) (fun e => P.A.c * w τ e) (hwcpos τ)
        (hcout τ) (hcons τ).1 ?_
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
                + bonus P.κ (fun e => P.A.c * w τ e) (child τ).wOut e)
          ≤ bonus P.κ wIn (w T) e := by
        intro e
        have hb := bonus_bound_rnd T P.A.c P.A.η P.κ P.ep P.hc0 P.hc1 P.hη0 P.hη1 P.hκ0 P.hκc
          P.hep1 (fun n => w n e)
          (fun τ => gain P.A.val l hist (y τ) (feedback (y τ) (child τ).x (z τ)) e)
          (fun τ => (child τ).wOut e)
          (by rw [hw0]; exact hpos e)
          (fun τ => gain_bounds _ _ _ e _ _)
          (fun τ => hcout τ e)
          (fun τ => by
            have hstep := (hprobe τ).2.2 e
            have hg := (gain_bounds P.A.val l hist e (y τ)
              (feedback (y τ) (child τ).x (z τ))).1
            have h1 : 0 < 1 + P.A.η * gain P.A.val l hist (y τ)
                (feedback (y τ) (child τ).x (z τ)) e := by
              have := P.hη0; have := P.hη1; nlinarith
            have hX : 0 < (1 - P.A.c) * w τ e
                * (1 + P.A.η * gain P.A.val l hist (y τ)
                    (feedback (y τ) (child τ).x (z τ)) e) + (child τ).wOut e :=
              add_pos (mul_pos (mul_pos (by linarith [P.hc1]) (hwpos τ e)) h1) (hcout τ e)
            rw [hstep]
            exact (P.hrnd _ hX).1)
        simp only [bonus]
        rw [← hw0]
        exact hb
      have hPsi := Psi_mono H m P.ω l d₀ inv.nonneg P.hω hbonus
      rw [Psi_add H m P.ω l d₀ (fun _ => Real.log P.κ + T * (Real.log (1 - P.A.c) + Real.log (1 - P.ep)))
          (fun e => ∑ τ : Fin T, (Real.log (1 + P.A.η
                  * gain P.A.val l hist (y τ) (feedback (y τ) (child τ).x (z τ)) e)
                + bonus P.κ (fun e => P.A.c * w τ e) (child τ).wOut e)),
        Psi_const H m P.ω l d₀ inv.sum_one, Psi_sum] at hPsi
      have hsumA : ∑ τ : Fin T, Psi H P.ω l m d₀ (fun e : Expert ι V k D =>
            Real.log (1 + P.A.η
                  * gain P.A.val l hist (y τ) (feedback (y τ) (child τ).x (z τ)) e)
                + bonus P.κ (fun e => P.A.c * w τ e) (child τ).wOut e)
          = ∑ τ : Fin T, (cur H m d₀ (fun e : Expert ι V k D => Real.log (1 + P.A.η
                * gain P.A.val l hist (y τ) (feedback (y τ) (child τ).x (z τ)) e))
              + Psi H P.ω l m d₀ (bonus P.κ (fun e => P.A.c * w τ e) (child τ).wOut)) := by
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
      show P.σ * (T : ℝ) ≤ Psi H P.ω l m d₀ (bonus P.κ wIn (w T))
      linarith

/-- The charging lemma for valid runs (exact market). -/
theorem node_claim (P : Params ι V k D) (H : Hyp ι V) (X : Exec ι (Expert ι V k D)) :
    ∀ (l : ℕ) (hist : ℕ → ι → ℝ) (wIn : Expert ι V k D → ℝ),
      X.Valid P.A l hist wIn → (∀ e, 0 < wIn e) → X.Consistent P.A.val H →
      ∀ (m : Slot ι → ℝ) (t : ℝ) (d₀ : Option (Fin D × Slot ι)),
        NodeInv P.A.val H P.ρ P.β l hist m t d₀ →
        (∀ s ∈ H.S, H.surplus P.A.val X.x s ≤ t) ∨
        (l < D ∧ P.σ * ((if l = 0 then P.A.r₀ else P.A.r : ℕ) : ℝ)
            ≤ Psi H P.ω l m d₀ (bonus P.κ wIn X.wOut)) :=
  fun l hist wIn hv =>
    node_claim_with (exactMarket P.A.val) P H X l hist wIn
      ((Exec.validWith_exact_iff P.A X l hist wIn).2 hv)

/-! ### The theorem -/

/-- **Extremal prices via the recursive market.** Let `X` be any valid run of the algorithm
from the root with unit initial wealth, and let `H` be any hypothesis consistent with every
label the run received. Then the returned prices meet every demand of `H`:
`val (a s) ≤ ± x_i` for every slot `s = (i, ±)` of `H`. -/
theorem price_search_correct (P : Params ι V k D) (X : Exec ι (Expert ι V k D))
    (hist₀ : ℕ → ι → ℝ) (hX : X.Valid P.A 0 hist₀ (fun _ => 1)) (H : Hyp ι V)
    (hH : X.Consistent P.A.val H) :
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
  rcases node_claim P H X 0 hist₀ _ hX (fun _ => one_pos) hH _ 0 none inv with h | ⟨-, hf⟩
  · exact h
  · exfalso
    simp only [if_true] at hf
    obtain ⟨hout, hsum⟩ :=
      Exec.wealth P.A P.hc0 P.hc1 P.hη0 P.hη1 P.hep1 P.hrnd X 0 hist₀ _ hX (fun _ => one_pos)
    have hE : ∑ _e : Expert ι V k D, (1 : ℝ) = Fintype.card (Expert ι V k D) := by simp
    have hcardE : (0 : ℝ) ≤ Fintype.card (Expert ι V k D) := Nat.cast_nonneg _
    have hb : ∀ e : Expert ι V k D, bonus P.κ (fun _ => 1) X.wOut e
        ≤ Real.log (1 + P.κ * Fintype.card (Expert ι V k D)) := by
      intro e
      have h1 : X.wOut e ≤ ∑ e, X.wOut e :=
        Finset.single_le_sum (fun i _ => (hout i).le) (Finset.mem_univ e)
      have h2 : X.wOut e ≤ Fintype.card (Expert ι V k D) := by linarith
      unfold bonus
      rw [div_one]
      apply Real.log_le_log
      · have := hout e; have := P.hκ0; nlinarith
      · have := P.hκ0; nlinarith
    have hPsi := Psi_mono H _ P.ω 0 none inv.nonneg P.hω hb
    rw [Psi_const H _ P.ω 0 none inv.sum_one] at hPsi
    have hres := P.reserve_bound (k := k) 0
    have hres0 := reserve_nonneg (D := D) P.ω 0 P.hω
    have hlog0 : 0 ≤ Real.log (1 + P.κ * Fintype.card (Expert ι V k D)) :=
      Real.log_nonneg (by have := P.hκ0; nlinarith)
    have hroot := P.hroot
    nlinarith

end SPLP
