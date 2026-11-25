import Mathlib
import SPLP.Instances

/-!
# Approximately cleared markets

In a valid run (`Exec.Valid`) every proposal minimizes the market potential for the true
wealth. Here the proposal may minimize the potential for *any* nonnegative weights `w'` whose
total distance from the true wealth is at most `ζ` times the total wealth
(`approxMarket`, `Exec.ValidWith`). This is what a market step computes when it works with
wealth rounded to a common grid, or with approximate sums of wealth over cells.

* `approx_gain_le`: such a proposal lets the experts gain at most `ζ` times the total wealth.
* `Exec.wealth_approx`: total wealth grows by at most the factor `(1 + η ζ)` per probe.
* `price_search_correct_approx`: the price search stays correct when the root condition
  absorbs the term `Pm · queries · η ζ`. The charging argument (`node_claim_with`) does not
  use the market condition at all.
* `Consts.price_search_approx_double`: for good constants, doubling the number of root probes
  allows `ζ = σ / (4 Pm η (2N)^e)`, a tolerance depending only on the number of coordinates,
  with at most `4 r₀ (2N)^e` label queries. Wealth is still rounded after every update
  (`Alg.rnd`), so the two relaxations compose.
* `price_search_k4_approx`: the arity-4 instance, exponent `46`, `ζ ≥ 2^-12 / (2N)^46`.
-/

set_option linter.unusedSectionVars false

namespace SPLP

open Finset

variable {ι V : Type*} {k D : ℕ} [Fintype ι] [DecidableEq ι] [Fintype V]

/-! ### One approximately cleared market -/

/-- **Approximate market lemma.** If the proposal minimizes the potential for weights within
total distance `ζ · ∑ w` of the true wealth `w`, the aggregate market gain under the true
wealth is at most `ζ · ∑ w`, for every feedback. -/
theorem approx_gain_le (val : V → ℝ) (l : ℕ) (hist : ℕ → ι → ℝ) (w : Expert ι V k D → ℝ)
    (y : ι → ℝ) (v : ι → Bool) {ζ : ℝ} (h : approxMarket val ζ l hist w y) :
    ∑ e, w e * gain val l hist y v e ≤ ζ * ∑ e, w e := by
  obtain ⟨w', hw', hdist, hmin⟩ := h
  have hmarket : ∑ e, w' e * gain val l hist y v e ≤ 0 :=
    market_no_profit (bidOf val l hist) (dirOf val l hist) w' hw' y hmin (vreal v) _
      (fun e o ho => minPay_le _ _ _ _ _ o ho)
  have hdiff : ∀ e, w e * gain val l hist y v e
      ≤ w' e * gain val l hist y v e + |w' e - w e| := by
    intro e
    have hg := gain_bounds val l hist e y v
    have h1 : (w e - w' e) * gain val l hist y v e ≤ |w' e - w e| :=
      calc (w e - w' e) * gain val l hist y v e
          ≤ |(w e - w' e) * gain val l hist y v e| := le_abs_self _
        _ = |w e - w' e| * |gain val l hist y v e| := abs_mul _ _
        _ ≤ |w e - w' e| * 1 :=
            mul_le_mul_of_nonneg_left (abs_le.2 hg) (abs_nonneg _)
        _ = |w' e - w e| := by rw [mul_one, abs_sub_comm]
    linarith
  calc ∑ e, w e * gain val l hist y v e
      ≤ ∑ e, (w' e * gain val l hist y v e + |w' e - w e|) :=
        Finset.sum_le_sum (fun e _ => hdiff e)
    _ = ∑ e, w' e * gain val l hist y v e + ∑ e, |w' e - w e| := Finset.sum_add_distrib
    _ ≤ ζ * ∑ e, w e := by linarith

/-! ### Total wealth grows slowly -/

theorem node_wealth_approx_aux (A : Alg V) {ζ : ℝ} (hζ : 0 ≤ ζ) (hc0 : 0 < A.c)
    (hc1 : A.c < 1) (hη0 : 0 < A.η) (hη1 : A.η < 1) {ep : ℝ} (hep1 : ep < 1)
    (hrnd : ∀ x : ℝ, 0 < x → (1 - ep) * x ≤ A.rnd x ∧ A.rnd x ≤ x) {T : ℕ}
    {y : Fin T → ι → ℝ} {z : Fin T → ι → Bool}
    {child : Fin T → Exec ι (Expert ι V k D)} {w : ℕ → Expert ι V k D → ℝ} {x : ι → ℝ}
    {l : ℕ} {hist : ℕ → ι → ℝ} {wIn : Expert ι V k D → ℝ}
    (hv : (Exec.node T y z child w x).ValidWith (approxMarket A.val ζ) A l hist wIn)
    (hpos : ∀ e, 0 < wIn e)
    (hch : ∀ τ : Fin T, ∀ (l : ℕ) (hist : ℕ → ι → ℝ) (wIn : Expert ι V k D → ℝ),
        (child τ).ValidWith (approxMarket A.val ζ) A l hist wIn → (∀ e, 0 < wIn e) →
        ∑ e, (child τ).wOut e ≤ (1 + A.η * ζ) ^ (child τ).queries * ∑ e, wIn e) :
    ∀ n, n ≤ T → ∑ e, w n e
      ≤ (1 + A.η * ζ) ^ (∑ j ∈ range n, if h : j < T then 1 + (child ⟨j, h⟩).queries else 0)
        * ∑ e, wIn e := by
  have hwpos := node_pos_aux (approxMarket A.val ζ) A hc0 hc1 hη0 hη1 hep1 hrnd hv hpos
    (fun τ => Exec.wealth_pos (approxMarket A.val ζ) A hc0 hc1 hη0 hη1 hep1 hrnd (child τ))
  obtain ⟨-, -, hw0, hprobe, -⟩ := hv
  have hg1 : 1 ≤ 1 + A.η * ζ := by nlinarith
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
    have hcout := Exec.wealth_pos (approxMarket A.val ζ) A hc0 hc1 hη0 hη1 hep1 hrnd
      (child ⟨n, hn'⟩) _ _ _ hchild hcpos
    have hcsum := hch ⟨n, hn'⟩ _ _ _ hchild hcpos
    have hgb : ∀ e : Expert ι V k D, -1 ≤ gain A.val l hist (y ⟨n, hn'⟩)
          (feedback (y ⟨n, hn'⟩) (child ⟨n, hn'⟩).x (z ⟨n, hn'⟩)) e :=
      fun e => (gain_bounds _ _ _ e _ _).1
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
        nlinarith [hgb e]
      exact add_pos (mul_pos (mul_pos (by linarith) (hposn e)) h1) (hcout e)
    have hmarket : ∑ e, ((1 - A.c) * w n e) * gain A.val l hist (y ⟨n, hn'⟩)
        (feedback (y ⟨n, hn'⟩) (child ⟨n, hn'⟩).x (z ⟨n, hn'⟩)) e
        ≤ ζ * ∑ e, (1 - A.c) * w n e :=
      approx_gain_le A.val l hist (fun e => (1 - A.c) * w n e) (y ⟨n, hn'⟩) _ hmk
    have hrew : ∀ e, w (n + 1) e ≤ (1 - A.c) * w n e
        + A.η * (((1 - A.c) * w n e) * gain A.val l hist (y ⟨n, hn'⟩)
            (feedback (y ⟨n, hn'⟩) (child ⟨n, hn'⟩).x (z ⟨n, hn'⟩)) e)
        + (child ⟨n, hn'⟩).wOut e := fun e => by
      rw [hs e]
      refine (hrnd _ (hXpos e)).2.trans (le_of_eq ?_)
      ring
    have hS0 : 0 ≤ ∑ e, w n e := Finset.sum_nonneg (fun e _ => (hposn e).le)
    have hG1 : 1 ≤ (1 + A.η * ζ) ^ (child ⟨n, hn'⟩).queries := one_le_pow₀ hg1
    have hcs : ∑ e, (child ⟨n, hn'⟩).wOut e
        ≤ (1 + A.η * ζ) ^ (child ⟨n, hn'⟩).queries * (A.c * ∑ e, w n e) := by
      rw [Finset.mul_sum]; exact hcsum
    have hmk' : ∑ e, ((1 - A.c) * w n e) * gain A.val l hist (y ⟨n, hn'⟩)
        (feedback (y ⟨n, hn'⟩) (child ⟨n, hn'⟩).x (z ⟨n, hn'⟩)) e
        ≤ ζ * ((1 - A.c) * ∑ e, w n e) := by
      rw [Finset.mul_sum]; exact hmarket
    have hstepsum : ∑ e, w (n + 1) e
        ≤ (1 + A.η * ζ) ^ (1 + (child ⟨n, hn'⟩).queries) * ∑ e, w n e := by
      have e1 : 0 ≤ (∑ e, w n e) * ((1 - A.c) * (1 + A.η * ζ))
          * ((1 + A.η * ζ) ^ (child ⟨n, hn'⟩).queries - 1) :=
        mul_nonneg (mul_nonneg hS0 (mul_nonneg (by linarith) (by linarith))) (by linarith)
      have e2 : 0 ≤ (∑ e, w n e) * (A.c * (1 + A.η * ζ) ^ (child ⟨n, hn'⟩).queries)
          * (A.η * ζ) :=
        mul_nonneg (mul_nonneg hS0 (mul_nonneg hc0.le (by linarith)))
          (mul_nonneg hη0.le hζ)
      have e3 : A.η * ∑ e, ((1 - A.c) * w n e) * gain A.val l hist (y ⟨n, hn'⟩)
          (feedback (y ⟨n, hn'⟩) (child ⟨n, hn'⟩).x (z ⟨n, hn'⟩)) e
          ≤ A.η * (ζ * ((1 - A.c) * ∑ e, w n e)) :=
        mul_le_mul_of_nonneg_left hmk' hη0.le
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
        _ ≤ (1 + A.η * ζ) ^ (1 + (child ⟨n, hn'⟩).queries) * ∑ e, w n e := by
            rw [pow_add, pow_one]
            nlinarith [e1, e2, e3, hcs]
    rw [Finset.sum_range_succ, dif_pos hn', pow_add, mul_assoc]
    calc ∑ e, w (n + 1) e
        ≤ (1 + A.η * ζ) ^ (1 + (child ⟨n, hn'⟩).queries) * ∑ e, w n e := hstepsum
      _ ≤ (1 + A.η * ζ) ^ (1 + (child ⟨n, hn'⟩).queries)
          * ((1 + A.η * ζ) ^ (∑ j ∈ range n,
              if h : j < T then 1 + (child ⟨j, h⟩).queries else 0) * ∑ e, wIn e) :=
          mul_le_mul_of_nonneg_left hsumn (pow_nonneg (by linarith) _)
      _ = (1 + A.η * ζ) ^ (∑ j ∈ range n,
              if h : j < T then 1 + (child ⟨j, h⟩).queries else 0)
          * ((1 + A.η * ζ) ^ (1 + (child ⟨n, hn'⟩).queries) * ∑ e, wIn e) := by ring

/-- **Wealth under approximate markets.** Every node returns total wealth at most
`(1 + η ζ)^queries` times its input total. -/
theorem Exec.wealth_approx (A : Alg V) {ζ : ℝ} (hζ : 0 ≤ ζ) (hc0 : 0 < A.c) (hc1 : A.c < 1)
    (hη0 : 0 < A.η) (hη1 : A.η < 1) {ep : ℝ} (hep1 : ep < 1)
    (hrnd : ∀ x : ℝ, 0 < x → (1 - ep) * x ≤ A.rnd x ∧ A.rnd x ≤ x)
    (X : Exec ι (Expert ι V k D)) :
    ∀ (l : ℕ) (hist : ℕ → ι → ℝ) (wIn : Expert ι V k D → ℝ),
      X.ValidWith (approxMarket A.val ζ) A l hist wIn → (∀ e, 0 < wIn e) →
      ∑ e, X.wOut e ≤ (1 + A.η * ζ) ^ X.queries * ∑ e, wIn e := by
  induction X with
  | leaf x wOut =>
    intro l hist wIn hv hpos
    obtain ⟨-, hw, -⟩ := hv
    simp [Exec.wOut, Exec.queries, hw]
  | node T y z child w x ih =>
    intro l hist wIn hv hpos
    have h := node_wealth_approx_aux A hζ hc0 hc1 hη0 hη1 hep1 hrnd hv hpos ih T le_rfl
    have hq : (∑ j ∈ range T, if h : j < T then 1 + (child ⟨j, h⟩).queries else 0)
        = ∑ τ : Fin T, (1 + (child τ).queries) := by
      rw [← Fin.sum_univ_eq_sum_range
        (fun j => if h : j < T then 1 + (child ⟨j, h⟩).queries else 0) T]
      exact Finset.sum_congr rfl (fun τ _ => dif_pos τ.2)
    rw [hq] at h
    exact h

/-! ### Exact runs are approximate runs -/

/-- A valid run with positive input wealth is a run with approximately cleared markets, for
every tolerance `ζ ≥ 0`. -/
theorem Exec.Valid.approx (A : Alg V) {ζ : ℝ} (hζ : 0 ≤ ζ) (hc0 : 0 < A.c) (hc1 : A.c < 1)
    (hη0 : 0 < A.η) (hη1 : A.η < 1) {ep : ℝ} (hep1 : ep < 1)
    (hrnd : ∀ x : ℝ, 0 < x → (1 - ep) * x ≤ A.rnd x ∧ A.rnd x ≤ x)
    (X : Exec ι (Expert ι V k D)) :
    ∀ (l : ℕ) (hist : ℕ → ι → ℝ) (wIn : Expert ι V k D → ℝ), X.Valid A l hist wIn →
      (∀ e, 0 < wIn e) → X.ValidWith (approxMarket A.val ζ) A l hist wIn := by
  induction X with
  | leaf x wOut =>
    intro l hist wIn hv _
    exact hv
  | node T y z child w x ih =>
    intro l hist wIn hv hpos
    have hwealth := node_wealth_aux A hc0 hc1 hη0 hη1 hep1 hrnd hv hpos
      (fun τ => Exec.wealth A hc0 hc1 hη0 hη1 hep1 hrnd (child τ))
    obtain ⟨hl, hT, hw0, hprobe, hmed⟩ := hv
    refine ⟨hl, hT, hw0, fun τ => ?_, hmed⟩
    have hposτ : ∀ e, 0 < w τ e := (hwealth τ (Nat.le_of_lt τ.2)).1
    refine ⟨⟨fun e => (1 - A.c) * w τ e,
        fun e => mul_nonneg (by linarith) (hposτ e).le, ?_, (hprobe τ).1⟩,
      ih τ _ _ _ (hprobe τ).2.1 (fun e => mul_pos hc0 (hposτ e)), (hprobe τ).2.2⟩
    simp only [sub_self, abs_zero, Finset.sum_const_zero]
    exact mul_nonneg hζ
      (Finset.sum_nonneg (fun e _ => mul_nonneg (by linarith) (hposτ e).le))

/-- With tolerance `0` an approximately cleared market is exactly cleared. -/
theorem exactMarket_of_approx_zero (val : V → ℝ) (l : ℕ) (hist : ℕ → ι → ℝ)
    (w : Expert ι V k D → ℝ) (y : ι → ℝ) (h : approxMarket val 0 l hist w y) :
    exactMarket val l hist w y := by
  obtain ⟨w', -, hdist, hmin⟩ := h
  rw [zero_mul] at hdist
  have h0 : ∀ e, w' e = w e := by
    intro e
    have h1 : |w' e - w e| ≤ ∑ e, |w' e - w e| :=
      Finset.single_le_sum (f := fun e => |w' e - w e|) (fun i _ => abs_nonneg _)
        (Finset.mem_univ e)
    have h2 : |w' e - w e| = 0 := le_antisymm (h1.trans hdist) (abs_nonneg _)
    linarith [abs_eq_zero.1 h2]
  have hw : w' = w := funext h0
  rw [hw] at hmin
  exact hmin

/-- With tolerance `0` the approximate runs are exactly the valid runs. -/
theorem Exec.valid_of_approx_zero (A : Alg V) (X : Exec ι (Expert ι V k D)) (l : ℕ)
    (hist : ℕ → ι → ℝ) (wIn : Expert ι V k D → ℝ)
    (h : X.ValidWith (approxMarket A.val 0) A l hist wIn) : X.Valid A l hist wIn :=
  (Exec.validWith_exact_iff A X l hist wIn).1
    (Exec.ValidWith.mono (exactMarket_of_approx_zero A.val) A X l hist wIn h)

/-! ### Correctness -/

/-- **Price search with approximately cleared markets.** Let `X` be a run from the root with
unit initial wealth in which every proposal minimizes the potential for weights within total
distance `ζ` times the total wealth of the true wealth. If the root makes enough probes to
absorb the wealth created by the approximation, the returned prices meet every demand of
every hypothesis consistent with the labels received. For `ζ = 0` the extra condition is
`Params.hroot`. -/
theorem price_search_correct_approx (P : Params ι V k D) {ζ : ℝ} (hζ : 0 ≤ ζ)
    (X : Exec ι (Expert ι V k D)) (hist₀ : ℕ → ι → ℝ)
    (hX : X.ValidWith (approxMarket P.A.val ζ) P.A 0 hist₀ (fun _ => 1))
    (hroot : P.Pm * (Real.log (1 + P.κ * Fintype.card (Expert ι V k D))
        + X.queries * (P.A.η * ζ)) < P.σ * P.A.r₀)
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
  rcases node_claim_with (approxMarket P.A.val ζ) P H X 0 hist₀ _ hX (fun _ => one_pos) hH
      _ 0 none inv with h | ⟨-, hf⟩
  · exact h
  · exfalso
    simp only [if_true] at hf
    have hout := Exec.wealth_pos (approxMarket P.A.val ζ) P.A P.hc0 P.hc1 P.hη0 P.hη1 P.hep1
      P.hrnd X 0 hist₀ _ hX (fun _ => one_pos)
    have hsum := Exec.wealth_approx P.A hζ P.hc0 P.hc1 P.hη0 P.hη1 P.hep1 P.hrnd X 0 hist₀ _
      hX (fun _ => one_pos)
    have hE : ∑ _e : Expert ι V k D, (1 : ℝ) = Fintype.card (Expert ι V k D) := by simp
    rw [hE] at hsum
    have hcardE : (0 : ℝ) ≤ Fintype.card (Expert ι V k D) := Nat.cast_nonneg _
    have hg0 : 0 ≤ P.A.η * ζ := mul_nonneg P.hη0.le hζ
    have hg1 : 1 ≤ 1 + P.A.η * ζ := by linarith
    have hG1 : 1 ≤ (1 + P.A.η * ζ) ^ X.queries := one_le_pow₀ hg1
    have hGpos : 0 < (1 + P.A.η * ζ) ^ X.queries := by linarith
    have hκ0 := P.hκ0
    have hκE : 0 ≤ P.κ * Fintype.card (Expert ι V k D) := mul_nonneg hκ0.le hcardE
    have hlogG : Real.log ((1 + P.A.η * ζ) ^ X.queries) ≤ X.queries * (P.A.η * ζ) := by
      rw [Real.log_pow]
      have := Real.log_le_sub_one_of_pos (x := 1 + P.A.η * ζ) (by linarith)
      exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    have hb : ∀ e : Expert ι V k D, bonus P.κ (fun _ => 1) X.wOut e
        ≤ Real.log (1 + P.κ * Fintype.card (Expert ι V k D)) + X.queries * (P.A.η * ζ) := by
      intro e
      have h1 : X.wOut e ≤ ∑ e, X.wOut e :=
        Finset.single_le_sum (fun i _ => (hout i).le) (Finset.mem_univ e)
      have h2 : X.wOut e
          ≤ (1 + P.A.η * ζ) ^ X.queries * Fintype.card (Expert ι V k D) := h1.trans hsum
      have h3 : 1 + P.κ * (X.wOut e / 1)
          ≤ (1 + P.A.η * ζ) ^ X.queries * (1 + P.κ * Fintype.card (Expert ι V k D)) := by
        rw [div_one]
        have := mul_le_mul_of_nonneg_left h2 hκ0.le
        nlinarith
      unfold bonus
      calc Real.log (1 + P.κ * (X.wOut e / 1))
          ≤ Real.log ((1 + P.A.η * ζ) ^ X.queries
              * (1 + P.κ * Fintype.card (Expert ι V k D))) := by
            apply Real.log_le_log _ h3
            have := hout e
            rw [div_one]
            nlinarith
        _ = Real.log ((1 + P.A.η * ζ) ^ X.queries)
            + Real.log (1 + P.κ * Fintype.card (Expert ι V k D)) :=
            Real.log_mul hGpos.ne' (by linarith : (1 + P.κ * Fintype.card (Expert ι V k D)) ≠ 0)
        _ ≤ Real.log (1 + P.κ * Fintype.card (Expert ι V k D))
            + X.queries * (P.A.η * ζ) := by linarith
    have hPsi := Psi_mono H _ P.ω 0 none inv.nonneg P.hω hb
    rw [Psi_const H _ P.ω 0 none inv.sum_one] at hPsi
    have hres := P.reserve_bound (k := k) 0
    have hres0 := reserve_nonneg (D := D) P.ω 0 P.hω
    have hB0 : 0 ≤ Real.log (1 + P.κ * Fintype.card (Expert ι V k D))
        + X.queries * (P.A.η * ζ) :=
      add_nonneg (Real.log_nonneg (by linarith))
        (mul_nonneg (Nat.cast_nonneg _) hg0)
    nlinarith

/-- The exact theorem is the case `ζ = 0`. -/
theorem price_search_correct_of_approx (P : Params ι V k D) (X : Exec ι (Expert ι V k D))
    (hist₀ : ℕ → ι → ℝ) (hX : X.Valid P.A 0 hist₀ (fun _ => 1)) (H : Hyp ι V)
    (hH : X.Consistent P.A.val H) :
    ∀ s ∈ H.S, H.surplus P.A.val X.x s ≤ 0 :=
  price_search_correct_approx P le_rfl X hist₀
    (Exec.Valid.approx P.A le_rfl P.hc0 P.hc1 P.hη0 P.hη1 P.hep1 P.hrnd X 0 hist₀ _ hX
      (fun _ => one_pos))
    (by simpa using P.hroot) H hH

/-! ### Explicit constants -/

namespace Consts

variable {k : ℕ}

/-- The analysis parameters of good constants with `r₀'` probes at the root, for any `r₀'` at
least the exact number `K.r₀`. -/
noncomputable def paramsRoot (K : Consts k) (hK : K.Good) (ι V : Type*) [Fintype ι]
    [DecidableEq ι] [Fintype V] (val : V → ℝ) (r₀' : ℕ)
    (h : K.r₀ ι V (K.depth hK (Fintype.card ι)) ≤ r₀') :
    Params ι V k (K.depth hK (Fintype.card ι)) :=
  { K.params hK ι V val with
    A := { val := val, r := K.r, r₀ := r₀', c := (K.c : ℝ), η := (K.η : ℝ), rnd := fl K.p }
    hR2 := by
      intro T hT
      have hr : K.r ≤ K.r₀ ι V (K.depth hK (Fintype.card ι)) := le_max_left _ _
      rcases hT with rfl | rfl
      · exact hR2_real hK _ le_rfl
      · exact hR2_real hK _ (hr.trans h)
    hroot := by
      have h1 := hroot_real (ι := ι) (V := V) hK (K.depth hK (Fintype.card ι))
      have h2 : (K.r₀ ι V (K.depth hK (Fintype.card ι)) : ℝ) ≤ (r₀' : ℝ) := by
        exact_mod_cast h
      have h3 := mul_le_mul_of_nonneg_left h2 (σ_pos_real hK).le
      exact lt_of_lt_of_le h1 h3 }

/-- The algorithm of good constants with `r₀'` probes at the root. -/
noncomputable def algRoot (K : Consts k) (ι V : Type*) [Fintype ι] [DecidableEq ι]
    [Fintype V] (val : V → ℝ) (r₀' : ℕ) : Alg V :=
  { val := val, r := K.r, r₀ := r₀', c := (K.c : ℝ), η := (K.η : ℝ), rnd := fl K.p }

/-- **Approximate markets with explicit constants.** With `r₀' ≥ r₀` probes at the root and a
tolerance `ζ ≥ 0` satisfying `Pm · η ζ · 2 r₀' (2N)^e ≤ σ (r₀' - r₀)`, every run with
approximately cleared markets (and rounded wealth) meets all demands of every consistent
hypothesis and makes at most `2 r₀' (2N)^e` label queries. -/
theorem price_search_approx (K : Consts k) (hK : K.Good) (e : ℕ)
    (he : ((K.r : ℚ)) ^ 2 ≤ (K.ρ ^ 2 / K.β) ^ e)
    {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V] [Nonempty ι] (val : V → ℝ)
    (r₀' : ℕ) (hr₀ : K.r₀ ι V (K.depth hK (Fintype.card ι)) ≤ r₀') {ζ : ℝ} (hζ0 : 0 ≤ ζ)
    (hζ : (K.Pm : ℝ) * ((K.η : ℝ) * ζ) * ((2 * r₀' * (2 * Fintype.card ι) ^ e : ℕ) : ℝ)
      ≤ (K.σ : ℝ) * ((r₀' : ℝ) - K.r₀ ι V (K.depth hK (Fintype.card ι))))
    (X : Exec ι (Expert ι V k (K.depth hK (Fintype.card ι)))) (hist₀ : ℕ → ι → ℝ)
    (hX : X.ValidWith (approxMarket val ζ) (K.algRoot ι V val r₀') 0 hist₀ (fun _ => 1)) :
    (∀ H : Hyp ι V, X.Consistent val H → ∀ s ∈ H.S, val (H.a s) ≤ sp X.x s) ∧
    X.queries ≤ 2 * r₀' * (2 * Fintype.card ι) ^ e := by
  have hN : 1 ≤ 2 * Fintype.card ι := by
    have := Fintype.card_pos (α := ι)
    omega
  have hD := depth_pos (K.b_real hK) hN
  have hq : X.queries ≤ 2 * r₀' * (2 * Fintype.card ι) ^ e := by
    have hq := queries_root_le_with (approxMarket val ζ) (K.algRoot ι V val r₀') hK.hr X
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
  have hqR : (X.queries : ℝ) ≤ ((2 * r₀' * (2 * Fintype.card ι) ^ e : ℕ) : ℝ) := by
    exact_mod_cast hq
  have hc : 0 ≤ (K.Pm : ℝ) * ((K.η : ℝ) * ζ) :=
    mul_nonneg (Pm_pos_real hK).le (mul_nonneg (η_pos_real hK).le hζ0)
  have hqc := mul_le_mul_of_nonneg_left hqR hc
  have h := price_search_correct_approx (K.paramsRoot hK ι V val r₀' hr₀) hζ0 X hist₀ hX
    (by
      show (K.Pm : ℝ) * (Real.log (1 + K.κ * Fintype.card (Expert ι V k _))
        + X.queries * ((K.η : ℝ) * ζ)) < (K.σ : ℝ) * (r₀' : ℝ)
      nlinarith) H hH s hs
  simp only [Hyp.surplus] at h
  have hval : (K.paramsRoot hK ι V val r₀' hr₀).A.val = val := rfl
  rw [hval] at h
  linarith

/-- The tolerance allowed when the number of root probes is doubled: it depends only on the
constants and on the number `N` of coordinates. -/
noncomputable def ζ (K : Consts k) (e N : ℕ) : ℝ :=
  (K.σ : ℝ) / (4 * (K.Pm : ℝ) * (K.η : ℝ) * ((2 * N) ^ e : ℕ))

theorem ζ_pos (K : Consts k) (hK : K.Good) (e : ℕ) {N : ℕ} (hN : 0 < N) : 0 < K.ζ e N := by
  unfold ζ
  have h1 := σ_pos_real hK
  have h2 := Pm_pos_real hK
  have h3 := η_pos_real hK
  have h4 : (0 : ℝ) < ((2 * N) ^ e : ℕ) := by
    have : 0 < (2 * N) ^ e := Nat.pow_pos (by omega)
    exact_mod_cast this
  positivity

/-- **Doubling the root.** With `2 r₀` probes at the root, every run whose proposals minimize
the potential for weights within total distance `ζ · (total wealth)` of the true wealth,
`ζ = σ / (4 Pm η (2N)^e)`, meets all demands of every consistent hypothesis and makes at most
`4 r₀ (2N)^e` label queries. -/
theorem price_search_approx_double (K : Consts k) (hK : K.Good) (e : ℕ)
    (he : ((K.r : ℚ)) ^ 2 ≤ (K.ρ ^ 2 / K.β) ^ e)
    {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V] [Nonempty ι] (val : V → ℝ)
    (X : Exec ι (Expert ι V k (K.depth hK (Fintype.card ι)))) (hist₀ : ℕ → ι → ℝ)
    (hX : X.ValidWith (approxMarket val (K.ζ e (Fintype.card ι)))
      (K.algRoot ι V val (2 * K.r₀ ι V (K.depth hK (Fintype.card ι)))) 0 hist₀
      (fun _ => 1)) :
    (∀ H : Hyp ι V, X.Consistent val H → ∀ s ∈ H.S, val (H.a s) ≤ sp X.x s) ∧
    X.queries ≤ 4 * K.r₀ ι V (K.depth hK (Fintype.card ι)) * (2 * Fintype.card ι) ^ e := by
  have hN : 0 < Fintype.card ι := Fintype.card_pos
  have h := K.price_search_approx hK e he val (2 * K.r₀ ι V (K.depth hK (Fintype.card ι)))
    (by omega) (K.ζ_pos hK e hN).le (by
      have h1 := σ_pos_real hK
      have h2 := Pm_pos_real hK
      have h3 := η_pos_real hK
      have h4 : (0 : ℝ) < ((2 * Fintype.card ι) ^ e : ℕ) := by
        have : 0 < (2 * Fintype.card ι) ^ e := Nat.pow_pos (by omega)
        exact_mod_cast this
      unfold ζ
      push_cast
      have h4' : (0 : ℝ) < (2 * (Fintype.card ι : ℝ)) ^ e := by
        have := h4
        push_cast at this
        exact this
      field_simp
      ring_nf
      exact le_rfl) X hist₀ hX
  refine ⟨h.1, h.2.trans (le_of_eq ?_)⟩
  ring

end Consts

/-! ### Arity 4 -/

variable [Nonempty ι]

/-- For the arity-4 constants the tolerance is at least `2^-12 / (2N)^46`. -/
theorem K4_ζ_ge (N : ℕ) (hN : 0 < N) :
    1 / (4096 * (((2 * N) ^ 46 : ℕ) : ℝ)) ≤ K4.ζ 46 N := by
  have h4 : (0 : ℝ) < ((2 * N) ^ 46 : ℕ) := by
    have : 0 < (2 * N) ^ 46 := Nat.pow_pos (by omega)
    exact_mod_cast this
  have hc : (1 : ℝ) / 4096 ≤ (K4.σ : ℝ) / (4 * (K4.Pm : ℝ) * (K4.η : ℝ)) := by
    have hq : (1 : ℚ) / 4096 ≤ K4.σ / (4 * K4.Pm * K4.η) := by
      norm_num [K4, Consts.σ, Consts.ε, Consts.q, Consts.lp, Consts.lam, Consts.Pm]
    have hr : ((1 / 4096 : ℚ) : ℝ) ≤ ((K4.σ / (4 * K4.Pm * K4.η) : ℚ) : ℝ) := by
      exact_mod_cast hq
    push_cast at hr
    exact hr
  unfold Consts.ζ
  have hsplit : (K4.σ : ℝ) / (4 * (K4.Pm : ℝ) * (K4.η : ℝ) * (((2 * N) ^ 46 : ℕ) : ℝ))
      = (K4.σ : ℝ) / (4 * (K4.Pm : ℝ) * (K4.η : ℝ)) / (((2 * N) ^ 46 : ℕ) : ℝ) := by
    rw [div_div]
  rw [hsplit, show (1 : ℝ) / (4096 * (((2 * N) ^ 46 : ℕ) : ℝ))
      = 1 / 4096 / (((2 * N) ^ 46 : ℕ) : ℝ) by rw [div_div]]
  exact div_le_div_of_nonneg_right hc h4.le

/-- **Arity 4 with approximately cleared markets.** With `2 r₀` probes at the root, every run
whose proposals minimize the potential for weights within total distance
`ζ · (total wealth)` of the true wealth, `ζ = K4.ζ 46 N ≥ 2^-12 / (2N)^46`, and whose wealth is
rounded to 41 significant bits after every update, meets all demands of every consistent
hypothesis and makes at most `4 r₀ (2N)^46` label queries. -/
theorem price_search_k4_approx (val : V → ℝ)
    (X : Exec ι (Expert ι V 4 (K4.depth K4_good (Fintype.card ι)))) (hist₀ : ℕ → ι → ℝ)
    (hX : X.ValidWith (approxMarket val (K4.ζ 46 (Fintype.card ι)))
      (K4.algRoot ι V val (2 * K4.r₀ ι V (K4.depth K4_good (Fintype.card ι)))) 0 hist₀
      (fun _ => 1)) :
    (∀ H : Hyp ι V, X.Consistent val H → ∀ s ∈ H.S, val (H.a s) ≤ sp X.x s) ∧
    X.queries ≤ 4 * K4.r₀ ι V (K4.depth K4_good (Fintype.card ι))
      * (2 * Fintype.card ι) ^ 46 :=
  K4.price_search_approx_double K4_good 46 K4_exp val X hist₀ hX

end SPLP
