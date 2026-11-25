import Mathlib
import SPLP.ApproxLevel

/-!
# The market condition the correctness proof uses

The proofs for approximately cleared markets use the market condition through one inequality
only (`approx_gain_le`): at the chosen proposal, for every feedback, the aggregate market gain
is at most `ζ` times the total wealth. `gainMarket val ζ` is that inequality as a market
condition. It is implied by `approxMarket val ζ` (`approxMarket_gain`), so every run with
approximately cleared markets is a run with this condition, and the results of
`SPLP/ApproxLevel.lean` hold for it verbatim:

* `Exec.wealth_gain_level`: a node at level `l` returns total wealth at most
  `growthAt A ζ D l` times its input total;
* `price_search_correct_gain_level`, `Consts.price_search_gain_level`,
  `price_search_k4_gain_const`: correctness and the query bound, for arity 4 with `ζ = 2^-25`.

A proposal therefore need not minimize any potential: any point at which no feedback lets the
market gain more than `ζ` times its wealth will do.
-/

set_option linter.unusedSectionVars false

namespace SPLP

open Finset

variable {ι V : Type*} {k D : ℕ} [Fintype ι] [DecidableEq ι] [Fintype V]

/-- The market condition used by the proofs: for every feedback, the aggregate gain at the
proposal is at most `ζ` times the total wealth in the market. -/
def gainMarket (val : V → ℝ) (ζ : ℝ) : MarketCond ι V k D :=
  fun l hist w y => ∀ v : ι → Bool, ∑ e, w e * gain val l hist y v e ≤ ζ * ∑ e, w e

/-- An approximately cleared market satisfies the gain condition. -/
theorem approxMarket_gain (val : V → ℝ) (ζ : ℝ) (l : ℕ) (hist : ℕ → ι → ℝ)
    (w : Expert ι V k D → ℝ) (y : ι → ℝ) (h : approxMarket val ζ l hist w y) :
    gainMarket val ζ l hist w y :=
  fun v => approx_gain_le val l hist w y v h

/-- A run with approximately cleared markets is a run with the gain condition. -/
theorem Exec.ValidWith.gain (A : Alg V) (ζ : ℝ) (X : Exec ι (Expert ι V k D)) (l : ℕ)
    (hist : ℕ → ι → ℝ) (wIn : Expert ι V k D → ℝ)
    (h : X.ValidWith (approxMarket A.val ζ) A l hist wIn) :
    X.ValidWith (gainMarket A.val ζ) A l hist wIn :=
  Exec.ValidWith.mono (fun l hist w y hm => approxMarket_gain A.val ζ l hist w y hm) A X l
    hist wIn h

/-! ### A first-order certificate for the gain condition

The gain condition quantifies over all `2^N` feedback vectors. It follows from one vector of
`N` numbers: a fractional choice `lam e` among the maximizing options of every expert (a
subgradient of the potential at `y`) whose aggregate price direction has 1-norm at most
`ζ` times the total wealth. So a proposal can be certified from the `N` net slot masses
`∑ e, w e * ∑ o, lam e o * dirOf .. e o i`, and at a point without ties from the masses of the
experts whose best option is each slot. -/

/-- **Certificate.** A subgradient of small 1-norm certifies the gain condition. -/
theorem gainMarket_of_selection (val : V → ℝ) (ζ : ℝ) (l : ℕ) (hist : ℕ → ι → ℝ)
    (w : Expert ι V k D → ℝ) (y : ι → ℝ) (hw : ∀ e, 0 ≤ w e)
    (lam : Expert ι V k D → Option (Fin k) → ℝ) (hlam0 : ∀ e o, 0 ≤ lam e o)
    (hlam1 : ∀ e, ∑ o, lam e o = 1)
    (hsupp : ∀ e o, lam e o ≠ 0 →
      util (bidOf val l hist) (dirOf val l hist) e o y
        = best (bidOf val l hist) (dirOf val l hist) e y)
    (hnorm : ∑ i, |∑ e, w e * ∑ o, lam e o * dirOf val l hist e o i| ≤ ζ * ∑ e, w e) :
    gainMarket val ζ l hist w y := by
  intro v
  have h1 : ∀ e, gain val l hist y v e
      ≤ ∑ o, lam e o * pay (dirOf val l hist) e o (vreal v) := by
    intro e
    calc gain val l hist y v e = (∑ o, lam e o) * gain val l hist y v e := by
          rw [hlam1, one_mul]
      _ = ∑ o, lam e o * gain val l hist y v e := Finset.sum_mul _ _ _
      _ ≤ ∑ o, lam e o * pay (dirOf val l hist) e o (vreal v) := by
          refine Finset.sum_le_sum (fun o _ => ?_)
          by_cases h0 : lam e o = 0
          · simp [h0]
          · exact mul_le_mul_of_nonneg_left (minPay_le _ _ _ _ _ o (hsupp e o h0)) (hlam0 e o)
  have h2 : ∀ e, w e * ∑ o, lam e o * pay (dirOf val l hist) e o (vreal v)
      = ∑ i, (w e * ∑ o, lam e o * dirOf val l hist e o i) * vreal v i := by
    intro e
    unfold pay
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun o _ => ?_))
    ring
  have h3 : ∀ i, (∑ e, w e * ∑ o, lam e o * dirOf val l hist e o i) * vreal v i
      ≤ |∑ e, w e * ∑ o, lam e o * dirOf val l hist e o i| := by
    intro i
    have hv : |vreal v i| = 1 := abs_sgn (v i)
    calc (∑ e, w e * ∑ o, lam e o * dirOf val l hist e o i) * vreal v i
        ≤ |(∑ e, w e * ∑ o, lam e o * dirOf val l hist e o i) * vreal v i| := le_abs_self _
      _ = |∑ e, w e * ∑ o, lam e o * dirOf val l hist e o i| := by rw [abs_mul, hv, mul_one]
  calc ∑ e, w e * gain val l hist y v e
      ≤ ∑ e, w e * ∑ o, lam e o * pay (dirOf val l hist) e o (vreal v) :=
        Finset.sum_le_sum (fun e _ => mul_le_mul_of_nonneg_left (h1 e) (hw e))
    _ = ∑ e, ∑ i, (w e * ∑ o, lam e o * dirOf val l hist e o i) * vreal v i :=
        Finset.sum_congr rfl (fun e _ => h2 e)
    _ = ∑ i, (∑ e, w e * ∑ o, lam e o * dirOf val l hist e o i) * vreal v i := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun i _ => (Finset.sum_mul _ _ _).symm)
    _ ≤ ∑ i, |∑ e, w e * ∑ o, lam e o * dirOf val l hist e o i| :=
        Finset.sum_le_sum (fun i _ => h3 i)
    _ ≤ ζ * ∑ e, w e := hnorm

/-! ### Wealth by level -/

theorem node_wealth_gain_aux (A : Alg V) {ζ : ℝ} (hζ : 0 ≤ ζ) (hc0 : 0 < A.c)
    (hc1 : A.c < 1) (hη0 : 0 < A.η) (hη1 : A.η < 1) {ep : ℝ} (hep1 : ep < 1)
    (hrnd : ∀ x : ℝ, 0 < x → (1 - ep) * x ≤ A.rnd x ∧ A.rnd x ≤ x) {T : ℕ}
    {y : Fin T → ι → ℝ} {z : Fin T → ι → Bool}
    {child : Fin T → Exec ι (Expert ι V k D)} {w : ℕ → Expert ι V k D → ℝ} {x : ι → ℝ}
    {l : ℕ} {hist : ℕ → ι → ℝ} {wIn : Expert ι V k D → ℝ}
    (hv : (Exec.node T y z child w x).ValidWith (gainMarket A.val ζ) A l hist wIn)
    (hpos : ∀ e, 0 < wIn e) {g : ℝ} (hg : 1 ≤ g)
    (hch : ∀ τ : Fin T, ∀ (hist : ℕ → ι → ℝ) (wIn : Expert ι V k D → ℝ),
        (child τ).ValidWith (gainMarket A.val ζ) A (l + 1) hist wIn → (∀ e, 0 < wIn e) →
        ∑ e, (child τ).wOut e ≤ g * ∑ e, wIn e) :
    ∀ n, n ≤ T → ∑ e, w n e
      ≤ ((1 - A.c) * (1 + A.η * ζ) + A.c * g) ^ n * ∑ e, wIn e := by
  have hwpos := node_pos_aux (gainMarket A.val ζ) A hc0 hc1 hη0 hη1 hep1 hrnd hv hpos
    (fun τ => Exec.wealth_pos (gainMarket A.val ζ) A hc0 hc1 hη0 hη1 hep1 hrnd (child τ))
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
    have hcout := Exec.wealth_pos (gainMarket A.val ζ) A hc0 hc1 hη0 hη1 hep1 hrnd
      (child ⟨n, hn'⟩) _ _ _ hchild hcpos
    have hcsum := hch ⟨n, hn'⟩ _ _ hchild hcpos
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
      hmk _
    have hrew : ∀ e, w (n + 1) e ≤ (1 - A.c) * w n e
        + A.η * (((1 - A.c) * w n e) * gain A.val l hist (y ⟨n, hn'⟩)
            (feedback (y ⟨n, hn'⟩) (child ⟨n, hn'⟩).x (z ⟨n, hn'⟩)) e)
        + (child ⟨n, hn'⟩).wOut e := fun e => by
      rw [hs e]
      refine (hrnd _ (hXpos e)).2.trans (le_of_eq ?_)
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

/-- **Wealth under the gain condition, by level.** A node at level `l` returns total wealth
at most `growthAt A ζ D l` times its input total. -/
theorem Exec.wealth_gain_level (A : Alg V) {ζ : ℝ} (hζ : 0 ≤ ζ) (hc0 : 0 < A.c)
    (hc1 : A.c < 1) (hη0 : 0 < A.η) (hη1 : A.η < 1) {ep : ℝ} (hep1 : ep < 1)
    (hrnd : ∀ x : ℝ, 0 < x → (1 - ep) * x ≤ A.rnd x ∧ A.rnd x ≤ x)
    (X : Exec ι (Expert ι V k D)) :
    ∀ (l : ℕ) (hist : ℕ → ι → ℝ) (wIn : Expert ι V k D → ℝ),
      X.ValidWith (gainMarket A.val ζ) A l hist wIn → (∀ e, 0 < wIn e) →
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
        (child τ).ValidWith (gainMarket A.val ζ) A (l + 1) hist wIn → (∀ e, 0 < wIn e) →
        ∑ e, (child τ).wOut e ≤ growthH A ζ (D - (l + 1)) * ∑ e, wIn e := by
      intro τ hist' wIn' hv' hpos'
      have h := ih τ (l + 1) hist' wIn' hv' hpos'
      have hG : growthAt A ζ D (l + 1) = growthH A ζ (D - (l + 1)) := by
        unfold growthAt
        rw [if_neg (Nat.succ_ne_zero l)]
      rw [hG] at h
      exact h
    have h := node_wealth_gain_aux A hζ hc0 hc1 hη0 hη1 hep1 hrnd hv hpos
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

/-! ### Correctness -/

/-- **Price search under the gain condition, level form.** The root has to absorb the
logarithm of the growth factor `growthAt P.A ζ D 0`, which does not involve the number of
queries. -/
theorem price_search_correct_gain_level (P : Params ι V k D) {ζ : ℝ} (hζ : 0 ≤ ζ)
    (X : Exec ι (Expert ι V k D)) (hist₀ : ℕ → ι → ℝ)
    (hX : X.ValidWith (gainMarket P.A.val ζ) P.A 0 hist₀ (fun _ => 1))
    (hroot : P.Pm * (Real.log (1 + P.κ * Fintype.card (Expert ι V k D))
        + Real.log (growthAt P.A ζ D 0)) < P.σ * P.A.r₀)
    (H : Hyp ι V) (hH : X.Consistent P.A.val H) :
    ∀ s ∈ H.S, H.surplus P.A.val X.x s ≤ 0 := by
  have hsum := Exec.wealth_gain_level P.A hζ P.hc0 P.hc1 P.hη0 P.hη1 P.hep1 P.hrnd X 0
    hist₀ _ hX (fun _ => one_pos)
  have hE : ∑ _e : Expert ι V k D, (1 : ℝ) = Fintype.card (Expert ι V k D) := by simp
  rw [hE] at hsum
  exact price_search_correct_of_growth (gainMarket P.A.val ζ) P X hist₀ hX
    (one_le_growthAt P.A hζ P.hc0 P.hc1 P.hη0 D 0) hsum le_rfl hroot H hH

/-! ### Explicit constants -/

namespace Consts

variable {k : ℕ}

/-- **The gain condition with a constant tolerance.** Let `c r (1 + α) ≤ u < 1` for some
`α ≤ 1`. With `r₀' ≥ r₀` probes at the root and a tolerance `ζ ≥ 0` satisfying
`r η ζ ≤ α (1 - u)` and `Pm · r₀' η ζ / (1 - u) ≤ σ (r₀' - r₀)`, every run whose proposals
satisfy the gain condition (with rounded wealth) meets all demands of every consistent
hypothesis and makes at most `2 r₀' (2N)^e` label queries. -/
theorem price_search_gain_level (K : Consts k) (hK : K.Good) (e : ℕ)
    (he : ((K.r : ℚ)) ^ 2 ≤ (K.ρ ^ 2 / K.β) ^ e)
    {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V] [Nonempty ι] (val : V → ℝ)
    (r₀' : ℕ) (hr₀ : K.r₀ ι V (K.depth hK (Fintype.card ι)) ≤ r₀') {ζ α u : ℝ}
    (hζ0 : 0 ≤ ζ) (hα1 : α ≤ 1)
    (hu : (K.c : ℝ) * (K.r : ℝ) * (1 + α) ≤ u) (hu1 : u < 1)
    (hζα : (K.r : ℝ) * ((K.η : ℝ) * ζ) ≤ α * (1 - u))
    (hζ : (K.Pm : ℝ) * ((r₀' : ℝ) * ((K.η : ℝ) * ζ) / (1 - u))
      ≤ (K.σ : ℝ) * ((r₀' : ℝ) - K.r₀ ι V (K.depth hK (Fintype.card ι))))
    (X : Exec ι (Expert ι V k (K.depth hK (Fintype.card ι)))) (hist₀ : ℕ → ι → ℝ)
    (hX : X.ValidWith (gainMarket val ζ) (K.algRoot ι V val r₀') 0 hist₀ (fun _ => 1)) :
    (∀ H : Hyp ι V, X.Consistent val H → ∀ s ∈ H.S, val (H.a s) ≤ sp X.x s) ∧
    X.queries ≤ 2 * r₀' * (2 * Fintype.card ι) ^ e := by
  have hN : 1 ≤ 2 * Fintype.card ι := by
    have := Fintype.card_pos (α := ι)
    omega
  have hD := depth_pos (K.b_real hK) hN
  have hq : X.queries ≤ 2 * r₀' * (2 * Fintype.card ι) ^ e := by
    have hq := queries_root_le_with (gainMarket val ζ) (K.algRoot ι V val r₀') hK.hr X
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
  have hsum := Exec.wealth_gain_level P.A hζ0 P.hc0 P.hc1 P.hη0 P.hη1 P.hep1 P.hrnd X 0
    hist₀ _ hX (fun _ => one_pos)
  have hE : ∑ _e : Expert ι V k (K.depth hK (Fintype.card ι)), (1 : ℝ)
      = Fintype.card (Expert ι V k (K.depth hK (Fintype.card ι))) := by simp
  rw [hE] at hsum
  have h := price_search_correct_of_growth (gainMarket val ζ) P X hist₀ hX hG1 hsum hlog
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

/-- **Arity 4 under the gain condition.** With `2 r₀` probes at the root, every run in which
at each proposal no feedback gives the market an aggregate gain above `2^-25` times its
wealth, and whose wealth is rounded to 41 significant bits after every update, meets all
demands of every consistent hypothesis and makes at most `4 r₀ (2N)^46` label queries. -/
theorem price_search_k4_gain_const (val : V → ℝ)
    (X : Exec ι (Expert ι V 4 (K4.depth K4_good (Fintype.card ι)))) (hist₀ : ℕ → ι → ℝ)
    (hX : X.ValidWith (gainMarket val (1 / 2 ^ 25))
      (K4.algRoot ι V val (2 * K4.r₀ ι V (K4.depth K4_good (Fintype.card ι)))) 0 hist₀
      (fun _ => 1)) :
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
  have h := K4.price_search_gain_level K4_good 46 K4_exp val
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
