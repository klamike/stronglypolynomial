import Mathlib
import SPLP.Approx

/-!
# Approximately cleared markets with a constant tolerance

`Exec.wealth_approx` charges the approximation error at every probe of the run, which forces a
tolerance of order `1 / (number of queries)`. But a child only receives the invested share
`c · w` of the wealth, and returns it. So the growth of total wealth obeys a recursion over
the levels:

* `growthH A ζ h`: the growth factor of a non-root node of height `h` (`1` at a leaf,
  `((1 - c)(1 + η ζ) + c · growthH h)^r` one level up);
* `growthAt A ζ D l`: the growth factor of a node at level `l` (the root makes `r₀` probes);
* `Exec.wealth_approx_level`: a node at level `l` returns total wealth at most
  `growthAt A ζ D l` times its input total;
* `growthH_le_exp`, `growthAt_zero_le_exp`: if `c r (1 + α) ≤ u < 1` and
  `r η ζ ≤ α (1 - u)`, then `growthH ≤ exp (r η ζ / (1 - u))` at every height and the root
  factor is at most `exp (r₀ η ζ / (1 - u))`. The number of queries no longer appears;
* `price_search_correct_approx_level`: correctness when the root absorbs `log (growthAt .. 0)`;
* `Consts.price_search_approx_level`, `price_search_k4_approx_const`: for arity 4 the
  tolerance `ζ = 2^-25` works, independently of the number of coordinates, the range and the
  pool, with `2 r₀` root probes and at most `4 r₀ (2N)^46` label queries.
-/

set_option linter.unusedSectionVars false

namespace SPLP

open Finset

variable {ι V : Type*} {k D : ℕ} [Fintype ι] [DecidableEq ι] [Fintype V]

/-! ### Growth factors by level -/

/-- Growth factor of total wealth at a non-root node of height `h` above the leaves. -/
noncomputable def growthH (A : Alg V) (ζ : ℝ) : ℕ → ℝ
  | 0 => 1
  | h + 1 => ((1 - A.c) * (1 + A.η * ζ) + A.c * growthH A ζ h) ^ A.r

/-- Growth factor of total wealth at a node of level `l` in a tree of depth `D`. -/
noncomputable def growthAt (A : Alg V) (ζ : ℝ) (D l : ℕ) : ℝ :=
  if l = 0 then
    (if D = 0 then 1
      else ((1 - A.c) * (1 + A.η * ζ) + A.c * growthH A ζ (D - 1)) ^ A.r₀)
  else growthH A ζ (D - l)

omit [Fintype V] in
theorem one_le_base (A : Alg V) {ζ g : ℝ} (hζ : 0 ≤ ζ) (hc0 : 0 < A.c) (hc1 : A.c < 1)
    (hη0 : 0 < A.η) (hg : 1 ≤ g) : 1 ≤ (1 - A.c) * (1 + A.η * ζ) + A.c * g := by
  have h1 : 0 ≤ (1 - A.c) * (A.η * ζ) :=
    mul_nonneg (by linarith) (mul_nonneg hη0.le hζ)
  have h2 : A.c * 1 ≤ A.c * g := mul_le_mul_of_nonneg_left hg hc0.le
  nlinarith

omit [Fintype V] in
theorem one_le_growthH (A : Alg V) {ζ : ℝ} (hζ : 0 ≤ ζ) (hc0 : 0 < A.c) (hc1 : A.c < 1)
    (hη0 : 0 < A.η) (h : ℕ) : 1 ≤ growthH A ζ h := by
  induction h with
  | zero => exact le_rfl
  | succ h ih =>
    show 1 ≤ ((1 - A.c) * (1 + A.η * ζ) + A.c * growthH A ζ h) ^ A.r
    exact one_le_pow₀ (one_le_base A hζ hc0 hc1 hη0 ih)

omit [Fintype V] in
theorem one_le_growthAt (A : Alg V) {ζ : ℝ} (hζ : 0 ≤ ζ) (hc0 : 0 < A.c) (hc1 : A.c < 1)
    (hη0 : 0 < A.η) (D l : ℕ) : 1 ≤ growthAt A ζ D l := by
  unfold growthAt
  split_ifs
  · exact le_rfl
  · exact one_le_pow₀ (one_le_base A hζ hc0 hc1 hη0 (one_le_growthH A hζ hc0 hc1 hη0 _))
  · exact one_le_growthH A hζ hc0 hc1 hη0 _

/-! ### Wealth by level -/

theorem node_wealth_level_aux (A : Alg V) {ζ : ℝ} (hζ : 0 ≤ ζ) (hc0 : 0 < A.c)
    (hc1 : A.c < 1) (hη0 : 0 < A.η) (hη1 : A.η < 1) {ep : ℝ} (hep1 : ep < 1)
    (hrnd : ∀ x : ℝ, 0 < x → (1 - ep) * x ≤ A.rnd x ∧ A.rnd x ≤ x) {T : ℕ}
    {y : Fin T → ι → ℝ} {z : Fin T → ι → Bool}
    {child : Fin T → Exec ι (Expert ι V k D)} {w : ℕ → Expert ι V k D → ℝ} {x : ι → ℝ}
    {l : ℕ} {hist : ℕ → ι → ℝ} {wIn : Expert ι V k D → ℝ}
    (hv : (Exec.node T y z child w x).ValidWith (approxMarket A.val ζ) A l hist wIn)
    (hpos : ∀ e, 0 < wIn e) {g : ℝ} (hg : 1 ≤ g)
    (hch : ∀ τ : Fin T, ∀ (hist : ℕ → ι → ℝ) (wIn : Expert ι V k D → ℝ),
        (child τ).ValidWith (approxMarket A.val ζ) A (l + 1) hist wIn → (∀ e, 0 < wIn e) →
        ∑ e, (child τ).wOut e ≤ g * ∑ e, wIn e) :
    ∀ n, n ≤ T → ∑ e, w n e
      ≤ ((1 - A.c) * (1 + A.η * ζ) + A.c * g) ^ n * ∑ e, wIn e := by
  have hwpos := node_pos_aux (approxMarket A.val ζ) A hc0 hc1 hη0 hη1 hep1 hrnd hv hpos
    (fun τ => Exec.wealth_pos (approxMarket A.val ζ) A hc0 hc1 hη0 hη1 hep1 hrnd (child τ))
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
    have hcout := Exec.wealth_pos (approxMarket A.val ζ) A hc0 hc1 hη0 hη1 hep1 hrnd
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
      approx_gain_le A.val l hist (fun e => (1 - A.c) * w n e) (y ⟨n, hn'⟩) _ hmk
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

/-- **Wealth under approximate markets, by level.** A node at level `l` returns total wealth
at most `growthAt A ζ D l` times its input total. -/
theorem Exec.wealth_approx_level (A : Alg V) {ζ : ℝ} (hζ : 0 ≤ ζ) (hc0 : 0 < A.c)
    (hc1 : A.c < 1) (hη0 : 0 < A.η) (hη1 : A.η < 1) {ep : ℝ} (hep1 : ep < 1)
    (hrnd : ∀ x : ℝ, 0 < x → (1 - ep) * x ≤ A.rnd x ∧ A.rnd x ≤ x)
    (X : Exec ι (Expert ι V k D)) :
    ∀ (l : ℕ) (hist : ℕ → ι → ℝ) (wIn : Expert ι V k D → ℝ),
      X.ValidWith (approxMarket A.val ζ) A l hist wIn → (∀ e, 0 < wIn e) →
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
        (child τ).ValidWith (approxMarket A.val ζ) A (l + 1) hist wIn → (∀ e, 0 < wIn e) →
        ∑ e, (child τ).wOut e ≤ growthH A ζ (D - (l + 1)) * ∑ e, wIn e := by
      intro τ hist' wIn' hv' hpos'
      have h := ih τ (l + 1) hist' wIn' hv' hpos'
      have hG : growthAt A ζ D (l + 1) = growthH A ζ (D - (l + 1)) := by
        unfold growthAt
        rw [if_neg (Nat.succ_ne_zero l)]
      rw [hG] at h
      exact h
    have h := node_wealth_level_aux A hζ hc0 hc1 hη0 hη1 hep1 hrnd hv hpos
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

/-! ### The growth factors are bounded independently of the number of queries -/

omit [Fintype V] in
/-- One probe: if the children grow by at most `exp a` with `0 ≤ a ≤ α ≤ 1`, the base of the
node's growth factor is at most `exp (η ζ + c a (1 + α))`. -/
theorem base_le_exp (A : Alg V) {ζ α a g : ℝ} (hζ : 0 ≤ ζ) (hc0 : 0 < A.c) (hc1 : A.c < 1)
    (hη0 : 0 < A.η) (ha0 : 0 ≤ a) (haα : a ≤ α) (hα1 : α ≤ 1) (hg : g ≤ Real.exp a) :
    (1 - A.c) * (1 + A.η * ζ) + A.c * g ≤ Real.exp (A.η * ζ + A.c * a * (1 + α)) := by
  have hexp : Real.exp a - 1 - a ≤ a ^ 2 :=
    (abs_le.1 (Real.abs_exp_sub_one_sub_id_le (by rw [abs_of_nonneg ha0]; linarith))).2
  have h1 : Real.exp a - 1 ≤ a * (1 + α) := by nlinarith
  have h2 : A.c * g ≤ A.c * Real.exp a := mul_le_mul_of_nonneg_left hg hc0.le
  have h3 : A.c * (Real.exp a - 1) ≤ A.c * (a * (1 + α)) :=
    mul_le_mul_of_nonneg_left h1 hc0.le
  have h4 : 0 ≤ A.c * (A.η * ζ) := mul_nonneg hc0.le (mul_nonneg hη0.le hζ)
  have h5 := Real.add_one_le_exp (A.η * ζ + A.c * a * (1 + α))
  nlinarith

omit [Fintype V] in
/-- **The growth factor of an internal node is bounded.** If `c r (1 + α) ≤ u < 1` and
`r η ζ ≤ α (1 - u)`, every non-root node, at every height, multiplies total wealth by at most
`exp (r η ζ / (1 - u))`. -/
theorem growthH_le_exp (A : Alg V) {ζ α u : ℝ} (hζ : 0 ≤ ζ) (hc0 : 0 < A.c) (hc1 : A.c < 1)
    (hη0 : 0 < A.η) (hα1 : α ≤ 1) (hu : A.c * A.r * (1 + α) ≤ u) (hu1 : u < 1)
    (hζα : A.r * (A.η * ζ) ≤ α * (1 - u)) (h : ℕ) :
    growthH A ζ h ≤ Real.exp (A.r * (A.η * ζ) / (1 - u)) := by
  have hu' : 0 < 1 - u := by linarith
  have hx0 : 0 ≤ (A.r : ℝ) * (A.η * ζ) :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hη0.le hζ)
  have ha0 : 0 ≤ A.r * (A.η * ζ) / (1 - u) := div_nonneg hx0 hu'.le
  have haα : A.r * (A.η * ζ) / (1 - u) ≤ α := by
    rw [div_le_iff₀ hu']; exact hζα
  have hae : A.r * (A.η * ζ) / (1 - u) * (1 - u) = A.r * (A.η * ζ) := by
    field_simp
  induction h with
  | zero =>
    show (1 : ℝ) ≤ _
    exact Real.one_le_exp ha0
  | succ h ih =>
    show ((1 - A.c) * (1 + A.η * ζ) + A.c * growthH A ζ h) ^ A.r ≤ _
    have hb := base_le_exp A hζ hc0 hc1 hη0 ha0 haα hα1 ih
    have hb0 : 0 ≤ (1 - A.c) * (1 + A.η * ζ) + A.c * growthH A ζ h := by
      linarith [one_le_base A hζ hc0 hc1 hη0 (one_le_growthH A hζ hc0 hc1 hη0 h)]
    calc ((1 - A.c) * (1 + A.η * ζ) + A.c * growthH A ζ h) ^ A.r
        ≤ (Real.exp (A.η * ζ + A.c * (A.r * (A.η * ζ) / (1 - u)) * (1 + α))) ^ A.r :=
          pow_le_pow_left₀ hb0 hb _
      _ = Real.exp (A.r * (A.η * ζ + A.c * (A.r * (A.η * ζ) / (1 - u)) * (1 + α))) := by
          rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (A.r * (A.η * ζ) / (1 - u)) := by
          apply Real.exp_le_exp.2
          have h1 : A.c * A.r * (1 + α) * (A.r * (A.η * ζ) / (1 - u))
              ≤ u * (A.r * (A.η * ζ) / (1 - u)) := mul_le_mul_of_nonneg_right hu ha0
          nlinarith

omit [Fintype V] in
/-- **The growth factor of the root is bounded.** Under the same hypotheses the whole run
multiplies total wealth by at most `exp (r₀ η ζ / (1 - u))`: the number of root probes times a
constant times `η ζ`. -/
theorem growthAt_zero_le_exp (A : Alg V) {ζ α u : ℝ} (hζ : 0 ≤ ζ) (hc0 : 0 < A.c)
    (hc1 : A.c < 1) (hη0 : 0 < A.η) (hα1 : α ≤ 1)
    (hu : A.c * A.r * (1 + α) ≤ u) (hu1 : u < 1) (hζα : A.r * (A.η * ζ) ≤ α * (1 - u))
    (D : ℕ) :
    growthAt A ζ D 0 ≤ Real.exp (A.r₀ * (A.η * ζ) / (1 - u)) := by
  have hu' : 0 < 1 - u := by linarith
  have hηζ : 0 ≤ A.η * ζ := mul_nonneg hη0.le hζ
  have hx0 : 0 ≤ (A.r : ℝ) * (A.η * ζ) := mul_nonneg (Nat.cast_nonneg _) hηζ
  have ha0 : 0 ≤ A.r * (A.η * ζ) / (1 - u) := div_nonneg hx0 hu'.le
  have haα : A.r * (A.η * ζ) / (1 - u) ≤ α := by
    rw [div_le_iff₀ hu']; exact hζα
  have hr0 : 0 ≤ (A.r₀ : ℝ) * (A.η * ζ) / (1 - u) :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) hηζ) hu'.le
  unfold growthAt
  rw [if_pos rfl]
  split_ifs with hD
  · exact Real.one_le_exp hr0
  · have ih := growthH_le_exp A hζ hc0 hc1 hη0 hα1 hu hu1 hζα (D - 1)
    have hb := base_le_exp A hζ hc0 hc1 hη0 ha0 haα hα1 ih
    have hb0 : 0 ≤ (1 - A.c) * (1 + A.η * ζ) + A.c * growthH A ζ (D - 1) := by
      linarith [one_le_base A hζ hc0 hc1 hη0 (one_le_growthH A hζ hc0 hc1 hη0 (D - 1))]
    have hinner : A.η * ζ + A.c * (A.r * (A.η * ζ) / (1 - u)) * (1 + α)
        ≤ A.η * ζ / (1 - u) := by
      rw [le_div_iff₀ hu']
      have h1 : A.c * A.r * (1 + α) * (A.η * ζ) ≤ u * (A.η * ζ) :=
        mul_le_mul_of_nonneg_right hu hηζ
      have h2 : A.c * (A.r * (A.η * ζ) / (1 - u)) * (1 + α) * (1 - u)
          = A.c * A.r * (1 + α) * (A.η * ζ) := by
        field_simp
      nlinarith
    calc ((1 - A.c) * (1 + A.η * ζ) + A.c * growthH A ζ (D - 1)) ^ A.r₀
        ≤ (Real.exp (A.η * ζ + A.c * (A.r * (A.η * ζ) / (1 - u)) * (1 + α))) ^ A.r₀ :=
          pow_le_pow_left₀ hb0 hb _
      _ = Real.exp (A.r₀ * (A.η * ζ + A.c * (A.r * (A.η * ζ) / (1 - u)) * (1 + α))) := by
          rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (A.r₀ * (A.η * ζ) / (1 - u)) := by
          apply Real.exp_le_exp.2
          have := mul_le_mul_of_nonneg_left hinner (Nat.cast_nonneg A.r₀)
          calc (A.r₀ : ℝ) * (A.η * ζ + A.c * (A.r * (A.η * ζ) / (1 - u)) * (1 + α))
              ≤ A.r₀ * (A.η * ζ / (1 - u)) := this
            _ = A.r₀ * (A.η * ζ) / (1 - u) := by ring

/-! ### Correctness -/

/-- **Price search from a bound on total wealth.** Let `X` be a run from the root with unit
initial wealth and any market condition. If its total output wealth is at most `G` times the
size of the pool and the root absorbs `log G`, the returned prices meet every demand of every
hypothesis consistent with the labels received. -/
theorem price_search_correct_of_growth (M : MarketCond ι V k D) (P : Params ι V k D)
    (X : Exec ι (Expert ι V k D)) (hist₀ : ℕ → ι → ℝ)
    (hX : X.ValidWith M P.A 0 hist₀ (fun _ => 1)) {G Γ : ℝ} (hG1 : 1 ≤ G)
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
  rcases node_claim_with M P H X 0 hist₀ _ hX (fun _ => one_pos) hH
      _ 0 none inv with h | ⟨-, hf⟩
  · exact h
  · exfalso
    simp only [if_true] at hf
    have hout := Exec.wealth_pos M P.A P.hc0 P.hc1 P.hη0 P.hη1 P.hep1
      P.hrnd X 0 hist₀ _ hX (fun _ => one_pos)
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
    have hPsi := Psi_mono H _ P.ω 0 none inv.nonneg P.hω hb
    rw [Psi_const H _ P.ω 0 none inv.sum_one] at hPsi
    have hres := P.reserve_bound (k := k) 0
    have hres0 := reserve_nonneg (D := D) P.ω 0 P.hω
    have hB0 : 0 ≤ Real.log (1 + P.κ * Fintype.card (Expert ι V k D)) + Γ :=
      add_nonneg (Real.log_nonneg (by linarith)) hΓ0
    nlinarith

/-- **Price search with approximately cleared markets, level form.** As
`price_search_correct_approx`, but the root only has to absorb the logarithm of the growth
factor `growthAt P.A ζ D 0`, which does not involve the number of queries. -/
theorem price_search_correct_approx_level (P : Params ι V k D) {ζ : ℝ} (hζ : 0 ≤ ζ)
    (X : Exec ι (Expert ι V k D)) (hist₀ : ℕ → ι → ℝ)
    (hX : X.ValidWith (approxMarket P.A.val ζ) P.A 0 hist₀ (fun _ => 1))
    (hroot : P.Pm * (Real.log (1 + P.κ * Fintype.card (Expert ι V k D))
        + Real.log (growthAt P.A ζ D 0)) < P.σ * P.A.r₀)
    (H : Hyp ι V) (hH : X.Consistent P.A.val H) :
    ∀ s ∈ H.S, H.surplus P.A.val X.x s ≤ 0 := by
  have hsum := Exec.wealth_approx_level P.A hζ P.hc0 P.hc1 P.hη0 P.hη1 P.hep1 P.hrnd X 0
    hist₀ _ hX (fun _ => one_pos)
  have hE : ∑ _e : Expert ι V k D, (1 : ℝ) = Fintype.card (Expert ι V k D) := by simp
  rw [hE] at hsum
  exact price_search_correct_of_growth (approxMarket P.A.val ζ) P X hist₀ hX
    (one_le_growthAt P.A hζ P.hc0 P.hc1 P.hη0 D 0) hsum le_rfl hroot H hH

/-! ### Explicit constants -/

namespace Consts

variable {k : ℕ}

/-- **Approximate markets with a constant tolerance.** Let `c r (1 + α) ≤ u < 1` for some
`α ≤ 1`. With `r₀' ≥ r₀` probes at the root and a tolerance `ζ ≥ 0` satisfying
`r η ζ ≤ α (1 - u)` and `Pm · r₀' η ζ / (1 - u) ≤ σ (r₀' - r₀)`, every run with approximately
cleared markets (and rounded wealth) meets all demands of every consistent hypothesis and
makes at most `2 r₀' (2N)^e` label queries. Neither condition on `ζ` involves the number of
queries. -/
theorem price_search_approx_level (K : Consts k) (hK : K.Good) (e : ℕ)
    (he : ((K.r : ℚ)) ^ 2 ≤ (K.ρ ^ 2 / K.β) ^ e)
    {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V] [Nonempty ι] (val : V → ℝ)
    (r₀' : ℕ) (hr₀ : K.r₀ ι V (K.depth hK (Fintype.card ι)) ≤ r₀') {ζ α u : ℝ}
    (hζ0 : 0 ≤ ζ) (hα1 : α ≤ 1)
    (hu : (K.c : ℝ) * (K.r : ℝ) * (1 + α) ≤ u) (hu1 : u < 1)
    (hζα : (K.r : ℝ) * ((K.η : ℝ) * ζ) ≤ α * (1 - u))
    (hζ : (K.Pm : ℝ) * ((r₀' : ℝ) * ((K.η : ℝ) * ζ) / (1 - u))
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
  let P := K.paramsRoot hK ι V val r₀' hr₀
  have hG : growthAt P.A ζ (K.depth hK (Fintype.card ι)) 0
      ≤ Real.exp ((r₀' : ℝ) * ((K.η : ℝ) * ζ) / (1 - u)) :=
    growthAt_zero_le_exp P.A hζ0 P.hc0 P.hc1 P.hη0 hα1 hu hu1 hζα _
  have hG1 := one_le_growthAt P.A hζ0 P.hc0 P.hc1 P.hη0 (K.depth hK (Fintype.card ι)) 0
  have hlog : Real.log (growthAt P.A ζ (K.depth hK (Fintype.card ι)) 0)
      ≤ (r₀' : ℝ) * ((K.η : ℝ) * ζ) / (1 - u) := by
    have := Real.log_le_log (by linarith) hG
    rwa [Real.log_exp] at this
  have hsum := Exec.wealth_approx_level P.A hζ0 P.hc0 P.hc1 P.hη0 P.hη1 P.hep1 P.hrnd X 0
    hist₀ _ hX (fun _ => one_pos)
  have hE : ∑ _e : Expert ι V k (K.depth hK (Fintype.card ι)), (1 : ℝ)
      = Fintype.card (Expert ι V k (K.depth hK (Fintype.card ι))) := by simp
  rw [hE] at hsum
  have h := price_search_correct_of_growth (approxMarket val ζ) P X hist₀ hX hG1 hsum hlog
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

/-- **Arity 4 with a constant tolerance.** With `2 r₀` probes at the root, every run whose
proposals minimize the potential for weights within total distance `2^-25 · (total wealth)`
of the true wealth, and whose wealth is rounded to 41 significant bits after every update,
meets all demands of every consistent hypothesis and makes at most `4 r₀ (2N)^46` label
queries. The tolerance does not depend on the number of coordinates, the range of the demands
or the pool. -/
theorem price_search_k4_approx_const (val : V → ℝ)
    (X : Exec ι (Expert ι V 4 (K4.depth K4_good (Fintype.card ι)))) (hist₀ : ℕ → ι → ℝ)
    (hX : X.ValidWith (approxMarket val (1 / 2 ^ 25))
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
  have h := K4.price_search_approx_level K4_good 46 K4_exp val
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
