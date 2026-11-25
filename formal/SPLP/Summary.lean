import Mathlib
import SPLP.Instances
import SPLP.Total
import SPLP.Cost
import SPLP.VertexRun
import SPLP.Eval

/-!
# Summary: the price search with fewer probes

The statements a reader should check. Everything is about the recursive market algorithm of
Section 6 of *Strongly polynomial linear programming* (OpenAI preprint, 24 November 2026), with
the same expert pool but different numerical constants and a sharper accounting.

* `price_search_k4_total`: with experts of arity `4`, for every rule answering the label
  queries there is a run of the algorithm; **every** run returns prices meeting all demands of
  every hypothesis consistent with the labels it received, and makes at most
  `2 r₀ (2N)^46` label queries.
* `K4_r₀_le`: `r₀ ≤ 125801 + 10112 · log (1 + |E|)`, and `card_expert` gives
  `|E| = (2N)^4 |V|^4 (2 D N |V| + 1)`.
* `price_search_k5_total`, `price_search_k6_total`: exponents `39` and `35` with experts of
  arity `5` and `6`.
* `preprint_exponent`: the preprint's constants give an exponent between `59` and `60`.
-/

namespace SPLP

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V]

/-- For good constants a valid run exists against every labelling rule. -/
theorem Consts.exists_run {k : ℕ} (K : Consts k) (hK : K.Good) (hk : 0 < k) [Nonempty V]
    (val : V → ℝ) (oracle : List ℕ → (ι → ℝ) → (ι → Bool)) (hist₀ : ℕ → ι → ℝ) :
    ∃ X : Exec ι (Expert ι V k (K.depth hK (Fintype.card ι))),
      X.Valid (K.alg hK ι V val) 0 hist₀ (fun _ => 1) ∧ X.LabelsFrom oracle [] :=
  exists_valid hk _ (K.params hK ι V val).hc0 (K.params hK ι V val).hc1
    (K.params hK ι V val).hη0 (K.params hK ι V val).hη1 (K.params hK ι V val).hep1
    (K.params hK ι V val).hrnd oracle hist₀

variable [Nonempty ι] [Nonempty V]

/-- **Arity 4, end to end.** Against any rule answering label queries the algorithm has a run,
and every run is correct with at most `2 r₀ (2N)^46` label queries. -/
theorem price_search_k4_total (val : V → ℝ) (hist₀ : ℕ → ι → ℝ) :
    (∀ oracle : List ℕ → (ι → ℝ) → (ι → Bool),
      ∃ X : Exec ι (Expert ι V 4 (K4.depth K4_good (Fintype.card ι))),
        X.Valid (K4.alg K4_good ι V val) 0 hist₀ (fun _ => 1) ∧ X.LabelsFrom oracle []) ∧
    (∀ X : Exec ι (Expert ι V 4 (K4.depth K4_good (Fintype.card ι))),
      X.Valid (K4.alg K4_good ι V val) 0 hist₀ (fun _ => 1) →
        (∀ H : Hyp ι V, X.Consistent val H → ∀ s ∈ H.S, val (H.a s) ≤ sp X.x s) ∧
        X.queries ≤ 2 * K4.r₀ ι V (K4.depth K4_good (Fintype.card ι))
          * (2 * Fintype.card ι) ^ 46) :=
  ⟨fun oracle => K4.exists_run K4_good (by norm_num) val oracle hist₀,
   fun X hX => price_search_k4 val X hist₀ hX⟩

/-- **Arity 5, end to end**: at most `2 r₀ (2N)^39` label queries. -/
theorem price_search_k5_total (val : V → ℝ) (hist₀ : ℕ → ι → ℝ) :
    (∀ oracle : List ℕ → (ι → ℝ) → (ι → Bool),
      ∃ X : Exec ι (Expert ι V 5 (K5.depth K5_good (Fintype.card ι))),
        X.Valid (K5.alg K5_good ι V val) 0 hist₀ (fun _ => 1) ∧ X.LabelsFrom oracle []) ∧
    (∀ X : Exec ι (Expert ι V 5 (K5.depth K5_good (Fintype.card ι))),
      X.Valid (K5.alg K5_good ι V val) 0 hist₀ (fun _ => 1) →
        (∀ H : Hyp ι V, X.Consistent val H → ∀ s ∈ H.S, val (H.a s) ≤ sp X.x s) ∧
        X.queries ≤ 2 * K5.r₀ ι V (K5.depth K5_good (Fintype.card ι))
          * (2 * Fintype.card ι) ^ 39) :=
  ⟨fun oracle => K5.exists_run K5_good (by norm_num) val oracle hist₀,
   fun X hX => price_search_k5 val X hist₀ hX⟩

/-- **Arity 6, end to end**: at most `2 r₀ (2N)^35` label queries. -/
theorem price_search_k6_total (val : V → ℝ) (hist₀ : ℕ → ι → ℝ) :
    (∀ oracle : List ℕ → (ι → ℝ) → (ι → Bool),
      ∃ X : Exec ι (Expert ι V 6 (K6.depth K6_good (Fintype.card ι))),
        X.Valid (K6.alg K6_good ι V val) 0 hist₀ (fun _ => 1) ∧ X.LabelsFrom oracle []) ∧
    (∀ X : Exec ι (Expert ι V 6 (K6.depth K6_good (Fintype.card ι))),
      X.Valid (K6.alg K6_good ι V val) 0 hist₀ (fun _ => 1) →
        (∀ H : Hyp ι V, X.Consistent val H → ∀ s ∈ H.S, val (H.a s) ≤ sp X.x s) ∧
        X.queries ≤ 2 * K6.r₀ ι V (K6.depth K6_good (Fintype.card ι))
          * (2 * Fintype.card ι) ^ 35) :=
  ⟨fun oracle => K6.exists_run K6_good (by norm_num) val oracle hist₀,
   fun X hX => price_search_k6 val X hist₀ hX⟩

omit [Nonempty ι] [Nonempty V] in
/-- The number of root probes for arity 4 is logarithmic in the size of the expert pool. -/
theorem K4_r₀_le (D : ℕ) :
    (K4.r₀ ι V D : ℝ) ≤ 125801 + 10112 * Real.log (1 + Fintype.card (Expert ι V 4 D)) := by
  have h := K4.r₀_le K4_good ι V D
  have hq : K4.Pm / K4.σ ≤ (10112 : ℚ) := by
    norm_num [K4, Consts.σ, Consts.ε, Consts.q, Consts.lp, Consts.lam, Consts.Pm]
  have hq' : (K4.Pm : ℝ) / (K4.σ : ℝ) ≤ 10112 := by exact_mod_cast hq
  have hlog : 0 ≤ Real.log (1 + (Fintype.card (Expert ι V 4 D) : ℝ)) :=
    Real.log_nonneg (by have : (0 : ℝ) ≤ Fintype.card (Expert ι V 4 D) := Nat.cast_nonneg _; linarith)
  have hr : ((K4.r : ℕ) : ℝ) = 125800 := by norm_num [K4]
  have := mul_le_mul_of_nonneg_right hq' hlog
  linarith


/-! ### Cost of the market step

`ProbeCost val p lo c cells t` (see `SPLP/Cost.lean`) holds at a probe when fewer than `t`
probes were completed before it, the experts fall into at most `cells` classes with common
wealth, common maximizing options and common gain, and every wealth value is a float with
`p + 1` significant bits in `(0, |E|]`, at least `lo^(completed probes) · c^level`. -/

omit [Nonempty V] in
/-- **Arity 4: every probe.** At most `classBound N 4 D Qmax` cells, with
`Qmax = 2 r₀ (2N)^46`. Wealth values are floats with `41` significant bits (`K4.p = 40`), lie
in `(0, |E|]` and are at least `ρ₀^t · 2^(-17 l)` with
`ρ₀ = (1 - 2^-40)(1 - 2^-17)(15/16)`, so their binary exponent has size logarithmic in the
number `t` of completed probes. -/
theorem probe_cost_k4 (val : V → ℝ)
    (X : Exec ι (Expert ι V 4 (K4.depth K4_good (Fintype.card ι)))) (hist₀ : ℕ → ι → ℝ)
    (hX : X.Valid (K4.alg K4_good ι V val) 0 hist₀ (fun _ => 1)) :
    X.ForallProbes
      (ProbeCost val K4.p
        ((1 - (K4.ep : ℝ)) * (1 - (K4.c : ℝ)) * (1 - (K4.η : ℝ))) (K4.c : ℝ)
        (classBound (Fintype.card ι) 4 (K4.depth K4_good (Fintype.card ι))
          (2 * K4.r₀ ι V (K4.depth K4_good (Fintype.card ι)) * (2 * Fintype.card ι) ^ 46))
        (2 * K4.r₀ ι V (K4.depth K4_good (Fintype.card ι)) * (2 * Fintype.card ι) ^ 46))
      0 hist₀ [] :=
  K4.probe_cost K4_good 46 K4_exp val X hist₀ hX

/-- **Arity 4: all probes.** The cell bound summed over the probes of a run is at most
`2 r₀ (40 r₀ + 1)^4 (2ND + 1) (2N)^234`. -/
theorem total_cells_k4 (N D ρ : ℕ) (hN : 1 ≤ N) :
    (2 * ρ * (2 * N) ^ 46) * classBound N 4 D (2 * ρ * (2 * N) ^ 46)
      ≤ 2 * ρ * (40 * ρ + 1) ^ 4 * (D * (2 * N) + 1) * (2 * N) ^ 234 := by
  have h := total_cells_le N 4 D 46 ρ (2 * ρ * (2 * N) ^ 46) hN le_rfl
  rw [pairs_four] at h
  exact h

omit [Nonempty V] in
/-- **Arity 3: every probe.** -/
theorem probe_cost_k3 (val : V → ℝ)
    (X : Exec ι (Expert ι V 3 (K3.depth K3_good (Fintype.card ι)))) (hist₀ : ℕ → ι → ℝ)
    (hX : X.Valid (K3.alg K3_good ι V val) 0 hist₀ (fun _ => 1)) :
    X.ForallProbes
      (ProbeCost val K3.p
        ((1 - (K3.ep : ℝ)) * (1 - (K3.c : ℝ)) * (1 - (K3.η : ℝ))) (K3.c : ℝ)
        (classBound (Fintype.card ι) 3 (K3.depth K3_good (Fintype.card ι))
          (2 * K3.r₀ ι V (K3.depth K3_good (Fintype.card ι)) * (2 * Fintype.card ι) ^ 66))
        (2 * K3.r₀ ι V (K3.depth K3_good (Fintype.card ι)) * (2 * Fintype.card ι) ^ 66))
      0 hist₀ [] :=
  K3.probe_cost K3_good 66 K3_exp val X hist₀ hX

set_option exponentiation.threshold 300 in
/-- **Arity 3: all probes.** At most `2 r₀ (24 r₀ + 1)^3 (2ND + 1) (2N)^267`. -/
theorem total_cells_k3 (N D ρ : ℕ) (hN : 1 ≤ N) :
    (2 * ρ * (2 * N) ^ 66) * classBound N 3 D (2 * ρ * (2 * N) ^ 66)
      ≤ 2 * ρ * (24 * ρ + 1) ^ 3 * (D * (2 * N) + 1) * (2 * N) ^ 267 := by
  have h := total_cells_le N 3 D 66 ρ (2 * ρ * (2 * N) ^ 66) hN le_rfl
  rw [pairs_three] at h
  exact h

omit [Nonempty V] in
/-- **Arity 5: every probe.** -/
theorem probe_cost_k5 (val : V → ℝ)
    (X : Exec ι (Expert ι V 5 (K5.depth K5_good (Fintype.card ι)))) (hist₀ : ℕ → ι → ℝ)
    (hX : X.Valid (K5.alg K5_good ι V val) 0 hist₀ (fun _ => 1)) :
    X.ForallProbes
      (ProbeCost val K5.p
        ((1 - (K5.ep : ℝ)) * (1 - (K5.c : ℝ)) * (1 - (K5.η : ℝ))) (K5.c : ℝ)
        (classBound (Fintype.card ι) 5 (K5.depth K5_good (Fintype.card ι))
          (2 * K5.r₀ ι V (K5.depth K5_good (Fintype.card ι)) * (2 * Fintype.card ι) ^ 39))
        (2 * K5.r₀ ι V (K5.depth K5_good (Fintype.card ι)) * (2 * Fintype.card ι) ^ 39))
      0 hist₀ [] :=
  K5.probe_cost K5_good 39 K5_exp val X hist₀ hX

/-- **Arity 5: all probes.** At most `2 r₀ (60 r₀ + 1)^5 (2ND + 1) (2N)^239`. -/
theorem total_cells_k5 (N D ρ : ℕ) (hN : 1 ≤ N) :
    (2 * ρ * (2 * N) ^ 39) * classBound N 5 D (2 * ρ * (2 * N) ^ 39)
      ≤ 2 * ρ * (60 * ρ + 1) ^ 5 * (D * (2 * N) + 1) * (2 * N) ^ 239 := by
  have h := total_cells_le N 5 D 39 ρ (2 * ρ * (2 * N) ^ 39) hN le_rfl
  rw [pairs_five] at h
  exact h

omit [Nonempty V] in
/-- **Arity 6: every probe.** -/
theorem probe_cost_k6 (val : V → ℝ)
    (X : Exec ι (Expert ι V 6 (K6.depth K6_good (Fintype.card ι)))) (hist₀ : ℕ → ι → ℝ)
    (hX : X.Valid (K6.alg K6_good ι V val) 0 hist₀ (fun _ => 1)) :
    X.ForallProbes
      (ProbeCost val K6.p
        ((1 - (K6.ep : ℝ)) * (1 - (K6.c : ℝ)) * (1 - (K6.η : ℝ))) (K6.c : ℝ)
        (classBound (Fintype.card ι) 6 (K6.depth K6_good (Fintype.card ι))
          (2 * K6.r₀ ι V (K6.depth K6_good (Fintype.card ι)) * (2 * Fintype.card ι) ^ 35))
        (2 * K6.r₀ ι V (K6.depth K6_good (Fintype.card ι)) * (2 * Fintype.card ι) ^ 35))
      0 hist₀ [] :=
  K6.probe_cost K6_good 35 K6_exp val X hist₀ hX

/-- **Arity 6: all probes.** At most `2 r₀ (84 r₀ + 1)^6 (2ND + 1) (2N)^251`. -/
theorem total_cells_k6 (N D ρ : ℕ) (hN : 1 ≤ N) :
    (2 * ρ * (2 * N) ^ 35) * classBound N 6 D (2 * ρ * (2 * N) ^ 35)
      ≤ 2 * ρ * (84 * ρ + 1) ^ 6 * (D * (2 * N) + 1) * (2 * N) ^ 251 := by
  have h := total_cells_le N 6 D 35 ρ (2 * ρ * (2 * N) ^ 35) hN le_rfl
  rw [pairs_six] at h
  exact h


/-! ### Proposals

The algorithm may always propose a vertex of its market potential. With integer demands in
`[-R, R]` every such proposal is half-integral and bounded by `(l + 1) · 2R(N + 1)` at level
`l`, independently of the wealth. -/

/-- Integer demands in `[-R, R]`, as a finite type with its valuation. -/
def intVal (R : ℕ) : Fin (2 * R + 1) → ℝ := fun v => (v : ℝ) - R

omit [Nonempty ι] [Nonempty V] in
/-- **Runs with half-integral bounded proposals exist**, for good constants, integer demands in
`[-R, R]` and every labelling rule. They are valid runs, so the correctness and cost theorems
above apply to them. -/
theorem Consts.exists_vertex_run {k : ℕ} (K : Consts k) (hK : K.Good) (hk : 0 < k) (R : ℕ)
    (oracle : List ℕ → (ι → ℝ) → (ι → Bool)) (hist₀ : ℕ → ι → ℝ) :
    ∃ X : Exec ι (Expert ι (Fin (2 * R + 1)) k (K.depth hK (Fintype.card ι))),
      X.Valid (K.alg hK ι (Fin (2 * R + 1)) (intVal R)) 0 hist₀ (fun _ => 1) ∧
      X.LabelsFrom oracle [] ∧
      X.ForallProbes (fun _ l _ y _ => ∀ i,
          (∃ z : ℤ, 2 * y i = z) ∧ |y i| ≤ (l + 1) * (2 * R * (Fintype.card ι + 1)))
        0 hist₀ [] := by
  obtain ⟨X, hv, hl, hvr⟩ := exists_valid_vertex (D := K.depth hK (Fintype.card ι)) hk
    (K.alg hK ι (Fin (2 * R + 1)) (intVal R))
    (K.params hK ι (Fin (2 * R + 1)) (intVal R)).hc0
    (K.params hK ι (Fin (2 * R + 1)) (intVal R)).hc1
    (K.params hK ι (Fin (2 * R + 1)) (intVal R)).hη0
    (K.params hK ι (Fin (2 * R + 1)) (intVal R)).hη1
    (K.params hK ι (Fin (2 * R + 1)) (intVal R)).hep1
    (K.params hK ι (Fin (2 * R + 1)) (intVal R)).hrnd oracle hist₀
  refine ⟨X, hv, hl, ?_⟩
  have hint : ∀ v : Fin (2 * R + 1), ∃ z : ℤ, intVal R v = z :=
    fun v => ⟨(v : ℤ) - R, by simp [intVal]⟩
  have hR : ∀ v : Fin (2 * R + 1), |intVal R v| ≤ (R : ℝ) := by
    intro v
    have h1 : ((v : ℕ) : ℝ) ≤ 2 * R := by
      have := v.2
      have h2 : (v : ℕ) ≤ 2 * R := by omega
      exact_mod_cast h2
    have h0 : (0 : ℝ) ≤ ((v : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [abs_le]
    constructor <;> simp only [intVal] <;> linarith
  have h1 := X.vertexRun_halfInt (intVal R) hint 0 hist₀ [] hvr (fun j hj => absurd hj (Nat.not_lt_zero j))
  have h2 := X.vertexRun_bound (intVal R) (R : ℝ) (Nat.cast_nonneg R) hR 0 hist₀ [] hvr
    (fun j hj => absurd hj (Nat.not_lt_zero j))
  refine Exec.ForallProbes.mono ?_ X 0 hist₀ [] (Exec.ForallProbes.and X 0 hist₀ [] h1 h2)
  rintro pre l hist y w ⟨ha, hb⟩ i
  exact ⟨ha i, hb i⟩

end SPLP
