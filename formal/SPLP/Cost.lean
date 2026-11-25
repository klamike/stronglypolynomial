import Mathlib
import SPLP.Bits
import SPLP.Final

/-!
# What a probe costs

`ProbeCost` records what the market step of one probe has to handle: how many cells of
experts there are, and how large the wealth values are. `probe_cost` proves it at every probe
of every valid run; `Consts.probe_cost` and `Consts.total_cells_le` specialize it to good
constants and bound the sum over all probes.
-/

set_option linter.unusedSectionVars false

namespace SPLP

open Finset

variable {ι V : Type*} {k D : ℕ} [Fintype ι] [DecidableEq ι] [Fintype V]

/-- What the market step at one probe has to handle.

* `early`: fewer than `t` probes were completed before this one, and its level is below `D`.
* `cells`: for every test point `y'` of the market step (in particular the proposal), the
  experts fall into at most `cells` classes on which the wealth, the maximizing options at
  `y'` and the gain at `y'` (for every feedback) are constant.
* `size`: every wealth value lies in `(0, |E|]`, is a float with `p + 1` significant bits,
  and is at least `lo^(completed probes) · c^level`. -/
structure ProbeCost (val : V → ℝ) (p : ℕ) (lo c : ℝ) (cells t : ℕ) (pre : List (Ctx ι)) (l : ℕ)
    (hist : ℕ → ι → ℝ) (y : ι → ℝ) (w : Expert ι V k D → ℝ) : Prop where
  early : pre.length < t ∧ l < D
  cells : ∀ y' : ι → ℝ, ∃ cell : Expert ι V k D →
      GroupKey ι k D × (Fin (pre ++ [(⟨l, hist, y'⟩ : Ctx ι)]).length × Pair k → SignType),
    (Set.range cell).ncard ≤ cells ∧
    ∀ e e', cell e = cell e' →
      w e = w e' ∧
      (∀ o, util (bidOf val l hist) (dirOf val l hist) e o y'
            = best (bidOf val l hist) (dirOf val l hist) e y' ↔
          util (bidOf val l hist) (dirOf val l hist) e' o y'
            = best (bidOf val l hist) (dirOf val l hist) e' y') ∧
      ∀ v, gain val l hist y' v e = gain val l hist y' v e'
  size : ∀ e, 0 < w e ∧ w e ≤ Fintype.card (Expert ι V k D) ∧
    IsFloat p (w e) ∧ lo ^ pre.length * c ^ l ≤ w e

theorem Exec.forallProbes_level (A : Alg V) (X : Exec ι (Expert ι V k D)) :
    ∀ (l : ℕ) (hist : ℕ → ι → ℝ) (wIn : Expert ι V k D → ℝ) (pre : List (Ctx ι)),
      X.Valid A l hist wIn → X.ForallProbes (fun _ l' _ _ _ => l' < D) l hist pre := by
  induction X with
  | leaf x wOut => intro _ _ _ _ _; trivial
  | node T y z child w x ih =>
    intro l hist wIn pre hv τ
    obtain ⟨hl, -, -, hprobe, -⟩ := hv
    exact ⟨hl, ih τ _ _ _ _ (hprobe τ).2.1⟩

theorem classBound_mono (N k D : ℕ) {Q Q' : ℕ} (h : Q ≤ Q') :
    classBound N k D Q ≤ classBound N k D Q' := by
  unfold classBound
  exact Nat.mul_le_mul_left _ (faceBound_mono_left (Nat.mul_le_mul_right _ h) k)

/-- **Cost of every probe.** Suppose `c = 2^{-a}` and the rounding map loses at most the
factor `1 - ep` and produces floats with `p + 1` significant bits. At every probe of a valid
run from the root with unit wealth: at most `classBound N k D Q` cells (`Q` the number of
probes of the run), and wealth values that are such floats, lie in `(0, |E|]`, and are at
least `((1 - ep)(1 - c)(1 - η))^t · c^l`. -/
theorem probe_cost (A : Alg V) (hc0 : 0 < A.c) (hc1 : A.c < 1) (hη0 : 0 < A.η)
    (hη1 : A.η < 1) {ep : ℝ} (hep0 : 0 ≤ ep) (hep1 : ep < 1)
    (hrnd : ∀ x : ℝ, 0 < x → (1 - ep) * x ≤ A.rnd x ∧ A.rnd x ≤ x)
    (p a : ℕ) (hc : A.c = 1 / (2 : ℝ) ^ a) (hfl : ∀ x : ℝ, 0 < x → IsFloat p (A.rnd x))
    (X : Exec ι (Expert ι V k D)) (hist₀ : ℕ → ι → ℝ)
    (hX : X.Valid A 0 hist₀ (fun _ => 1)) :
    X.ForallProbes
      (ProbeCost A.val p ((1 - ep) * (1 - A.c) * (1 - A.η)) A.c
        (classBound (Fintype.card ι) k D X.queries) X.queries)
      0 hist₀ [] := by
  have h1 := cells_at_every_probe A X hist₀ hX
  have h2 := X.forallProbes_length 0 hist₀ [] X.queries (by simp)
  have h3 := X.forallProbes_level A 0 hist₀ (fun _ => 1) [] hX
  have h4 := (X.wealth_float A hc0 hc1 hη0 hη1 hep1 hrnd p a hc hfl 0 hist₀ (fun _ => 1) [] hX
    (fun _ => one_pos) (fun _ => IsFloat.one p)).1
  have h5 := X.wealth_total A hc0 hc1 hη0 hη1 hep1 hrnd 0 hist₀ (fun _ => 1) []
    (Fintype.card (Expert ι V k D)) hX (fun _ => one_pos) (by simp)
  have h6 := (X.wealth_lower A hc0 hc1 hη0 hη1 hep0 hep1 hrnd 0 hist₀ (fun _ => 1) [] hX
    (fun _ => one_pos) (fun _ => by simp)).1
  have h := Exec.ForallProbes.and X 0 hist₀ [] h1
    (Exec.ForallProbes.and X 0 hist₀ [] h2
      (Exec.ForallProbes.and X 0 hist₀ [] h3
        (Exec.ForallProbes.and X 0 hist₀ [] h4 (Exec.ForallProbes.and X 0 hist₀ [] h5 h6))))
  refine Exec.ForallProbes.mono ?_ X 0 hist₀ [] h
  rintro pre l hist y w ⟨hcell, hlen, hlev, hfloat, ⟨hpos, hsum⟩, hlow⟩
  refine ⟨⟨hlen, hlev⟩, hcell, fun e => ⟨hpos e, ?_, hfloat e, hlow e⟩⟩
  exact (Finset.single_le_sum (fun i _ => (hpos i).le) (Finset.mem_univ e)).trans hsum

/-- The sum over all probes of the cell bound: at most `Q · classBound N k D Q`, and for
`Q ≤ 2 ρ M^e` with `M = 2N` this is at most
`2 ρ (4 · pairs k · ρ + 1)^k (D M + 1) M^(e (k+1) + k)`. -/
theorem total_cells_le (N k D e ρ Q : ℕ) (hN : 1 ≤ N) (hQ : Q ≤ 2 * ρ * (2 * N) ^ e) :
    Q * classBound N k D Q
      ≤ 2 * ρ * (4 * pairs k * ρ + 1) ^ k * (D * (2 * N) + 1) * (2 * N) ^ (e * (k + 1) + k) := by
  have hM : 1 ≤ (2 * N) ^ e := Nat.one_le_pow _ _ (by omega)
  have hface : faceBound (Q * pairs k) k ≤ ((4 * pairs k * ρ + 1) * (2 * N) ^ e) ^ k := by
    refine (faceBound_le_pow _ _).trans (Nat.pow_le_pow_left ?_ k)
    calc 2 * (Q * pairs k) + 1
        ≤ 2 * (2 * ρ * (2 * N) ^ e * pairs k) + 1 := by
          have := Nat.mul_le_mul_right (pairs k) hQ
          omega
      _ = 4 * pairs k * ρ * (2 * N) ^ e + 1 := by ring
      _ ≤ 4 * pairs k * ρ * (2 * N) ^ e + (2 * N) ^ e := by omega
      _ = (4 * pairs k * ρ + 1) * (2 * N) ^ e := by ring
  unfold classBound
  calc Q * ((2 * N) ^ k * (D * (2 * N) + 1) * faceBound (Q * pairs k) k)
      ≤ (2 * ρ * (2 * N) ^ e) * ((2 * N) ^ k * (D * (2 * N) + 1)
          * ((4 * pairs k * ρ + 1) * (2 * N) ^ e) ^ k) :=
        Nat.mul_le_mul hQ (Nat.mul_le_mul_left _ hface)
    _ = 2 * ρ * (4 * pairs k * ρ + 1) ^ k * (D * (2 * N) + 1)
          * (2 * N) ^ (e * (k + 1) + k) := by
        have h1 : ((4 * pairs k * ρ + 1) * (2 * N) ^ e) ^ k
            = (4 * pairs k * ρ + 1) ^ k * (2 * N) ^ (e * k) := by
          rw [Nat.mul_pow, ← pow_mul]
        have h2 : (2 * N) ^ (e * (k + 1) + k)
            = (2 * N) ^ e * (2 * N) ^ k * (2 * N) ^ (e * k) := by
          rw [← pow_add, ← pow_add]
          congr 1
          ring
        rw [h1, h2]
        ring

namespace Consts

variable {k : ℕ}

/-- **Cost of every probe, for good constants.** At every probe of every valid run: at most
`classBound N k D Qmax` cells, where `Qmax = 2 r₀ (2N)^e` bounds the number of probes, and
wealth values that are floats with `p + 1` significant bits in `(0, |E|]`, at least
`((1 - ep)(1 - c)(1 - η))^t · c^l`. -/
theorem probe_cost (K : Consts k) (hK : K.Good) (e : ℕ)
    (he : ((K.r : ℚ)) ^ 2 ≤ (K.ρ ^ 2 / K.β) ^ e)
    {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V]
    [Nonempty ι] (val : V → ℝ)
    (X : Exec ι (Expert ι V k (K.depth hK (Fintype.card ι)))) (hist₀ : ℕ → ι → ℝ)
    (hX : X.Valid (K.alg hK ι V val) 0 hist₀ (fun _ => 1)) :
    X.ForallProbes
      (ProbeCost val K.p ((1 - (K.ep : ℝ)) * (1 - (K.c : ℝ)) * (1 - (K.η : ℝ))) (K.c : ℝ)
        (classBound (Fintype.card ι) k (K.depth hK (Fintype.card ι))
          (2 * K.r₀ ι V (K.depth hK (Fintype.card ι)) * (2 * Fintype.card ι) ^ e))
        (2 * K.r₀ ι V (K.depth hK (Fintype.card ι)) * (2 * Fintype.card ι) ^ e))
      0 hist₀ [] := by
  have hq := (K.price_search hK e he val X hist₀ hX).2
  have hc : (K.alg hK ι V val).c = 1 / (2 : ℝ) ^ K.a := by
    show ((K.c : ℚ) : ℝ) = 1 / (2 : ℝ) ^ K.a
    simp only [Consts.c]
    push_cast
    ring
  have h := SPLP.probe_cost (K.alg hK ι V val) (K.params hK ι V val).hc0
    (K.params hK ι V val).hc1 (K.params hK ι V val).hη0 (K.params hK ι V val).hη1
    (K.params hK ι V val).hep0 (K.params hK ι V val).hep1 (K.params hK ι V val).hrnd
    K.p K.a hc (fun x hx => fl_isFloat K.p hx) X hist₀ hX
  refine Exec.ForallProbes.mono ?_ X 0 hist₀ [] h
  rintro pre l hist y w ⟨⟨h1, h2⟩, hcells, hsize⟩
  refine ⟨⟨lt_of_lt_of_le h1 hq, h2⟩, fun y' => ?_, hsize⟩
  obtain ⟨cell, hcard, hcell⟩ := hcells y'
  exact ⟨cell, hcard.trans (classBound_mono _ _ _ hq), hcell⟩

end Consts

end SPLP
