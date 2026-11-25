import Mathlib
import SPLP.Cells
import SPLP.Float

/-!
# Size of the wealth values

When every updated wealth value is rounded down to `p + 1` significant bits, every wealth value
handled at a probe is a float `m · 2^j` with `m < 2^(p+1)`, lies in `(0, |E|]`, and is at least
`ρ₀^t · c^l`, where `t` is the number of probes completed before, `l` the level, and
`ρ₀ = (1 - ep)(1 - c)(1 - η)`. So a wealth value takes `p + 1` bits of mantissa and an exponent
of size logarithmic in `t`.
-/

set_option linter.unusedSectionVars false

namespace SPLP

open Finset

/-- `x` is an integer multiple of `Q^{-M}`. -/
def IsFrac (Q M : ℕ) (x : ℝ) : Prop := ∃ m : ℤ, x = m / (Q : ℝ) ^ M

namespace IsFrac

variable {Q M M' : ℕ} {x y : ℝ}

theorem mono (hQ : 0 < Q) (h : M ≤ M') (hx : IsFrac Q M x) : IsFrac Q M' x := by
  obtain ⟨m, rfl⟩ := hx
  refine ⟨m * (Q : ℤ) ^ (M' - M), ?_⟩
  have hQ' : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hpow : (Q : ℝ) ^ M' = (Q : ℝ) ^ M * (Q : ℝ) ^ (M' - M) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow]
  push_cast
  field_simp

theorem add (hx : IsFrac Q M x) (hy : IsFrac Q M y) : IsFrac Q M (x + y) := by
  obtain ⟨m, rfl⟩ := hx
  obtain ⟨n, rfl⟩ := hy
  exact ⟨m + n, by push_cast; ring⟩

theorem mul (hx : IsFrac Q M x) (hy : IsFrac Q M' y) : IsFrac Q (M + M') (x * y) := by
  obtain ⟨m, rfl⟩ := hx
  obtain ⟨n, rfl⟩ := hy
  exact ⟨m * n, by push_cast; rw [pow_add]; ring⟩

theorem one : IsFrac Q 0 1 := ⟨1, by simp⟩

/-- A value in `(0, B]` that is a multiple of `Q^{-M}` has a numerator in `(0, B Q^M]`. -/
theorem num_bound (hQ : 0 < Q) {B : ℝ} (hx : IsFrac Q M x) (h0 : 0 < x) (hB : x ≤ B) :
    ∃ m : ℤ, x = m / (Q : ℝ) ^ M ∧ 0 < m ∧ (m : ℝ) ≤ B * (Q : ℝ) ^ M := by
  obtain ⟨m, rfl⟩ := hx
  have hpow : (0 : ℝ) < (Q : ℝ) ^ M := pow_pos (by exact_mod_cast hQ) M
  refine ⟨m, rfl, ?_, ?_⟩
  · have : (0 : ℝ) < m := by
      by_contra hcon
      have : (m : ℝ) / (Q : ℝ) ^ M ≤ 0 := div_nonpos_of_nonpos_of_nonneg (not_lt.1 hcon) hpow.le
      linarith
    exact_mod_cast this
  · rwa [div_le_iff₀ hpow] at hB

end IsFrac

variable {ι V : Type*} {k D : ℕ} [Fintype ι] [DecidableEq ι]

/-- Gains are integers (`-1`, `0` or `1`). -/
theorem gain_int (val : V → ℝ) (l : ℕ) (hist : ℕ → ι → ℝ) (y : ι → ℝ) (v : ι → Bool)
    (e : Expert ι V k D) : ∃ z : ℤ, gain val l hist y v e = z := by
  obtain ⟨o, -, ho⟩ := Finset.exists_mem_eq_inf' (bestSet_nonempty (bidOf val l hist)
    (dirOf val l hist) e y) (fun o => pay (dirOf val l hist) e o (vreal v))
  have hgain : gain val l hist y v e = pay (dirOf val l hist) e o (vreal v) := ho
  rw [hgain]
  cases o with
  | none => exact ⟨0, by rw [pay_none]; simp⟩
  | some q =>
    cases h : thr val l hist e with
    | none => exact ⟨0, by rw [pay_some_of_inactive h]; simp⟩
    | some τ =>
      rw [pay_some_of_thr h]
      split_ifs
      · exact ⟨1, by simp⟩
      · exact ⟨-1, by simp⟩

variable [Fintype V]

/-- **Wealth values are floats.** If the rounding map produces floats with `p + 1` significant
bits and `c = 2^{-a}`, then in a valid run entered with float wealth, the wealth before every
probe and the returned wealth are floats. -/
theorem Exec.wealth_float (A : Alg V) (hc0 : 0 < A.c) (hc1 : A.c < 1) (hη0 : 0 < A.η)
    (hη1 : A.η < 1) {ep : ℝ} (hep1 : ep < 1)
    (hrnd : ∀ x : ℝ, 0 < x → (1 - ep) * x ≤ A.rnd x ∧ A.rnd x ≤ x)
    (p a : ℕ) (hc : A.c = 1 / (2 : ℝ) ^ a) (hfl : ∀ x : ℝ, 0 < x → IsFloat p (A.rnd x))
    (X : Exec ι (Expert ι V k D)) :
    ∀ (l : ℕ) (hist : ℕ → ι → ℝ) (wIn : Expert ι V k D → ℝ) (pre : List (Ctx ι)),
      X.Valid A l hist wIn → (∀ e, 0 < wIn e) → (∀ e, IsFloat p (wIn e)) →
      X.ForallProbes (fun _ _ _ _ w => ∀ e, IsFloat p (w e)) l hist pre ∧
        (∀ e, IsFloat p (X.wOut e)) := by
  induction X with
  | leaf x wOut =>
    intro l hist wIn pre hv _ hin
    obtain ⟨-, hw, -⟩ := hv
    refine ⟨trivial, fun e => ?_⟩
    simp only [Exec.wOut, hw]
    exact hin e
  | node T y z child w x ih =>
    intro l hist wIn pre hv hpos hin
    have hwealth := node_wealth_aux A hc0 hc1 hη0 hη1 hep1 hrnd hv hpos
      (fun τ => Exec.wealth A hc0 hc1 hη0 hη1 hep1 hrnd (child τ))
    obtain ⟨-, -, hw0, hprobe, -⟩ := hv
    have key : ∀ n, n ≤ T → ∀ e, IsFloat p (w n e) := by
      intro n
      induction n with
      | zero =>
        intro _ e
        rw [hw0]
        exact hin e
      | succ n _ =>
        intro hn e
        have hn' : n < T := hn
        obtain ⟨-, hchild, hstep⟩ := hprobe ⟨n, hn'⟩
        have hwn := (hwealth n (Nat.le_of_lt hn')).1
        have hcout := (Exec.wealth A hc0 hc1 hη0 hη1 hep1 hrnd (child ⟨n, hn'⟩) _ _ _ hchild
          (fun e => mul_pos hc0 (hwn e))).1 e
        have hg := (gain_bounds A.val l hist e (y ⟨n, hn'⟩)
          (feedback (y ⟨n, hn'⟩) (child ⟨n, hn'⟩).x (z ⟨n, hn'⟩))).1
        have h1 : 0 < 1 + A.η * gain A.val l hist (y ⟨n, hn'⟩)
            (feedback (y ⟨n, hn'⟩) (child ⟨n, hn'⟩).x (z ⟨n, hn'⟩)) e := by nlinarith
        have hX := add_pos (mul_pos (mul_pos (by linarith : 0 < 1 - A.c) (hwn e)) h1) hcout
        have hs := hstep e
        simp only at hs
        rw [hs]
        exact hfl _ hX
    refine ⟨fun τ => ⟨key τ (Nat.le_of_lt τ.2), ?_⟩, key T le_rfl⟩
    refine (ih τ (l + 1) _ _ _ (hprobe τ).2.1
      (fun e => mul_pos hc0 ((hwealth τ (Nat.le_of_lt τ.2)).1 e)) (fun e => ?_)).1
    rw [hc]
    exact (key τ (Nat.le_of_lt τ.2) e).div_two_pow a

/-- **Wealth is not too small.** With `ρ₀ = (1 - ep)(1 - c)(1 - η)`: in a valid run entered at
level `l` after the probes `pre` with wealth at least `ρ₀^|pre| · c^l`, the wealth before a
probe at level `l'` with `t` probes completed before it is at least `ρ₀^t · c^l'`. -/
theorem Exec.wealth_lower (A : Alg V) (hc0 : 0 < A.c) (hc1 : A.c < 1) (hη0 : 0 < A.η)
    (hη1 : A.η < 1) {ep : ℝ} (hep0 : 0 ≤ ep) (hep1 : ep < 1)
    (hrnd : ∀ x : ℝ, 0 < x → (1 - ep) * x ≤ A.rnd x ∧ A.rnd x ≤ x)
    (X : Exec ι (Expert ι V k D)) :
    ∀ (l : ℕ) (hist : ℕ → ι → ℝ) (wIn : Expert ι V k D → ℝ) (pre : List (Ctx ι)),
      X.Valid A l hist wIn → (∀ e, 0 < wIn e) →
      (∀ e, ((1 - ep) * (1 - A.c) * (1 - A.η)) ^ pre.length * A.c ^ l ≤ wIn e) →
      X.ForallProbes (fun pre' l' _ _ w =>
          ∀ e, ((1 - ep) * (1 - A.c) * (1 - A.η)) ^ pre'.length * A.c ^ l' ≤ w e) l hist pre ∧
        (∀ e, ((1 - ep) * (1 - A.c) * (1 - A.η)) ^ (pre.length + (X.contexts l hist).length)
          * A.c ^ l ≤ X.wOut e) := by
  have hρ0 : 0 < (1 - ep) * (1 - A.c) * (1 - A.η) :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  have hρ1 : (1 - ep) * (1 - A.c) * (1 - A.η) ≤ 1 := by
    have h1 : (1 - ep) * (1 - A.c) ≤ 1 := by nlinarith
    have h2 : 0 ≤ (1 - ep) * (1 - A.c) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  induction X with
  | leaf x wOut =>
    intro l hist wIn pre hv _ hin
    obtain ⟨-, hw, -⟩ := hv
    refine ⟨trivial, fun e => ?_⟩
    simp only [Exec.contexts, List.length_nil, Nat.add_zero, Exec.wOut, hw]
    exact hin e
  | node T y z child w x ih =>
    intro l hist wIn pre hv hpos hin
    have hwealth := node_wealth_aux A hc0 hc1 hη0 hη1 hep1 hrnd hv hpos
      (fun τ => Exec.wealth A hc0 hc1 hη0 hη1 hep1 hrnd (child τ))
    obtain ⟨-, -, hw0, hprobe, -⟩ := hv
    have hcl : 0 ≤ A.c ^ l := pow_nonneg hc0.le l
    have key : ∀ n, n ≤ T → ∀ e,
        ((1 - ep) * (1 - A.c) * (1 - A.η)) ^
            (pre.length + (before (nodeSegs T y child l hist) n).length) * A.c ^ l ≤ w n e := by
      intro n
      induction n with
      | zero =>
        intro _ e
        rw [hw0]
        simpa [before] using hin e
      | succ n ihn =>
        intro hn e
        have hn' : n < T := hn
        obtain ⟨-, hchild, hstep⟩ := hprobe ⟨n, hn'⟩
        have hwn := (hwealth n (Nat.le_of_lt hn')).1
        have hcout := (Exec.wealth A hc0 hc1 hη0 hη1 hep1 hrnd (child ⟨n, hn'⟩) _ _ _ hchild
          (fun e => mul_pos hc0 (hwn e))).1 e
        have hg := (gain_bounds A.val l hist e (y ⟨n, hn'⟩)
          (feedback (y ⟨n, hn'⟩) (child ⟨n, hn'⟩).x (z ⟨n, hn'⟩))).1
        have h1 : 1 - A.η ≤ 1 + A.η * gain A.val l hist (y ⟨n, hn'⟩)
            (feedback (y ⟨n, hn'⟩) (child ⟨n, hn'⟩).x (z ⟨n, hn'⟩)) e := by nlinarith
        have h1' : 0 < 1 + A.η * gain A.val l hist (y ⟨n, hn'⟩)
            (feedback (y ⟨n, hn'⟩) (child ⟨n, hn'⟩).x (z ⟨n, hn'⟩)) e := by linarith
        have hX := add_pos (mul_pos (mul_pos (by linarith : 0 < 1 - A.c) (hwn e)) h1') hcout
        have hs := hstep e
        simp only at hs
        -- one probe loses at most the factor `ρ₀`
        have hstep1 : (1 - ep) * (1 - A.c) * (1 - A.η) * w n e ≤ w (n + 1) e := by
          rw [hs]
          refine le_trans ?_ (hrnd _ hX).1
          have h2 : (1 - A.c) * w n e * (1 - A.η)
              ≤ (1 - A.c) * w n e * (1 + A.η * gain A.val l hist (y ⟨n, hn'⟩)
                (feedback (y ⟨n, hn'⟩) (child ⟨n, hn'⟩).x (z ⟨n, hn'⟩)) e) :=
            mul_le_mul_of_nonneg_left h1 (mul_pos (by linarith) (hwn e)).le
          have h3 : (1 - ep) * ((1 - A.c) * w n e * (1 - A.η))
              ≤ (1 - ep) * ((1 - A.c) * w n e * (1 + A.η * gain A.val l hist (y ⟨n, hn'⟩)
                (feedback (y ⟨n, hn'⟩) (child ⟨n, hn'⟩).x (z ⟨n, hn'⟩)) e)
                + (child ⟨n, hn'⟩).wOut e) :=
            mul_le_mul_of_nonneg_left (by linarith) (by linarith)
          calc (1 - ep) * (1 - A.c) * (1 - A.η) * w n e
              = (1 - ep) * ((1 - A.c) * w n e * (1 - A.η)) := by ring
            _ ≤ _ := h3
        have hlen : (before (nodeSegs T y child l hist) n).length + 1
            ≤ (before (nodeSegs T y child l hist) (n + 1)).length := by
          have hbs := before_succ (nodeSegs T y child l hist) ⟨n, hn'⟩
          simp only at hbs
          rw [hbs, List.length_append]
          simp [nodeSegs]
        have hpow : ((1 - ep) * (1 - A.c) * (1 - A.η)) ^
              (pre.length + (before (nodeSegs T y child l hist) (n + 1)).length)
            ≤ ((1 - ep) * (1 - A.c) * (1 - A.η)) ^
              (pre.length + (before (nodeSegs T y child l hist) n).length + 1) :=
          pow_le_pow_of_le_one hρ0.le hρ1 (by omega)
        calc ((1 - ep) * (1 - A.c) * (1 - A.η)) ^
              (pre.length + (before (nodeSegs T y child l hist) (n + 1)).length) * A.c ^ l
            ≤ ((1 - ep) * (1 - A.c) * (1 - A.η)) ^
              (pre.length + (before (nodeSegs T y child l hist) n).length + 1) * A.c ^ l :=
              mul_le_mul_of_nonneg_right hpow hcl
          _ = (1 - ep) * (1 - A.c) * (1 - A.η) * (((1 - ep) * (1 - A.c) * (1 - A.η)) ^
              (pre.length + (before (nodeSegs T y child l hist) n).length) * A.c ^ l) := by
              rw [pow_succ]; ring
          _ ≤ (1 - ep) * (1 - A.c) * (1 - A.η) * w n e :=
              mul_le_mul_of_nonneg_left (ihn (Nat.le_of_lt hn') e) hρ0.le
          _ ≤ w (n + 1) e := hstep1
    refine ⟨fun τ => ⟨fun e => ?_, ?_⟩, fun e => ?_⟩
    · have := key τ (Nat.le_of_lt τ.2) e
      simpa [List.length_append] using this
    · refine (ih τ (l + 1) _ _ _ (hprobe τ).2.1
        (fun e => mul_pos hc0 ((hwealth τ (Nat.le_of_lt τ.2)).1 e)) (fun e => ?_)).1
      have := key τ (Nat.le_of_lt τ.2) e
      have h2 := mul_le_mul_of_nonneg_left this hc0.le
      calc ((1 - ep) * (1 - A.c) * (1 - A.η)) ^
            (pre ++ before (nodeSegs T y child l hist) τ).length * A.c ^ (l + 1)
          = A.c * (((1 - ep) * (1 - A.c) * (1 - A.η)) ^
            (pre.length + (before (nodeSegs T y child l hist) τ).length) * A.c ^ l) := by
            rw [List.length_append, pow_succ]; ring
        _ ≤ A.c * w τ e := h2
    · rw [Exec.contexts_node]
      exact key T le_rfl e

/-- **Size of wealth.** At every probe of a valid run, wealth is positive and of total at most
the total entering the run. -/
theorem Exec.wealth_total (A : Alg V) (hc0 : 0 < A.c) (hc1 : A.c < 1) (hη0 : 0 < A.η)
    (hη1 : A.η < 1) {ep : ℝ} (hep1 : ep < 1)
    (hrnd : ∀ x : ℝ, 0 < x → (1 - ep) * x ≤ A.rnd x ∧ A.rnd x ≤ x)
    (X : Exec ι (Expert ι V k D)) :
    ∀ (l : ℕ) (hist : ℕ → ι → ℝ) (wIn : Expert ι V k D → ℝ) (pre : List (Ctx ι)) (B : ℝ),
      X.Valid A l hist wIn → (∀ e, 0 < wIn e) → ∑ e, wIn e ≤ B →
      X.ForallProbes (fun _ _ _ _ w => (∀ e, 0 < w e) ∧ ∑ e, w e ≤ B) l hist pre := by
  induction X with
  | leaf x wOut => intro _ _ _ _ _ _ _ _; trivial
  | node T y z child w x ih =>
    intro l hist wIn pre B hv hpos hB τ
    have hw := node_wealth_aux A hc0 hc1 hη0 hη1 hep1 hrnd hv hpos
      (fun τ => Exec.wealth A hc0 hc1 hη0 hη1 hep1 hrnd (child τ)) τ (Nat.le_of_lt τ.2)
    obtain ⟨-, -, -, hprobe, -⟩ := hv
    refine ⟨⟨hw.1, hw.2.trans hB⟩, ?_⟩
    refine ih τ (l + 1) _ _ _ B (hprobe τ).2.1 (fun e => mul_pos hc0 (hw.1 e)) ?_
    have hsum0 : 0 ≤ ∑ e, w τ e := Finset.sum_nonneg (fun e _ => (hw.1 e).le)
    rw [← Finset.mul_sum]
    nlinarith [hw.2]

end SPLP
