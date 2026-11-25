import Mathlib
import SPLP.HalfInt
import SPLP.Cells

/-!
# Runs with vertex proposals

The algorithm may always propose a vertex minimizer. In such runs, for integer demands bounded
by `R`, every proposal is half-integral and bounded by `(l + 1) · 2R(N + 1)` at level `l`. So a
proposal coordinate takes one of at most `8 D R (N + 1) + 1` values, whatever the wealth.
-/

set_option linter.unusedSectionVars false

namespace SPLP

open Finset

variable {ι V : Type*} {k D : ℕ} [Fintype ι] [DecidableEq ι] [Fintype V]

/-- Every proposal of the run is a vertex of its market potential. -/
def Exec.VertexRun (val : V → ℝ) : Exec ι (Expert ι V k D) → ℕ → (ℕ → ι → ℝ) → Prop
  | .leaf _ _, _, _ => True
  | .node T y _ child _ _, l, hist =>
      ∀ τ : Fin T, IsVertex (k := k) (D := D) val l hist (y τ) ∧
        (child τ).VertexRun val (l + 1) (Function.update hist l (y τ))

theorem exists_valid_vertex_aux [Nonempty V] (hk : 0 < k) (A : Alg V) (hc0 : 0 < A.c)
    (hc1 : A.c < 1) (hη0 : 0 < A.η) (hη1 : A.η < 1) {ep : ℝ} (hep1 : ep < 1)
    (hrnd : ∀ x : ℝ, 0 < x → (1 - ep) * x ≤ A.rnd x ∧ A.rnd x ≤ x)
    (oracle : List ℕ → (ι → ℝ) → (ι → Bool)) :
    ∀ (d l : ℕ), l + d = D → ∀ (hist : ℕ → ι → ℝ) (wIn : Expert ι V k D → ℝ) (pos : List ℕ),
      (∀ e, 0 < wIn e) →
      ∃ X : Exec ι (Expert ι V k D),
        X.Valid A l hist wIn ∧ X.LabelsFrom oracle pos ∧ X.VertexRun A.val l hist := by
  intro d
  induction d with
  | zero =>
    intro l hl hist wIn pos _
    choose x hx using fun i => exists_isMedian (fun j : Fin l => hist j i)
    exact ⟨.leaf x wIn, ⟨by omega, rfl, hx⟩, trivial, trivial⟩
  | succ d ih =>
    intro l hl hist wIn pos hpos
    have hlD : l < D := by omega
    have hstep : ∀ (n : ℕ) (w : Expert ι V k D → ℝ),
        ∃ (y : ι → ℝ) (c : Exec ι (Expert ι V k D)), (∀ e, 0 < w e) →
          (∀ y', Phi A.val l hist (fun e => (1 - A.c) * w e) y
              ≤ Phi A.val l hist (fun e => (1 - A.c) * w e) y') ∧
          IsVertex (k := k) (D := D) A.val l hist y ∧
          c.Valid A (l + 1) (Function.update hist l y) (fun e => A.c * w e) ∧
          c.LabelsFrom oracle (pos ++ [n]) ∧
          c.VertexRun A.val (l + 1) (Function.update hist l y) := by
      intro n w
      by_cases hw : ∀ e, 0 < w e
      · obtain ⟨y, hy, hvert⟩ := exists_vertex_min hk A.val l hist (fun e => (1 - A.c) * w e)
          (fun e => mul_pos (by linarith) (hw e))
        obtain ⟨c, hcv, hcl, hcvr⟩ := ih (l + 1) (by omega) (Function.update hist l y)
          (fun e => A.c * w e) (pos ++ [n]) (fun e => mul_pos hc0 (hw e))
        exact ⟨y, c, fun _ => ⟨hy, hvert, hcv, hcl, hcvr⟩⟩
      · exact ⟨0, .leaf 0 0, fun h => absurd h hw⟩
    choose ystep cstep hspec using hstep
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
        obtain ⟨-, -, hcv, -, -⟩ := hspec n (W n) ihn
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
      ?_, ?_, ?_⟩
    · refine ⟨hlD, rfl, rfl, fun τ => ?_, hx⟩
      obtain ⟨hmin, -, hcv, -, -⟩ := hspec τ (W τ) (hWpos τ)
      exact ⟨hmin, hcv, fun e => by rw [hWs τ]⟩
    · intro τ
      exact ⟨rfl, (hspec τ (W τ) (hWpos τ)).2.2.2.1⟩
    · intro τ
      exact ⟨(hspec τ (W τ) (hWpos τ)).2.1, (hspec τ (W τ) (hWpos τ)).2.2.2.2⟩

/-- **Vertex runs exist** against every labelling rule. -/
theorem exists_valid_vertex [Nonempty V] (hk : 0 < k) (A : Alg V) (hc0 : 0 < A.c)
    (hc1 : A.c < 1) (hη0 : 0 < A.η) (hη1 : A.η < 1) {ep : ℝ} (hep1 : ep < 1)
    (hrnd : ∀ x : ℝ, 0 < x → (1 - ep) * x ≤ A.rnd x ∧ A.rnd x ≤ x)
    (oracle : List ℕ → (ι → ℝ) → (ι → Bool)) (hist₀ : ℕ → ι → ℝ) :
    ∃ X : Exec ι (Expert ι V k D),
      X.Valid A 0 hist₀ (fun _ => 1) ∧ X.LabelsFrom oracle [] ∧ X.VertexRun A.val 0 hist₀ :=
  exists_valid_vertex_aux hk A hc0 hc1 hη0 hη1 hep1 hrnd oracle D 0 (by omega) hist₀ _ []
    (fun _ => one_pos)

/-- In a vertex run with integer demands, every proposal is half-integral. -/
theorem Exec.vertexRun_halfInt (val : V → ℝ) (hint : ∀ v, ∃ z : ℤ, val v = z)
    (X : Exec ι (Expert ι V k D)) :
    ∀ (l : ℕ) (hist : ℕ → ι → ℝ) (pre : List (Ctx ι)), X.VertexRun val l hist →
      (∀ j, j < l → ∀ i, ∃ z : ℤ, 2 * hist j i = z) →
      X.ForallProbes (fun _ _ _ y _ => ∀ i, ∃ z : ℤ, 2 * y i = z) l hist pre := by
  induction X with
  | leaf x wOut => intro _ _ _ _ _; trivial
  | node T y z child w x ih =>
    intro l hist pre hv hh τ
    have hy := halfInt_of_vertex val l hist (y τ) hint hh (hv τ).1
    refine ⟨hy, ih τ (l + 1) _ _ (hv τ).2 ?_⟩
    intro j hj i
    by_cases hjl : j = l
    · subst hjl
      rw [Function.update_self]
      exact hy i
    · rw [Function.update_of_ne hjl]
      exact hh j (by omega) i

/-- In a vertex run with demands bounded by `R`, a proposal at level `l` is bounded by
`(l + 1) · 2R(N + 1)`. -/
theorem Exec.vertexRun_bound (val : V → ℝ) (R : ℝ) (hR0 : 0 ≤ R) (hR : ∀ v, |val v| ≤ R)
    (X : Exec ι (Expert ι V k D)) :
    ∀ (l : ℕ) (hist : ℕ → ι → ℝ) (pre : List (Ctx ι)), X.VertexRun val l hist →
      (∀ j, j < l → ∀ i, |hist j i| ≤ l * (2 * R * (Fintype.card ι + 1))) →
      X.ForallProbes
        (fun _ l' _ y _ => ∀ i, |y i| ≤ (l' + 1) * (2 * R * (Fintype.card ι + 1)))
        l hist pre := by
  have hB : (0 : ℝ) ≤ 2 * R * (Fintype.card ι + 1) := by positivity
  induction X with
  | leaf x wOut => intro _ _ _ _ _; trivial
  | node T y z child w x ih =>
    intro l hist pre hv hh τ
    have hy : ∀ i, |y τ i| ≤ (l + 1) * (2 * R * (Fintype.card ι + 1)) := by
      intro i
      have := bound_of_vertex val l hist (y τ) R (l * (2 * R * (Fintype.card ι + 1))) hR hh
        (by positivity) (hv τ).1 i
      linarith
    refine ⟨hy, ih τ (l + 1) _ _ (hv τ).2 ?_⟩
    intro j hj i
    by_cases hjl : j = l
    · subst hjl
      rw [Function.update_self]
      push_cast
      exact hy i
    · rw [Function.update_of_ne hjl]
      have h1 := hh j (by omega) i
      push_cast
      nlinarith

end SPLP
