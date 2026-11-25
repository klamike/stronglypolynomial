import Mathlib
import SPLP.Descent
import SPLP.Invariant

/-!
# Margins, rounding and localization

Tools for reducing the range of the demands, and the point at which they stop.

* `lockstep_feedback_margin`: `n` exact-label queries of the lockstep descent started at an
  integral point `y` give a feedback vector at `y` that is correct on every slot whose surplus
  is within `n / 2` of the maximum. Exact labels can be turned into labels with a margin, at a
  cost linear in the margin.
* `consistentAt_of_margin_of_round`: labels with margin `G` for a hypothesis are exact labels
  for every hypothesis obtained by rounding its demands down by at most `G`. With a margin the
  demands may be taken from a grid of width `G`.
* `Hyp.localize_consistentAt`, `Hyp.localize_range`, `Hyp.localize_meets`: lowering all demands
  by `τ ≥ 0` and truncating them to the cube of radius `r` around a point `y` whose surpluses
  are below `τ + r` gives a hypothesis with demands within `r` of `y` that is consistent with
  the original labels after an explicit override outside the cube. Meeting it brings every
  original surplus down to `τ`. With `feedback_correct` this says that one label with margin
  `r` costs no more than one price search of range `r`
  (`feedback_margin_of_localized`).
-/

namespace SPLP

variable {ι V : Type*}

/-! ### Exact labels give labels with a margin -/

/-- After `n` lockstep queries from a point `y` with integral surpluses, the feedback at `y`
from the reached point is correct on every slot whose doubled surplus at `y` is at least
`B₀ - n`, where `B₀` bounds the doubled surpluses at `y`. -/
theorem lockstep_feedback_margin [Fintype ι] [DecidableEq ι] {val : V → ℝ} {H : Hyp ι V} (z : ℕ → ι → Bool) (y : ι → ℝ)
    (hint : H.IntAt val y) (hcons : ∀ n, H.ConsistentAt val (halfRun z y n) (z n))
    (B₀ : ℕ) (hB₀ : ∀ s ∈ H.S, 2 * H.surplus val y s ≤ B₀) (n : ℕ) (hn : n ≤ B₀) :
    ∀ s ∈ H.S, ((B₀ : ℝ) - n) / 2 ≤ H.surplus val y s →
      feedback y (halfRun z y n) (z n) s.1 = s.2 := by
  have hmax : ((max ((B₀ : ℤ) - n) 0 : ℤ) : ℝ) = (B₀ : ℝ) - n := by
    rw [max_eq_left (by omega)]
    push_cast
    ring
  refine feedback_correct val H y (halfRun z y n) (z n) (((B₀ : ℝ) - n) / 2) ?_ ?_ (hcons n)
  · have : (n : ℝ) ≤ B₀ := by exact_mod_cast hn
    linarith
  · intro s hs
    have h := (lockstep_inv z y hint hcons B₀ hB₀ n).2 s hs
    rw [hmax] at h
    linarith

/-! ### A margin allows rounded demands -/

/-- Labels with margin `G` for `H` are exact labels for any hypothesis `H'` on the same slots
whose demands are those of `H` rounded down by at most `G`. -/
theorem consistentAt_of_margin_of_round {V' : Type*} {val : V → ℝ} {val' : V' → ℝ}
    {H : Hyp ι V} {H' : Hyp ι V'} {G : ℝ} {x : ι → ℝ} {z : ι → Bool}
    (hS : H'.S = H.S)
    (hlo : ∀ s ∈ H.S, val' (H'.a s) ≤ val (H.a s))
    (hhi : ∀ s ∈ H.S, val (H.a s) ≤ val' (H'.a s) + G)
    (h : H.ConsistentAtMargin val G x z) : H'.ConsistentAt val' x z := by
  intro s hs hmax h0
  rw [hS] at hs
  refine h s hs (fun u hu => ?_) ⟨s, hs, ?_⟩
  · have h1 := hmax u (by rw [hS]; exact hu)
    have h2 := hhi u hu
    have h3 := hlo s hs
    simp only [Hyp.surplus] at h1 ⊢
    linarith
  · have h3 := hlo s hs
    simp only [Hyp.surplus] at h0 ⊢
    linarith

/-- Meeting the rounded demands leaves every surplus of the original hypothesis at most `G`. -/
theorem surplus_le_of_round_meets {V' : Type*} {val : V → ℝ} {val' : V' → ℝ}
    {H : Hyp ι V} {H' : Hyp ι V'} {G : ℝ} {x : ι → ℝ}
    (hhi : ∀ s ∈ H.S, val (H.a s) ≤ val' (H'.a s) + G)
    (hmeet : ∀ s ∈ H.S, val' (H'.a s) ≤ sp x s) :
    ∀ s ∈ H.S, H.surplus val x s ≤ G := by
  intro s hs
  have h1 := hhi s hs
  have h2 := hmeet s hs
  simp only [Hyp.surplus]
  linarith

/-! ### Localization -/

/-- The hypothesis `H` with all demands lowered by `τ` and then raised to at least `r` below
the point `y`. Its demands are real numbers. -/
noncomputable def Hyp.localize (val : V → ℝ) (H : Hyp ι V) (τ r : ℝ) (y : ι → ℝ) : Hyp ι ℝ where
  S := H.S
  ne := H.ne
  a := fun s => max (val (H.a s) - τ) (sp y s - r)

/-- Labels with the coordinates outside the cube of radius `r` around `y` replaced by the
direction back to the cube. -/
noncomputable def overrideLabel (y : ι → ℝ) (r : ℝ) (p : ι → ℝ) (z : ι → Bool) : ι → Bool :=
  fun i => if y i + r ≤ p i then false else if p i ≤ y i - r then true else z i

theorem Hyp.localize_surplus (val : V → ℝ) (H : Hyp ι V) (τ r : ℝ) (y p : ι → ℝ) (s : Slot ι) :
    (H.localize val τ r y).surplus id p s
      = max (H.surplus val p s - τ) (sp y s - r - sp p s) := by
  simp only [Hyp.surplus, Hyp.localize, id]
  rw [show val (H.a s) - sp p s - τ = val (H.a s) - τ - sp p s by ring, max_sub_sub_right]

/-- The demands of the localized hypothesis are within `r` of the point `y`. -/
theorem Hyp.localize_range {val : V → ℝ} {H : Hyp ι V} {τ r : ℝ} {y : ι → ℝ} (hr : 0 < r)
    (hy : ∀ s ∈ H.S, H.surplus val y s < τ + r) :
    ∀ s ∈ H.S, sp y s - r ≤ (H.localize val τ r y).a s ∧
      (H.localize val τ r y).a s < sp y s + r := by
  intro s hs
  refine ⟨le_max_right _ _, max_lt ?_ (by linarith)⟩
  have := hy s hs
  simp only [Hyp.surplus] at this
  linarith

/-- Meeting the localized hypothesis brings every surplus of `H` down to `τ`. -/
theorem Hyp.localize_meets {val : V → ℝ} {H : Hyp ι V} {τ r : ℝ} {y x : ι → ℝ}
    (hmeet : ∀ s ∈ H.S, (H.localize val τ r y).surplus id x s ≤ 0) :
    ∀ s ∈ H.S, H.surplus val x s ≤ τ := by
  intro s hs
  have h := hmeet s hs
  rw [Hyp.localize_surplus] at h
  linarith [le_max_left (H.surplus val x s - τ) (sp y s - r - sp x s)]

/-- If every surplus of `H` at `y` is below `τ + r` with `τ ≥ 0`, labels consistent with `H` at
`p` become, after the override, consistent with the localized hypothesis at `p`. -/
theorem Hyp.localize_consistentAt {val : V → ℝ} {H : Hyp ι V} {τ r : ℝ} {y p : ι → ℝ}
    {z : ι → Bool} (hτ : 0 ≤ τ) (hr : 0 < r)
    (hy : ∀ s ∈ H.S, H.surplus val y s < τ + r) (h : H.ConsistentAt val p z) :
    (H.localize val τ r y).ConsistentAt id p (overrideLabel y r p z) := by
  rintro ⟨i, b⟩ hs hmax h0
  have hs' : (i, b) ∈ H.S := hs
  rw [Hyp.localize_surplus] at h0
  by_cases hart : H.surplus val p (i, b) - τ ≤ sp y (i, b) - r - sp p (i, b)
  · -- the truncation is active: the point is outside the cube on this side
    rw [max_eq_right hart] at h0
    cases b with
    | true =>
      have h1 : p i ≤ y i - r := by
        simp only [sp, sgn, if_true, one_mul] at h0
        linarith
      have h2 : ¬ y i + r ≤ p i := by
        intro h2
        linarith
      simp [overrideLabel, h1, h2]
    | false =>
      have h1 : y i + r ≤ p i := by
        simp only [sp, sgn, Bool.false_eq_true, if_false] at h0
        linarith
      simp [overrideLabel, h1]
  · -- the true demand is active: the slot has maximum surplus for `H`
    have hgt := not_le.1 hart
    rw [max_eq_left hgt.le] at h0
    have hz : z i = b := by
      refine h (i, b) hs' (fun u hu => ?_) (by linarith)
      have hu' := hmax u hu
      rw [Hyp.localize_surplus, Hyp.localize_surplus, max_eq_left hgt.le] at hu'
      linarith [le_max_left (H.surplus val p u - τ) (sp y u - r - sp p u)]
    have hyb := hy (i, b) hs'
    cases b with
    | true =>
      have h2 : ¬ y i + r ≤ p i := by
        intro h2
        simp only [Hyp.surplus, sp, sgn, if_true, one_mul] at h0 hyb
        linarith
      by_cases h1 : p i ≤ y i - r
      · simp [overrideLabel, h1, h2]
      · simp [overrideLabel, h1, h2, hz]
    | false =>
      by_cases h1 : y i + r ≤ p i
      · simp [overrideLabel, h1]
      · have h2 : ¬ p i ≤ y i - r := by
          intro h2
          simp only [Hyp.surplus, sp, sgn, Bool.false_eq_true, if_false] at h0 hyb
          linarith
        simp [overrideLabel, h1, h2, hz]

/-- One label with a margin from one price search of bounded range: if `x` meets the localized
hypothesis and its label is consistent with `H`, the feedback at `y` is correct on every slot
of surplus at least `τ`, while every surplus at `y` is below `τ + r`. -/
theorem feedback_margin_of_localized [Fintype ι] [DecidableEq ι] {val : V → ℝ} {H : Hyp ι V} {τ r : ℝ} {y x : ι → ℝ}
    {z : ι → Bool} (hτ : 0 ≤ τ)
    (hmeet : ∀ s ∈ H.S, (H.localize val τ r y).surplus id x s ≤ 0)
    (hcons : H.ConsistentAt val x z) :
    ∀ s ∈ H.S, τ ≤ H.surplus val y s → feedback y x z s.1 = s.2 :=
  feedback_correct val H y x z τ hτ (Hyp.localize_meets hmeet) hcons

/-! ### Rounding is impossible with exact labels

Two hypotheses on two coordinates with real demands, and one label rule on the integer points
consistent with both. Their demands rounded down to integers require opposite labels at the
origin. So no rule that turns the labels observed at integer points into labels for the rounded
hypothesis can be right for both: with exact labels, demands cannot be replaced by rounded
demands, whatever is done with the answers. -/

namespace RoundingExample

/-- Demands `1/5` on the first coordinate's slot of sign `b`, and the point `1/2` on the second
coordinate. -/
noncomputable def hyp (b : Bool) : Hyp (Fin 2) ℝ where
  S := {(0, b), (1, true), (1, false)}
  ne := ⟨(0, b), by simp⟩
  a := fun s => if s.1 = 0 then 1 / 5 else if s.2 then 1 / 2 else -(1 / 2)

/-- The demands of `hyp b` rounded down to integers. -/
noncomputable def hypFloor (b : Bool) : Hyp (Fin 2) ℝ where
  S := {(0, b), (1, true), (1, false)}
  ne := ⟨(0, b), by simp⟩
  a := fun s => if s.1 = 0 then 0 else if s.2 then 0 else -1

theorem hypFloor_eq_floor (b : Bool) (s : Slot (Fin 2)) :
    (hypFloor b).a s = ⌊(hyp b).a s⌋ := by
  simp only [hypFloor, hyp]
  split_ifs <;> norm_num [Int.floor_eq_iff]

/-- One label rule on the integer points. -/
def oracle (p : Fin 2 → ℤ) : Fin 2 → Bool :=
  fun i => if i = 0 then decide (p 0 < 0) else decide (p 1 ≤ 0)

/-- The rule is consistent with both hypotheses at every integer point. -/
theorem oracle_consistent (b : Bool) (p : Fin 2 → ℤ) :
    (hyp b).ConsistentAt id (fun i => (p i : ℝ)) (oracle p) := by
  intro s hs hmax h0
  have hs' : s = (0, b) ∨ s = (1, true) ∨ s = (1, false) := by
    simpa [hyp] using hs
  have m1 := hmax (1, true) (by simp [hyp])
  have m2 := hmax (1, false) (by simp [hyp])
  have hp1 : (p 1 : ℝ) ≤ 0 ∨ (1 : ℝ) ≤ p 1 := by
    rcases le_or_gt (p 1) 0 with h | h
    · left; exact_mod_cast h
    · right; exact_mod_cast (by omega : (1 : ℤ) ≤ p 1)
  rcases hs' with rfl | rfl | rfl
  · -- the slot on the first coordinate: its surplus is at least 1/2
    cases b with
    | true =>
      simp only [Hyp.surplus, hyp, sp, sgn, id] at m1 m2 h0
      norm_num at m1 m2 h0
      have h2 : p 0 < 0 := by
        have : (p 0 : ℝ) < 0 := by rcases hp1 with h | h <;> linarith
        exact_mod_cast this
      simp [oracle, h2]
    | false =>
      simp only [Hyp.surplus, hyp, sp, sgn, id] at m1 m2 h0
      norm_num at m1 m2 h0
      have h2 : ¬ p 0 < 0 := by
        have : (0 : ℝ) < p 0 := by rcases hp1 with h | h <;> linarith
        have : (0 : ℤ) < p 0 := by exact_mod_cast this
        omega
      simp [oracle, h2]
  · simp only [Hyp.surplus, hyp, sp, sgn, id] at h0
    norm_num at h0
    have h2 : p 1 ≤ 0 := by
      have : (p 1 : ℝ) < 1 := by linarith
      have : p 1 < 1 := by exact_mod_cast this
      omega
    simp [oracle, h2]
  · simp only [Hyp.surplus, hyp, sp, sgn, id] at h0
    norm_num at h0
    have h2 : ¬ p 1 ≤ 0 := by
      have : (0 : ℝ) < p 1 := by linarith
      have : (0 : ℤ) < p 1 := by exact_mod_cast this
      omega
    simp [oracle, h2]

/-- The rounded hypotheses require opposite labels at the origin. -/
theorem no_common_label (z : Fin 2 → Bool) :
    ¬ ((hypFloor true).ConsistentAt id (fun _ => 0) z ∧
       (hypFloor false).ConsistentAt id (fun _ => 0) z) := by
  rintro ⟨h1, h2⟩
  have a1 := h1 (0, true) (by simp [hypFloor])
    (fun u hu => by
      have hu' : u = (0, true) ∨ u = (1, true) ∨ u = (1, false) := by simpa [hypFloor] using hu
      rcases hu' with rfl | rfl | rfl <;> simp [Hyp.surplus, hypFloor, sp, sgn])
    (by simp [Hyp.surplus, hypFloor, sp, sgn])
  have a2 := h2 (0, false) (by simp [hypFloor])
    (fun u hu => by
      have hu' : u = (0, false) ∨ u = (1, true) ∨ u = (1, false) := by simpa [hypFloor] using hu
      rcases hu' with rfl | rfl | rfl <;> simp [Hyp.surplus, hypFloor, sp, sgn])
    (by simp [Hyp.surplus, hypFloor, sp, sgn])
  simp only at a1 a2
  rw [a1] at a2
  exact absurd a2 (by decide)

end RoundingExample

end SPLP
