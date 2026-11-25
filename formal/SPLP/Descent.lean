import Mathlib
import SPLP.Defs

/-!
# Label oracles with a margin: plain descent

The price theorem of the preprint assumes labels that are correct only at slots of *maximum*
surplus. This file studies a stronger oracle, correct at every slot whose surplus is within an
additive margin `G` of the maximum (`Hyp.ConsistentAtMargin`; `G = 0` is the preprint's
notion). For such an oracle no experts and no markets are needed: moving every price by
`e ≤ G / 2` in the direction of its label lowers the maximum surplus by `e` whenever some
demand is unmet (`descent_step_decrease`). With integer data, a coarse phase with step `e₁`
followed by `e₁ - 1` unit steps meets every demand of every consistent hypothesis after
`n₁ + e₁ - 1` queries, where `n₁ e₁` bounds the initial surplus (`descent_meets_demands`).

The number of queries is linear in the range of the demands, not logarithmic: this is a
different regime from the recursive market, not a replacement for it.
-/

namespace SPLP

variable {ι V : Type*}

/-- Consistency with a label vector `z` returned at the query `x`, for an oracle with additive
margin `G`: when some surplus is nonnegative, every slot whose surplus is within `G` of all
others carries its own sign as label. -/
def Hyp.ConsistentAtMargin (val : V → ℝ) (H : Hyp ι V) (G : ℝ) (x : ι → ℝ) (z : ι → Bool) :
    Prop :=
  ∀ s ∈ H.S, (∀ u ∈ H.S, H.surplus val x u ≤ H.surplus val x s + G) →
    (∃ u ∈ H.S, 0 ≤ H.surplus val x u) → z s.1 = s.2

/-- Margin zero is the consistency notion of the price theorem. -/
theorem Hyp.consistentAtMargin_zero (val : V → ℝ) (H : Hyp ι V) (x : ι → ℝ) (z : ι → Bool) :
    H.ConsistentAtMargin val 0 x z ↔ H.ConsistentAt val x z := by
  constructor
  · intro h s hs hmax h0
    exact h s hs (fun u hu => by linarith [hmax u hu]) ⟨s, hs, h0⟩
  · rintro h s hs hmax ⟨u, hu, hu0⟩
    have hm : ∀ u ∈ H.S, H.surplus val x u ≤ H.surplus val x s := fun u hu => by
      have := hmax u hu; linarith
    exact h s hs hm (hu0.trans (hm u hu))

/-- A larger margin is a stronger requirement on the oracle. -/
theorem Hyp.ConsistentAtMargin.mono {val : V → ℝ} {H : Hyp ι V} {G G' : ℝ} {x : ι → ℝ}
    {z : ι → Bool} (h : H.ConsistentAtMargin val G x z) (hG : G' ≤ G) :
    H.ConsistentAtMargin val G' x z :=
  fun s hs hmax hpos => h s hs (fun u hu => (hmax u hu).trans (by linarith)) hpos

/-- One descent step: move every price by `e` in the direction of its label. -/
def descentStep (e : ℝ) (p : ι → ℝ) (z : ι → Bool) : ι → ℝ := fun i => p i + e * sgn (z i)

theorem sgn_mul_sgn_ite (b c : Bool) : sgn b * sgn c = if b = c then 1 else -1 := by
  cases b <;> cases c <;> simp [sgn]

/-- A step lowers the surplus of a slot by `e` if its label agrees with its sign, and raises
it by `e` otherwise. -/
theorem surplus_descentStep (val : V → ℝ) (H : Hyp ι V) (e : ℝ) (p : ι → ℝ) (z : ι → Bool)
    (s : Slot ι) :
    H.surplus val (descentStep e p z) s
      = H.surplus val p s - e * (if z s.1 = s.2 then 1 else -1) := by
  have h := sgn_mul_sgn_ite s.2 (z s.1)
  have hexp : sgn s.2 * (p s.1 + e * sgn (z s.1))
      = sgn s.2 * p s.1 + e * (sgn s.2 * sgn (z s.1)) := by ring
  simp only [Hyp.surplus, sp, descentStep]
  rw [hexp, h]
  by_cases hz : z s.1 = s.2
  · rw [if_pos hz, if_pos hz.symm]; ring
  · rw [if_neg hz, if_neg (fun h' => hz h'.symm)]; ring

theorem surplus_descentStep_le (val : V → ℝ) (H : Hyp ι V) {e : ℝ} (he : 0 ≤ e) (p : ι → ℝ)
    (z : ι → Bool) (s : Slot ι) :
    H.surplus val (descentStep e p z) s ≤ H.surplus val p s + e := by
  rw [surplus_descentStep]
  split_ifs <;> linarith

/-- **Descent step.** With margin `G` and step `e ≤ G / 2`, if some surplus is nonnegative
then every surplus ends at least `e` below the previous maximum. -/
theorem descent_step_decrease {val : V → ℝ} {H : Hyp ι V} {G e : ℝ} {p : ι → ℝ} {z : ι → Bool}
    (hcons : H.ConsistentAtMargin val G p z) (he0 : 0 ≤ e) (heG : 2 * e ≤ G)
    (hpos : ∃ u ∈ H.S, 0 ≤ H.surplus val p u) {B : ℝ}
    (hB : ∀ s ∈ H.S, H.surplus val p s ≤ B) :
    ∀ s ∈ H.S, H.surplus val (descentStep e p z) s ≤ B - e := by
  intro s hs
  by_cases hnear : ∀ u ∈ H.S, H.surplus val p u ≤ H.surplus val p s + G
  · rw [surplus_descentStep, if_pos (hcons s hs hnear hpos)]
    linarith [hB s hs]
  · rw [not_forall] at hnear
    obtain ⟨u, hu⟩ := hnear
    rw [Classical.not_imp] at hu
    obtain ⟨huS, hlt⟩ := hu
    rw [not_le] at hlt
    have h1 := surplus_descentStep_le val H he0 p z s
    linarith [hB u huS]

/-- All surpluses of the hypothesis at `p` are integers. -/
def Hyp.IntAt (val : V → ℝ) (H : Hyp ι V) (p : ι → ℝ) : Prop :=
  ∀ s ∈ H.S, ∃ n : ℤ, H.surplus val p s = n

theorem Hyp.intAt_of_int (val : V → ℝ) (H : Hyp ι V) (p : ι → ℝ)
    (hval : ∀ v, ∃ n : ℤ, val v = n) (hp : ∀ i, ∃ n : ℤ, p i = n) : H.IntAt val p := by
  rintro ⟨i, h⟩ -
  obtain ⟨a, ha⟩ := hval (H.a (i, h))
  obtain ⟨b, hb⟩ := hp i
  cases h with
  | true => exact ⟨a - b, by simp [Hyp.surplus, sp, sgn, ha, hb]⟩
  | false => exact ⟨a + b, by simp [Hyp.surplus, sp, sgn, ha, hb]⟩

theorem Hyp.IntAt.descentStep {val : V → ℝ} {H : Hyp ι V} {p : ι → ℝ}
    (h : H.IntAt val p) (e : ℕ) (z : ι → Bool) : H.IntAt val (descentStep (e : ℝ) p z) := by
  intro s hs
  obtain ⟨n, hn⟩ := h s hs
  rw [surplus_descentStep, hn]
  split_ifs
  · exact ⟨n - e, by push_cast; ring⟩
  · exact ⟨n + e, by push_cast; ring⟩

/-- One step with integer data: the bound `B` becomes `max (B - e) (e - 1)`. -/
theorem descent_step_int {val : V → ℝ} {H : Hyp ι V} {G : ℝ} {e : ℕ} {p : ι → ℝ}
    {z : ι → Bool} (hcons : H.ConsistentAtMargin val G p z) (heG : 2 * (e : ℝ) ≤ G)
    (hint : H.IntAt val p) {B : ℤ} (hB : ∀ s ∈ H.S, H.surplus val p s ≤ B) :
    ∀ s ∈ H.S, H.surplus val (descentStep (e : ℝ) p z) s ≤ ((max (B - e) (e - 1) : ℤ) : ℝ) := by
  intro s hs
  by_cases hpos : ∃ u ∈ H.S, 0 ≤ H.surplus val p u
  · have h := descent_step_decrease hcons (Nat.cast_nonneg e) heG hpos hB s hs
    have h2 : ((B - e : ℤ) : ℝ) ≤ ((max (B - e) (e - 1) : ℤ) : ℝ) := by
      exact_mod_cast le_max_left _ _
    have h3 : ((B - e : ℤ) : ℝ) = (B : ℝ) - (e : ℝ) := by push_cast; ring
    rw [h3] at h2
    linarith
  · have hneg : H.surplus val p s < 0 := by
      by_contra hcon
      exact hpos ⟨s, hs, not_lt.1 hcon⟩
    obtain ⟨n, hn⟩ := hint s hs
    have hn1 : n ≤ -1 := by
      have : (n : ℝ) < 0 := by rw [← hn]; exact hneg
      have : n < 0 := by exact_mod_cast this
      omega
    have h1 := surplus_descentStep_le val H (Nat.cast_nonneg e) p z s
    have h2 : ((e - 1 : ℤ) : ℝ) ≤ ((max (B - e) (e - 1) : ℤ) : ℝ) := by
      exact_mod_cast le_max_right _ _
    have h3 : (n : ℝ) ≤ -1 := by exact_mod_cast hn1
    have h4 : ((e - 1 : ℤ) : ℝ) = (e : ℝ) - 1 := by push_cast; ring
    rw [h4] at h2
    rw [hn] at h1
    linarith

/-- The descent run for step sizes `e n` and labels `z n`. -/
def descentRun (e : ℕ → ℕ) (z : ℕ → ι → Bool) (p₀ : ι → ℝ) : ℕ → ι → ℝ
  | 0 => p₀
  | n + 1 => descentStep (e n : ℝ) (descentRun e z p₀ n) (z n)

/-- The bound on the maximum surplus along a descent run. -/
def descentBound (e : ℕ → ℕ) (B₀ : ℤ) : ℕ → ℤ
  | 0 => B₀
  | n + 1 => max (descentBound e B₀ n - e n) (e n - 1)

/-- Along a descent run with steps `e n ≤ G / 2`, every surplus of every hypothesis consistent
with the answers stays below `descentBound`. -/
theorem descent_bound {val : V → ℝ} {H : Hyp ι V} {G : ℝ} (e : ℕ → ℕ) (z : ℕ → ι → Bool)
    (p₀ : ι → ℝ) (hG : ∀ n, 2 * (e n : ℝ) ≤ G)
    (hcons : ∀ n, H.ConsistentAtMargin val G (descentRun e z p₀ n) (z n))
    (hint : H.IntAt val p₀) {B₀ : ℤ} (hB₀ : ∀ s ∈ H.S, H.surplus val p₀ s ≤ B₀) :
    ∀ n, H.IntAt val (descentRun e z p₀ n) ∧
      ∀ s ∈ H.S, H.surplus val (descentRun e z p₀ n) s ≤ (descentBound e B₀ n : ℝ) := by
  intro n
  induction n with
  | zero => exact ⟨hint, hB₀⟩
  | succ n ih =>
    exact ⟨ih.1.descentStep (e n) (z n), descent_step_int (hcons n) (hG n) ih.1 ih.2⟩

/-- Two-phase schedule: `n₁` steps of size `e₁`, then unit steps. -/
def twoPhase (n₁ e₁ : ℕ) : ℕ → ℕ := fun n => if n < n₁ then e₁ else 1

theorem descentBound_phase1 (n₁ e₁ : ℕ) (B₀ : ℤ) :
    ∀ n, n ≤ n₁ → descentBound (twoPhase n₁ e₁) B₀ n ≤ max (B₀ - n * e₁) (e₁ - 1) := by
  intro n
  induction n with
  | zero => intro _; simp [descentBound]
  | succ n ih =>
    intro hn
    have h := ih (Nat.le_of_succ_le hn)
    have he : twoPhase n₁ e₁ n = e₁ := by simp [twoPhase, Nat.lt_of_succ_le hn]
    simp only [descentBound, he]
    push_cast
    have h1 : (B₀ - (n + 1) * e₁ : ℤ) = B₀ - n * e₁ - e₁ := by ring
    rw [h1]
    omega

theorem descentBound_phase2 (n₁ e₁ : ℕ) (B₀ : ℤ)
    (h₁ : descentBound (twoPhase n₁ e₁) B₀ n₁ ≤ e₁ - 1) :
    ∀ j : ℕ, descentBound (twoPhase n₁ e₁) B₀ (n₁ + j) ≤ max ((e₁ : ℤ) - 1 - (j : ℤ)) 0 := by
  intro j
  induction j with
  | zero =>
    simp only [Nat.add_zero, Nat.cast_zero, sub_zero]
    exact le_max_of_le_left h₁
  | succ j ih =>
    have he : twoPhase n₁ e₁ (n₁ + j) = 1 := by simp [twoPhase]
    rw [← Nat.add_assoc]
    simp only [descentBound, he]
    push_cast
    omega

/-- **Descent meets all demands.** Integer demands and prices, an oracle with margin `G`,
a coarse step `e₁` with `1 ≤ e₁ ≤ G / 2`, and `n₁` coarse steps with `B₀ ≤ n₁ e₁`, where `B₀`
bounds every initial surplus. Then after `n₁ + e₁ - 1` queries, and at every later step, the
current prices meet every demand of every hypothesis consistent with the answers. -/
theorem descent_meets_demands {val : V → ℝ} {H : Hyp ι V} {G : ℝ} (n₁ e₁ : ℕ) (he₁ : 1 ≤ e₁)
    (heG : 2 * (e₁ : ℝ) ≤ G) (z : ℕ → ι → Bool) (p₀ : ι → ℝ)
    (hcons : ∀ n, H.ConsistentAtMargin val G (descentRun (twoPhase n₁ e₁) z p₀ n) (z n))
    (hint : H.IntAt val p₀) {B₀ : ℤ} (hB₀ : ∀ s ∈ H.S, H.surplus val p₀ s ≤ B₀)
    (hn₁ : B₀ ≤ n₁ * e₁) :
    ∀ n, n₁ + (e₁ - 1) ≤ n →
      ∀ s ∈ H.S, H.surplus val (descentRun (twoPhase n₁ e₁) z p₀ n) s ≤ 0 := by
  intro n hn s hs
  have hG : ∀ m, 2 * ((twoPhase n₁ e₁ m : ℕ) : ℝ) ≤ G := by
    intro m
    unfold twoPhase
    split_ifs
    · exact heG
    · have : (1 : ℝ) ≤ (e₁ : ℝ) := by exact_mod_cast he₁
      push_cast
      linarith
  have hb := (descent_bound (twoPhase n₁ e₁) z p₀ hG hcons hint hB₀ n).2 s hs
  have h1 := descentBound_phase1 n₁ e₁ B₀ n₁ le_rfl
  have h1' : descentBound (twoPhase n₁ e₁) B₀ n₁ ≤ e₁ - 1 := by omega
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_add_right_le hn)
  have h2 := descentBound_phase2 n₁ e₁ B₀ h1' j
  have hj : (e₁ : ℤ) - 1 - j ≤ 0 := by omega
  have h3 : descentBound (twoPhase n₁ e₁) B₀ (n₁ + j) ≤ 0 := by omega
  have h4 : (descentBound (twoPhase n₁ e₁) B₀ (n₁ + j) : ℝ) ≤ 0 := by exact_mod_cast h3
  linarith

/-! ### Exact labels: descent in lockstep

For the preprint's own oracle (labels correct only at slots of maximum surplus) the same
descent works with half steps, because every price moves by exactly `1/2` at every query: all
surpluses then stay in one residue class modulo `1`, so a slot that is not maximal is at least
a full unit below the maximum and cannot overtake it. -/

/-- The run that moves every price by `1/2` in the direction of its label. -/
noncomputable def halfRun (z : ℕ → ι → Bool) (p₀ : ι → ℝ) : ℕ → ι → ℝ
  | 0 => p₀
  | n + 1 => descentStep (1 / 2) (halfRun z p₀ n) (z n)

theorem lockstep_inv {val : V → ℝ} {H : Hyp ι V} (z : ℕ → ι → Bool) (p₀ : ι → ℝ)
    (hint : H.IntAt val p₀) (hcons : ∀ n, H.ConsistentAt val (halfRun z p₀ n) (z n))
    (B₀ : ℕ) (hB₀ : ∀ s ∈ H.S, 2 * H.surplus val p₀ s ≤ B₀) :
    ∀ n : ℕ, (∀ s ∈ H.S, ∃ m : ℤ, 2 * H.surplus val (halfRun z p₀ n) s = m ∧
        (2 : ℤ) ∣ m - n) ∧
      ∀ s ∈ H.S, 2 * H.surplus val (halfRun z p₀ n) s ≤ ((max ((B₀ : ℤ) - n) 0 : ℤ) : ℝ) := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun s hs => ?_, fun s hs => ?_⟩
    · obtain ⟨k, hk⟩ := hint s hs
      refine ⟨2 * k, ?_, ?_⟩
      · show 2 * H.surplus val p₀ s = ((2 * k : ℤ) : ℝ)
        rw [hk]; push_cast; ring
      · exact ⟨k, by push_cast; ring⟩
    · have h := hB₀ s hs
      have h2 : ((max ((B₀ : ℤ) - (0 : ℕ)) 0 : ℤ) : ℝ) = (B₀ : ℝ) := by
        have : max ((B₀ : ℤ) - ((0 : ℕ) : ℤ)) 0 = (B₀ : ℤ) := by
          simp
        rw [this]; norm_cast
      show 2 * H.surplus val p₀ s ≤ _
      rw [h2]; exact h
  | succ n ih =>
    obtain ⟨hlat, hbd⟩ := ih
    have hstep : ∀ s : Slot ι, 2 * H.surplus val (halfRun z p₀ (n + 1)) s
        = 2 * H.surplus val (halfRun z p₀ n) s - (if z n s.1 = s.2 then 1 else -1) := by
      intro s
      show 2 * H.surplus val (descentStep (1 / 2) (halfRun z p₀ n) (z n)) s = _
      rw [surplus_descentStep]
      ring
    refine ⟨fun s hs => ?_, fun s hs => ?_⟩
    · obtain ⟨m, hm, hpar⟩ := hlat s hs
      rw [hstep s, hm]
      obtain ⟨c, hc⟩ := hpar
      split_ifs
      · exact ⟨m - 1, by push_cast; ring, ⟨c - 1, by push_cast; linarith⟩⟩
      · exact ⟨m + 1, by push_cast; ring, ⟨c, by push_cast; linarith⟩⟩
    · obtain ⟨m, hm, hpar⟩ := hlat s hs
      have hb := hbd s hs
      rw [hm] at hb
      have hmb : m ≤ max ((B₀ : ℤ) - n) 0 := by exact_mod_cast hb
      rw [hstep s, hm]
      by_cases hpos : ∃ u ∈ H.S, 0 ≤ H.surplus val (halfRun z p₀ n) u
      · have key : (m : ℝ) - (if z n s.1 = s.2 then 1 else -1)
            ≤ ((max ((B₀ : ℤ) - n) 0 - 1 : ℤ) : ℝ) := by
          by_cases hmax : ∀ u ∈ H.S, H.surplus val (halfRun z p₀ n) u
              ≤ H.surplus val (halfRun z p₀ n) s
          · obtain ⟨u, hu, hu0⟩ := hpos
            have hz := hcons n s hs hmax (hu0.trans (hmax u hu))
            rw [if_pos hz]
            have : ((m - 1 : ℤ) : ℝ) ≤ ((max ((B₀ : ℤ) - n) 0 - 1 : ℤ) : ℝ) := by
              exact_mod_cast sub_le_sub_right hmb 1
            push_cast at this ⊢
            linarith
          · rw [not_forall] at hmax
            obtain ⟨u, hu⟩ := hmax
            rw [Classical.not_imp] at hu
            obtain ⟨huS, hlt⟩ := hu
            rw [not_le] at hlt
            obtain ⟨mu, hmu, hparu⟩ := hlat u huS
            have hbu := hbd u huS
            rw [hmu] at hbu
            have hmub : mu ≤ max ((B₀ : ℤ) - n) 0 := by exact_mod_cast hbu
            have hlt' : (m : ℝ) < mu := by
              have := mul_lt_mul_of_pos_left hlt (by norm_num : (0 : ℝ) < 2)
              rw [hm, hmu] at this
              exact this
            have hlt'' : m < mu := by exact_mod_cast hlt'
            have hm2 : m + 2 ≤ mu := by
              obtain ⟨c, hc⟩ := hpar
              obtain ⟨c', hc'⟩ := hparu
              omega
            have h1 : (m : ℝ) - (if z n s.1 = s.2 then 1 else -1) ≤ (m : ℝ) + 1 := by
              split_ifs <;> linarith
            have h2 : ((m + 1 : ℤ) : ℝ) ≤ ((max ((B₀ : ℤ) - n) 0 - 1 : ℤ) : ℝ) := by
              exact_mod_cast (by omega : m + 1 ≤ max ((B₀ : ℤ) - n) 0 - 1)
            push_cast at h2 ⊢
            linarith
        have hle : ((max ((B₀ : ℤ) - n) 0 - 1 : ℤ) : ℝ)
            ≤ ((max ((B₀ : ℤ) - ((n + 1 : ℕ) : ℤ)) 0 : ℤ) : ℝ) := by
          exact_mod_cast (by push_cast; omega :
            max ((B₀ : ℤ) - n) 0 - 1 ≤ max ((B₀ : ℤ) - ((n + 1 : ℕ) : ℤ)) 0)
        exact key.trans hle
      · have hneg : H.surplus val (halfRun z p₀ n) s < 0 := by
          by_contra hcon
          exact hpos ⟨s, hs, not_lt.1 hcon⟩
        have hm0 : (m : ℝ) < 0 := by rw [← hm]; linarith
        have hm0' : m < 0 := by exact_mod_cast hm0
        have h1 : (m : ℝ) - (if z n s.1 = s.2 then 1 else -1) ≤ (m : ℝ) + 1 := by
          split_ifs <;> linarith
        have h2 : ((m + 1 : ℤ) : ℝ) ≤ ((max ((B₀ : ℤ) - ((n + 1 : ℕ) : ℤ)) 0 : ℤ) : ℝ) := by
          exact_mod_cast (by omega : m + 1 ≤ max ((B₀ : ℤ) - ((n + 1 : ℕ) : ℤ)) 0)
        push_cast at h2 ⊢
        linarith

/-- **The price problem is easy in the range of the demands.** In the model of the preprint's
price theorem (integer demands, labels correct only at slots of maximum surplus), start from
integer prices and move every price by `1/2` in the direction of its label. If `B₀` bounds
twice every initial surplus (`B₀ = 2R` from the origin when demands lie in `[-R, R]`), then
after `B₀` queries, and at every later step, the prices meet every demand of every hypothesis
consistent with the answers. No experts, no market, one addition per coordinate per query;
but the number of queries is linear in `R`, where the recursive market is logarithmic. -/
theorem lockstep_meets_demands {val : V → ℝ} {H : Hyp ι V} (z : ℕ → ι → Bool) (p₀ : ι → ℝ)
    (hint : H.IntAt val p₀) (hcons : ∀ n, H.ConsistentAt val (halfRun z p₀ n) (z n))
    (B₀ : ℕ) (hB₀ : ∀ s ∈ H.S, 2 * H.surplus val p₀ s ≤ B₀) :
    ∀ n, B₀ ≤ n → ∀ s ∈ H.S, H.surplus val (halfRun z p₀ n) s ≤ 0 := by
  intro n hn s hs
  have h := (lockstep_inv z p₀ hint hcons B₀ hB₀ n).2 s hs
  have h0 : max ((B₀ : ℤ) - n) 0 = 0 := by
    have : (B₀ : ℤ) ≤ n := by exact_mod_cast hn
    omega
  rw [h0] at h
  have : 2 * H.surplus val (halfRun z p₀ n) s ≤ 0 := by exact_mod_cast h
  linarith

end SPLP
