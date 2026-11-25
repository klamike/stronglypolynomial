import Mathlib
import SPLP.Vertex

/-!
# Vertices are half-integral and bounded

With integer demands and half-integral proposals on the path, every vertex of the market
potential is half-integral; with demands bounded by `R` and path proposals bounded by `Hb`,
every vertex is bounded by `2R(N+1) + Hb`.
-/

set_option linter.unusedSectionVars false

namespace SPLP

open Finset

variable {ι V : Type*} {k D : ℕ} [Fintype ι] [DecidableEq ι] [Fintype V]

/-! ### Ties of bidding experts -/

/-- Payoff of an inside option of a bidding expert along an arbitrary direction `d`. -/
private lemma halfInt_pay_some_of_thr {val : V → ℝ} {l : ℕ} {hist : ℕ → ι → ℝ}
    {e : Expert ι V k D} {τ : ℝ} (h : thr val l hist e = some τ) (q : Fin k) (d : ι → ℝ) :
    pay (dirOf val l hist) e (some q) d = sgn (e.1 q).2 * d (e.1 q).1 := by
  simp [pay, dirOf, h]

/-- The threshold of a bidding expert is zero, or a demand value minus a signed proposal on
the path. -/
private lemma halfInt_thr_cases {val : V → ℝ} {l : ℕ} {hist : ℕ → ι → ℝ}
    {e : Expert ι V k D} {τ : ℝ} (h : thr val l hist e = some τ) :
    τ = 0 ∨ ∃ (j : ℕ) (p : Slot ι) (b : V), j < l ∧ τ = val b - sp (hist j) p := by
  obtain ⟨slots, bids, desc⟩ := e
  cases desc with
  | none =>
    have h' : some (0 : ℝ) = some τ := h
    exact Or.inl (Option.some.inj h').symm
  | some t =>
    obtain ⟨j, p, b⟩ := t
    have h' : (if (j : ℕ) < l then some (val b - sp (hist j) p) else none) = some τ := h
    by_cases hj : (j : ℕ) < l
    · rw [if_pos hj] at h'
      exact Or.inr ⟨j, p, b, hj, (Option.some.inj h').symm⟩
    · rw [if_neg hj] at h'
      cases h'

/-- To check that `d` preserves the ties at `y` it suffices to look at bidding experts: at the
ties of an inside option with the outside option, and at the ties between two inside options. -/
private lemma halfInt_tieHom_of_slots {val : V → ℝ} {l : ℕ} {hist : ℕ → ι → ℝ} {y d : ι → ℝ}
    (h0 : ∀ (e : Expert ι V k D) (τ : ℝ), thr val l hist e = some τ → ∀ q : Fin k,
      sp y (e.1 q) = val (e.2.1 q) - τ → sgn (e.1 q).2 * d (e.1 q).1 = 0)
    (h1 : ∀ (e : Expert ι V k D) (τ : ℝ), thr val l hist e = some τ → ∀ q q' : Fin k,
      sp y (e.1 q) - sp y (e.1 q') = val (e.2.1 q) - val (e.2.1 q') →
      sgn (e.1 q).2 * d (e.1 q).1 = sgn (e.1 q').2 * d (e.1 q').1) :
    TieHom (k := k) (D := D) val l hist y d := by
  intro e o o' hu
  cases hthr : thr val l hist e with
  | none =>
    -- an expert that does not bid is paid nothing
    have hp : ∀ o, pay (dirOf val l hist) e o d = 0 := by
      intro o
      cases o with
      | none => exact pay_none val l hist e d
      | some q => exact pay_some_of_inactive hthr q d
    rw [hp o, hp o']
  | some τ =>
    cases o with
    | none =>
      cases o' with
      | none => rfl
      | some q' =>
        rw [util_none, util_some_of_thr hthr] at hu
        rw [pay_none, halfInt_pay_some_of_thr hthr]
        exact (h0 e τ hthr q' (by linarith)).symm
    | some q =>
      cases o' with
      | none =>
        rw [util_none, util_some_of_thr hthr] at hu
        rw [pay_none, halfInt_pay_some_of_thr hthr]
        exact h0 e τ hthr q (by linarith)
      | some q' =>
        rw [util_some_of_thr hthr, util_some_of_thr hthr] at hu
        rw [halfInt_pay_some_of_thr hthr, halfInt_pay_some_of_thr hthr]
        exact h1 e τ hthr q q' (by linarith)

/-! ### Half-integrality -/

/-- **Half-integrality.** If the demand values are integers and the proposals on the path are
half-integral, every vertex is half-integral. -/
theorem halfInt_of_vertex (val : V → ℝ) (l : ℕ) (hist : ℕ → ι → ℝ) (y : ι → ℝ)
    (hint : ∀ v, ∃ z : ℤ, val v = z)
    (hhist : ∀ j, j < l → ∀ i, ∃ z : ℤ, 2 * hist j i = z)
    (hv : IsVertex (k := k) (D := D) val l hist y) :
    ∀ i, ∃ z : ℤ, 2 * y i = z := by
  -- `sin` is odd, so the direction `sin (2π y)` reads off the signed prices
  have hsin : ∀ s : Slot ι,
      sgn s.2 * Real.sin (2 * Real.pi * y s.1) = Real.sin (2 * Real.pi * sp y s) := by
    rintro ⟨i, h⟩
    cases h
    · have h1 : sgn false = -1 := by simp [sgn]
      simp only [sp, h1]
      rw [show 2 * Real.pi * (-1 * y i) = -(2 * Real.pi * y i) by ring, Real.sin_neg]
      ring
    · have h1 : sgn true = 1 := by simp [sgn]
      simp only [sp, h1, one_mul]
  -- the thresholds of bidding experts are half-integral
  have hτ : ∀ (e : Expert ι V k D) (τ : ℝ), thr val l hist e = some τ →
      ∃ z : ℤ, 2 * τ = z := by
    intro e τ h
    rcases halfInt_thr_cases h with rfl | ⟨j, ⟨i, s⟩, b, hj, rfl⟩
    · exact ⟨0, by simp⟩
    · obtain ⟨z1, hz1⟩ := hint b
      obtain ⟨z2, hz2⟩ := hhist j hj i
      cases s
      · have h1 : sgn false = -1 := by simp [sgn]
        refine ⟨2 * z1 + z2, ?_⟩
        simp only [sp, h1]
        push_cast
        rw [← hz1, ← hz2]
        ring
      · have h1 : sgn true = 1 := by simp [sgn]
        refine ⟨2 * z1 - z2, ?_⟩
        simp only [sp, h1]
        push_cast
        rw [← hz1, ← hz2]
        ring
  -- hence the direction `sin (2π y)` preserves all ties
  have htie : TieHom (k := k) (D := D) val l hist y
      (fun i => Real.sin (2 * Real.pi * y i)) := by
    refine halfInt_tieHom_of_slots ?_ ?_
    · -- a tie with the outside option: the signed price is half-integral
      intro e τ hthr q hq
      obtain ⟨z1, hz1⟩ := hint (e.2.1 q)
      obtain ⟨z2, hz2⟩ := hτ e τ hthr
      have h2 : 2 * Real.pi * sp y (e.1 q) = ((2 * z1 - z2 : ℤ) : ℝ) * Real.pi := by
        push_cast
        rw [hq, ← hz1, ← hz2]
        ring
      show sgn (e.1 q).2 * Real.sin (2 * Real.pi * y (e.1 q).1) = 0
      rw [hsin (e.1 q), h2, Real.sin_int_mul_pi]
    · -- a tie between two inside options: the signed prices differ by an integer
      intro e τ hthr q q' hq
      obtain ⟨z1, hz1⟩ := hint (e.2.1 q)
      obtain ⟨z2, hz2⟩ := hint (e.2.1 q')
      have h2 : 2 * Real.pi * sp y (e.1 q)
          = 2 * Real.pi * sp y (e.1 q') + ((z1 - z2 : ℤ) : ℝ) * (2 * Real.pi) := by
        push_cast
        rw [← hz1, ← hz2]
        linear_combination (2 * Real.pi) * hq
      show sgn (e.1 q).2 * Real.sin (2 * Real.pi * y (e.1 q).1)
        = sgn (e.1 q').2 * Real.sin (2 * Real.pi * y (e.1 q').1)
      rw [hsin (e.1 q), hsin (e.1 q'), h2, Real.sin_add_int_mul_two_pi]
  -- so it vanishes, as `y` is a vertex
  have hd := hv _ htie
  intro i
  have hi : Real.sin (2 * Real.pi * y i) = 0 := congrFun hd i
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hi
  refine ⟨n, ?_⟩
  have h3 : Real.pi * (2 * y i) = Real.pi * n := by linarith
  exact mul_left_cancel₀ Real.pi_ne_zero h3

/-! ### Boundedness -/

/-- The absolute value of a signed price is the absolute value of the price. -/
private lemma bound_abs_sp (y : ι → ℝ) (s : Slot ι) : |sp y s| = |y s.1| := by
  rw [sp, abs_mul, abs_sgn, one_mul]

/-- The map sending `x` to its sign if `|x|` exceeds a threshold `T ≥ 0`, and to zero
otherwise, is odd. -/
private lemma bound_sgn_mul_signAbove {T : ℝ} (hT : 0 ≤ T) (h : Bool) (x : ℝ) :
    sgn h * (if T < |x| then (if 0 < x then (1 : ℝ) else -1) else 0)
      = if T < |sgn h * x| then (if 0 < sgn h * x then (1 : ℝ) else -1) else 0 := by
  cases h
  · have h1 : sgn false = -1 := by simp [sgn]
    rw [h1, show -1 * x = -x by ring, abs_neg]
    by_cases hx : T < |x|
    · rw [if_pos hx, if_pos hx]
      have hx0 : x ≠ 0 := by
        rintro rfl
        rw [abs_zero] at hx
        linarith
      rcases lt_or_gt_of_ne hx0 with hneg | hpos
      · rw [if_neg (not_lt.mpr hneg.le), if_pos (by linarith : (0 : ℝ) < -x)]
        ring
      · rw [if_pos hpos, if_neg (by linarith : ¬ (0 : ℝ) < -x)]
        ring
    · rw [if_neg hx, if_neg hx, mul_zero]
  · have h1 : sgn true = 1 := by simp [sgn]
    rw [h1, one_mul, one_mul]

/-- Two reals at distance at most `r ≤ T`, neither of which has absolute value in the window
`(T - r, T]`, lie on the same side of the threshold `T`, and have the same sign if they lie
above it. -/
private lemma bound_signAbove_eq_of_gap {T r a b : ℝ} (hrT : r ≤ T) (hab : |a - b| ≤ r)
    (ha : T - r < |a| → T < |a|) (hb : T - r < |b| → T < |b|) :
    (if T < |a| then (if 0 < a then (1 : ℝ) else -1) else 0)
      = if T < |b| then (if 0 < b then (1 : ℝ) else -1) else 0 := by
  have h1 : |a| - |b| ≤ r := (abs_sub_abs_le_abs_sub a b).trans hab
  have h2 : |b| - |a| ≤ r := by
    rw [abs_sub_comm] at hab
    exact (abs_sub_abs_le_abs_sub b a).trans hab
  obtain ⟨h3, h4⟩ := abs_le.mp hab
  by_cases hA : T < |a|
  · have hB : T < |b| := hb (by linarith)
    rw [if_pos hA, if_pos hB]
    by_cases hb0 : 0 < b
    · have ha0 : 0 < a := by
        rw [abs_of_pos hb0] at hB
        linarith
      rw [if_pos ha0, if_pos hb0]
    · have ha0 : ¬ 0 < a := by
        rw [abs_of_nonpos (not_lt.mp hb0)] at hB
        linarith
      rw [if_neg ha0, if_neg hb0]
  · have hB : ¬ T < |b| := fun hB => hA (ha (by linarith))
    rw [if_neg hA, if_neg hB]

/-- If no price has absolute value in the window `(T - 2R, T]`, where `2R + Hb ≤ T`, then the
sign pattern of the prices above `T` preserves all ties. -/
private lemma bound_tieHom_of_gap (val : V → ℝ) (l : ℕ) (hist : ℕ → ι → ℝ) (y : ι → ℝ)
    (R Hb T : ℝ) (hR : ∀ v, |val v| ≤ R) (hH : ∀ j, j < l → ∀ i, |hist j i| ≤ Hb)
    (hHb : 0 ≤ Hb) (hT : 2 * R + Hb ≤ T) (hgap : ∀ i, T - 2 * R < |y i| → T < |y i|) :
    TieHom (k := k) (D := D) val l hist y
      (fun i => if T < |y i| then (if 0 < y i then (1 : ℝ) else -1) else 0) := by
  have hgap' : ∀ s : Slot ι, T - 2 * R < |sp y s| → T < |sp y s| := by
    intro s hs
    rw [bound_abs_sp] at hs ⊢
    exact hgap s.1 hs
  refine halfInt_tieHom_of_slots ?_ ?_
  · -- a tie with the outside option: the price is at most `2R + Hb ≤ T` in absolute value
    intro e τ hthr q hq
    have hR0 : 0 ≤ R := (abs_nonneg _).trans (hR (e.2.1 q))
    have hτ : |τ| ≤ R + Hb := by
      rcases halfInt_thr_cases hthr with rfl | ⟨j, p, b, hj, rfl⟩
      · rw [abs_zero]
        linarith
      · have h1 := abs_le.mp (hR b)
        have h2 := abs_le.mp ((bound_abs_sp (hist j) p).le.trans (hH j hj p.1))
        exact abs_le.mpr ⟨by linarith, by linarith⟩
    have h1 : |sp y (e.1 q)| ≤ T := by
      rw [hq]
      have h2 := abs_le.mp (hR (e.2.1 q))
      have h3 := abs_le.mp hτ
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hT0 : 0 ≤ T := by linarith
    rw [bound_sgn_mul_signAbove hT0]
    exact if_neg (not_lt.mpr h1)
  · -- a tie between two inside options: the signed prices differ by at most `2R`
    intro e τ hthr q q' hq
    have hR0 : 0 ≤ R := (abs_nonneg _).trans (hR (e.2.1 q))
    have hB : |sp y (e.1 q) - sp y (e.1 q')| ≤ 2 * R := by
      rw [hq]
      have h1 := abs_le.mp (hR (e.2.1 q))
      have h2 := abs_le.mp (hR (e.2.1 q'))
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hT0 : 0 ≤ T := by linarith
    rw [bound_sgn_mul_signAbove hT0, bound_sgn_mul_signAbove hT0]
    exact bound_signAbove_eq_of_gap (by linarith) hB (hgap' (e.1 q)) (hgap' (e.1 q'))

/-- **Boundedness.** If the demand values are bounded by `R` and the proposals on the path by
`Hb`, every vertex is bounded by `2R(N+1) + Hb`. -/
theorem bound_of_vertex (val : V → ℝ) (l : ℕ) (hist : ℕ → ι → ℝ) (y : ι → ℝ) (R Hb : ℝ)
    (hR : ∀ v, |val v| ≤ R) (hH : ∀ j, j < l → ∀ i, |hist j i| ≤ Hb) (hHb : 0 ≤ Hb)
    (hv : IsVertex (k := k) (D := D) val l hist y) :
    ∀ i, |y i| ≤ 2 * R * (Fintype.card ι + 1) + Hb := by
  intro i₀
  by_contra hcon
  rw [not_le] at hcon
  -- `R` is nonnegative: otherwise there are no demand values, hence no ties, so every
  -- direction preserves the ties and `y` is not a vertex
  have hR0 : 0 ≤ R := by
    by_contra hR0
    have htie : TieHom (k := k) (D := D) val l hist y (fun _ => 1) := by
      refine halfInt_tieHom_of_slots ?_ ?_
      · intro e τ _ q _
        exact absurd ((abs_nonneg _).trans (hR (e.2.1 q))) hR0
      · intro e τ _ q _ _
        exact absurd ((abs_nonneg _).trans (hR (e.2.1 q))) hR0
    have h1 : (1 : ℝ) = 0 := congrFun (hv _ htie) i₀
    exact one_ne_zero h1
  -- the thresholds `θ m = 2R + Hb + m * 2R`; the claim is `|y i₀| ≤ θ N`
  let θ : ℕ → ℝ := fun m => 2 * R + Hb + m * (2 * R)
  have hθsucc : ∀ m, θ (m + 1) = θ m + 2 * R := by
    intro m
    simp only [θ]
    push_cast
    ring
  have hθmono : ∀ a b, a ≤ b → θ a ≤ θ b := by
    intro a b hab
    have h1 : (a : ℝ) ≤ b := Nat.cast_le.mpr hab
    have h2 : (a : ℝ) * (2 * R) ≤ b * (2 * R) :=
      mul_le_mul_of_nonneg_right h1 (by linarith)
    simp only [θ]
    linarith
  have hθge : ∀ m, 2 * R + Hb ≤ θ m := by
    intro m
    have h1 : 0 ≤ (m : ℝ) * (2 * R) := mul_nonneg (Nat.cast_nonneg m) (by linarith)
    simp only [θ]
    linarith
  have hi₀ : θ (Fintype.card ι) < |y i₀| := by
    have h1 : θ (Fintype.card ι) = 2 * R * (Fintype.card ι + 1) + Hb := by
      simp only [θ]
      ring
    rw [h1]
    exact hcon
  -- `U m`: the coordinates above the `m`-th threshold
  let U : ℕ → Finset ι := fun m => univ.filter (fun i => θ m < |y i|)
  have hUmem : ∀ m i, i ∈ U m ↔ θ m < |y i| := by
    intro m i
    simp [U]
  have hUsub : ∀ m, U (m + 1) ⊆ U m := by
    intro m i hi
    rw [hUmem] at hi ⊢
    exact lt_of_le_of_lt (hθmono m (m + 1) (Nat.le_succ m)) hi
  -- pigeonhole: some window `(θ m, θ (m+1)]` with `m < N` contains no `|y i|`
  obtain ⟨m, hm, hgap⟩ : ∃ m, m < Fintype.card ι ∧ U m ⊆ U (m + 1) := by
    by_contra hno
    have hno' : ∀ m, m < Fintype.card ι → ¬ U m ⊆ U (m + 1) :=
      fun m hm hsub => hno ⟨m, hm, hsub⟩
    have key : ∀ m, m ≤ Fintype.card ι → (U m).card + m ≤ (U 0).card := by
      intro m
      induction m with
      | zero => intro _; simp
      | succ m ih =>
        intro hm
        have h1 := ih (by omega)
        have h2 : (U (m + 1)).card < (U m).card :=
          Finset.card_lt_card ⟨hUsub m, hno' m (by omega)⟩
        omega
    have h1 := key (Fintype.card ι) le_rfl
    have h2 : (U 0).card ≤ Fintype.card ι := Finset.card_le_univ _
    have h3 : 0 < (U (Fintype.card ι)).card :=
      Finset.card_pos.mpr ⟨i₀, (hUmem _ i₀).mpr hi₀⟩
    omega
  -- the sign pattern of `y` above the window preserves all ties, and is nonzero at `i₀`
  have htie := bound_tieHom_of_gap (k := k) (D := D) val l hist y R Hb (θ (m + 1)) hR hH hHb
    (hθge (m + 1)) (by
      intro i hi
      rw [hθsucc] at hi
      exact (hUmem (m + 1) i).mp (hgap ((hUmem m i).mpr (by linarith))))
  have hd : (if θ (m + 1) < |y i₀| then (if 0 < y i₀ then (1 : ℝ) else -1) else 0) = 0 :=
    congrFun (hv _ htie) i₀
  have h1 : θ (m + 1) < |y i₀| :=
    lt_of_le_of_lt (hθmono (m + 1) (Fintype.card ι) (Nat.succ_le_of_lt hm)) hi₀
  rw [if_pos h1] at hd
  by_cases h0 : 0 < y i₀
  · rw [if_pos h0] at hd
    exact one_ne_zero hd
  · rw [if_neg h0] at hd
    exact neg_ne_zero.mpr one_ne_zero hd

end SPLP
