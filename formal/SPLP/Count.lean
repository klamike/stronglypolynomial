import Mathlib
import SPLP.Consts

/-!
# Number of label queries

A valid run makes one label query per probe. With `r` probes at every non-root internal node,
`r₀` at the root and leaves at level `D`, this is `r₀ (1 + r + ⋯ + r^(D-1))`. For the least
admissible depth and `r ≤ (ρ/√β)^e`, it is at most `2 r₀ (2N)^e`.
-/

set_option linter.unusedSectionVars false

namespace SPLP

open Finset

variable {ι V : Type*} {k D : ℕ} [Fintype ι] [DecidableEq ι] [Fintype V]

/-- Number of probes strictly below a non-root node with `d` levels remaining. -/
def below (r : ℕ) : ℕ → ℕ
  | 0 => 0
  | d + 1 => r * (1 + below r d)

theorem below_le (r : ℕ) (hr : 2 ≤ r) (d : ℕ) : below r d + 2 ≤ 2 * r ^ d := by
  induction d with
  | zero => simp [below]
  | succ d ih =>
    have h1 : r * (1 + below r d) + r ≤ r * (2 * r ^ d) := by
      have : 1 + below r d + 1 ≤ 2 * r ^ d := by omega
      calc r * (1 + below r d) + r = r * (1 + below r d + 1) := by ring
        _ ≤ r * (2 * r ^ d) := Nat.mul_le_mul_left r this
    have h2 : r * (2 * r ^ d) = 2 * r ^ (d + 1) := by ring
    simp only [below]
    omega

theorem queries_of_validWith (M : MarketCond ι V k D) (A : Alg V)
    (X : Exec ι (Expert ι V k D)) :
    ∀ (l : ℕ) (hist : ℕ → ι → ℝ) (wIn : Expert ι V k D → ℝ), X.ValidWith M A l hist wIn →
      0 < l → X.queries = below A.r (D - l) := by
  induction X with
  | leaf x wOut =>
    intro l hist wIn hv _
    obtain ⟨hl, -, -⟩ := hv
    simp [Exec.queries, hl, below]
  | node T y z child w x ih =>
    intro l hist wIn hv hl0
    obtain ⟨hl, hT, -, hprobe, -⟩ := hv
    have hT' : T = A.r := by rw [hT, if_neg (Nat.pos_iff_ne_zero.1 hl0)]
    have hch : ∀ τ : Fin T, (child τ).queries = below A.r (D - (l + 1)) :=
      fun τ => ih τ (l + 1) _ _ (hprobe τ).2.1 (Nat.succ_pos l)
    have hD : D - l = (D - (l + 1)) + 1 := by omega
    simp only [Exec.queries, hch, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
    rw [hD, hT']
    rfl

/-- The query count does not depend on the market condition. -/
theorem queries_root_with (M : MarketCond ι V k D) (A : Alg V) (X : Exec ι (Expert ι V k D))
    (hist : ℕ → ι → ℝ) (wIn : Expert ι V k D → ℝ) (hX : X.ValidWith M A 0 hist wIn)
    (hD : 0 < D) : X.queries = A.r₀ * (1 + below A.r (D - 1)) := by
  cases X with
  | leaf x wOut =>
    obtain ⟨hl, -, -⟩ := hX
    omega
  | node T y z child w x =>
    obtain ⟨-, hT, -, hprobe, -⟩ := hX
    have hT' : T = A.r₀ := by rw [hT, if_pos rfl]
    have hch : ∀ τ : Fin T, (child τ).queries = below A.r (D - 1) :=
      fun τ => queries_of_validWith M A (child τ) 1 _ _ (hprobe τ).2.1 Nat.one_pos
    simp only [Exec.queries, hch, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
    rw [hT']

theorem queries_root_le_with (M : MarketCond ι V k D) (A : Alg V) (hr : 2 ≤ A.r)
    (X : Exec ι (Expert ι V k D)) (hist : ℕ → ι → ℝ) (wIn : Expert ι V k D → ℝ)
    (hX : X.ValidWith M A 0 hist wIn) (hD : 0 < D) :
    X.queries ≤ 2 * A.r₀ * A.r ^ (D - 1) := by
  rw [queries_root_with M A X hist wIn hX hD]
  have := below_le A.r hr (D - 1)
  calc A.r₀ * (1 + below A.r (D - 1)) ≤ A.r₀ * (2 * A.r ^ (D - 1)) :=
        Nat.mul_le_mul_left _ (by omega)
    _ = 2 * A.r₀ * A.r ^ (D - 1) := by ring

theorem queries_of_valid (A : Alg V) (X : Exec ι (Expert ι V k D)) :
    ∀ (l : ℕ) (hist : ℕ → ι → ℝ) (wIn : Expert ι V k D → ℝ), X.Valid A l hist wIn → 0 < l →
      X.queries = below A.r (D - l) :=
  fun l hist wIn hv =>
    queries_of_validWith _ A X l hist wIn ((Exec.validWith_exact_iff A X l hist wIn).2 hv)

/-- **Query count.** A valid run from the root makes exactly
`r₀ (1 + r + ⋯ + r^(D-1))` label queries. -/
theorem queries_root (A : Alg V) (X : Exec ι (Expert ι V k D)) (hist : ℕ → ι → ℝ)
    (wIn : Expert ι V k D → ℝ) (hX : X.Valid A 0 hist wIn) (hD : 0 < D) :
    X.queries = A.r₀ * (1 + below A.r (D - 1)) :=
  queries_root_with _ A X hist wIn ((Exec.validWith_exact_iff A X 0 hist wIn).2 hX) hD

theorem queries_root_le (A : Alg V) (hr : 2 ≤ A.r) (X : Exec ι (Expert ι V k D))
    (hist : ℕ → ι → ℝ) (wIn : Expert ι V k D → ℝ) (hX : X.Valid A 0 hist wIn) (hD : 0 < D) :
    X.queries ≤ 2 * A.r₀ * A.r ^ (D - 1) :=
  queries_root_le_with _ A hr X hist wIn ((Exec.validWith_exact_iff A X 0 hist wIn).2 hX) hD

/-! ### The least admissible depth -/

theorem exists_depth {B : ℝ} (hB : 1 < B) (M : ℕ) : ∃ D : ℕ, ((M : ℝ)) ^ 2 < B ^ D :=
  pow_unbounded_of_one_lt _ hB

/-- The least `D` with `M² < B^D`. -/
noncomputable def depth {B : ℝ} (hB : 1 < B) (M : ℕ) : ℕ := by
  classical exact Nat.find (exists_depth hB M)

theorem depth_spec {B : ℝ} (hB : 1 < B) (M : ℕ) : ((M : ℝ)) ^ 2 < B ^ depth hB M := by
  classical exact Nat.find_spec (exists_depth hB M)

theorem depth_pos {B : ℝ} (hB : 1 < B) {M : ℕ} (hM : 1 ≤ M) : 0 < depth hB M := by
  by_contra h
  have h0 : depth hB M = 0 := by omega
  have hs := depth_spec hB M
  rw [h0, pow_zero] at hs
  have : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  nlinarith

theorem depth_min {B : ℝ} (hB : 1 < B) {M : ℕ} (hM : 1 ≤ M) :
    B ^ (depth hB M - 1) ≤ ((M : ℝ)) ^ 2 := by
  classical
  have hpos := depth_pos hB hM
  have hlt : depth hB M - 1 < depth hB M := by omega
  have := Nat.find_min (exists_depth hB M) hlt
  exact not_lt.1 this

/-- If `r² ≤ B^e` and `B^(D-1) ≤ M²` then `r^(D-1) ≤ M^e`. -/
theorem pow_depth_le {B : ℝ} (hB : 1 < B) {r M e D' : ℕ} (hr : ((r : ℝ)) ^ 2 ≤ B ^ e)
    (hD : B ^ D' ≤ ((M : ℝ)) ^ 2) : r ^ D' ≤ M ^ e := by
  have h1 : (((r : ℝ)) ^ D') ^ 2 ≤ (((M : ℝ)) ^ e) ^ 2 := by
    calc (((r : ℝ)) ^ D') ^ 2 = (((r : ℝ)) ^ 2) ^ D' := by ring
      _ ≤ (B ^ e) ^ D' := pow_le_pow_left₀ (by positivity) hr D'
      _ = (B ^ D') ^ e := by ring
      _ ≤ (((M : ℝ)) ^ 2) ^ e := pow_le_pow_left₀ (by positivity) hD e
      _ = (((M : ℝ)) ^ e) ^ 2 := by ring
  have h2 : ((r : ℝ)) ^ D' ≤ ((M : ℝ)) ^ e :=
    le_of_sq_le_sq h1 (by positivity)
  exact_mod_cast h2

end SPLP
