import Mathlib
import SPLP.Strategy

/-!
# A single-coordinate query model

`SPLP.Upstream` mirrors the query model of another development: a hidden instance has a sign
`positive`, a set `active` of coordinates containing a fixed `anchor`, and a cost in `[0, R]`
on each coordinate. A query names a rational price vector and one coordinate; the reply is
constrained (to equal `positive`) only when the query is forced: its coordinate is active and
minimizes cost plus signed price over the active set. A decision tree must output `positive`.

`exists_tree` builds such a tree from the price search of `SPLP/Strategy.lean`: a hidden
instance is the hypothesis with slots `(i, positive)`, `i` active, and demands
`R + 1 - cost i ∈ [1, R + 1]`. A slot of maximum surplus is a forced coordinate, so asking all
`N` coordinates at a point queried by the strategy yields a label vector consistent with the
hypothesis. The returned prices meet the demand `≥ 1` of the anchor on the side `positive`, so
their sign at the anchor is the answer.
-/

set_option linter.unusedSectionVars false

namespace SPLP

namespace Upstream

/-- A query: a rational price vector and the coordinate whose label is asked. -/
structure Query (N : ℕ) where
  prices : Fin N → ℚ
  index : Fin N

/-- A hidden instance. -/
structure Hidden (N R : ℕ) (anchor : Fin N) where
  positive : Bool
  active : Finset (Fin N)
  anchor_mem : anchor ∈ active
  cost : Fin N → Fin (R + 1)

variable {N R : ℕ} {anchor : Fin N}

def Hidden.signedPrice (h : Hidden N R anchor) (t : ℚ) : ℚ := if h.positive then t else -t

def Hidden.Forced (h : Hidden N R anchor) (q : Query N) : Prop :=
  q.index ∈ h.active ∧ ∀ j ∈ h.active,
    (h.cost q.index : ℕ) + h.signedPrice (q.prices q.index)
      ≤ (h.cost j : ℕ) + h.signedPrice (q.prices j)

inductive Tree (N : ℕ) where
  | result (answer : Bool)
  | ask (query : Query N) (next : Bool → Tree N)

inductive Tree.Reaches (h : Hidden N R anchor) : Tree N → Bool → Prop where
  | result (answer : Bool) : Reaches h (.result answer) answer
  | ask {q : Query N} {next : Bool → Tree N} {reply answer : Bool}
      (allowed : h.Forced q → reply = h.positive) (rest : Reaches h (next reply) answer) :
      Reaches h (.ask q next) answer

def Tree.Correct (h : Hidden N R anchor) (t : Tree N) : Prop :=
  ∀ answer, Tree.Reaches h t answer → answer = h.positive

def Tree.height : Tree N → ℕ
  | .result _ => 0
  | .ask _ next => max (height (next false)) (height (next true)) + 1

end Upstream

/-! ### Hidden instances as hypotheses -/

variable {N R : ℕ} {anchor : Fin N}

/-- Demands `0, …, R + 1`, read as real numbers. -/
def natVal (R : ℕ) : Fin (R + 2) → ℝ := fun v => ((v : ℕ) : ℝ)

theorem natVal_int (R : ℕ) : ∀ v, ∃ n : ℤ, natVal R v = n :=
  fun v => ⟨((v : ℕ) : ℤ), by simp [natVal]⟩

/-- The hypothesis of a hidden instance: the slots `(i, positive)` for `i` active, with
demand `R + 1 - cost i`. -/
def hypOf (h : Upstream.Hidden N R anchor) : Hyp (Fin N) (Fin (R + 2)) where
  S := h.active.image (fun i => (i, h.positive))
  ne := ⟨(anchor, h.positive), Finset.mem_image_of_mem _ h.anchor_mem⟩
  a := fun s => ⟨R + 1 - (h.cost s.1 : ℕ), by omega⟩

theorem natVal_hypOf (h : Upstream.Hidden N R anchor) (s : Slot (Fin N)) :
    natVal R ((hypOf h).a s) = (R : ℝ) + 1 - ((h.cost s.1 : ℕ) : ℝ) := by
  have hc : (h.cost s.1 : ℕ) ≤ R + 1 := by
    have := (h.cost s.1).2
    omega
  simp only [natVal, hypOf]
  rw [Nat.cast_sub hc]
  push_cast
  ring

/-- A slot of maximum surplus is a forced coordinate. -/
theorem forced_of_max (h : Upstream.Hidden N R anchor) (x : Fin N → ℝ) (p : Fin N → ℚ)
    (hp : ∀ i, ((p i : ℚ) : ℝ) = x i) (i : Fin N) (hi : i ∈ h.active)
    (hmax : ∀ u ∈ (hypOf h).S,
      (hypOf h).surplus (natVal R) x u ≤ (hypOf h).surplus (natVal R) x (i, h.positive)) :
    h.Forced ⟨p, i⟩ := by
  refine ⟨hi, fun j hj => ?_⟩
  have hj' := hmax (j, h.positive) (Finset.mem_image_of_mem _ hj)
  simp only [Hyp.surplus, natVal_hypOf, sp, sgn] at hj'
  rw [← Rat.cast_le (K := ℝ)]
  simp only [Upstream.Hidden.signedPrice]
  rcases hb : h.positive with _ | _
  · simp only [hb, Bool.false_eq_true, if_false] at hj' ⊢
    push_cast
    rw [hp, hp]
    linarith
  · simp only [hb, if_true] at hj' ⊢
    push_cast
    rw [hp, hp]
    linarith

/-! ### From label vectors to single labels -/

/-- Ask the labels of the coordinates in the list at the prices `p`, record the replies in
`acc`, and continue with the collected vector. -/
def askList (p : Fin N → ℚ) :
    List (Fin N) → (Fin N → Bool) → ((Fin N → Bool) → Upstream.Tree N) → Upstream.Tree N
  | [], acc, cont => cont acc
  | i :: is, acc, cont => .ask ⟨p, i⟩ (fun b => askList p is (Function.update acc i b) cont)

theorem askList_height (p : Fin N → ℚ) (cont : (Fin N → Bool) → Upstream.Tree N) (B : ℕ)
    (hB : ∀ z, (cont z).height ≤ B) :
    ∀ (L : List (Fin N)) (acc : Fin N → Bool), (askList p L acc cont).height ≤ L.length + B
  | [], acc => by
    simpa [askList] using hB acc
  | i :: is, acc => by
    have h1 := askList_height p cont B hB is (Function.update acc i false)
    have h2 := askList_height p cont B hB is (Function.update acc i true)
    simp only [askList, Upstream.Tree.height, List.length_cons]
    omega

theorem askList_reaches (h : Upstream.Hidden N R anchor) (p : Fin N → ℚ)
    (cont : (Fin N → Bool) → Upstream.Tree N) (ans : Bool) :
    ∀ (L : List (Fin N)) (acc : Fin N → Bool),
      Upstream.Tree.Reaches h (askList p L acc cont) ans →
      ∃ z, Upstream.Tree.Reaches h (cont z) ans ∧
        (∀ i ∈ L, h.Forced ⟨p, i⟩ → z i = h.positive) ∧ (∀ i, i ∉ L → z i = acc i)
  | [], acc, hr => ⟨acc, hr, fun i hi => absurd hi (by simp), fun _ _ => rfl⟩
  | i :: is, acc, hr => by
    rw [askList] at hr
    cases hr with
    | @ask _ _ reply _ allowed rest =>
      obtain ⟨z, hz, h1, h2⟩ := askList_reaches h p cont ans is _ rest
      refine ⟨z, hz, ?_, ?_⟩
      · intro j hj hf
        by_cases hjis : j ∈ is
        · exact h1 j hjis hf
        · have hji : j = i := by
            rcases List.mem_cons.1 hj with e | e
            · exact e
            · exact absurd e hjis
          subst hji
          rw [h2 j hjis, Function.update_self]
          exact allowed hf
      · intro j hj
        have hji : j ≠ i := fun e => hj (e ▸ List.mem_cons_self)
        have hjis : j ∉ is := fun e => hj (List.mem_cons_of_mem _ e)
        rw [h2 j hjis, Function.update_of_ne hji]

open Classical in
/-- Rational representatives of the coordinates of a point (`0` where irrational). -/
noncomputable def ratOf (x : Fin N → ℝ) : Fin N → ℚ :=
  fun i => if h : ∃ q : ℚ, (q : ℝ) = x i then Classical.choose h else 0

theorem ratOf_spec {x : Fin N → ℝ} (hx : Strat.IsRat x) (i : Fin N) :
    ((ratOf x i : ℚ) : ℝ) = x i := by
  unfold ratOf
  rw [dif_pos (hx i)]
  exact Classical.choose_spec (hx i)

/-- Replace each label-vector query of a strategy by `N` single-coordinate queries at the
same point, and the result by a Boolean read off it. -/
noncomputable def toTree {α : Type*} (out : α → Bool) : Strat (Fin N) α → Upstream.Tree N
  | .done a => .result (out a)
  | .ask x next =>
      askList (ratOf x) (List.finRange N) (fun _ => false) (fun z => toTree out (next z))

theorem toTree_height {α : Type*} (out : α → Bool) (S : Strat (Fin N) α) :
    (toTree out S).height ≤ N * S.height := by
  induction S with
  | done a => simp [toTree, Upstream.Tree.height]
  | ask x next ih =>
    rw [toTree]
    have key := askList_height (ratOf x) (fun z => toTree out (next z))
      (N * Finset.univ.sup fun z => (next z).height)
      (fun z => (ih z).trans (Nat.mul_le_mul_left _
        (Finset.le_sup (f := fun z => (next z).height) (Finset.mem_univ z))))
      (List.finRange N) (fun _ => false)
    rw [List.length_finRange] at key
    simp only [Strat.height]
    rw [Nat.mul_succ]
    omega

/-- A branch of the tree comes from a branch of the strategy whose answers are consistent
with the hypothesis of the hidden instance. -/
theorem toTree_reaches (h : Upstream.Hidden N R anchor) {α : Type*} (out : α → Bool)
    (Q : α → Prop) (S : Strat (Fin N) α) (hrat : S.Forall Strat.IsRat Q) (ans : Bool) :
    Upstream.Tree.Reaches h (toTree out S) ans →
      ∃ a, S.Reaches (fun p z => (hypOf h).ConsistentAt (natVal R) p z) a ∧ ans = out a := by
  induction S with
  | done a =>
    intro hr
    rw [toTree] at hr
    cases hr
    exact ⟨a, .done a, rfl⟩
  | ask x next ih =>
    intro hr
    rw [toTree] at hr
    obtain ⟨hx, hnext⟩ := Strat.forall_ask_iff.1 hrat
    obtain ⟨z, hz, h1, -⟩ := askList_reaches h (ratOf x) _ ans _ _ hr
    obtain ⟨a, ha, rfl⟩ := ih z (hnext z) hz
    refine ⟨a, .ask ?_ ha, rfl⟩
    intro s hs hmax _
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hs
    exact h1 i (List.mem_finRange i)
      (forced_of_max h x (ratOf x) (ratOf_spec hx) i hi hmax)

/-! ### The bridge -/

/-- **A decision tree for the single-coordinate model.** For `N` coordinates and costs in
`[0, R]` there is a tree of height at most `N · 2 r₀ (2N)^46` that outputs the hidden sign of
every hidden instance, whatever the unconstrained replies. -/
theorem exists_tree (N R : ℕ) (anchor : Fin N) :
    ∃ t : Upstream.Tree N,
      t.height ≤ N * (2 * K4.r₀ (Fin N) (Fin (R + 2)) (K4.depth K4_good N) * (2 * N) ^ 46) ∧
      ∀ h : Upstream.Hidden N R anchor, Upstream.Tree.Correct h t := by
  classical
  haveI : Nonempty (Fin N) := ⟨anchor⟩
  refine ⟨toTree (fun x : Fin N → ℝ => decide (0 < x anchor)) (strategyK4 (natVal R)), ?_, ?_⟩
  · have h1 := strategyK4_height (ι := Fin N) (natVal R)
    rw [Fintype.card_fin] at h1
    exact (toTree_height _ _).trans (Nat.mul_le_mul_left _ h1)
  · intro h ans hr
    obtain ⟨x, hx, rfl⟩ := toTree_reaches h _ _ _
      (strategyK4_allRational (ι := Fin N) (natVal R) (natVal_int R)) ans hr
    have hdem := strategyK4_correct (natVal R) (hypOf h) x hx (anchor, h.positive)
      (Finset.mem_image_of_mem _ h.anchor_mem)
    rw [natVal_hypOf] at hdem
    have hc : (((h.cost anchor : ℕ) : ℝ)) ≤ R := by
      have := (h.cost anchor).2
      exact_mod_cast Nat.lt_succ_iff.1 this
    simp only [sp, sgn] at hdem
    rcases hb : h.positive with _ | _
    · simp only [hb, Bool.false_eq_true, if_false] at hdem
      have : ¬ 0 < x anchor := by linarith
      simp [this]
    · simp only [hb, if_true] at hdem
      have : 0 < x anchor := by linarith
      simp [this]

/-! ### An explicit height bound -/

/-- The arity-4 depth is at most `8 N²` (a crude bound; it is in fact logarithmic in `N`). -/
theorem K4_depth_le (N : ℕ) (hN : 1 ≤ N) : K4.depth K4_good N ≤ 8 * N ^ 2 := by
  have hB := K4.b_real K4_good
  have hM : 1 ≤ 2 * N := by omega
  have hmin : ((K4.ρ : ℝ) ^ 2 / (K4.β : ℝ)) ^ (K4.depth K4_good N - 1)
      ≤ (((2 * N : ℕ)) : ℝ) ^ 2 := depth_min hB hM
  have hpos : 0 < K4.depth K4_good N := depth_pos hB hM
  have hq : (3 / 2 : ℚ) ≤ K4.ρ ^ 2 / K4.β := by norm_num [K4, Consts.ρ]
  have hr : (3 / 2 : ℝ) ≤ (K4.ρ : ℝ) ^ 2 / (K4.β : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).2 hq
    push_cast at h
    exact h
  have hbern : 1 + ((K4.depth K4_good N - 1 : ℕ) : ℝ) * (1 / 2)
      ≤ (1 + 1 / 2 : ℝ) ^ (K4.depth K4_good N - 1) := one_add_mul_le_pow (by norm_num) _
  have hpow : (1 + 1 / 2 : ℝ) ^ (K4.depth K4_good N - 1)
      ≤ ((K4.ρ : ℝ) ^ 2 / (K4.β : ℝ)) ^ (K4.depth K4_good N - 1) :=
    pow_le_pow_left₀ (by norm_num) (by linarith) _
  rw [Nat.cast_pred hpos] at hbern
  push_cast at hmin
  have h1 : ((K4.depth K4_good N : ℕ) : ℝ) ≤ ((8 * N ^ 2 : ℕ) : ℝ) := by
    push_cast
    nlinarith
  exact_mod_cast h1

/-- The arity-4 expert pool of the bridge has at most `272 N⁷ (R + 2)⁵` experts. -/
theorem K4_card_expert_le (N R : ℕ) (hN : 1 ≤ N) :
    Fintype.card (Expert (Fin N) (Fin (R + 2)) 4 (K4.depth K4_good N))
      ≤ 272 * N ^ 7 * (R + 2) ^ 5 := by
  rw [card_expert, Fintype.card_fin, Fintype.card_fin]
  have hD := K4_depth_le N hN
  have h1 : K4.depth K4_good N * (2 * N * (R + 2)) + 1 ≤ 17 * N ^ 3 * (R + 2) := by
    have h2 : K4.depth K4_good N * (2 * N * (R + 2)) ≤ 8 * N ^ 2 * (2 * N * (R + 2)) :=
      Nat.mul_le_mul_right _ hD
    have h3 : 1 ≤ N ^ 3 * (R + 2) := Nat.one_le_iff_ne_zero.2 (by positivity)
    calc K4.depth K4_good N * (2 * N * (R + 2)) + 1
        ≤ 8 * N ^ 2 * (2 * N * (R + 2)) + 1 := by omega
      _ = 16 * (N ^ 3 * (R + 2)) + 1 := by ring
      _ ≤ 17 * (N ^ 3 * (R + 2)) := by omega
      _ = 17 * N ^ 3 * (R + 2) := by ring
  calc (2 * N) ^ 4 * (R + 2) ^ 4 * (K4.depth K4_good N * (2 * N * (R + 2)) + 1)
      ≤ (2 * N) ^ 4 * (R + 2) ^ 4 * (17 * N ^ 3 * (R + 2)) := Nat.mul_le_mul_left _ h1
    _ = 272 * N ^ 7 * (R + 2) ^ 5 := by ring

/-- The number of root probes of the bridge is `O(log N + log R)`. -/
theorem K4_r₀_le_log (N R : ℕ) (hN : 1 ≤ N) :
    (K4.r₀ (Fin N) (Fin (R + 2)) (K4.depth K4_good N) : ℝ)
      ≤ 186473 + 70784 * Real.log N + 50560 * Real.log (R + 2) := by
  have h := K4_r₀_le (ι := Fin N) (V := Fin (R + 2)) (K4.depth K4_good N)
  have hcard : ((Fintype.card (Expert (Fin N) (Fin (R + 2)) 4 (K4.depth K4_good N)) : ℕ) : ℝ)
      ≤ ((272 * N ^ 7 * (R + 2) ^ 5 : ℕ) : ℝ) := by
    exact_mod_cast K4_card_expert_le N R hN
  push_cast at hcard
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hR' : (1 : ℝ) ≤ (R : ℝ) + 2 := by
    have : (0 : ℝ) ≤ R := Nat.cast_nonneg R
    linarith
  have h1 : (1 : ℝ) ≤ (N : ℝ) ^ 7 * ((R : ℝ) + 2) ^ 5 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hN') (one_le_pow₀ hR')
  have hcard' : (1 : ℝ) + Fintype.card (Expert (Fin N) (Fin (R + 2)) 4 (K4.depth K4_good N))
      ≤ 273 * (N : ℝ) ^ 7 * ((R : ℝ) + 2) ^ 5 := by nlinarith
  have hlog := Real.log_le_log (by positivity) hcard'
  have hNpos : (0 : ℝ) < N := by linarith
  have hRpos : (0 : ℝ) < (R : ℝ) + 2 := by linarith
  have hsplit : Real.log (273 * (N : ℝ) ^ 7 * ((R : ℝ) + 2) ^ 5)
      = Real.log 273 + 7 * Real.log N + 5 * Real.log (R + 2) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have h273 : Real.log 273 ≤ 6 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he := Real.exp_one_gt_d9
    have h6 : Real.exp 6 = Real.exp 1 ^ 6 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [h6]
    calc (273 : ℝ) ≤ 2.7 ^ 6 := by norm_num
      _ ≤ Real.exp 1 ^ 6 := pow_le_pow_left₀ (by norm_num) (by linarith) 6
  rw [hsplit] at hlog
  linarith

/-- **The decision tree with an explicit height**: at most
`N · 2 (186473 + 70784 log N + 50560 log (R + 2)) (2N)^46` single-coordinate queries. -/
theorem exists_tree_explicit (N R : ℕ) (anchor : Fin N) :
    ∃ t : Upstream.Tree N,
      (t.height : ℝ) ≤ N * (2 * (186473 + 70784 * Real.log N + 50560 * Real.log (R + 2))
        * (2 * N) ^ 46) ∧
      ∀ h : Upstream.Hidden N R anchor, Upstream.Tree.Correct h t := by
  obtain ⟨t, ht, hc⟩ := exists_tree N R anchor
  refine ⟨t, ?_, hc⟩
  have hN : 1 ≤ N := by
    have := anchor.2
    omega
  have h1 : (t.height : ℝ) ≤ ((N * (2 * K4.r₀ (Fin N) (Fin (R + 2)) (K4.depth K4_good N)
      * (2 * N) ^ 46) : ℕ) : ℝ) := by exact_mod_cast ht
  push_cast at h1
  refine h1.trans ?_
  gcongr
  exact K4_r₀_le_log N R hN

end SPLP
