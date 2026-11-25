import Mathlib
import SPLP.Market
import SPLP.Median

/-!
# The recursive price search: definitions

This file fixes the objects of Theorem 2 ("Extremal prices") of the preprint
*Strongly polynomial linear programming* and of the recursive market algorithm of its
Section 6, in a relational form:

* `Hyp`: a hypothesis (a set of slots with demands), its surplus and consistency with a label.
* `Expert`: an expert guessing `k` slots with demands and a threshold description.
* `Exec`: the record of one run of the recursive algorithm (a tree of probes), together with
  `Exec.Valid` (the record obeys the algorithm) and `Exec.Consistent` (a hypothesis agrees with
  every label recorded in the run).

Nothing here depends on how minimizers, medians or labels are chosen: `Exec.Valid` allows any
market minimizer, any weak median and arbitrary labels, so a statement about all valid records
covers every adaptive label oracle.
-/

namespace SPLP

open Finset

/-! ### Generic market: least payoff among maximizing options -/

section Generic

variable {ι E O : Type*} [Fintype ι] [Fintype O] [Nonempty O]

theorem util_le_best (b : E → O → ℝ) (u : E → O → ι → ℝ) (e : E) (o : O) (y : ι → ℝ) :
    util b u e o y ≤ best b u e y :=
  Finset.le_sup' (fun o => util b u e o y) (Finset.mem_univ o)

theorem bestSet_nonempty (b : E → O → ℝ) (u : E → O → ι → ℝ) (e : E) (y : ι → ℝ) :
    (univ.filter (fun o => util b u e o y = best b u e y)).Nonempty := by
  obtain ⟨o, -, ho⟩ := Finset.exists_mem_eq_sup' (univ_nonempty (α := O))
    (fun o => util b u e o y)
  exact ⟨o, by simp [best, ho]⟩

/-- The least payoff among the options maximizing utility at `y`. -/
noncomputable def minPay (b : E → O → ℝ) (u : E → O → ι → ℝ) (e : E) (y v : ι → ℝ) : ℝ :=
  (univ.filter (fun o => util b u e o y = best b u e y)).inf' (bestSet_nonempty b u e y)
    (fun o => pay u e o v)

theorem minPay_le (b : E → O → ℝ) (u : E → O → ι → ℝ) (e : E) (y v : ι → ℝ) (o : O)
    (h : util b u e o y = best b u e y) : minPay b u e y v ≤ pay u e o v :=
  Finset.inf'_le _ (by simp [h])

theorem le_minPay (b : E → O → ℝ) (u : E → O → ι → ℝ) (e : E) (y v : ι → ℝ) (a : ℝ)
    (h : ∀ o, util b u e o y = best b u e y → a ≤ pay u e o v) : a ≤ minPay b u e y v := by
  refine (Finset.le_inf'_iff _ _).2 ?_
  intro o ho
  exact h o (by simpa using ho)

theorem minPay_le_of_forall (b : E → O → ℝ) (u : E → O → ι → ℝ) (e : E) (y v : ι → ℝ) (a : ℝ)
    (h : ∀ o, util b u e o y = best b u e y → pay u e o v ≤ a) : minPay b u e y v ≤ a := by
  obtain ⟨o, ho⟩ := bestSet_nonempty b u e y
  have ho' : util b u e o y = best b u e y := by simpa using ho
  exact (minPay_le b u e y v o ho').trans (h o ho')

end Generic

/-! ### Slots, hypotheses, labels -/

/-- A slot is a coordinate together with a sign (`true` is `+`, `false` is `-`). -/
abbrev Slot (ι : Type*) := ι × Bool

/-- The sign of a slot as a real number. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- Signed price of a slot: `y_i` on `(i,+)` and `-y_i` on `(i,-)`. -/
def sp {ι : Type*} (y : ι → ℝ) (s : Slot ι) : ℝ := sgn s.2 * y s.1

/-- A hypothesis: a nonempty set of slots with a demand on each. Demands are drawn from a
finite type `V` and read through a valuation `val : V → ℝ` (for instance the integers in
`[-R, R]`). -/
structure Hyp (ι V : Type*) where
  S : Finset (Slot ι)
  ne : S.Nonempty
  a : Slot ι → V

variable {ι V : Type*}

/-- Surplus `a_s - y_s` of slot `s` at prices `y`. -/
def Hyp.surplus (val : V → ℝ) (H : Hyp ι V) (y : ι → ℝ) (s : Slot ι) : ℝ :=
  val (H.a s) - sp y s

/-- The hypothesis agrees with the label vector `z` returned at the query `x`: every slot of
maximum surplus, when that maximum is nonnegative, carries its own sign as label. -/
def Hyp.ConsistentAt (val : V → ℝ) (H : Hyp ι V) (x : ι → ℝ) (z : ι → Bool) : Prop :=
  ∀ s ∈ H.S, (∀ u ∈ H.S, H.surplus val x u ≤ H.surplus val x s) →
    0 ≤ H.surplus val x s → z s.1 = s.2

/-! ### Experts -/

/-- An expert: `k` slots with a guessed demand on each, and either the zero threshold (`none`)
or a pivot level `j < D`, a pivot slot and a guessed demand on it. -/
abbrev Expert (ι V : Type*) (k D : ℕ) :=
  (Fin k → Slot ι) × (Fin k → V) × Option (Fin D × Slot ι × V)

variable {k D : ℕ}

/-- The threshold estimate of an expert at a node of level `l` whose path carries the proposals
`hist 0, …, hist (l-1)`. It is `none` when the expert does not bid at this level. -/
def thr (val : V → ℝ) (l : ℕ) (hist : ℕ → ι → ℝ) (e : Expert ι V k D) : Option ℝ :=
  match e.2.2 with
  | none => some 0
  | some (j, p, b) => if (j : ℕ) < l then some (val b - sp (hist j) p) else none

/-- Bids of the options of an expert: `none` is the outside option. -/
def bidOf (val : V → ℝ) (l : ℕ) (hist : ℕ → ι → ℝ) (e : Expert ι V k D) :
    Option (Fin k) → ℝ
  | none => 0
  | some q =>
    match thr val l hist e with
    | none => 0
    | some τ => val (e.2.1 q) - τ

/-- Price directions of the options of an expert. -/
def dirOf [DecidableEq ι] (val : V → ℝ) (l : ℕ) (hist : ℕ → ι → ℝ) (e : Expert ι V k D) :
    Option (Fin k) → ι → ℝ
  | none => fun _ => 0
  | some q =>
    match thr val l hist e with
    | none => fun _ => 0
    | some _ => fun i => if i = (e.1 q).1 then sgn (e.1 q).2 else 0

/-- A feedback vector as a direction in price space. -/
def vreal (v : ι → Bool) : ι → ℝ := fun i => sgn (v i)

/-- Feedback at the proposal `y` from the child's prices `x`, ties broken by the labels `z`
queried at `x` (equation (5.2) of the preprint). -/
noncomputable def feedback (y x : ι → ℝ) (z : ι → Bool) : ι → Bool :=
  fun i => if y i < x i then true else if x i < y i then false else z i

variable [Fintype ι] [DecidableEq ι]

/-- The market gain of an expert: the least payoff among its maximizing options. -/
noncomputable def gain (val : V → ℝ) (l : ℕ) (hist : ℕ → ι → ℝ) (y : ι → ℝ) (v : ι → Bool)
    (e : Expert ι V k D) : ℝ :=
  minPay (bidOf val l hist) (dirOf val l hist) e y (vreal v)

variable [Fintype V]

/-- The market potential `Φ` at a node, for the wealth vector `w`. -/
noncomputable def Phi (val : V → ℝ) (l : ℕ) (hist : ℕ → ι → ℝ) (w : Expert ι V k D → ℝ)
    (y : ι → ℝ) : ℝ :=
  potential (bidOf val l hist) (dirOf val l hist) w y

/-! ### Records of a run -/

/-- The record of a run of the recursive algorithm below one node.

A leaf records its returned prices and wealth. An internal node records, for each of its `T`
probes, the proposal `y`, the labels `z` queried at the child's prices, and the child's record;
the wealth `w τ` before probe `τ` (so `w T` is returned); and its returned prices `x`. -/
inductive Exec (ι E : Type*) : Type _ where
  | leaf (x : ι → ℝ) (wOut : E → ℝ) : Exec ι E
  | node (T : ℕ) (y : Fin T → ι → ℝ) (z : Fin T → ι → Bool) (child : Fin T → Exec ι E)
      (w : ℕ → E → ℝ) (x : ι → ℝ) : Exec ι E

/-- Prices returned by a node. -/
def Exec.x {E : Type*} : Exec ι E → ι → ℝ
  | .leaf x _ => x
  | .node _ _ _ _ _ x => x

/-- Wealth returned by a node. -/
def Exec.wOut {E : Type*} : Exec ι E → E → ℝ
  | .leaf _ wOut => wOut
  | .node T _ _ _ w _ => w T

/-- Number of label queries recorded below a node (one per probe). -/
def Exec.queries {E : Type*} : Exec ι E → ℕ
  | .leaf _ _ => 0
  | .node T _ _ child _ _ => ∑ τ : Fin T, (1 + (child τ).queries)

/-- The numerical parameters of the algorithm: valuation of demands, number of probes at
non-root internal nodes and at the root, investment share `c`, learning rate `η`, and the
rounding `rnd` applied to every updated wealth value (the identity for exact arithmetic). -/
structure Alg (V : Type*) where
  val : V → ℝ
  r : ℕ
  r₀ : ℕ
  c : ℝ
  η : ℝ
  rnd : ℝ → ℝ

/-- `X.Valid A l hist wIn`: the record `X` is a run of the algorithm at a node of level `l`
whose path carries the proposals `hist 0, …, hist (l-1)` and which receives wealth `wIn`.
Leaves sit at level `D` and return a coordinatewise median of the path's proposals.
An internal node makes `r` probes (`r₀` at the root). In each probe it keeps the share `1 - c`
of the current wealth in a market, proposes a minimizer of that market's potential, sends the
share `c` to a child, queries labels at the child's prices and updates the wealth to
`rnd ((1 - c) w (1 + η g) + w')`. It returns a coordinatewise median of its children's
prices. -/
def Exec.Valid (A : Alg V) :
    Exec ι (Expert ι V k D) → ℕ → (ℕ → ι → ℝ) → (Expert ι V k D → ℝ) → Prop
  | .leaf x wOut, l, hist, wIn =>
      l = D ∧ wOut = wIn ∧ ∀ i, IsMedian (fun j : Fin l => hist j i) (x i)
  | .node T y z child w x, l, hist, wIn =>
      l < D ∧ T = (if l = 0 then A.r₀ else A.r) ∧ w 0 = wIn ∧
      (∀ τ : Fin T,
        (∀ y', Phi A.val l hist (fun e => (1 - A.c) * w τ e) (y τ)
              ≤ Phi A.val l hist (fun e => (1 - A.c) * w τ e) y') ∧
        (child τ).Valid A (l + 1) (Function.update hist l (y τ)) (fun e => A.c * w τ e) ∧
        (∀ e, w (τ + 1) e = A.rnd ((1 - A.c) * w τ e
            * (1 + A.η * gain A.val l hist (y τ) (feedback (y τ) (child τ).x (z τ)) e)
            + (child τ).wOut e))) ∧
      (∀ i, IsMedian (fun τ : Fin T => (child τ).x i) (x i))

/-- The hypothesis agrees with every label recorded in the run. -/
def Exec.Consistent {E : Type*} (val : V → ℝ) (H : Hyp ι V) : Exec ι E → Prop
  | .leaf _ _ => True
  | .node T _ z child _ _ =>
      ∀ τ : Fin T, H.ConsistentAt val (child τ).x (z τ) ∧ (child τ).Consistent val H

/-! ### Runs with a general market condition -/

/-- A market condition: `M l hist w y` says that the proposal `y` is acceptable at a node of
level `l` with path `hist` when the wealth kept in the market is `w`. -/
abbrev MarketCond (ι V : Type*) (k D : ℕ) :=
  ℕ → (ℕ → ι → ℝ) → (Expert ι V k D → ℝ) → (ι → ℝ) → Prop

/-- The exact market: the proposal minimizes the potential for the true wealth. -/
def exactMarket (val : V → ℝ) : MarketCond ι V k D :=
  fun l hist w y => ∀ y', Phi val l hist w y ≤ Phi val l hist w y'

/-- The approximately cleared market: the proposal minimizes the potential for some
nonnegative weights `w'` whose total distance from the true wealth `w` is at most `ζ` times
the total wealth. -/
def approxMarket (val : V → ℝ) (ζ : ℝ) : MarketCond ι V k D :=
  fun l hist w y => ∃ w' : Expert ι V k D → ℝ, (∀ e, 0 ≤ w' e) ∧
    ∑ e, |w' e - w e| ≤ ζ * ∑ e, w e ∧
    ∀ y', Phi val l hist w' y ≤ Phi val l hist w' y'

/-- `Exec.Valid` with the market condition replaced by `M`. -/
def Exec.ValidWith (M : MarketCond ι V k D) (A : Alg V) :
    Exec ι (Expert ι V k D) → ℕ → (ℕ → ι → ℝ) → (Expert ι V k D → ℝ) → Prop
  | .leaf x wOut, l, hist, wIn =>
      l = D ∧ wOut = wIn ∧ ∀ i, IsMedian (fun j : Fin l => hist j i) (x i)
  | .node T y z child w x, l, hist, wIn =>
      l < D ∧ T = (if l = 0 then A.r₀ else A.r) ∧ w 0 = wIn ∧
      (∀ τ : Fin T,
        M l hist (fun e => (1 - A.c) * w τ e) (y τ) ∧
        (child τ).ValidWith M A (l + 1) (Function.update hist l (y τ)) (fun e => A.c * w τ e) ∧
        (∀ e, w (τ + 1) e = A.rnd ((1 - A.c) * w τ e
            * (1 + A.η * gain A.val l hist (y τ) (feedback (y τ) (child τ).x (z τ)) e)
            + (child τ).wOut e))) ∧
      (∀ i, IsMedian (fun τ : Fin T => (child τ).x i) (x i))

/-- A valid run is a run with the exact market condition. -/
theorem Exec.validWith_exact_iff (A : Alg V) (X : Exec ι (Expert ι V k D)) :
    ∀ (l : ℕ) (hist : ℕ → ι → ℝ) (wIn : Expert ι V k D → ℝ),
      X.ValidWith (exactMarket A.val) A l hist wIn ↔ X.Valid A l hist wIn := by
  induction X with
  | leaf x wOut =>
    intro l hist wIn
    exact Iff.rfl
  | node T y z child w x ih =>
    intro l hist wIn
    simp only [Exec.ValidWith, Exec.Valid, exactMarket, ih]

omit [Fintype V] in
/-- Weakening the market condition keeps a run valid. -/
theorem Exec.ValidWith.mono {M M' : MarketCond ι V k D}
    (h : ∀ l hist w y, M l hist w y → M' l hist w y) (A : Alg V)
    (X : Exec ι (Expert ι V k D)) :
    ∀ (l : ℕ) (hist : ℕ → ι → ℝ) (wIn : Expert ι V k D → ℝ),
      X.ValidWith M A l hist wIn → X.ValidWith M' A l hist wIn := by
  induction X with
  | leaf x wOut =>
    intro l hist wIn hv
    exact hv
  | node T y z child w x ih =>
    intro l hist wIn hv
    obtain ⟨hl, hT, hw0, hprobe, hmed⟩ := hv
    exact ⟨hl, hT, hw0, fun τ => ⟨h _ _ _ _ (hprobe τ).1, ih τ _ _ _ (hprobe τ).2.1,
      (hprobe τ).2.2⟩, hmed⟩

end SPLP
