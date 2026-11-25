import Mathlib
import SPLP.Summary

/-!
# The price search as one adaptive strategy

`Exec.Valid` is a relation between a record and the algorithm: it allows any market minimizer
and any weak median. Here the algorithm is a single decision tree. A `Strat ι α` either stops
with a result or asks the label vector at a point and continues with a strategy that depends
on the answer. The program `prog` makes canonical choices (a vertex minimizer of the market
potential, an entry of the family as its median) and returns the whole record of its run.

* `prog_spec`: on every branch the returned record is a valid vertex run, and the queries
  asked on the branch are exactly the label queries of the record, in order.
* `exists_strategy_k4`: for integer demands there is a strategy of height at most
  `2 r₀ (2N)^46` whose queries and results are rational and whose result meets every demand of
  every hypothesis consistent with the answers on its branch.
-/

set_option linter.unusedSectionVars false

namespace SPLP

open Finset

/-- An adaptive strategy: stop with a result, or ask the label vector at the point `x` and
continue according to the answer. -/
inductive Strat (ι : Type*) (α : Type*) where
  | done (a : α) : Strat ι α
  | ask (x : ι → ℝ) (next : (ι → Bool) → Strat ι α) : Strat ι α

namespace Strat

variable {ι : Type*} {α β : Type*}

/-- Run `S`, then continue with the strategy `f a` chosen by its result. -/
def bind : Strat ι α → (α → Strat ι β) → Strat ι β
  | .done a, f => f a
  | .ask x next, f => .ask x (fun z => (next z).bind f)

/-- Apply `f` to the result. -/
def map (f : α → β) (S : Strat ι α) : Strat ι β := S.bind (fun a => .done (f a))

/-- The largest number of queries on a branch. -/
def height [Fintype ι] [DecidableEq ι] : Strat ι α → ℕ
  | .done _ => 0
  | .ask _ next => (Finset.univ.sup fun z => (next z).height) + 1

/-- `S.Reaches ok a`: some branch of `S` on which every answer `z` to a query `x` satisfies
`ok x z` ends with the result `a`. -/
inductive Reaches (ok : (ι → ℝ) → (ι → Bool) → Prop) : Strat ι α → α → Prop
  | done (a : α) : Reaches ok (.done a) a
  | ask {x : ι → ℝ} {next : (ι → Bool) → Strat ι α} {z : ι → Bool} {a : α} (h : ok x z)
      (rest : Reaches ok (next z) a) : Reaches ok (.ask x next) a

/-- `S.Trace tr a`: the branch of `S` whose queries and answers are listed in `tr`, in order,
ends with the result `a`. -/
inductive Trace : Strat ι α → List ((ι → ℝ) × (ι → Bool)) → α → Prop
  | done (a : α) : Trace (.done a) [] a
  | ask {x : ι → ℝ} {next : (ι → Bool) → Strat ι α} {z : ι → Bool}
      {tr : List ((ι → ℝ) × (ι → Bool))} {a : α} (rest : Trace (next z) tr a) :
      Trace (.ask x next) ((x, z) :: tr) a

theorem trace_done_iff {a b : α} {tr : List ((ι → ℝ) × (ι → Bool))} :
    Trace (.done a : Strat ι α) tr b ↔ tr = [] ∧ b = a := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact .done _

theorem trace_ask_iff {x : ι → ℝ} {next : (ι → Bool) → Strat ι α}
    {tr : List ((ι → ℝ) × (ι → Bool))} {b : α} :
    Trace (.ask x next) tr b ↔ ∃ z tr', tr = (x, z) :: tr' ∧ Trace (next z) tr' b := by
  constructor
  · intro h
    cases h with
    | ask rest => exact ⟨_, _, rfl, rest⟩
  · rintro ⟨z, tr', rfl, h⟩
    exact .ask h

theorem trace_bind_iff (S : Strat ι α) (f : α → Strat ι β)
    (tr : List ((ι → ℝ) × (ι → Bool))) (b : β) :
    Trace (S.bind f) tr b ↔
      ∃ a tr₁ tr₂, Trace S tr₁ a ∧ Trace (f a) tr₂ b ∧ tr = tr₁ ++ tr₂ := by
  induction S generalizing tr with
  | done a =>
    constructor
    · intro h
      exact ⟨a, [], tr, .done a, h, rfl⟩
    · rintro ⟨a', t1, t2, h1, h2, rfl⟩
      obtain ⟨rfl, rfl⟩ := trace_done_iff.1 h1
      exact h2
  | ask x next ih =>
    constructor
    · intro h
      obtain ⟨z, tr', rfl, h'⟩ := trace_ask_iff.1 h
      obtain ⟨a, t1, t2, h1, h2, rfl⟩ := (ih z tr').1 h'
      exact ⟨a, (x, z) :: t1, t2, .ask h1, h2, rfl⟩
    · rintro ⟨a, t1, t2, h1, h2, rfl⟩
      obtain ⟨z, t1', rfl, h1'⟩ := trace_ask_iff.1 h1
      exact Trace.ask ((ih z (t1' ++ t2)).2 ⟨a, t1', t2, h1', h2, rfl⟩)

theorem trace_map_iff (S : Strat ι α) (f : α → β) (tr : List ((ι → ℝ) × (ι → Bool)))
    (b : β) : Trace (S.map f) tr b ↔ ∃ a, Trace S tr a ∧ b = f a := by
  unfold map
  rw [trace_bind_iff]
  constructor
  · rintro ⟨a, t1, t2, h1, h2, rfl⟩
    obtain ⟨rfl, rfl⟩ := trace_done_iff.1 h2
    exact ⟨a, by simpa using h1, rfl⟩
  · rintro ⟨a, h, rfl⟩
    exact ⟨a, tr, [], h, .done _, by simp⟩

/-- A result is reached under the constraint `ok` exactly when it is the result of a branch
all of whose queries and answers satisfy `ok`. -/
theorem reaches_iff_trace {ok : (ι → ℝ) → (ι → Bool) → Prop} {S : Strat ι α} {a : α} :
    Reaches ok S a ↔ ∃ tr, Trace S tr a ∧ ∀ p ∈ tr, ok p.1 p.2 := by
  constructor
  · intro h
    induction h with
    | done a => exact ⟨[], .done a, by simp⟩
    | ask h rest ih =>
      obtain ⟨tr, ht, hok⟩ := ih
      refine ⟨_ :: tr, .ask ht, ?_⟩
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact h
      · exact hok p hp
  · rintro ⟨tr, ht, hok⟩
    induction ht with
    | done a => exact .done a
    | ask rest ih =>
      exact .ask (hok _ List.mem_cons_self)
        (ih (fun p hp => hok p (List.mem_cons_of_mem _ hp)))

/-- Every strategy has a branch. -/
theorem exists_trace (S : Strat ι α) : ∃ tr a, Trace S tr a := by
  induction S with
  | done a => exact ⟨[], a, .done a⟩
  | ask x next ih =>
    obtain ⟨tr, a, h⟩ := ih (fun _ => false)
    exact ⟨_, a, .ask h⟩

section Height

variable [Fintype ι] [DecidableEq ι]

theorem Trace.length_le_height {S : Strat ι α} {tr : List ((ι → ℝ) × (ι → Bool))} {a : α}
    (h : Trace S tr a) : tr.length ≤ S.height := by
  induction h with
  | done a => exact Nat.zero_le _
  | @ask x next z tr a rest ih =>
    simp only [List.length_cons, height]
    exact Nat.succ_le_succ
      (ih.trans (Finset.le_sup (f := fun z => (next z).height) (Finset.mem_univ z)))

/-- The height is the length of some branch. -/
theorem exists_trace_height (S : Strat ι α) :
    ∃ tr a, Trace S tr a ∧ tr.length = S.height := by
  induction S with
  | done a => exact ⟨[], a, .done a, rfl⟩
  | ask x next ih =>
    obtain ⟨z, -, hz⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (ι → Bool))
      Finset.univ_nonempty (fun z => (next z).height)
    obtain ⟨tr, a, h, hl⟩ := ih z
    refine ⟨_, a, .ask h, ?_⟩
    simp only [List.length_cons, height, hl, hz]

/-- A bound on the length of every branch bounds the height. -/
theorem height_le_of_trace (S : Strat ι α) (B : ℕ)
    (h : ∀ tr a, Trace S tr a → tr.length ≤ B) : S.height ≤ B := by
  obtain ⟨tr, a, ht, hl⟩ := exists_trace_height S
  exact hl ▸ h tr a ht

end Height

/-- Every queried point of `S` satisfies `P` and every result satisfies `Q`. -/
inductive Forall (P : (ι → ℝ) → Prop) (Q : α → Prop) : Strat ι α → Prop
  | done {a : α} (h : Q a) : Forall P Q (.done a)
  | ask {x : ι → ℝ} {next : (ι → Bool) → Strat ι α} (h : P x)
      (rest : ∀ z, Forall P Q (next z)) : Forall P Q (.ask x next)

theorem forall_done_iff {P : (ι → ℝ) → Prop} {Q : α → Prop} {a : α} :
    Forall P Q (.done a : Strat ι α) ↔ Q a :=
  ⟨fun h => by cases h; assumption, fun h => .done h⟩

theorem forall_ask_iff {P : (ι → ℝ) → Prop} {Q : α → Prop} {x : ι → ℝ}
    {next : (ι → Bool) → Strat ι α} :
    Forall P Q (.ask x next) ↔ P x ∧ ∀ z, Forall P Q (next z) :=
  ⟨fun h => by cases h with | ask h rest => exact ⟨h, rest⟩, fun h => .ask h.1 h.2⟩

/-- A property of the queries and of the result on every branch holds throughout the tree. -/
theorem forall_of_trace (P : (ι → ℝ) → Prop) (Q : α → Prop) (S : Strat ι α)
    (h : ∀ tr a, Trace S tr a → (∀ p ∈ tr, P p.1) ∧ Q a) : Forall P Q S := by
  induction S with
  | done a => exact .done (h [] a (.done a)).2
  | ask x next ih =>
    refine .ask ?_ (fun z => ih z (fun tr a ht => ?_))
    · obtain ⟨tr, a, ht⟩ := exists_trace (next (fun _ => false))
      exact (h _ a (.ask ht)).1 (x, fun _ => false) List.mem_cons_self
    · obtain ⟨h1, h2⟩ := h _ a (Trace.ask (x := x) ht)
      exact ⟨fun p hp => h1 p (List.mem_cons_of_mem _ hp), h2⟩

/-- A point with rational coordinates. -/
def IsRat (x : ι → ℝ) : Prop := ∀ i, ∃ q : ℚ, (q : ℝ) = x i

/-- Every queried point and every result of the strategy is rational in every coordinate. -/
def AllRational (S : Strat ι (ι → ℝ)) : Prop := S.Forall IsRat IsRat

end Strat

/-! ### The queries of a record -/

section Records

variable {ι : Type*} {E : Type*}

/-- The label queries of a record with their answers, in the order in which the algorithm
makes them: below each probe the queries of its child, then the query at the child's
prices. -/
def Exec.trace : Exec ι E → List ((ι → ℝ) × (ι → Bool))
  | .leaf _ _ => []
  | .node T _ z child _ _ =>
      (List.finRange T).flatMap (fun τ => (child τ).trace ++ [((child τ).x, z τ)])

theorem Exec.trace_length (X : Exec ι E) : X.trace.length = X.queries := by
  induction X with
  | leaf x wOut => rfl
  | node T y z child w x ih =>
    simp only [Exec.trace, Exec.queries, List.length_flatMap, List.length_append, ih,
      List.length_singleton, Fin.sum_univ_def]
    congr 1
    refine List.map_congr_left (fun τ _ => ?_)
    omega

/-- The returned prices are entries of the families whose medians they are (or `0`). -/
def Exec.MedSel : Exec ι E → ℕ → (ℕ → ι → ℝ) → Prop
  | .leaf x _, l, hist => ∀ i, x i = 0 ∨ ∃ j, j < l ∧ x i = hist j i
  | .node T y _ child _ x, l, hist =>
      (∀ i, x i = 0 ∨ ∃ τ : Fin T, x i = (child τ).x i) ∧
      ∀ τ : Fin T, (child τ).MedSel (l + 1) (Function.update hist l (y τ))

theorem Exec.consistent_of_trace {V : Type*} (val : V → ℝ) (H : Hyp ι V) (X : Exec ι E) :
    (∀ p ∈ X.trace, H.ConsistentAt val p.1 p.2) → X.Consistent val H := by
  induction X with
  | leaf x wOut => intro _; trivial
  | node T y z child w x ih =>
    intro h τ
    refine ⟨h ((child τ).x, z τ) ?_, ih τ (fun p hp => h p ?_)⟩
    · simp only [Exec.trace, List.mem_flatMap]
      exact ⟨τ, List.mem_finRange τ, by simp⟩
    · simp only [Exec.trace, List.mem_flatMap]
      exact ⟨τ, List.mem_finRange τ, by simp [hp]⟩

/-- The queries of the probes `0, …, n - 1` of a loop in progress. -/
def accTr (zs : ℕ → ι → Bool) (cs : ℕ → Exec ι E) (n : ℕ) : List ((ι → ℝ) × (ι → Bool)) :=
  (List.range n).flatMap (fun τ => (cs τ).trace ++ [((cs τ).x, zs τ)])

theorem accTr_eq_finRange (zs : ℕ → ι → Bool) (cs : ℕ → Exec ι E) (n : ℕ) :
    accTr zs cs n = (List.finRange n).flatMap
      (fun τ : Fin n => (cs τ).trace ++ [((cs τ).x, zs τ)]) := by
  unfold accTr
  rw [← List.map_coe_finRange_eq_range, List.flatMap_map]

theorem accTr_succ_update (zs : ℕ → ι → Bool) (cs : ℕ → Exec ι E) (n : ℕ) (z : ι → Bool)
    (c : Exec ι E) :
    accTr (Function.update zs n z) (Function.update cs n c) (n + 1)
      = accTr zs cs n ++ (c.trace ++ [(c.x, z)]) := by
  unfold accTr
  rw [List.range_succ, List.flatMap_append]
  congr 1
  · refine List.flatMap_congr (fun τ hτ => ?_)
    have hne : τ ≠ n := (List.mem_range.1 hτ).ne
    rw [Function.update_of_ne hne, Function.update_of_ne hne]
  · simp

end Records

/-! ### The program -/

section Program

variable {ι V : Type*} {k D : ℕ} [Fintype ι] [DecidableEq ι] [Fintype V]

/-- Some entry of a nonempty family is a weak median of it. -/
theorem exists_isMedian_entry {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) :
    ∃ j, IsMedian f (f j) := by
  obtain ⟨x, hx1, hx2⟩ := exists_isMedian f
  have hne : (univ.filter (fun j => f j ≤ x)).Nonempty := by
    rw [← Finset.card_pos]
    omega
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image _ f hne
  rw [Finset.mem_filter] at hj
  refine ⟨j, ?_, ?_⟩
  · refine hx1.trans (Nat.mul_le_mul_left 2 (Finset.card_le_card ?_))
    intro i hi
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hmax i hi⟩
  · refine hx2.trans (Nat.mul_le_mul_left 2 (Finset.card_le_card ?_))
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, hj.2.trans hi.2⟩

open Classical in
/-- The canonical median: an entry of the family that is a weak median (`0` for the empty
family). -/
noncomputable def medOf {n : ℕ} (f : Fin n → ℝ) : ℝ :=
  if h : ∃ j, IsMedian f (f j) then f (Classical.choose h) else 0

theorem medOf_isMedian {n : ℕ} (f : Fin n → ℝ) : IsMedian f (medOf f) := by
  unfold medOf
  split_ifs with h
  · exact Classical.choose_spec h
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · exact ⟨by omega, by omega⟩
    · exact absurd (exists_isMedian_entry hn f) h

theorem medOf_mem {n : ℕ} (f : Fin n → ℝ) : medOf f = 0 ∨ ∃ j, medOf f = f j := by
  unfold medOf
  split_ifs with h
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inl rfl

open Classical in
/-- The canonical proposal: a vertex minimizer of the market potential for the wealth `w`. -/
noncomputable def pickY (val : V → ℝ) (l : ℕ) (hist : ℕ → ι → ℝ)
    (w : Expert ι V k D → ℝ) : ι → ℝ :=
  if h : ∃ y : ι → ℝ, (∀ y', Phi val l hist w y ≤ Phi val l hist w y') ∧
      IsVertex (k := k) (D := D) val l hist y
  then Classical.choose h else 0

theorem pickY_spec [Nonempty V] (hk : 0 < k) (val : V → ℝ) (l : ℕ) (hist : ℕ → ι → ℝ)
    (w : Expert ι V k D → ℝ) (hw : ∀ e, 0 < w e) :
    (∀ y', Phi val l hist w (pickY val l hist w) ≤ Phi val l hist w y') ∧
      IsVertex (k := k) (D := D) val l hist (pickY val l hist w) := by
  unfold pickY
  rw [dif_pos (exists_vertex_min hk val l hist w hw)]
  exact Classical.choose_spec (exists_vertex_min hk val l hist w hw)

/-- The wealth after a probe with proposal `y`, child record `c` and labels `z`. -/
noncomputable def stepW (A : Alg V) (l : ℕ) (hist : ℕ → ι → ℝ) (w : Expert ι V k D → ℝ)
    (y : ι → ℝ) (c : Exec ι (Expert ι V k D)) (z : ι → Bool) : Expert ι V k D → ℝ :=
  fun e => A.rnd ((1 - A.c) * w e
    * (1 + A.η * gain A.val l hist y (feedback y c.x z) e) + c.wOut e)

/-- The probes of a node at level `l` with path `hist`. `loop … m n ys zs cs W` makes `m` more
probes after the `n` probes whose proposals, labels and child records are `ys`, `zs`, `cs`
(below `n`) and whose wealth sequence is `W` (up to `n`), and returns the record of the
node. -/
noncomputable def loop (A : Alg V) (l : ℕ) (hist : ℕ → ι → ℝ)
    (child : (ℕ → ι → ℝ) → (Expert ι V k D → ℝ) → Strat ι (Exec ι (Expert ι V k D))) :
    ℕ → ℕ → (ℕ → ι → ℝ) → (ℕ → ι → Bool) → (ℕ → Exec ι (Expert ι V k D)) →
      (ℕ → Expert ι V k D → ℝ) → Strat ι (Exec ι (Expert ι V k D))
  | 0, n, ys, zs, cs, W =>
      .done (.node n (fun τ => ys τ) (fun τ => zs τ) (fun τ => cs τ) W
        (fun i => medOf (fun τ : Fin n => (cs τ).x i)))
  | m + 1, n, ys, zs, cs, W =>
      (child (Function.update hist l (pickY A.val l hist (fun e => (1 - A.c) * W n e)))
          (fun e => A.c * W n e)).bind fun c =>
        .ask c.x fun z =>
          loop A l hist child m (n + 1)
            (Function.update ys n (pickY A.val l hist (fun e => (1 - A.c) * W n e)))
            (Function.update zs n z) (Function.update cs n c)
            (Function.update W (n + 1)
              (stepW A l hist (W n) (pickY A.val l hist (fun e => (1 - A.c) * W n e)) c z))

/-- **The price search as a program.** `prog A d l hist wIn` runs the node of level `l` with
path `hist` and input wealth `wIn`, with `d` levels below it, and returns its record. -/
noncomputable def prog (A : Alg V) :
    ℕ → ℕ → (ℕ → ι → ℝ) → (Expert ι V k D → ℝ) → Strat ι (Exec ι (Expert ι V k D))
  | 0, l, hist, wIn => .done (.leaf (fun i => medOf (fun j : Fin l => hist j i)) wIn)
  | d + 1, l, hist, wIn =>
      loop A l hist (prog A d (l + 1)) (if l = 0 then A.r₀ else A.r) 0
        (fun _ _ => 0) (fun _ _ => false) (fun _ => .leaf 0 0) (fun _ => wIn)

/-- A valid vertex run whose returned prices are entries of the families they summarize. -/
def Exec.Good (A : Alg V) (X : Exec ι (Expert ι V k D)) (l : ℕ) (hist : ℕ → ι → ℝ)
    (wIn : Expert ι V k D → ℝ) : Prop :=
  X.Valid A l hist wIn ∧ X.VertexRun A.val l hist ∧ X.MedSel l hist

theorem loop_spec [Nonempty V] (hk : 0 < k) (A : Alg V) (hc0 : 0 < A.c) (hc1 : A.c < 1)
    (hη0 : 0 < A.η) (hη1 : A.η < 1) {ep : ℝ} (hep1 : ep < 1)
    (hrnd : ∀ x : ℝ, 0 < x → (1 - ep) * x ≤ A.rnd x ∧ A.rnd x ≤ x)
    (l : ℕ) (hl : l < D) (hist : ℕ → ι → ℝ) (wIn : Expert ι V k D → ℝ)
    (child : (ℕ → ι → ℝ) → (Expert ι V k D → ℝ) → Strat ι (Exec ι (Expert ι V k D)))
    (hchild : ∀ hist' w' tr c, (∀ e, 0 < w' e) → (child hist' w').Trace tr c →
      c.Good A (l + 1) hist' w' ∧ tr = c.trace) :
    ∀ (m n : ℕ) (ys : ℕ → ι → ℝ) (zs : ℕ → ι → Bool) (cs : ℕ → Exec ι (Expert ι V k D))
      (W : ℕ → Expert ι V k D → ℝ) (tr : List ((ι → ℝ) × (ι → Bool)))
      (X : Exec ι (Expert ι V k D)),
      n + m = (if l = 0 then A.r₀ else A.r) → W 0 = wIn → (∀ e, 0 < W n e) →
      (∀ τ, τ < n →
        (∀ y', Phi A.val l hist (fun e => (1 - A.c) * W τ e) (ys τ)
            ≤ Phi A.val l hist (fun e => (1 - A.c) * W τ e) y') ∧
        IsVertex (k := k) (D := D) A.val l hist (ys τ) ∧
        (cs τ).Good A (l + 1) (Function.update hist l (ys τ)) (fun e => A.c * W τ e) ∧
        W (τ + 1) = stepW A l hist (W τ) (ys τ) (cs τ) (zs τ)) →
      (loop A l hist child m n ys zs cs W).Trace tr X →
      X.Good A l hist wIn ∧ accTr zs cs n ++ tr = X.trace := by
  intro m
  induction m with
  | zero =>
    intro n ys zs cs W tr X hn hW0 _ hpr ht
    rw [loop, Strat.trace_done_iff] at ht
    obtain ⟨rfl, rfl⟩ := ht
    refine ⟨⟨⟨hl, by simpa using hn, hW0, fun τ => ?_, fun i => medOf_isMedian _⟩,
      fun τ => ?_, fun i => medOf_mem _, fun τ => ?_⟩, ?_⟩
    · obtain ⟨h1, -, h3, h4⟩ := hpr τ τ.2
      exact ⟨h1, h3.1, fun e => by rw [h4]; rfl⟩
    · obtain ⟨-, h2, h3, -⟩ := hpr τ τ.2
      exact ⟨h2, h3.2.1⟩
    · exact (hpr τ τ.2).2.2.1.2.2
    · rw [List.append_nil, accTr_eq_finRange]
      rfl
  | succ m ih =>
    intro n ys zs cs W tr X hn hW0 hpos hpr ht
    rw [loop, Strat.trace_bind_iff] at ht
    obtain ⟨c, tr₁, tr₂, hc, ht2, rfl⟩ := ht
    obtain ⟨z, tr₃, rfl, hrest⟩ := Strat.trace_ask_iff.1 ht2
    set y := pickY A.val l hist (fun e => (1 - A.c) * W n e) with hy
    obtain ⟨hmin, hvert⟩ := pickY_spec (D := D) hk A.val l hist (fun e => (1 - A.c) * W n e)
      (fun e => mul_pos (by linarith) (hpos e))
    obtain ⟨hcg, rfl⟩ := hchild _ _ _ _ (fun e => mul_pos hc0 (hpos e)) hc
    have hnn : n ≠ n + 1 := by omega
    have key := ih (n + 1) (Function.update ys n y) (Function.update zs n z)
      (Function.update cs n c) (Function.update W (n + 1) (stepW A l hist (W n) y c z)) tr₃ X
      (by omega) (by rw [Function.update_of_ne (by omega)]; exact hW0) ?_ ?_ hrest
    · refine ⟨key.1, ?_⟩
      rw [← key.2, accTr_succ_update]
      simp
    · -- the wealth stays positive
      intro e
      rw [Function.update_self]
      have hcout := (Exec.wealth A hc0 hc1 hη0 hη1 hep1 hrnd c _ _ _ hcg.1
        (fun e => mul_pos hc0 (hpos e))).1 e
      have hg := (gain_bounds A.val l hist e y (feedback y c.x z)).1
      have h1 : 0 < 1 + A.η * gain A.val l hist y (feedback y c.x z) e := by nlinarith
      have hX := add_pos (mul_pos (mul_pos (by linarith : 0 < 1 - A.c) (hpos e)) h1) hcout
      exact lt_of_lt_of_le (mul_pos (by linarith) hX) (hrnd _ hX).1
    · intro τ hτ
      rcases Nat.lt_succ_iff_lt_or_eq.1 hτ with hlt | rfl
      · have h1 : τ ≠ n := hlt.ne
        have h2 : τ ≠ n + 1 := by omega
        have h3 : τ + 1 ≠ n + 1 := by omega
        rw [Function.update_of_ne h1, Function.update_of_ne h1, Function.update_of_ne h1,
          Function.update_of_ne h2, Function.update_of_ne h3]
        exact hpr τ hlt
      · rw [Function.update_self, Function.update_self, Function.update_self,
          Function.update_self, Function.update_of_ne hnn]
        exact ⟨hmin, hvert, hcg, rfl⟩

/-- **The program follows the algorithm.** On every branch the returned record is a valid
vertex run, and the queries and answers of the branch are those of the record. -/
theorem prog_spec [Nonempty V] (hk : 0 < k) (A : Alg V) (hc0 : 0 < A.c) (hc1 : A.c < 1)
    (hη0 : 0 < A.η) (hη1 : A.η < 1) {ep : ℝ} (hep1 : ep < 1)
    (hrnd : ∀ x : ℝ, 0 < x → (1 - ep) * x ≤ A.rnd x ∧ A.rnd x ≤ x) :
    ∀ (d l : ℕ), l + d = D → ∀ (hist : ℕ → ι → ℝ) (wIn : Expert ι V k D → ℝ)
      (tr : List ((ι → ℝ) × (ι → Bool))) (X : Exec ι (Expert ι V k D)),
      (∀ e, 0 < wIn e) → (prog A d l hist wIn).Trace tr X →
      X.Good A l hist wIn ∧ tr = X.trace := by
  intro d
  induction d with
  | zero =>
    intro l hl hist wIn tr X _ ht
    rw [prog, Strat.trace_done_iff] at ht
    obtain ⟨rfl, rfl⟩ := ht
    refine ⟨⟨⟨by omega, rfl, fun i => medOf_isMedian _⟩, trivial, fun i => ?_⟩, rfl⟩
    rcases medOf_mem (fun j : Fin l => hist j i) with h | ⟨j, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨j, j.2, h⟩
  | succ d ih =>
    intro l hl hist wIn tr X hpos ht
    rw [prog] at ht
    have key := loop_spec hk A hc0 hc1 hη0 hη1 hep1 hrnd l (by omega) hist wIn
      (prog A d (l + 1))
      (fun hist' w' tr c hw hc => ih (l + 1) (by omega) hist' w' tr c hw hc)
      _ 0 _ _ _ _ tr X (by simp) rfl hpos (fun τ hτ => absurd hτ (Nat.not_lt_zero τ)) ht
    refine ⟨key.1, ?_⟩
    rw [← key.2]
    simp [accTr]

/-- In a vertex run with integer demands whose returned prices are entries of their families,
every queried point and the returned prices are half-integral. -/
theorem Exec.halfInt_of_medSel (val : V → ℝ) (hint : ∀ v, ∃ z : ℤ, val v = z)
    (X : Exec ι (Expert ι V k D)) :
    ∀ (l : ℕ) (hist : ℕ → ι → ℝ), X.VertexRun val l hist → X.MedSel l hist →
      (∀ j, j < l → ∀ i, ∃ z : ℤ, 2 * hist j i = z) →
      (∀ i, ∃ z : ℤ, 2 * X.x i = z) ∧ ∀ p ∈ X.trace, ∀ i, ∃ z : ℤ, 2 * p.1 i = z := by
  induction X with
  | leaf x wOut =>
    intro l hist _ hm hh
    refine ⟨fun i => ?_, fun p hp => absurd hp (by simp [Exec.trace])⟩
    rcases hm i with h | ⟨j, hj, h⟩
    · exact ⟨0, by simp [Exec.x, h]⟩
    · simp only [Exec.x]
      rw [h]
      exact hh j hj i
  | node T y z child w x ih =>
    intro l hist hv hm hh
    have hchild : ∀ τ, (∀ i, ∃ n : ℤ, 2 * (child τ).x i = n) ∧
        ∀ p ∈ (child τ).trace, ∀ i, ∃ n : ℤ, 2 * p.1 i = n := by
      intro τ
      have hy := halfInt_of_vertex val l hist (y τ) hint hh (hv τ).1
      refine ih τ (l + 1) _ (hv τ).2 (hm.2 τ) ?_
      intro j hj i
      by_cases hjl : j = l
      · subst hjl
        rw [Function.update_self]
        exact hy i
      · rw [Function.update_of_ne hjl]
        exact hh j (by omega) i
    refine ⟨fun i => ?_, ?_⟩
    · rcases hm.1 i with h | ⟨τ, h⟩
      · exact ⟨0, by simp [Exec.x, h]⟩
      · simp only [Exec.x]
        rw [h]
        exact (hchild τ).1 i
    · intro p hp
      simp only [Exec.trace, List.mem_flatMap, List.mem_append, List.mem_singleton] at hp
      obtain ⟨τ, -, hp | rfl⟩ := hp
      · exact (hchild τ).2 p hp
      · exact (hchild τ).1

/-! ### The strategy -/

/-- The price search from the root with unit wealth, returning the record of its run. -/
noncomputable def searchExec (A : Alg V) (hist₀ : ℕ → ι → ℝ) :
    Strat ι (Exec ι (Expert ι V k D)) :=
  prog A D 0 hist₀ (fun _ => 1)

/-- The price search as a strategy returning prices. -/
noncomputable def search (k D : ℕ) (A : Alg V) (hist₀ : ℕ → ι → ℝ) : Strat ι (ι → ℝ) :=
  (searchExec (k := k) (D := D) A hist₀).map Exec.x

section Spec

variable [Nonempty V] (hk : 0 < k) (A : Alg V) (hc0 : 0 < A.c) (hc1 : A.c < 1)
  (hη0 : 0 < A.η) (hη1 : A.η < 1) {ep : ℝ} (hep1 : ep < 1)
  (hrnd : ∀ x : ℝ, 0 < x → (1 - ep) * x ≤ A.rnd x ∧ A.rnd x ≤ x) (hist₀ : ℕ → ι → ℝ)

include hk hc0 hc1 hη0 hη1 hep1 hrnd

/-- On every branch the record is a valid vertex run and the branch lists its queries. -/
theorem searchExec_trace {tr : List ((ι → ℝ) × (ι → Bool))} {X : Exec ι (Expert ι V k D)}
    (h : (searchExec A hist₀).Trace tr X) :
    X.Valid A 0 hist₀ (fun _ => 1) ∧ X.VertexRun A.val 0 hist₀ ∧ X.MedSel 0 hist₀ ∧
      tr = X.trace := by
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := prog_spec hk A hc0 hc1 hη0 hη1 hep1 hrnd D 0 (by omega) hist₀
    (fun _ => 1) tr X (fun _ => one_pos) h
  exact ⟨h1, h2, h3, h4⟩

/-- **(A1) Validity.** Whatever the answers, the program returns a valid run. -/
theorem searchExec_valid {X : Exec ι (Expert ι V k D)}
    (h : (searchExec A hist₀).Reaches (fun _ _ => True) X) :
    X.Valid A 0 hist₀ (fun _ => 1) := by
  obtain ⟨tr, ht, -⟩ := Strat.reaches_iff_trace.1 h
  exact (searchExec_trace hk A hc0 hc1 hη0 hη1 hep1 hrnd hist₀ ht).1

/-- **(A1) Queries.** The number of queries on a branch is the number of label queries of the
record it returns. -/
theorem searchExec_queries {tr : List ((ι → ℝ) × (ι → Bool))}
    {X : Exec ι (Expert ι V k D)} (h : (searchExec A hist₀).Trace tr X) :
    tr.length = X.queries := by
  rw [(searchExec_trace hk A hc0 hc1 hη0 hη1 hep1 hrnd hist₀ h).2.2.2, Exec.trace_length]

/-- **(A1) Height.** A bound on the label queries of all valid runs bounds the height. -/
theorem search_height_le (B : ℕ)
    (hB : ∀ X : Exec ι (Expert ι V k D), X.Valid A 0 hist₀ (fun _ => 1) → X.queries ≤ B) :
    (search k D A hist₀).height ≤ B := by
  refine Strat.height_le_of_trace _ B (fun tr x ht => ?_)
  obtain ⟨X, hX, -⟩ := (Strat.trace_map_iff _ _ _ _).1 ht
  rw [searchExec_queries hk A hc0 hc1 hη0 hη1 hep1 hrnd hist₀ hX]
  exact hB X (searchExec_trace hk A hc0 hc1 hη0 hη1 hep1 hrnd hist₀ hX).1

/-- **(A2) Consistency.** If the answers on a branch agree with a hypothesis, the hypothesis
is consistent with the record. -/
theorem searchExec_consistent (H : Hyp ι V) {X : Exec ι (Expert ι V k D)}
    (h : (searchExec A hist₀).Reaches (fun p z => H.ConsistentAt A.val p z) X) :
    X.Valid A 0 hist₀ (fun _ => 1) ∧ X.Consistent A.val H := by
  obtain ⟨tr, ht, hok⟩ := Strat.reaches_iff_trace.1 h
  obtain ⟨h1, -, -, rfl⟩ := searchExec_trace hk A hc0 hc1 hη0 hη1 hep1 hrnd hist₀ ht
  exact ⟨h1, Exec.consistent_of_trace A.val H X hok⟩

/-- A branch of `search` comes from a branch of `searchExec`. -/
theorem search_reaches {ok : (ι → ℝ) → (ι → Bool) → Prop} {x : ι → ℝ}
    (h : (search k D A hist₀).Reaches ok x) :
    ∃ X : Exec ι (Expert ι V k D), (searchExec A hist₀).Reaches ok X ∧ x = X.x := by
  obtain ⟨tr, ht, hok⟩ := Strat.reaches_iff_trace.1 h
  obtain ⟨X, hX, rfl⟩ := (Strat.trace_map_iff _ _ _ _).1 ht
  exact ⟨X, Strat.reaches_iff_trace.2 ⟨tr, hX, hok⟩, rfl⟩

/-- **(A3) Half-integrality.** With integer demands every queried point and every result of
the strategy is half-integral. -/
theorem search_halfInt (hint : ∀ v, ∃ n : ℤ, A.val v = n) :
    (search k D A hist₀).Forall (fun x => ∀ i, ∃ n : ℤ, 2 * x i = (n : ℝ))
      (fun x => ∀ i, ∃ n : ℤ, 2 * x i = (n : ℝ)) := by
  refine Strat.forall_of_trace _ _ _ (fun tr x ht => ?_)
  obtain ⟨X, hX, rfl⟩ := (Strat.trace_map_iff _ _ _ _).1 ht
  obtain ⟨-, h2, h3, rfl⟩ := searchExec_trace hk A hc0 hc1 hη0 hη1 hep1 hrnd hist₀ hX
  obtain ⟨hx, hq⟩ := X.halfInt_of_medSel A.val hint 0 hist₀ h2 h3
    (fun j hj => absurd hj (Nat.not_lt_zero j))
  exact ⟨hq, hx⟩

end Spec

theorem Strat.Forall.mono {α : Type*} {P P' : (ι → ℝ) → Prop} {Q Q' : α → Prop}
    (hP : ∀ x, P x → P' x) (hQ : ∀ a, Q a → Q' a) {S : Strat ι α} (h : S.Forall P Q) :
    S.Forall P' Q' := by
  induction h with
  | done h => exact .done (hQ _ h)
  | ask h _ ih => exact .ask (hP _ h) ih

theorem isRat_of_halfInt {x : ι → ℝ} (h : ∀ i, ∃ n : ℤ, 2 * x i = n) : Strat.IsRat x := by
  intro i
  obtain ⟨n, hn⟩ := h i
  refine ⟨(n : ℚ) / 2, ?_⟩
  push_cast
  linarith

end Program

/-! ### Arity 4 -/

section K4

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V] [Nonempty ι] [Nonempty V]

/-- The arity-4 price search as a strategy, started with the zero history. -/
noncomputable def strategyK4 (val : V → ℝ) : Strat ι (ι → ℝ) :=
  search 4 (K4.depth K4_good (Fintype.card ι)) (K4.alg K4_good ι V val) (fun _ _ => 0)

/-- Height of the arity-4 strategy: at most `2 r₀ (2N)^46` queries on every branch. -/
theorem strategyK4_height (val : V → ℝ) :
    (strategyK4 (ι := ι) val).height
      ≤ 2 * K4.r₀ ι V (K4.depth K4_good (Fintype.card ι)) * (2 * Fintype.card ι) ^ 46 :=
  search_height_le (by norm_num) _ (K4.params K4_good ι V val).hc0
    (K4.params K4_good ι V val).hc1 (K4.params K4_good ι V val).hη0
    (K4.params K4_good ι V val).hη1 (K4.params K4_good ι V val).hep1
    (K4.params K4_good ι V val).hrnd _ _
    (fun X hX => (price_search_k4 val X _ hX).2)

/-- Correctness of the arity-4 strategy: on a branch whose answers agree with `H`, the result
meets every demand of `H`. -/
theorem strategyK4_correct (val : V → ℝ) (H : Hyp ι V) (x : ι → ℝ)
    (h : (strategyK4 (ι := ι) val).Reaches (fun p z => H.ConsistentAt val p z) x) :
    ∀ s ∈ H.S, val (H.a s) ≤ sp x s := by
  obtain ⟨X, hX, rfl⟩ := search_reaches (by norm_num) _ (K4.params K4_good ι V val).hc0
    (K4.params K4_good ι V val).hc1 (K4.params K4_good ι V val).hη0
    (K4.params K4_good ι V val).hη1 (K4.params K4_good ι V val).hep1
    (K4.params K4_good ι V val).hrnd _ h
  obtain ⟨hv, hc⟩ := searchExec_consistent (by norm_num) (K4.alg K4_good ι V val)
    (K4.params K4_good ι V val).hc0
    (K4.params K4_good ι V val).hc1 (K4.params K4_good ι V val).hη0
    (K4.params K4_good ι V val).hη1 (K4.params K4_good ι V val).hep1
    (K4.params K4_good ι V val).hrnd _ H hX
  exact (price_search_k4 val X _ hv).1 H hc

/-- Rationality of the arity-4 strategy for integer demands. -/
theorem strategyK4_allRational (val : V → ℝ) (hint : ∀ v, ∃ n : ℤ, val v = n) :
    (strategyK4 (ι := ι) val).AllRational :=
  Strat.Forall.mono (fun _ => isRat_of_halfInt) (fun _ => isRat_of_halfInt)
    (search_halfInt (k := 4) (by norm_num) (K4.alg K4_good ι V val) (K4.params K4_good ι V val).hc0
      (K4.params K4_good ι V val).hc1 (K4.params K4_good ι V val).hη0
      (K4.params K4_good ι V val).hη1 (K4.params K4_good ι V val).hep1
      (K4.params K4_good ι V val).hrnd _ hint)

/-- **The price search as one adaptive strategy (arity 4).** For integer demands there is a
decision tree that asks at most `2 r₀ (2N)^46` label vectors on every branch, queries and
returns only rational points, and whose result meets every demand of every hypothesis
consistent with the answers on its branch. -/
theorem exists_strategy_k4 (val : V → ℝ) (hint : ∀ v, ∃ n : ℤ, val v = n) :
    ∃ S : Strat ι (ι → ℝ),
      S.height ≤ 2 * K4.r₀ ι V (K4.depth K4_good (Fintype.card ι))
        * (2 * Fintype.card ι) ^ 46 ∧
      S.AllRational ∧
      ∀ H : Hyp ι V, ∀ x, S.Reaches (fun p z => H.ConsistentAt val p z) x →
        ∀ s ∈ H.S, val (H.a s) ≤ sp x s :=
  ⟨strategyK4 val, strategyK4_height val, strategyK4_allRational val hint,
    fun H x h => strategyK4_correct val H x h⟩

end K4

end SPLP
