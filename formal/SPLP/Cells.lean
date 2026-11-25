import Mathlib
import SPLP.Main
import SPLP.Arrangement

/-!
# Cells of experts

The market step never has to look at experts one by one. Two experts of the same *group*
(same slots, same threshold description up to the guessed demands) that order their options in
the same way at every probe made so far have the same wealth. This file makes that precise:

* `Exec.contexts`: the probes of a run, in the order in which they are completed;
* `Agree`: two experts of the same group order their options alike at each of a list of probes;
* `Exec.wealth_agree`: at every probe of a valid run, wealth is constant on the classes of
  `Agree` for the probes completed before it;
* `exists_types`: those classes number at most `|groups| · faceBound (pairs · t) k` after `t`
  probes, where `faceBound n k = ∑_{i ≤ k} 2^i (n choose i) ≤ (2n+1)^k`.
-/

set_option linter.unusedSectionVars false

namespace SPLP

open Finset

variable {ι V : Type*} {k D : ℕ}

/-! ### Probes of a run -/

/-- What an expert sees at a probe: the level, the proposals on the path, and the proposal. -/
structure Ctx (ι : Type*) where
  l : ℕ
  hist : ℕ → ι → ℝ
  y : ι → ℝ

/-- The probes completed before the `n`-th probe of a node, given the list `segs τ` of probes
completed during the `τ`-th probe. -/
def before {T : ℕ} (segs : Fin T → List (Ctx ι)) : ℕ → List (Ctx ι)
  | 0 => []
  | n + 1 => before segs n ++ (if h : n < T then segs ⟨n, h⟩ else [])

theorem before_succ {T : ℕ} (segs : Fin T → List (Ctx ι)) (τ : Fin T) :
    before segs (τ + 1) = before segs τ ++ segs τ := by
  simp [before]

theorem before_subset {T : ℕ} (segs : Fin T → List (Ctx ι)) {n n' : ℕ} (h : n ≤ n') :
    ∀ c ∈ before segs n, c ∈ before segs n' := by
  induction n' with
  | zero =>
    have : n = 0 := Nat.le_zero.1 h
    subst this
    exact fun c hc => hc
  | succ m ih =>
    rcases Nat.lt_or_ge n (m + 1) with hlt | hge
    · intro c hc
      simp only [before, List.mem_append]
      exact Or.inl (ih (Nat.lt_succ_iff.1 hlt) c hc)
    · have : n = m + 1 := le_antisymm h hge
      subst this
      exact fun c hc => hc

theorem length_before_le {T : ℕ} (segs : Fin T → List (Ctx ι)) {n n' : ℕ} (h : n ≤ n') :
    (before segs n).length ≤ (before segs n').length := by
  induction n' with
  | zero =>
    have : n = 0 := Nat.le_zero.1 h
    subst this
    exact le_rfl
  | succ m ih =>
    rcases Nat.lt_or_ge n (m + 1) with hlt | hge
    · simp only [before, List.length_append]
      exact (ih (Nat.lt_succ_iff.1 hlt)).trans (Nat.le_add_right _ _)
    · have : n = m + 1 := le_antisymm h hge
      subst this
      exact le_rfl

/-- The probes of a run in the order in which they are completed: each probe is followed by
the probes of its child. -/
def Exec.contexts {E : Type*} : Exec ι E → ℕ → (ℕ → ι → ℝ) → List (Ctx ι)
  | .leaf _ _, _, _ => []
  | .node T y _ child _ _, l, hist =>
      before (fun τ : Fin T => (⟨l, hist, y τ⟩ : Ctx ι)
        :: (child τ).contexts (l + 1) (Function.update hist l (y τ))) T

/-- The probes completed during each probe of a node. -/
def nodeSegs {E : Type*} (T : ℕ) (y : Fin T → ι → ℝ) (child : Fin T → Exec ι E) (l : ℕ)
    (hist : ℕ → ι → ℝ) : Fin T → List (Ctx ι) :=
  fun τ => (⟨l, hist, y τ⟩ : Ctx ι) :: (child τ).contexts (l + 1) (Function.update hist l (y τ))

theorem Exec.contexts_node {E : Type*} (T : ℕ) (y : Fin T → ι → ℝ) (z : Fin T → ι → Bool)
    (child : Fin T → Exec ι E) (w : ℕ → E → ℝ) (x : ι → ℝ) (l : ℕ) (hist : ℕ → ι → ℝ) :
    (Exec.node T y z child w x).contexts l hist = before (nodeSegs T y child l hist) T := rfl

/-- `X.ForallProbes P l hist pre`: the property `P` holds at every probe of the run `X`, where
`P` receives the list of probes completed before it (starting from `pre`), the level, the path,
the proposal and the wealth before the probe. -/
def Exec.ForallProbes {E : Type*}
    (P : List (Ctx ι) → ℕ → (ℕ → ι → ℝ) → (ι → ℝ) → (E → ℝ) → Prop) :
    Exec ι E → ℕ → (ℕ → ι → ℝ) → List (Ctx ι) → Prop
  | .leaf _ _, _, _, _ => True
  | .node T y _ child w _, l, hist, pre =>
      ∀ τ : Fin T,
        P (pre ++ before (nodeSegs T y child l hist) τ) l hist (y τ) (w τ) ∧
        (child τ).ForallProbes P (l + 1) (Function.update hist l (y τ))
          (pre ++ before (nodeSegs T y child l hist) τ)

theorem Exec.ForallProbes.mono {E : Type*}
    {P Q : List (Ctx ι) → ℕ → (ℕ → ι → ℝ) → (ι → ℝ) → (E → ℝ) → Prop}
    (hPQ : ∀ pre l hist y w, P pre l hist y w → Q pre l hist y w) (X : Exec ι E) :
    ∀ l hist pre, X.ForallProbes P l hist pre → X.ForallProbes Q l hist pre := by
  induction X with
  | leaf x wOut => intro _ _ _ _; trivial
  | node T y z child w x ih =>
    intro l hist pre h τ
    exact ⟨hPQ _ _ _ _ _ (h τ).1, ih τ _ _ _ (h τ).2⟩

theorem Exec.ForallProbes.and {E : Type*}
    {P Q : List (Ctx ι) → ℕ → (ℕ → ι → ℝ) → (ι → ℝ) → (E → ℝ) → Prop} (X : Exec ι E) :
    ∀ l hist pre, X.ForallProbes P l hist pre → X.ForallProbes Q l hist pre →
      X.ForallProbes (fun pre l hist y w => P pre l hist y w ∧ Q pre l hist y w) l hist pre := by
  induction X with
  | leaf x wOut => intro _ _ _ _ _; trivial
  | node T y z child w x ih =>
    intro l hist pre h1 h2 τ
    exact ⟨⟨(h1 τ).1, (h2 τ).1⟩, ih τ _ _ _ (h1 τ).2 (h2 τ).2⟩

/-- The number of completed probes equals the number of label queries. -/
theorem Exec.length_contexts {E : Type*} (X : Exec ι E) :
    ∀ l hist, (X.contexts l hist).length = X.queries := by
  induction X with
  | leaf x wOut => intro _ _; rfl
  | node T y z child w x ih =>
    intro l hist
    rw [Exec.contexts_node]
    have key : ∀ n (hn : n ≤ T), (before (nodeSegs T y child l hist) n).length
        = ∑ τ : Fin T, if (τ : ℕ) < n then (1 + (child τ).queries) else 0 := by
      intro n
      induction n with
      | zero => intro _; simp [before]
      | succ n ihn =>
        intro hn
        have hn' : n < T := hn
        simp only [before, List.length_append, dif_pos hn', ihn (Nat.le_of_lt hn')]
        have hseg : (nodeSegs T y child l hist ⟨n, hn'⟩).length
            = 1 + (child ⟨n, hn'⟩).queries := by
          simp [nodeSegs, ih, Nat.add_comm]
        rw [hseg]
        have hsplit : ∀ τ : Fin T, (if (τ : ℕ) < n + 1 then (1 + (child τ).queries) else 0)
            = (if (τ : ℕ) < n then (1 + (child τ).queries) else 0)
              + (if τ = ⟨n, hn'⟩ then (1 + (child τ).queries) else 0) := by
          intro τ
          by_cases h1 : (τ : ℕ) < n
          · have h2 : τ ≠ ⟨n, hn'⟩ := fun h => by rw [h] at h1; exact lt_irrefl _ h1
            simp [h1, h2, Nat.lt_succ_of_lt h1]
          · by_cases h2 : τ = ⟨n, hn'⟩
            · subst h2; simp
            · have h3 : ¬ (τ : ℕ) < n + 1 := by
                intro h
                apply h2
                apply Fin.ext
                have : (τ : ℕ) = n := by omega
                exact this
              simp [h1, h2, h3]
        rw [Finset.sum_congr rfl (fun τ _ => hsplit τ), Finset.sum_add_distrib]
        simp
    rw [key T le_rfl]
    simp [Exec.queries]


/-! ### Experts that behave alike -/

variable [Fintype ι] [DecidableEq ι]

/-- Same group: same slots, same pivot level and pivot slot. Only the guessed demands may
differ. -/
def SameGroup (e e' : Expert ι V k D) : Prop :=
  e.1 = e'.1 ∧ e.2.2.map (fun t => (t.1, t.2.1)) = e'.2.2.map (fun t => (t.1, t.2.1))

/-- The two experts order their options in the same way at the probe `c`. -/
def SameOrder (val : V → ℝ) (c : Ctx ι) (e e' : Expert ι V k D) : Prop :=
  ∀ o o' : Option (Fin k),
    util (bidOf val c.l c.hist) (dirOf val c.l c.hist) e o c.y
        ≤ util (bidOf val c.l c.hist) (dirOf val c.l c.hist) e o' c.y ↔
      util (bidOf val c.l c.hist) (dirOf val c.l c.hist) e' o c.y
        ≤ util (bidOf val c.l c.hist) (dirOf val c.l c.hist) e' o' c.y

/-- Same group and same order of options at every probe of the list. -/
def Agree (val : V → ℝ) (cs : List (Ctx ι)) (e e' : Expert ι V k D) : Prop :=
  SameGroup e e' ∧ ∀ c ∈ cs, SameOrder val c e e'

theorem Agree.mono {val : V → ℝ} {cs cs' : List (Ctx ι)} {e e' : Expert ι V k D}
    (h : Agree val cs e e') (hsub : ∀ c ∈ cs', c ∈ cs) : Agree val cs' e e' :=
  ⟨h.1, fun c hc => h.2 c (hsub c hc)⟩

theorem util_eq_best_iff {E O : Type*} [Fintype O] [Nonempty O] (b : E → O → ℝ)
    (u : E → O → ι → ℝ) (e : E) (o : O) (y : ι → ℝ) :
    util b u e o y = best b u e y ↔ ∀ o', util b u e o' y ≤ util b u e o y := by
  constructor
  · intro h o'
    rw [h]
    exact util_le_best b u e o' y
  · intro h
    apply le_antisymm (util_le_best b u e o y)
    exact Finset.sup'_le _ _ (fun o' _ => h o')

/-- Experts of the same group have the same price directions: these depend on the slots and
on whether the expert bids at this level, not on the guessed demands. -/
theorem dirOf_congr (val : V → ℝ) (l : ℕ) (hist : ℕ → ι → ℝ) {e e' : Expert ι V k D}
    (h : SameGroup e e') : dirOf val l hist e = dirOf val l hist e' := by
  obtain ⟨s, b, d⟩ := e
  obtain ⟨s', b', d'⟩ := e'
  obtain ⟨h1, h2⟩ := h
  simp only at h1 h2
  subst h1
  funext o
  cases o with
  | none => rfl
  | some q =>
    cases d with
    | none =>
      cases d' with
      | none => simp [dirOf, thr]
      | some t' => simp at h2
    | some t =>
      cases d' with
      | none => simp at h2
      | some t' =>
        obtain ⟨j, p, v⟩ := t
        obtain ⟨j', p', v'⟩ := t'
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
        obtain ⟨rfl, rfl⟩ := h2
        by_cases hj : (j : ℕ) < l
        · simp [dirOf, thr, hj]
        · simp [dirOf, thr, hj]

/-- Experts of the same group with the same order of options at a probe have the same
maximizing options there. -/
theorem argmax_congr {val : V → ℝ} {l : ℕ} {hist : ℕ → ι → ℝ} {y : ι → ℝ}
    {e e' : Expert ι V k D} (ho : SameOrder val ⟨l, hist, y⟩ e e') (o : Option (Fin k)) :
    util (bidOf val l hist) (dirOf val l hist) e o y
        = best (bidOf val l hist) (dirOf val l hist) e y ↔
      util (bidOf val l hist) (dirOf val l hist) e' o y
        = best (bidOf val l hist) (dirOf val l hist) e' y := by
  rw [util_eq_best_iff, util_eq_best_iff]
  constructor
  · intro h o'
    exact (ho o' o).1 (h o')
  · intro h o'
    exact (ho o' o).2 (h o')

/-- ... and therefore the same gain, whatever the feedback. -/
theorem gain_congr {val : V → ℝ} {l : ℕ} {hist : ℕ → ι → ℝ} {y : ι → ℝ}
    {e e' : Expert ι V k D} (hg : SameGroup e e') (ho : SameOrder val ⟨l, hist, y⟩ e e')
    (v : ι → Bool) : gain val l hist y v e = gain val l hist y v e' := by
  have hdir := dirOf_congr val l hist hg
  have hpay : ∀ o, pay (dirOf val l hist) e o (vreal v) = pay (dirOf val l hist) e' o (vreal v) := by
    intro o
    simp only [pay, hdir]
  unfold gain
  apply le_antisymm
  · refine le_minPay _ _ _ _ _ _ (fun o ho' => ?_)
    rw [← hpay o]
    exact minPay_le _ _ _ _ _ o ((argmax_congr ho o).2 ho')
  · refine le_minPay _ _ _ _ _ _ (fun o ho' => ?_)
    rw [hpay o]
    exact minPay_le _ _ _ _ _ o ((argmax_congr ho o).1 ho')

/-! ### Wealth is constant on cells -/

variable [Fintype V]

/-- **Wealth factors through cells.** In a valid run entered with wealth that is constant on
the classes of `Agree` for the probes `pre` completed so far, the wealth before every probe is
constant on the classes of `Agree` for the probes completed before that probe, and the
returned wealth is constant on the classes for all probes of the run. -/
theorem Exec.wealth_agree (A : Alg V) (X : Exec ι (Expert ι V k D)) :
    ∀ (l : ℕ) (hist : ℕ → ι → ℝ) (wIn : Expert ι V k D → ℝ) (pre : List (Ctx ι)),
      X.Valid A l hist wIn →
      (∀ e e', Agree A.val pre e e' → wIn e = wIn e') →
      X.ForallProbes (fun pre' _ _ _ w => ∀ e e', Agree A.val pre' e e' → w e = w e')
          l hist pre ∧
        (∀ e e', Agree A.val (pre ++ X.contexts l hist) e e' → X.wOut e = X.wOut e') := by
  induction X with
  | leaf x wOut =>
    intro l hist wIn pre hv hin
    obtain ⟨-, hw, -⟩ := hv
    refine ⟨trivial, fun e e' h => ?_⟩
    simp only [Exec.contexts, List.append_nil] at h
    simp only [Exec.wOut, hw]
    exact hin e e' h
  | node T y z child w x ih =>
    intro l hist wIn pre hv hin
    obtain ⟨-, -, hw0, hprobe, -⟩ := hv
    -- wealth before the `n`-th probe
    have key : ∀ n, n ≤ T → ∀ e e',
        Agree A.val (pre ++ before (nodeSegs T y child l hist) n) e e' → w n e = w n e' := by
      intro n
      induction n with
      | zero =>
        intro _ e e' h
        rw [hw0]
        exact hin e e' (h.mono (fun c hc => by simp [before, hc]))
      | succ n ihn =>
        intro hn e e' h
        have hn' : n < T := hn
        obtain ⟨-, hchild, hstep⟩ := hprobe ⟨n, hn'⟩
        have hbs := before_succ (nodeSegs T y child l hist) ⟨n, hn'⟩
        simp only at hbs
        rw [hbs] at h
        -- agreement on the earlier probes
        have h1 : Agree A.val (pre ++ before (nodeSegs T y child l hist) n) e e' :=
          h.mono (fun c hc => by
            rcases List.mem_append.1 hc with hc | hc
            · exact List.mem_append.2 (Or.inl hc)
            · exact List.mem_append.2 (Or.inr (List.mem_append.2 (Or.inl hc))))
        have hwn := ihn (Nat.le_of_lt hn') e e' h1
        -- agreement at this probe
        have h2 : SameOrder A.val ⟨l, hist, y ⟨n, hn'⟩⟩ e e' :=
          h.2 _ (List.mem_append.2 (Or.inr (List.mem_append.2 (Or.inr (by simp [nodeSegs])))))
        have hgain := gain_congr h.1 h2
          (feedback (y ⟨n, hn'⟩) (child ⟨n, hn'⟩).x (z ⟨n, hn'⟩))
        -- agreement inside the child
        have hcin : ∀ e e', Agree A.val (pre ++ before (nodeSegs T y child l hist) n) e e' →
            A.c * w n e = A.c * w n e' := fun e e' h => by
          rw [ihn (Nat.le_of_lt hn') e e' h]
        have hcout := (ih ⟨n, hn'⟩ (l + 1) _ _ _ hchild hcin).2 e e'
          (h.mono (fun c hc => by
            rcases List.mem_append.1 hc with hc | hc
            · rcases List.mem_append.1 hc with hc | hc
              · exact List.mem_append.2 (Or.inl hc)
              · exact List.mem_append.2 (Or.inr (List.mem_append.2 (Or.inl hc)))
            · exact List.mem_append.2 (Or.inr (List.mem_append.2 (Or.inr (by
                simp only [nodeSegs, List.mem_cons]
                exact Or.inr hc))))))
        have hs := hstep e
        have hs' := hstep e'
        simp only at hs hs'
        rw [hs, hs', hwn, hgain, hcout]
    refine ⟨fun τ => ⟨key τ (Nat.le_of_lt τ.2), ?_⟩, ?_⟩
    · exact (ih τ (l + 1) _ _ _ (hprobe τ).2.1 (fun e e' h => by
        rw [key τ (Nat.le_of_lt τ.2) e e' h])).1
    · intro e e' h
      rw [Exec.contexts_node] at h
      exact key T le_rfl e e' h


/-! ### Counting cells -/

/-- A group of experts: the slots, and the pivot level and pivot slot if any. -/
abbrev GroupKey (ι : Type*) (k D : ℕ) := (Fin k → Slot ι) × Option (Fin D × Slot ι)

/-- The group of an expert. -/
def groupKey (e : Expert ι V k D) : GroupKey ι k D :=
  (e.1, e.2.2.map (fun t => (t.1, t.2.1)))

theorem sameGroup_iff (e e' : Expert ι V k D) : SameGroup e e' ↔ groupKey e = groupKey e' := by
  simp [SameGroup, groupKey, Prod.ext_iff]

/-- Number of groups. -/
theorem card_groupKey (ι : Type*) [Fintype ι] [DecidableEq ι] (k D : ℕ) :
    Fintype.card (GroupKey ι k D)
      = (2 * Fintype.card ι) ^ k * (D * (2 * Fintype.card ι) + 1) := by
  simp [GroupKey, Slot, Fintype.card_prod, Fintype.card_option, mul_comm]

/-- The guessed demands of an expert relative to its guessed pivot demand: the only data by
which experts of one group differ, as a point of `ℝ^k`. -/
def redBid (val : V → ℝ) (e : Expert ι V k D) : Fin k → ℝ :=
  fun q => val (e.2.1 q) - (match e.2.2 with
    | none => 0
    | some t => val t.2.2)

/-- The prices seen by a group at a probe, relative to the pivot price. -/
def offset (g : GroupKey ι k D) (c : Ctx ι) : Fin k → ℝ :=
  fun q => sp c.y (g.1 q) - (match g.2 with
    | none => 0
    | some jp => sp (c.hist jp.1) jp.2)

/-- Whether the experts of a group bid at a probe. -/
def activeAt (g : GroupKey ι k D) (c : Ctx ι) : Prop :=
  match g.2 with
  | none => True
  | some jp => (jp.1 : ℕ) < c.l

theorem util_some_of_active (val : V → ℝ) (c : Ctx ι) (e : Expert ι V k D)
    (h : activeAt (groupKey e) c) (q : Fin k) :
    util (bidOf val c.l c.hist) (dirOf val c.l c.hist) e (some q) c.y
      = redBid val e q - offset (groupKey e) c q := by
  obtain ⟨s, b, d⟩ := e
  cases d with
  | none =>
    have hthr : thr val c.l c.hist ((s, b, none) : Expert ι V k D) = some 0 := rfl
    rw [util_some_of_thr hthr]
    simp [redBid, offset, groupKey]
  | some t =>
    obtain ⟨j, p, v⟩ := t
    have hj : (j : ℕ) < c.l := h
    have hthr : thr val c.l c.hist ((s, b, some (j, p, v)) : Expert ι V k D)
        = some (val v - sp (c.hist j) p) := by simp [thr, hj]
    rw [util_some_of_thr hthr]
    simp [redBid, offset, groupKey]
    ring

theorem util_of_inactive (val : V → ℝ) (c : Ctx ι) (e : Expert ι V k D)
    (h : ¬ activeAt (groupKey e) c) (o : Option (Fin k)) :
    util (bidOf val c.l c.hist) (dirOf val c.l c.hist) e o c.y = 0 := by
  obtain ⟨s, b, d⟩ := e
  cases d with
  | none => exact absurd trivial h
  | some t =>
    obtain ⟨j, p, v⟩ := t
    have hj : ¬ (j : ℕ) < c.l := h
    have hthr : thr val c.l c.hist ((s, b, some (j, p, v)) : Expert ι V k D) = none := by
      simp [thr, hj]
    cases o with
    | none => exact util_none _ _ _ _ _
    | some q => exact util_some_of_inactive hthr q _

/-- A point of `ℝ^k` with a zero prepended: the outside option has utility zero. -/
def ext0 (x : Fin k → ℝ) : Fin (k + 1) → ℝ := Fin.cons 0 x

/-- Options indexed by `Fin (k+1)`: index `0` is the outside option. -/
def opt (a : Fin (k + 1)) : Option (Fin k) := Fin.cases none some a

theorem opt_surj (o : Option (Fin k)) : ∃ a : Fin (k + 1), opt a = o := by
  cases o with
  | none => exact ⟨0, rfl⟩
  | some q => exact ⟨q.succ, by simp [opt]⟩

theorem util_opt_of_active (val : V → ℝ) (c : Ctx ι) (e : Expert ι V k D)
    (h : activeAt (groupKey e) c) (a : Fin (k + 1)) :
    util (bidOf val c.l c.hist) (dirOf val c.l c.hist) e (opt a) c.y
      = ext0 (redBid val e) a - ext0 (offset (groupKey e) c) a := by
  refine Fin.cases ?_ ?_ a
  · simp [opt, ext0, util_none]
  · intro q
    simp [opt, ext0, util_some_of_active val c e h]

/-- Unordered pairs of options. -/
abbrev Pair (k : ℕ) := {p : Fin (k + 1) × Fin (k + 1) // p.1 < p.2}

/-- Number of unordered pairs of options (`(k+1) choose 2`). -/
def pairs (k : ℕ) : ℕ := Fintype.card (Pair k)

/-- The signs of the pairwise differences of option utilities at each probe of the list. -/
noncomputable def sig (val : V → ℝ) (cs : List (Ctx ι)) (e : Expert ι V k D) :
    Fin cs.length × Pair k → SignType :=
  fun j => SignType.sign
    ((ext0 (redBid val e) j.2.1.1 - ext0 (redBid val e) j.2.1.2)
      - (ext0 (offset (groupKey e) (cs.get j.1)) j.2.1.1
          - ext0 (offset (groupKey e) (cs.get j.1)) j.2.1.2))

/-- The cell of an expert after the probes `cs`: its group and its sign vector. -/
noncomputable def ty (val : V → ℝ) (cs : List (Ctx ι)) (e : Expert ι V k D) :
    GroupKey ι k D × (Fin cs.length × Pair k → SignType) :=
  (groupKey e, sig val cs e)

/-- Experts in the same cell agree at every probe of the list. -/
theorem agree_of_ty_eq (val : V → ℝ) (cs : List (Ctx ι)) {e e' : Expert ι V k D}
    (h : ty val cs e = ty val cs e') : Agree val cs e e' := by
  have hg : groupKey e = groupKey e' := congrArg Prod.fst h
  have hs : sig val cs e = sig val cs e' := congrArg Prod.snd h
  have hmain : ∀ i : Fin cs.length, SameOrder val (cs.get i) e e' := by
    intro i o o'
    by_cases hact : activeAt (groupKey e) (cs.get i)
    · have hact' : activeAt (groupKey e') (cs.get i) := hg ▸ hact
      obtain ⟨a, rfl⟩ := opt_surj o
      obtain ⟨b, rfl⟩ := opt_surj o'
      rw [util_opt_of_active val _ e hact, util_opt_of_active val _ e hact,
        util_opt_of_active val _ e' hact', util_opt_of_active val _ e' hact', ← hg]
      have key : SignType.sign
            ((ext0 (redBid val e) a - ext0 (redBid val e) b)
              - (ext0 (offset (groupKey e) (cs.get i)) a
                  - ext0 (offset (groupKey e) (cs.get i)) b))
          = SignType.sign
            ((ext0 (redBid val e') a - ext0 (redBid val e') b)
              - (ext0 (offset (groupKey e) (cs.get i)) a
                  - ext0 (offset (groupKey e) (cs.get i)) b)) := by
        rcases lt_trichotomy a b with hab | hab | hab
        · have := congrFun hs (i, ⟨(a, b), hab⟩)
          simpa only [sig, ← hg] using this
        · subst hab
          simp
        · have := congrFun hs (i, ⟨(b, a), hab⟩)
          simp only [sig, ← hg] at this
          have e1 : ∀ X : Fin (k + 1) → ℝ,
              (X a - X b) - (ext0 (offset (groupKey e) (cs.get i)) a
                  - ext0 (offset (groupKey e) (cs.get i)) b)
                = -((X b - X a) - (ext0 (offset (groupKey e) (cs.get i)) b
                  - ext0 (offset (groupKey e) (cs.get i)) a)) := fun X => by ring
          rw [e1, e1, Left.sign_neg, Left.sign_neg, this]
      have h1 : ∀ X : Fin (k + 1) → ℝ,
          (X a - ext0 (offset (groupKey e) (cs.get i)) a
              ≤ X b - ext0 (offset (groupKey e) (cs.get i)) b) ↔
            SignType.sign ((X a - X b) - (ext0 (offset (groupKey e) (cs.get i)) a
                - ext0 (offset (groupKey e) (cs.get i)) b)) ≤ 0 := fun X => by
        rw [sign_nonpos_iff]
        constructor <;> intro h <;> linarith
      exact (h1 _).trans ((by rw [key] : _ ↔ _).trans (h1 _).symm)
    · have hact' : ¬ activeAt (groupKey e') (cs.get i) := hg ▸ hact
      rw [util_of_inactive val _ e hact, util_of_inactive val _ e hact,
        util_of_inactive val _ e' hact', util_of_inactive val _ e' hact']
  refine ⟨(sameGroup_iff e e').2 hg, fun c hc => ?_⟩
  obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hc
  exact hmain i

/-- Evaluation of the extended point as a linear functional. -/
noncomputable def evalExt (a : Fin (k + 1)) : (Fin k → ℝ) →ₗ[ℝ] ℝ :=
  Fin.cases (motive := fun _ => (Fin k → ℝ) →ₗ[ℝ] ℝ) 0 (fun q => LinearMap.proj q) a

theorem evalExt_apply (a : Fin (k + 1)) (x : Fin k → ℝ) : evalExt a x = ext0 x a := by
  refine Fin.cases ?_ ?_ a
  · simp [evalExt, ext0]
  · intro q
    simp [evalExt, ext0]

/-- Within one group the sign vectors are those of an arrangement of
`pairs k · |cs|` hyperplanes in `ℝ^k`. -/
theorem card_sig_le (val : V → ℝ) (cs : List (Ctx ι)) (g : GroupKey ι k D)
    (S : Finset (Fin cs.length × Pair k → SignType))
    (hS : ∀ σ ∈ S, ∃ e : Expert ι V k D, groupKey e = g ∧ sig val cs e = σ) :
    S.card ≤ faceBound (cs.length * pairs k) k := by
  have h := card_signVectors_le (E := Fin k → ℝ) (J := Fin cs.length × Pair k)
    (fun j => evalExt j.2.1.1 - evalExt j.2.1.2)
    (fun j => ext0 (offset g (cs.get j.1)) j.2.1.1 - ext0 (offset g (cs.get j.1)) j.2.1.2)
    k (by simp) S ?_
  · simpa [pairs, Fintype.card_prod] using h
  · intro σ hσ
    obtain ⟨e, hge, rfl⟩ := hS σ hσ
    refine ⟨redBid val e, fun j => ?_⟩
    simp [sig, hge, evalExt_apply]

/-- **Number of cells.** After the probes `cs` the experts fall into at most
`|groups| · faceBound (|cs| · pairs k) k` cells. -/
theorem card_types_le (val : V → ℝ) (cs : List (Ctx ι)) :
    (Set.range (ty (k := k) (D := D) val cs)).ncard
      ≤ Fintype.card (GroupKey ι k D) * faceBound (cs.length * pairs k) k := by
  classical
  have hfin : (Set.range (ty (k := k) (D := D) val cs)).ncard
      = (univ.image (ty (k := k) (D := D) val cs)).card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext t
    simp
  rw [hfin]
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := (univ : Finset (GroupKey ι k D)))
    (fun _ _ => Finset.mem_univ _)]
  calc ∑ g : GroupKey ι k D, ((univ.image (ty (k := k) (D := D) val cs)).filter
          (fun t => t.1 = g)).card
      ≤ ∑ _g : GroupKey ι k D, faceBound (cs.length * pairs k) k := by
        refine Finset.sum_le_sum (fun g _ => ?_)
        have hinj : Set.InjOn Prod.snd
            (((univ.image (ty (k := k) (D := D) val cs)).filter (fun t => t.1 = g) :
              Finset _) : Set (GroupKey ι k D × (Fin cs.length × Pair k → SignType))) := by
          intro t ht t' ht' hsnd
          have h1 : t.1 = g := (Finset.mem_filter.1 ht).2
          have h2 : t'.1 = g := (Finset.mem_filter.1 ht').2
          exact Prod.ext (h1.trans h2.symm) hsnd
        rw [← Finset.card_image_of_injOn hinj]
        refine card_sig_le val cs g _ (fun σ hσ => ?_)
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hσ
        obtain ⟨ht1, ht2⟩ := Finset.mem_filter.1 ht
        obtain ⟨e, -, rfl⟩ := Finset.mem_image.1 ht1
        exact ⟨e, ht2, rfl⟩
    _ = Fintype.card (GroupKey ι k D) * faceBound (cs.length * pairs k) k := by
        simp


/-! ### Cells at every probe of a run -/

/-- At every probe, the number of probes completed before it is less than the total. -/
theorem Exec.forallProbes_length {E : Type*} (X : Exec ι E) :
    ∀ (l : ℕ) (hist : ℕ → ι → ℝ) (pre : List (Ctx ι)) (B : ℕ), pre.length + X.queries ≤ B →
      X.ForallProbes (fun pre' _ _ _ _ => pre'.length < B) l hist pre := by
  induction X with
  | leaf x wOut => intro _ _ _ _ _; trivial
  | node T y z child w x ih =>
    intro l hist pre B hB τ
    have hq : (Exec.node T y z child w x).queries
        = (before (nodeSegs T y child l hist) T).length := by
      rw [← Exec.contexts_node T y z child w x l hist, Exec.length_contexts]
    have hlen : (before (nodeSegs T y child l hist) τ).length + (1 + (child τ).queries)
        ≤ (before (nodeSegs T y child l hist) T).length := by
      have h1 : (before (nodeSegs T y child l hist) (τ + 1)).length
          = (before (nodeSegs T y child l hist) τ).length + (1 + (child τ).queries) := by
        rw [before_succ, List.length_append]
        simp [nodeSegs, Exec.length_contexts, Nat.add_comm]
      rw [← h1]
      exact length_before_le _ (Nat.succ_le_of_lt τ.2)
    constructor
    · simp only [List.length_append]
      omega
    · apply ih τ
      simp only [List.length_append]
      omega

/-- The uniform bound on the number of cells during a run with `Q` probes on `N` coordinates:
`(2N)^k (2ND + 1)` groups, each cut by `Q · pairs k` hyperplanes in `ℝ^k`. -/
def classBound (N k D Q : ℕ) : ℕ :=
  (2 * N) ^ k * (D * (2 * N) + 1) * faceBound (Q * pairs k) k

/-- **Cells at every probe.** In a valid run from the root with unit wealth, at every probe
and for every test point `y'` of the market step (in particular the proposal), the experts fall
into at most `classBound N k D Q` cells (`Q` the total number of probes) such that experts of
one cell have the same wealth before the probe, the same maximizing options at `y'`, and the
same gain at `y'` whatever the feedback. The cell of an expert is determined by its group and
by how it orders its options at the probes completed so far and at `y'`. -/
theorem cells_at_every_probe (A : Alg V) (X : Exec ι (Expert ι V k D)) (hist₀ : ℕ → ι → ℝ)
    (hX : X.Valid A 0 hist₀ (fun _ => 1)) :
    X.ForallProbes (fun pre l hist _ w => ∀ y' : ι → ℝ,
      ∃ cell : Expert ι V k D →
          GroupKey ι k D × (Fin (pre ++ [(⟨l, hist, y'⟩ : Ctx ι)]).length × Pair k → SignType),
        (Set.range cell).ncard ≤ classBound (Fintype.card ι) k D X.queries ∧
        ∀ e e', cell e = cell e' →
          w e = w e' ∧
          (∀ o, util (bidOf A.val l hist) (dirOf A.val l hist) e o y'
                = best (bidOf A.val l hist) (dirOf A.val l hist) e y' ↔
              util (bidOf A.val l hist) (dirOf A.val l hist) e' o y'
                = best (bidOf A.val l hist) (dirOf A.val l hist) e' y') ∧
          ∀ v, gain A.val l hist y' v e = gain A.val l hist y' v e') 0 hist₀ [] := by
  have h1 := (X.wealth_agree A 0 hist₀ (fun _ => 1) [] hX (fun _ _ _ => rfl)).1
  have h2 := X.forallProbes_length 0 hist₀ [] X.queries (by simp)
  refine Exec.ForallProbes.mono ?_ X 0 hist₀ [] (Exec.ForallProbes.and X 0 hist₀ [] h1 h2)
  rintro pre l hist y w ⟨hw, hlen⟩ y'
  refine ⟨ty A.val (pre ++ [(⟨l, hist, y'⟩ : Ctx ι)]), ?_, ?_⟩
  · refine (card_types_le A.val _).trans ?_
    unfold classBound
    rw [card_groupKey]
    refine Nat.mul_le_mul_left _ (faceBound_mono_left ?_ k)
    refine Nat.mul_le_mul_right _ ?_
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · intro e e' h
    have hag := agree_of_ty_eq A.val _ h
    have hpre : Agree A.val pre e e' :=
      hag.mono (fun c hc => List.mem_append.2 (Or.inl hc))
    have hord : SameOrder A.val ⟨l, hist, y'⟩ e e' := hag.2 _ (by simp)
    exact ⟨hw e e' hpre, fun o => argmax_congr hord o, fun v => gain_congr hag.1 hord v⟩

/-- **One option per cell.** Refine the cells after the probes `cs` by a test point `c`. Then
all experts of one cell attain their best utility at `c` on a common option, so the market
potential at `c` is a sum over cells of `(common wealth) × (sum over the cell of one affine
function of the prices)`. -/
theorem best_common_option (val : V → ℝ) (cs : List (Ctx ι)) (c : Ctx ι)
    (t : GroupKey ι k D × (Fin (cs ++ [c]).length × Pair k → SignType)) :
    ∃ o : Option (Fin k), ∀ e : Expert ι V k D, ty val (cs ++ [c]) e = t →
      best (bidOf val c.l c.hist) (dirOf val c.l c.hist) e c.y
        = util (bidOf val c.l c.hist) (dirOf val c.l c.hist) e o c.y := by
  by_cases hne : ∃ e₀ : Expert ι V k D, ty val (cs ++ [c]) e₀ = t
  · obtain ⟨e₀, he₀⟩ := hne
    obtain ⟨o, ho⟩ := bestSet_nonempty (bidOf val c.l c.hist) (dirOf val c.l c.hist) e₀ c.y
    have ho' : util (bidOf val c.l c.hist) (dirOf val c.l c.hist) e₀ o c.y
        = best (bidOf val c.l c.hist) (dirOf val c.l c.hist) e₀ c.y := by simpa using ho
    refine ⟨o, fun e he => ?_⟩
    have hag := agree_of_ty_eq val (cs ++ [c]) (he₀.trans he.symm)
    have hord : SameOrder val c e₀ e := hag.2 c (by simp)
    exact ((argmax_congr (l := c.l) (hist := c.hist) (y := c.y) hord o).1 ho').symm
  · exact ⟨none, fun e he => absurd ⟨e, he⟩ hne⟩

/-- `pairs k = (k+1) choose 2` for the arities used below. -/
theorem pairs_three : pairs 3 = 6 := by decide

theorem pairs_four : pairs 4 = 10 := by decide

theorem pairs_five : pairs 5 = 15 := by decide

theorem pairs_six : pairs 6 = 21 := by decide

end SPLP
