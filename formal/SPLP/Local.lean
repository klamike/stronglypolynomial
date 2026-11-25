import Mathlib
import SPLP.Cells

/-!
# Wealth and potential relative to a snapshot (exact arithmetic)

`Exec.wealth_agree` says that wealth is constant on the cells of *all* probes completed so
far. This file proves a relative version for the algorithm **without rounding**
(`A.rnd = id`). Fix a node of a valid run and call its input wealth the *snapshot*. At every probe below that node (at any depth)

* `Exec.wealth_factor`: wealth = snapshot × multiplier, and the multiplier is constant on the
  cells of the probes completed **inside that node** so far;
* `Exec.cells_relative`: those cells, refined by a test point, number at most
  `|groups| · faceBound ((n + 1) · pairs k) k` with `n` the number of probes completed inside
  the node, and experts of one cell have the same maximizing options and gains at the test
  point;
* `Phi_eq_cellSum_rel`, `Exec.potential_relative`: the market potential at a test point is a
  sum over those cells of (multiplier of the cell) × (sum over the cell of snapshot × one
  affine function of the prices).

Taking the root as the node (snapshot `1`) gives back the global statements. Taking the node
that runs the probe gives a number of terms that depends only on the probes of that node; at a
node whose children are leaves this is at most the number of probes of one node, whatever the
number of probes completed in the whole run.

What this does **not** give: the sums of the snapshot over a cell are not computed here. The
snapshot itself takes different values on the cells of all earlier probes, so this is a
statement about structure, not yet about cost.

The statements need exact arithmetic: rounding to a fixed number of significant bits is not
compatible with factoring out an arbitrary snapshot.
-/

set_option linter.unusedSectionVars false

namespace SPLP

open Finset

variable {ι V : Type*} {k D : ℕ} [Fintype ι] [DecidableEq ι] [Fintype V]

/-- **Wealth relative to a reference wealth.** If a node of a valid run is entered with wealth
`w₀ · M`, where `M` is constant on the classes of `Agree` for the probes `pre`, then before
every probe below it the wealth is `w₀ · M'` with `M'` constant on the classes for the probes
completed before that probe (starting from `pre`), and likewise for the returned wealth.
With `w₀ = 1` this is `Exec.wealth_agree`. -/
theorem Exec.wealth_factor (A : Alg V) (hid : ∀ x : ℝ, A.rnd x = x)
    (w₀ : Expert ι V k D → ℝ) (X : Exec ι (Expert ι V k D)) :
    ∀ (l : ℕ) (hist : ℕ → ι → ℝ) (wIn : Expert ι V k D → ℝ) (pre : List (Ctx ι)),
      X.Valid A l hist wIn →
      (∃ M : Expert ι V k D → ℝ, (∀ e, wIn e = w₀ e * M e) ∧
        ∀ e e', Agree A.val pre e e' → M e = M e') →
      X.ForallProbes (fun pre' _ _ _ w => ∃ M : Expert ι V k D → ℝ,
          (∀ e, w e = w₀ e * M e) ∧ ∀ e e', Agree A.val pre' e e' → M e = M e')
          l hist pre ∧
        (∃ M : Expert ι V k D → ℝ, (∀ e, X.wOut e = w₀ e * M e) ∧
          ∀ e e', Agree A.val (pre ++ X.contexts l hist) e e' → M e = M e') := by
  induction X with
  | leaf x wOut =>
    intro l hist wIn pre hv hin
    obtain ⟨-, hw, -⟩ := hv
    obtain ⟨M, hM, hMc⟩ := hin
    refine ⟨trivial, M, fun e => ?_, fun e e' h => ?_⟩
    · simp only [Exec.wOut, hw]
      exact hM e
    · simp only [Exec.contexts, List.append_nil] at h
      exact hMc e e' h
  | node T y z child w x ih =>
    intro l hist wIn pre hv hin
    obtain ⟨-, -, hw0, hprobe, -⟩ := hv
    -- wealth before the `n`-th probe
    have key : ∀ n, n ≤ T → ∃ M : Expert ι V k D → ℝ, (∀ e, w n e = w₀ e * M e) ∧
        ∀ e e', Agree A.val (pre ++ before (nodeSegs T y child l hist) n) e e' →
          M e = M e' := by
      intro n
      induction n with
      | zero =>
        intro _
        obtain ⟨M, hM, hMc⟩ := hin
        refine ⟨M, fun e => ?_, fun e e' h => ?_⟩
        · rw [hw0]
          exact hM e
        · exact hMc e e' (h.mono (fun c hc => by simp [before, hc]))
      | succ n ihn =>
        intro hn
        have hn' : n < T := hn
        obtain ⟨-, hchild, hstep⟩ := hprobe ⟨n, hn'⟩
        obtain ⟨M, hM, hMc⟩ := ihn (Nat.le_of_lt hn')
        have hbs := before_succ (nodeSegs T y child l hist) ⟨n, hn'⟩
        simp only at hbs
        -- the child's input is the reference wealth times a multiplier
        have hc1 : ∀ e, A.c * w n e = w₀ e * (A.c * M e) := fun e => by
          rw [hM e]; ring
        have hc2 : ∀ e e', Agree A.val (pre ++ before (nodeSegs T y child l hist) n) e e' →
            A.c * M e = A.c * M e' := fun e e' h => by rw [hMc e e' h]
        obtain ⟨Mc, hMc1, hMc2⟩ :=
          (ih ⟨n, hn'⟩ (l + 1) _ _ _ hchild ⟨fun e => A.c * M e, hc1, hc2⟩).2
        -- the new multiplier
        have hw1 : ∀ e, w (n + 1) e = w₀ e * ((1 - A.c) * M e
            * (1 + A.η * gain A.val l hist (y ⟨n, hn'⟩)
                (feedback (y ⟨n, hn'⟩) (child ⟨n, hn'⟩).x (z ⟨n, hn'⟩)) e) + Mc e) := by
          intro e
          have hs := hstep e
          simp only at hs
          rw [hs, hid, hM e, hMc1 e]
          ring
        have hw2 : ∀ e e',
            Agree A.val (pre ++ before (nodeSegs T y child l hist) (n + 1)) e e' →
            (1 - A.c) * M e * (1 + A.η * gain A.val l hist (y ⟨n, hn'⟩)
                (feedback (y ⟨n, hn'⟩) (child ⟨n, hn'⟩).x (z ⟨n, hn'⟩)) e) + Mc e
              = (1 - A.c) * M e' * (1 + A.η * gain A.val l hist (y ⟨n, hn'⟩)
                (feedback (y ⟨n, hn'⟩) (child ⟨n, hn'⟩).x (z ⟨n, hn'⟩)) e') + Mc e' := by
          intro e e' h
          rw [hbs] at h
          have h1 : Agree A.val (pre ++ before (nodeSegs T y child l hist) n) e e' :=
            h.mono (fun c hc => by
              rcases List.mem_append.1 hc with hc | hc
              · exact List.mem_append.2 (Or.inl hc)
              · exact List.mem_append.2 (Or.inr (List.mem_append.2 (Or.inl hc))))
          have h2 : SameOrder A.val ⟨l, hist, y ⟨n, hn'⟩⟩ e e' :=
            h.2 _ (List.mem_append.2 (Or.inr (List.mem_append.2 (Or.inr (by simp [nodeSegs])))))
          have hgain := gain_congr h.1 h2
            (feedback (y ⟨n, hn'⟩) (child ⟨n, hn'⟩).x (z ⟨n, hn'⟩))
          have hcout := hMc2 e e'
            (h.mono (fun c hc => by
              rcases List.mem_append.1 hc with hc | hc
              · rcases List.mem_append.1 hc with hc | hc
                · exact List.mem_append.2 (Or.inl hc)
                · exact List.mem_append.2 (Or.inr (List.mem_append.2 (Or.inl hc)))
              · exact List.mem_append.2 (Or.inr (List.mem_append.2 (Or.inr (by
                  simp only [nodeSegs, List.mem_cons]
                  exact Or.inr hc))))))
          rw [hMc e e' h1, hgain, hcout]
        exact ⟨_, hw1, hw2⟩
    refine ⟨fun τ => ⟨key τ (Nat.le_of_lt τ.2), ?_⟩, ?_⟩
    · obtain ⟨M, hM, hMc⟩ := key τ (Nat.le_of_lt τ.2)
      have hc1 : ∀ e, A.c * w τ e = w₀ e * (A.c * M e) := fun e => by
        rw [hM e]; ring
      have hc2 : ∀ e e', Agree A.val (pre ++ before (nodeSegs T y child l hist) τ) e e' →
          A.c * M e = A.c * M e' := fun e e' h => by rw [hMc e e' h]
      exact (ih τ (l + 1) _ _ _ (hprobe τ).2.1 ⟨fun e => A.c * M e, hc1, hc2⟩).1
    · rw [Exec.contexts_node]
      exact key T le_rfl

/-- **Cells relative to a snapshot.** Let `X` be any node of a valid run, entered with wealth
`wIn`. At every probe below `X`, with `pre` the probes completed inside `X` before it, the
wealth is `wIn · M`, and for every test point `y'` the experts fall into at most
`|groups| · faceBound ((|pre| + 1) · pairs k) k` cells on which `M`, the maximizing options
at `y'` and the gain at `y'` are constant. The bound does not involve the probes completed
before `X` was entered. -/
theorem Exec.cells_relative (A : Alg V) (hid : ∀ x : ℝ, A.rnd x = x)
    (X : Exec ι (Expert ι V k D)) (l : ℕ)
    (hist : ℕ → ι → ℝ) (wIn : Expert ι V k D → ℝ) (hX : X.Valid A l hist wIn) :
    X.ForallProbes (fun pre l' hist' _ w => ∃ M : Expert ι V k D → ℝ,
      (∀ e, w e = wIn e * M e) ∧ ∀ y' : ι → ℝ,
      ∃ cell : Expert ι V k D →
          GroupKey ι k D × (Fin (pre ++ [(⟨l', hist', y'⟩ : Ctx ι)]).length × Pair k → SignType),
        (Set.range cell).ncard
          ≤ Fintype.card (GroupKey ι k D) * faceBound ((pre.length + 1) * pairs k) k ∧
        ∀ e e', cell e = cell e' →
          M e = M e' ∧
          (∀ o, util (bidOf A.val l' hist') (dirOf A.val l' hist') e o y'
                = best (bidOf A.val l' hist') (dirOf A.val l' hist') e y' ↔
              util (bidOf A.val l' hist') (dirOf A.val l' hist') e' o y'
                = best (bidOf A.val l' hist') (dirOf A.val l' hist') e' y') ∧
          ∀ v, gain A.val l' hist' y' v e = gain A.val l' hist' y' v e') l hist [] := by
  have h1 := (X.wealth_factor A hid wIn l hist wIn [] hX
    ⟨fun _ => 1, fun e => (mul_one _).symm, fun _ _ _ => rfl⟩).1
  refine Exec.ForallProbes.mono ?_ X l hist [] h1
  rintro pre l' hist' y w ⟨M, hM, hMc⟩
  refine ⟨M, hM, fun y' => ⟨ty A.val (pre ++ [(⟨l', hist', y'⟩ : Ctx ι)]), ?_, ?_⟩⟩
  · have hlen : (pre ++ [(⟨l', hist', y'⟩ : Ctx ι)]).length = pre.length + 1 := by simp
    rw [← hlen]
    exact card_types_le A.val _
  · intro e e' h
    have hag := agree_of_ty_eq A.val _ h
    have hpre : Agree A.val pre e e' :=
      hag.mono (fun c hc => List.mem_append.2 (Or.inl hc))
    have hord : SameOrder A.val ⟨l', hist', y'⟩ e e' := hag.2 _ (by simp)
    exact ⟨hMc e e' hpre, fun o => argmax_congr hord o, fun v => gain_congr hag.1 hord v⟩

open Classical in
/-- **Evaluation relative to a snapshot.** If the wealth is `w₀ · M` with `M` constant on the
cells of the probes `cs`, then at any test point `c` the market potential is a sum over the
cells refined by `c` of (the value `μ` of `M` on the cell) × (the sum over the cell of `w₀`
times the utility of one option `o` common to the cell). -/
theorem Phi_eq_cellSum_rel (val : V → ℝ) (cs : List (Ctx ι)) (c : Ctx ι)
    (w₀ M : Expert ι V k D → ℝ) (hM : ∀ e e', Agree val cs e e' → M e = M e') :
    ∃ (o : GroupKey ι k D × (Fin (cs ++ [c]).length × Pair k → SignType) → Option (Fin k))
      (μ : GroupKey ι k D × (Fin (cs ++ [c]).length × Pair k → SignType) → ℝ),
      (∀ e, μ (ty val (cs ++ [c]) e) = M e) ∧
      Phi val c.l c.hist (fun e => w₀ e * M e) c.y
        = ∑ t ∈ univ.image (ty (k := k) (D := D) val (cs ++ [c])),
            μ t * ∑ e ∈ univ.filter (fun e : Expert ι V k D => ty val (cs ++ [c]) e = t),
              w₀ e * util (bidOf val c.l c.hist) (dirOf val c.l c.hist) e (o t) c.y := by
  classical
  -- the common best option and the common multiplier of every cell
  choose o ho using best_common_option (k := k) (D := D) val cs c
  have hμ : ∀ t : GroupKey ι k D × (Fin (cs ++ [c]).length × Pair k → SignType),
      ∃ m : ℝ, ∀ e : Expert ι V k D, ty val (cs ++ [c]) e = t → M e = m := by
    intro t
    by_cases hne : ∃ e₀ : Expert ι V k D, ty val (cs ++ [c]) e₀ = t
    · obtain ⟨e₀, he₀⟩ := hne
      refine ⟨M e₀, fun e he => ?_⟩
      have hag := agree_of_ty_eq val (cs ++ [c]) (he.trans he₀.symm)
      exact hM e e₀ (hag.mono (fun c' hc' => List.mem_append.2 (Or.inl hc')))
    · exact ⟨0, fun e he => absurd ⟨e, he⟩ hne⟩
  choose μ hμ' using hμ
  refine ⟨o, μ, fun e => (hμ' _ e rfl).symm, ?_⟩
  unfold Phi potential
  refine (Finset.sum_fiberwise_of_maps_to (g := ty (k := k) (D := D) val (cs ++ [c]))
    (t := univ.image (ty (k := k) (D := D) val (cs ++ [c])))
    (fun e _ => Finset.mem_image_of_mem _ (Finset.mem_univ e)) _).symm.trans ?_
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun e he => ?_)
  have het : ty val (cs ++ [c]) e = t := (Finset.mem_filter.1 he).2
  show w₀ e * M e * best (bidOf val c.l c.hist) (dirOf val c.l c.hist) e c.y
    = μ t * (w₀ e * util (bidOf val c.l c.hist) (dirOf val c.l c.hist) e (o t) c.y)
  rw [ho t e het, hμ' t e het]
  ring

open Classical in
/-- **The potential at every probe, relative to a snapshot.** Let `X` be any node of a valid
run, entered with wealth `wIn`. At every probe below `X`, with `pre` the probes completed
inside `X` before it, and for every test point `y'`, the potential of that probe's market is
a sum of at most `|groups| · faceBound ((|pre| + 1) · pairs k) k` terms, each of the form
(a number `μ t`) × (the sum over one cell of `wIn` times the utility of one option). -/
theorem Exec.potential_relative (A : Alg V) (hid : ∀ x : ℝ, A.rnd x = x)
    (X : Exec ι (Expert ι V k D)) (l : ℕ)
    (hist : ℕ → ι → ℝ) (wIn : Expert ι V k D → ℝ) (hX : X.Valid A l hist wIn) :
    X.ForallProbes (fun pre l' hist' _ w => ∀ y' : ι → ℝ,
      ∃ (S : Finset (GroupKey ι k D ×
            (Fin (pre ++ [(⟨l', hist', y'⟩ : Ctx ι)]).length × Pair k → SignType)))
        (o : GroupKey ι k D ×
            (Fin (pre ++ [(⟨l', hist', y'⟩ : Ctx ι)]).length × Pair k → SignType)
              → Option (Fin k))
        (μ : GroupKey ι k D ×
            (Fin (pre ++ [(⟨l', hist', y'⟩ : Ctx ι)]).length × Pair k → SignType) → ℝ),
        S.card ≤ Fintype.card (GroupKey ι k D) * faceBound ((pre.length + 1) * pairs k) k ∧
        Phi A.val l' hist' (fun e => (1 - A.c) * w e) y'
          = ∑ t ∈ S, μ t *
              ∑ e ∈ univ.filter (fun e : Expert ι V k D =>
                  ty A.val (pre ++ [(⟨l', hist', y'⟩ : Ctx ι)]) e = t),
                wIn e * util (bidOf A.val l' hist') (dirOf A.val l' hist') e (o t) y')
      l hist [] := by
  classical
  have h1 := (X.wealth_factor A hid wIn l hist wIn [] hX
    ⟨fun _ => 1, fun e => (mul_one _).symm, fun _ _ _ => rfl⟩).1
  refine Exec.ForallProbes.mono ?_ X l hist [] h1
  rintro pre l' hist' y w ⟨M, hM, hMc⟩ y'
  obtain ⟨o, μ, -, hΦ⟩ := Phi_eq_cellSum_rel (k := k) (D := D) A.val pre
    (⟨l', hist', y'⟩ : Ctx ι) wIn (fun e => (1 - A.c) * M e)
    (fun e e' h => by rw [hMc e e' h])
  refine ⟨univ.image (ty (k := k) (D := D) A.val (pre ++ [(⟨l', hist', y'⟩ : Ctx ι)])),
    o, μ, ?_, ?_⟩
  · have hfin : (univ.image
          (ty (k := k) (D := D) A.val (pre ++ [(⟨l', hist', y'⟩ : Ctx ι)]))).card
        = (Set.range
          (ty (k := k) (D := D) A.val (pre ++ [(⟨l', hist', y'⟩ : Ctx ι)]))).ncard := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext t
      simp
    have hlen : (pre ++ [(⟨l', hist', y'⟩ : Ctx ι)]).length = pre.length + 1 := by simp
    rw [hfin, ← hlen]
    exact card_types_le A.val _
  · have hw : (fun e => (1 - A.c) * w e) = (fun e => wIn e * ((1 - A.c) * M e)) := by
      funext e
      rw [hM e]
      ring
    rw [hw]
    exact hΦ

end SPLP
