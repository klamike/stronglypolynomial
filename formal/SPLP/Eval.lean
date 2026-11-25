import Mathlib
import SPLP.Cells

/-!
# Evaluating the potential cell by cell

If wealth is constant on the cells of the probes `cs`, then at any test point `c` the market
potential is a sum over the cells refined by `c`: (wealth of the cell) times (the sum of the
bids of the cell on its common best option, minus the size of the cell times one price term).
So one evaluation needs, per cell, its wealth, its size and one sum of bids.
-/

set_option linter.unusedSectionVars false

namespace SPLP

open Finset

variable {ι V : Type*} {k D : ℕ} [Fintype ι] [DecidableEq ι] [Fintype V]

/-- On a set `s` of experts of one cell `t` (after the probes `cs` and the test point `c`), the
wealth-weighted sum of best utilities is the wealth of a representative `r` of the cell times
(the sum over `s` of the bids on the common best option `o`, minus the size of `s` times the
price term of `r`). -/
private theorem sum_best_of_cell (val : V → ℝ) (cs : List (Ctx ι)) (c : Ctx ι)
    (w : Expert ι V k D → ℝ) (hw : ∀ e e', Agree val cs e e' → w e = w e')
    (t : GroupKey ι k D × (Fin (cs ++ [c]).length × Pair k → SignType))
    (o : Option (Fin k)) (r : Expert ι V k D)
    (ho : ∀ e : Expert ι V k D, ty val (cs ++ [c]) e = t →
      best (bidOf val c.l c.hist) (dirOf val c.l c.hist) e c.y
        = util (bidOf val c.l c.hist) (dirOf val c.l c.hist) e o c.y)
    (hr : ty val (cs ++ [c]) r = t) (s : Finset (Expert ι V k D))
    (hs : ∀ e ∈ s, ty val (cs ++ [c]) e = t) :
    ∑ e ∈ s, w e * best (bidOf val c.l c.hist) (dirOf val c.l c.hist) e c.y
      = w r * ((∑ e ∈ s, bidOf val c.l c.hist e o)
          - (s.card : ℝ) * ∑ i, dirOf val c.l c.hist r o i * c.y i) := by
  have key : ∀ e ∈ s, w e * best (bidOf val c.l c.hist) (dirOf val c.l c.hist) e c.y
      = w r * bidOf val c.l c.hist e o
        - w r * ∑ i, dirOf val c.l c.hist r o i * c.y i := by
    intro e he
    -- `e` and `r` lie in the same cell, so they agree at the probes `cs` and at `c`
    have hag : Agree val (cs ++ [c]) e r :=
      agree_of_ty_eq val (cs ++ [c]) ((hs e he).trans hr.symm)
    have hwe : w e = w r := hw e r (hag.mono fun x hx => List.mem_append.2 (Or.inl hx))
    have hdir : dirOf val c.l c.hist e = dirOf val c.l c.hist r :=
      dirOf_congr val c.l c.hist hag.1
    rw [ho e (hs e he), hwe, util, hdir, mul_sub]
  rw [Finset.sum_congr rfl key, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    nsmul_eq_mul]
  ring

open Classical in
/-- **Evaluation by cells.** -/
theorem Phi_eq_cellSum [Nonempty V] (val : V → ℝ) (cs : List (Ctx ι)) (c : Ctx ι)
    (w : Expert ι V k D → ℝ) (hw : ∀ e e', Agree val cs e e' → w e = w e') :
    ∃ (o : GroupKey ι k D × (Fin (cs ++ [c]).length × Pair k → SignType) → Option (Fin k))
      (rep : GroupKey ι k D × (Fin (cs ++ [c]).length × Pair k → SignType) → Expert ι V k D),
      Phi val c.l c.hist w c.y
        = ∑ t ∈ univ.image (ty (k := k) (D := D) val (cs ++ [c])),
            w (rep t) *
              ((∑ e ∈ univ.filter (fun e : Expert ι V k D => ty val (cs ++ [c]) e = t),
                  bidOf val c.l c.hist e (o t))
                - ((univ.filter (fun e : Expert ι V k D => ty val (cs ++ [c]) e = t)).card : ℝ)
                    * ∑ i, dirOf val c.l c.hist (rep t) (o t) i * c.y i) := by
  -- one common best option per cell
  choose o ho using fun t : GroupKey ι k D × (Fin (cs ++ [c]).length × Pair k → SignType) =>
    best_common_option (V := V) val cs c t
  -- one representative per cell: an expert of the cell if there is one, otherwise any expert
  -- (it is never used: the sum only runs over the cells that contain an expert)
  have hrep : ∀ t : GroupKey ι k D × (Fin (cs ++ [c]).length × Pair k → SignType),
      ∃ r : Expert ι V k D,
        (∃ e : Expert ι V k D, ty val (cs ++ [c]) e = t) → ty val (cs ++ [c]) r = t := by
    intro t
    by_cases h : ∃ e : Expert ι V k D, ty val (cs ++ [c]) e = t
    · obtain ⟨e, he⟩ := h
      exact ⟨e, fun _ => he⟩
    · exact ⟨(t.1.1, fun _ => Classical.arbitrary V, none), fun h' => absurd h' h⟩
  choose rep hrep using hrep
  refine ⟨o, rep, ?_⟩
  -- regroup the potential by cells
  have hfib : Phi val c.l c.hist w c.y
      = ∑ t ∈ univ.image (ty (k := k) (D := D) val (cs ++ [c])),
          ∑ e ∈ univ.filter (fun e : Expert ι V k D => ty val (cs ++ [c]) e = t),
            w e * best (bidOf val c.l c.hist) (dirOf val c.l c.hist) e c.y := by
    unfold Phi potential
    exact (Finset.sum_fiberwise_of_maps_to
      (fun e _ => Finset.mem_image_of_mem _ (Finset.mem_univ e)) _).symm
  rw [hfib]
  -- evaluate cell by cell
  refine Finset.sum_congr rfl fun t ht => ?_
  obtain ⟨e₀, -, he₀⟩ := Finset.mem_image.1 ht
  exact sum_best_of_cell val cs c w hw t (o t) (rep t) (ho t) (hrep t ⟨e₀, he₀⟩) _
    fun e he => (Finset.mem_filter.1 he).2

end SPLP
