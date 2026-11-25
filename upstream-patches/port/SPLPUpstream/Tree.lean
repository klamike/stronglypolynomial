import SPLP.UpstreamModel
import OAI.Optimization.LinearProgramming.PriceGame.Model

/-!
# A short correct strategy in upstream's own price-game model

`SPLP.exists_tree` is stated for a verbatim copy of the query model of the upstream
development (`SPLP.Upstream`). This file imports upstream's actual definitions
(`OAI.Optimization.LinearProgramming.PriceGame`, file `PriceGame/Model.lean`, unchanged) and
transfers the result to them.
-/

namespace SPLPUpstream

open OAI.Optimization.LinearProgramming

variable {N R : ℕ} {anchor : Fin N}

/-- A tree over the copied model as a tree over upstream's model. -/
def toReal : SPLP.Upstream.Tree N → PriceGame.Tree N
  | .result a => .result a
  | .ask q next => .ask ⟨q.prices, q.index⟩ (fun b => toReal (next b))

/-- An upstream hidden instance as an instance of the copied model. -/
def toCopy (h : PriceGame.Hidden N R anchor) : SPLP.Upstream.Hidden N R anchor :=
  ⟨h.positive, h.active, h.anchor_mem, h.cost⟩

theorem height_toReal (t : SPLP.Upstream.Tree N) : (toReal t).height = t.height := by
  induction t with
  | result a => rfl
  | ask q next ih =>
    simp only [toReal, PriceGame.Tree.height, SPLP.Upstream.Tree.height, ih]

theorem forced_iff (h : PriceGame.Hidden N R anchor) (q : SPLP.Upstream.Query N) :
    (toCopy h).Forced q ↔ h.Forced ⟨q.prices, q.index⟩ := Iff.rfl

theorem reaches_toReal (h : PriceGame.Hidden N R anchor) (t : SPLP.Upstream.Tree N)
    (a : Bool) (hr : PriceGame.Tree.Reaches h (toReal t) a) :
    SPLP.Upstream.Tree.Reaches (toCopy h) t a := by
  induction t with
  | result b =>
    cases hr
    exact .result _
  | ask q next ih =>
    cases hr with
    | ask allowed rest =>
      exact .ask (fun hf => allowed ((forced_iff h q).1 hf)) (ih _ rest)

theorem correct_toReal (h : PriceGame.Hidden N R anchor) (t : SPLP.Upstream.Tree N)
    (hc : SPLP.Upstream.Tree.Correct (toCopy h) t) : PriceGame.Tree.Correct h (toReal t) :=
  fun a hr => hc a (reaches_toReal h t a hr)

/-- **A correct strategy of height `N · 2 r₀ (2N)^46` in upstream's model.** -/
theorem exists_tree (N R : ℕ) (anchor : Fin N) :
    ∃ t : PriceGame.Tree N,
      t.height ≤ N * (2 * SPLP.K4.r₀ (Fin N) (Fin (R + 2)) (SPLP.K4.depth SPLP.K4_good N)
        * (2 * N) ^ 46) ∧
      ∀ h : PriceGame.Hidden N R anchor, PriceGame.Tree.Correct h t := by
  obtain ⟨t, ht, hc⟩ := SPLP.exists_tree N R anchor
  exact ⟨toReal t, by rw [height_toReal]; exact ht, fun h => correct_toReal h t (hc (toCopy h))⟩

/-- The same with the number of root probes made explicit. -/
theorem exists_tree_explicit (N R : ℕ) (anchor : Fin N) :
    ∃ t : PriceGame.Tree N,
      (t.height : ℝ) ≤ N * (2 * (186473 + 70784 * Real.log N + 50560 * Real.log (R + 2))
        * (2 * N) ^ 46) ∧
      ∀ h : PriceGame.Hidden N R anchor, PriceGame.Tree.Correct h t := by
  obtain ⟨t, ht, hc⟩ := SPLP.exists_tree_explicit N R anchor
  exact ⟨toReal t, by rw [height_toReal]; exact ht, fun h => correct_toReal h t (hc (toCopy h))⟩

end SPLPUpstream
