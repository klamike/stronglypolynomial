import Mathlib
import SPLP.Cells

/-!
# Wealth depends only on the best options

The cells of `SPLP/Cells.lean` record how an expert orders all its options at every completed
probe. Wealth depends on less: only on which options are *maximizing* at each completed probe.
`Exec.wealth_agreeMax` states this for the coarser relation `AgreeMax`; `Exec.wealth_rel` is
the general principle (any relation that is monotone in the list of probes and forces equal
gains).
-/

set_option linter.unusedSectionVars false

namespace SPLP

open Finset

variable {ι V : Type*} {k D : ℕ} [Fintype ι] [DecidableEq ι]

/-- The two experts have the same maximizing options at the probe `c`. -/
def SameArgmax (val : V → ℝ) (c : Ctx ι) (e e' : Expert ι V k D) : Prop :=
  ∀ o : Option (Fin k),
    util (bidOf val c.l c.hist) (dirOf val c.l c.hist) e o c.y
        = best (bidOf val c.l c.hist) (dirOf val c.l c.hist) e c.y ↔
      util (bidOf val c.l c.hist) (dirOf val c.l c.hist) e' o c.y
        = best (bidOf val c.l c.hist) (dirOf val c.l c.hist) e' c.y

/-- Same group and same maximizing options at every probe of the list. -/
def AgreeMax (val : V → ℝ) (cs : List (Ctx ι)) (e e' : Expert ι V k D) : Prop :=
  SameGroup e e' ∧ ∀ c ∈ cs, SameArgmax val c e e'

/-- Agreement on the full order of options implies agreement on the maximizing options. -/
theorem Agree.agreeMax {val : V → ℝ} {cs : List (Ctx ι)} {e e' : Expert ι V k D}
    (h : Agree val cs e e') : AgreeMax val cs e e' :=
  ⟨h.1, fun c hc o => argmax_congr (l := c.l) (hist := c.hist) (y := c.y) (h.2 c hc) o⟩

/-- Experts of the same group with the same maximizing options have the same gain. -/
theorem gain_congr_argmax {val : V → ℝ} {l : ℕ} {hist : ℕ → ι → ℝ} {y : ι → ℝ}
    {e e' : Expert ι V k D} (hg : SameGroup e e') (ho : SameArgmax val ⟨l, hist, y⟩ e e')
    (v : ι → Bool) : gain val l hist y v e = gain val l hist y v e' := by
  have hdir := dirOf_congr val l hist hg
  have hpay : ∀ o, pay (dirOf val l hist) e o (vreal v) = pay (dirOf val l hist) e' o (vreal v) := by
    intro o
    simp only [pay, hdir]
  unfold gain
  apply le_antisymm
  · refine le_minPay _ _ _ _ _ _ (fun o ho' => ?_)
    rw [← hpay o]
    exact minPay_le _ _ _ _ _ o ((ho o).2 ho')
  · refine le_minPay _ _ _ _ _ _ (fun o ho' => ?_)
    rw [hpay o]
    exact minPay_le _ _ _ _ _ o ((ho o).1 ho')

variable [Fintype V]

/-- **General principle.** Let `Agr cs` be a relation between experts that only gets weaker
when probes are removed from `cs` and that forces equal gains at every probe of `cs`. In a
valid run entered with wealth constant on the classes of `Agr pre`, the wealth before every
probe is constant on the classes of `Agr` for the probes completed before it. -/
theorem Exec.wealth_rel (A : Alg V)
    (Agr : List (Ctx ι) → Expert ι V k D → Expert ι V k D → Prop)
    (hmono : ∀ (cs cs' : List (Ctx ι)) (e e' : Expert ι V k D), Agr cs e e' →
      (∀ c ∈ cs', c ∈ cs) → Agr cs' e e')
    (hgain : ∀ (cs : List (Ctx ι)) (e e' : Expert ι V k D) (l : ℕ) (hist : ℕ → ι → ℝ)
      (y : ι → ℝ), Agr cs e e' → (⟨l, hist, y⟩ : Ctx ι) ∈ cs →
      ∀ v, gain A.val l hist y v e = gain A.val l hist y v e')
    (X : Exec ι (Expert ι V k D)) :
    ∀ (l : ℕ) (hist : ℕ → ι → ℝ) (wIn : Expert ι V k D → ℝ) (pre : List (Ctx ι)),
      X.Valid A l hist wIn →
      (∀ e e', Agr pre e e' → wIn e = wIn e') →
      X.ForallProbes (fun pre' _ _ _ w => ∀ e e', Agr pre' e e' → w e = w e') l hist pre ∧
        (∀ e e', Agr (pre ++ X.contexts l hist) e e' → X.wOut e = X.wOut e') := by
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
    have key : ∀ n, n ≤ T → ∀ e e',
        Agr (pre ++ before (nodeSegs T y child l hist) n) e e' → w n e = w n e' := by
      intro n
      induction n with
      | zero =>
        intro _ e e' h
        rw [hw0]
        exact hin e e' (hmono _ _ e e' h (fun c hc => by simp [before, hc]))
      | succ n ihn =>
        intro hn e e' h
        have hn' : n < T := hn
        obtain ⟨-, hchild, hstep⟩ := hprobe ⟨n, hn'⟩
        have hbs := before_succ (nodeSegs T y child l hist) ⟨n, hn'⟩
        simp only at hbs
        rw [hbs] at h
        have h1 : Agr (pre ++ before (nodeSegs T y child l hist) n) e e' :=
          hmono _ _ e e' h (fun c hc => by
            rcases List.mem_append.1 hc with hc | hc
            · exact List.mem_append.2 (Or.inl hc)
            · exact List.mem_append.2 (Or.inr (List.mem_append.2 (Or.inl hc))))
        have hwn := ihn (Nat.le_of_lt hn') e e' h1
        have hgain' := hgain _ e e' l hist (y ⟨n, hn'⟩) h
          (List.mem_append.2 (Or.inr (List.mem_append.2 (Or.inr (by simp [nodeSegs])))))
          (feedback (y ⟨n, hn'⟩) (child ⟨n, hn'⟩).x (z ⟨n, hn'⟩))
        have hcin : ∀ e e', Agr (pre ++ before (nodeSegs T y child l hist) n) e e' →
            A.c * w n e = A.c * w n e' := fun e e' h => by
          rw [ihn (Nat.le_of_lt hn') e e' h]
        have hcout := (ih ⟨n, hn'⟩ (l + 1) _ _ _ hchild hcin).2 e e'
          (hmono _ _ e e' h (fun c hc => by
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
        rw [hs, hs', hwn, hgain', hcout]
    refine ⟨fun τ => ⟨key τ (Nat.le_of_lt τ.2), ?_⟩, ?_⟩
    · exact (ih τ (l + 1) _ _ _ (hprobe τ).2.1 (fun e e' h => by
        rw [key τ (Nat.le_of_lt τ.2) e e' h])).1
    · intro e e' h
      rw [Exec.contexts_node] at h
      exact key T le_rfl e e' h

/-- **Wealth depends only on the best options.** At every probe of a valid run from the root
with unit wealth, two experts of the same group that had the same maximizing options at every
probe completed before have the same wealth. -/
theorem Exec.wealth_agreeMax (A : Alg V) (X : Exec ι (Expert ι V k D)) (hist₀ : ℕ → ι → ℝ)
    (hX : X.Valid A 0 hist₀ (fun _ => 1)) :
    X.ForallProbes (fun pre _ _ _ w => ∀ e e', AgreeMax A.val pre e e' → w e = w e')
      0 hist₀ [] :=
  (Exec.wealth_rel A (AgreeMax A.val)
    (fun _ _ _ _ h hsub => ⟨h.1, fun c hc => h.2 c (hsub c hc)⟩)
    (fun _ _ _ _ _ _ h hc v => gain_congr_argmax h.1 (h.2 _ hc) v)
    X 0 hist₀ (fun _ => 1) [] hX (fun _ _ _ => rfl)).1

end SPLP
