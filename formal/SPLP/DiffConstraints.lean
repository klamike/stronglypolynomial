import Mathlib

/-!
# Difference constraints are feasible exactly when no short closed walk is negative

A system `p i - p j ≤ w i j` over the pairs `(i, j)` of a finite set `E` has a real solution if
and only if every closed walk in `E` with at most `card ι` vertices has nonnegative total
weight. The closed walk through the vertices of a list `l`, in cyclic order, has the edges
`l.zip (l.rotate 1)`.

The proof of the substantial direction uses potentials: `p v` is the infimum of the weights of
all walks starting at `v`. This set is bounded below because a walk with a repeated vertex
contains a closed walk without repeated vertices (`exists_dup_decomp`), whose removal does not
increase the weight (`walk_lb`).
-/

namespace SPLP

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace DiffConstraints

/-- Weight of the walk `a, l₀, l₁, …`. -/
def wt (w : ι → ι → ℝ) : ι → List ι → ℝ
  | _, [] => 0
  | a, b :: l => w a b + wt w b l

/-- `a, l₀, l₁, …` is a walk in `E`. -/
def IsWalk (E : Finset (ι × ι)) : ι → List ι → Prop
  | _, [] => True
  | a, b :: l => (a, b) ∈ E ∧ IsWalk E b l

omit [Fintype ι] [DecidableEq ι] in
theorem wt_append_cons (w : ι → ι → ℝ) (a b : ι) (l₁ l₂ : List ι) :
    wt w a (l₁ ++ b :: l₂) = wt w a (l₁ ++ [b]) + wt w b l₂ := by
  induction l₁ generalizing a with
  | nil => simp [wt]
  | cons x t ih => simp [wt, ih, add_assoc]

omit [Fintype ι] [DecidableEq ι] in
theorem isWalk_append_cons (E : Finset (ι × ι)) (a b : ι) (l₁ l₂ : List ι) :
    IsWalk E a (l₁ ++ b :: l₂) ↔ IsWalk E a (l₁ ++ [b]) ∧ IsWalk E b l₂ := by
  induction l₁ generalizing a with
  | nil => simp [IsWalk]
  | cons x t ih => simp [IsWalk, ih, and_assoc]

omit [Fintype ι] [DecidableEq ι] in
theorem zip_wt (w : ι → ι → ℝ) (a b : ι) (l : List ι) :
    ((List.zip (a :: l) (l ++ [b])).map (fun e => w e.1 e.2)).sum = wt w a (l ++ [b]) := by
  induction l generalizing a with
  | nil => simp [wt]
  | cons x t ih =>
    have := ih x
    simp only [List.cons_append, List.zip_cons_cons, List.map_cons, List.sum_cons, wt] at this ⊢
    rw [this]

omit [Fintype ι] [DecidableEq ι] in
theorem zip_tele (p : ι → ℝ) (a b : ι) (l : List ι) :
    ((List.zip (a :: l) (l ++ [b])).map (fun e => p e.1 - p e.2)).sum = p a - p b := by
  induction l generalizing a with
  | nil => simp
  | cons x t ih =>
    have := ih x
    simp only [List.cons_append, List.zip_cons_cons, List.map_cons, List.sum_cons] at this ⊢
    rw [this]; ring

omit [Fintype ι] [DecidableEq ι] in
theorem zip_walk (E : Finset (ι × ι)) (a b : ι) (l : List ι) (h : IsWalk E a (l ++ [b])) :
    ∀ e ∈ List.zip (a :: l) (l ++ [b]), e ∈ E := by
  induction l generalizing a with
  | nil =>
    intro e he
    simp only [List.nil_append, List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at he
    subst he
    exact h.1
  | cons x t ih =>
    intro e he
    simp only [List.cons_append, List.zip_cons_cons, List.mem_cons] at he
    rcases he with rfl | he
    · exact h.1
    · exact ih x h.2 e he

omit [Fintype ι] [DecidableEq ι] in
theorem exists_dup_decomp : ∀ L : List ι, ¬ L.Nodup →
    ∃ l₁ c l₂ l₃, L = l₁ ++ c :: (l₂ ++ c :: l₃) ∧ (c :: l₂).Nodup := by
  intro L
  induction L with
  | nil => intro h; exact absurd List.nodup_nil h
  | cons x t ih =>
    intro h
    by_cases ht : t.Nodup
    · have hx : x ∈ t := by
        by_contra hx
        exact h (List.nodup_cons.2 ⟨hx, ht⟩)
      obtain ⟨as, bs, rfl, hxas⟩ := List.eq_append_cons_of_mem hx
      exact ⟨[], x, as, bs, rfl, List.nodup_cons.2 ⟨hxas, ht.of_append_left⟩⟩
    · obtain ⟨l₁, c, l₂, l₃, rfl, hnd⟩ := ih ht
      exact ⟨x :: l₁, c, l₂, l₃, rfl, hnd⟩

omit [Fintype ι] [DecidableEq ι] in
theorem wt_ge_length (E : Finset (ι × ι)) (w : ι → ι → ℝ) (M : ℝ)
    (hM : ∀ e ∈ E, -M ≤ w e.1 e.2) (a : ι) (l : List ι) (h : IsWalk E a l) :
    -(l.length * M) ≤ wt w a l := by
  induction l generalizing a with
  | nil => simp [wt]
  | cons x t ih =>
    have h1 := hM _ h.1
    have h2 := ih x h.2
    simp only [wt, List.length_cons, Nat.cast_add, Nat.cast_one] at h2 ⊢
    linarith

omit [DecidableEq ι] in
/-- The hypothesis of the main theorem, restated for a closed walk without repeated vertices. -/
theorem closed_nonneg (E : Finset (ι × ι)) (w : ι → ι → ℝ)
    (H : ∀ l : List ι, l ≠ [] → l.length ≤ Fintype.card ι →
      (∀ e ∈ l.zip (l.rotate 1), e ∈ E) →
      0 ≤ ((l.zip (l.rotate 1)).map (fun e => w e.1 e.2)).sum)
    (c : ι) (l : List ι) (hnd : (c :: l).Nodup) (hw : IsWalk E c (l ++ [c])) :
    0 ≤ wt w c (l ++ [c]) := by
  have hrot : (c :: l).rotate 1 = l ++ [c] := by
    rw [List.rotate_cons_succ, List.rotate_zero]
  have := H (c :: l) (List.cons_ne_nil _ _) hnd.length_le_card
    (by rw [hrot]; exact zip_walk E c c l hw)
  rwa [hrot, zip_wt] at this

/-- Every walk weighs at least `-(card ι * M)` if no short closed walk is negative. -/
theorem walk_lb (E : Finset (ι × ι)) (w : ι → ι → ℝ)
    (H : ∀ l : List ι, l ≠ [] → l.length ≤ Fintype.card ι →
      (∀ e ∈ l.zip (l.rotate 1), e ∈ E) →
      0 ≤ ((l.zip (l.rotate 1)).map (fun e => w e.1 e.2)).sum)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ e ∈ E, -M ≤ w e.1 e.2) :
    ∀ (k : ℕ) (a : ι) (l : List ι), l.length = k → IsWalk E a l →
      -(Fintype.card ι * M) ≤ wt w a l := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro a l hk hw
    by_cases hnd : (a :: l).Nodup
    · have h1 := wt_ge_length E w M hM a l hw
      have h2 : (l.length : ℝ) ≤ Fintype.card ι := by
        have := hnd.length_le_card
        simp only [List.length_cons] at this
        exact_mod_cast (by omega : l.length ≤ Fintype.card ι)
      nlinarith
    · obtain ⟨l₁, c, l₂, l₃, heq, hnd2⟩ := exists_dup_decomp _ hnd
      cases l₁ with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        rw [isWalk_append_cons] at hw
        rw [wt_append_cons]
        have h1 := closed_nonneg E w H a l₂ hnd2 hw.1
        have h2 := ih l₃.length (by rw [← hk]; simp only [List.length_append, List.length_cons]; omega) a l₃ rfl hw.2
        linarith
      | cons x l₁ =>
        simp only [List.cons_append, List.cons.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        rw [isWalk_append_cons E a c l₁, isWalk_append_cons E c c l₂] at hw
        rw [wt_append_cons w a c l₁, wt_append_cons w c c l₂]
        have h1 := closed_nonneg E w H c l₂ hnd2 hw.2.1
        have h2 := ih (l₁ ++ c :: l₃).length (by rw [← hk]; simp only [List.length_append, List.length_cons]; omega) a (l₁ ++ c :: l₃) rfl
          ((isWalk_append_cons E a c l₁ l₃).2 ⟨hw.1, hw.2.2⟩)
        rw [wt_append_cons] at h2
        linarith

end DiffConstraints

open DiffConstraints in
theorem diff_feasible_iff (E : Finset (ι × ι)) (w : ι → ι → ℝ) :
    (∃ p : ι → ℝ, ∀ e ∈ E, p e.1 - p e.2 ≤ w e.1 e.2) ↔
      ∀ l : List ι, l ≠ [] → l.length ≤ Fintype.card ι →
        (∀ e ∈ l.zip (l.rotate 1), e ∈ E) →
        0 ≤ ((l.zip (l.rotate 1)).map (fun e => w e.1 e.2)).sum := by
  constructor
  · rintro ⟨p, hp⟩ l hl - hE
    obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hl
    have hrot : (a :: t).rotate 1 = t ++ [a] := by
      rw [List.rotate_cons_succ, List.rotate_zero]
    rw [hrot] at hE ⊢
    have h0 := zip_tele p a a t
    have hle : ((List.zip (a :: t) (t ++ [a])).map (fun e => p e.1 - p e.2)).sum ≤
        ((List.zip (a :: t) (t ++ [a])).map (fun e => w e.1 e.2)).sum :=
      List.sum_le_sum fun e he => hp e (hE e he)
    linarith
  · intro H
    set M : ℝ := ∑ e ∈ E, |w e.1 e.2| with hMdef
    have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hM : ∀ e ∈ E, -M ≤ w e.1 e.2 := by
      intro e he
      have h1 : |w e.1 e.2| ≤ M :=
        Finset.single_le_sum (f := fun e : ι × ι => |w e.1 e.2|)
          (fun _ _ => abs_nonneg _) he
      have h2 := neg_abs_le (w e.1 e.2)
      linarith
    let S : ι → Set ℝ := fun v => {x | ∃ l, IsWalk E v l ∧ wt w v l = x}
    have hne : ∀ v, (S v).Nonempty := fun v => ⟨0, [], trivial, rfl⟩
    have hbdd : ∀ v, BddBelow (S v) := by
      intro v
      refine ⟨-(Fintype.card ι * M), ?_⟩
      rintro x ⟨l, hl, rfl⟩
      exact walk_lb E w H M hM0 hM l.length v l rfl hl
    refine ⟨fun v => sInf (S v), ?_⟩
    rintro ⟨a, b⟩ hab
    have key : sInf (S a) - w a b ≤ sInf (S b) := by
      refine le_csInf (hne b) ?_
      rintro x ⟨l, hl, rfl⟩
      have : sInf (S a) ≤ w a b + wt w b l :=
        csInf_le (hbdd a) ⟨b :: l, ⟨hab, hl⟩, rfl⟩
      linarith
    show sInf (S a) - sInf (S b) ≤ w a b
    linarith

/-! ### Feasibility depends only on the signs of short integer forms

The weights are integer affine forms in data `y : m → ℝ`: a form is a function `Option m → ℤ`,
with its constant at `none`. If every edge form has 1-norm at most `A`, the weight of a closed
walk with at most `card ι` vertices is a form of 1-norm at most `card ι * A`. So feasibility at
data `g` passes to any data `f` on which all forms of that norm that are nonnegative at `g` are
nonnegative. A general elimination of `card ι` unknowns (the preprint's Lemma 4.1) needs
agreement up to norm `(card ι + 1) A^(card ι + 1)`. -/

/-- Value of an integer affine form at `y`. -/
def evalForm {m : Type*} [Fintype m] (y : m → ℝ) (F : Option m → ℤ) : ℝ :=
  F none + ∑ u, (F (some u) : ℝ) * y u

/-- The 1-norm of an integer affine form, constant included. -/
def normForm {m : Type*} [Fintype m] (F : Option m → ℤ) : ℕ := ∑ o, (F o).natAbs

theorem evalForm_list_sum {m : Type*} [Fintype m] (y : m → ℝ) (L : List (Option m → ℤ)) :
    evalForm y L.sum = (L.map (evalForm y)).sum := by
  induction L with
  | nil => simp [evalForm]
  | cons F L ih =>
    rw [List.sum_cons, List.map_cons, List.sum_cons, ← ih]
    simp only [evalForm, Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]
    ring

theorem normForm_list_sum_le {m : Type*} [Fintype m] (L : List (Option m → ℤ)) (A : ℕ)
    (hL : ∀ F ∈ L, normForm F ≤ A) : normForm L.sum ≤ L.length * A := by
  induction L with
  | nil => simp [normForm]
  | cons F L ih =>
    have h1 : normForm (F + L.sum) ≤ normForm F + normForm L.sum := by
      simp only [normForm, Pi.add_apply, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum (fun o _ => Int.natAbs_add_le _ _)
    have h2 := ih (fun G hG => hL G (List.mem_cons_of_mem _ hG))
    have h3 := hL F List.mem_cons_self
    rw [List.sum_cons, List.length_cons]
    nlinarith

/-- **Difference constraints transfer along sign agreement at norm `card ι * A`.** -/
theorem diff_feasible_of_type {m : Type*} [Fintype m] (E : Finset (ι × ι))
    (F : ι → ι → Option m → ℤ) (A : ℕ) (hF : ∀ e ∈ E, normForm (F e.1 e.2) ≤ A)
    (f g : m → ℝ)
    (htype : ∀ G : Option m → ℤ, normForm G ≤ Fintype.card ι * A →
      0 ≤ evalForm g G → 0 ≤ evalForm f G)
    (hg : ∃ p : ι → ℝ, ∀ e ∈ E, p e.1 - p e.2 ≤ evalForm g (F e.1 e.2)) :
    ∃ p : ι → ℝ, ∀ e ∈ E, p e.1 - p e.2 ≤ evalForm f (F e.1 e.2) := by
  rw [diff_feasible_iff E (fun i j => evalForm g (F i j))] at hg
  rw [diff_feasible_iff E (fun i j => evalForm f (F i j))]
  intro l hl hlen hE
  have key : ∀ y : m → ℝ, ((l.zip (l.rotate 1)).map (fun e => evalForm y (F e.1 e.2))).sum
      = evalForm y ((l.zip (l.rotate 1)).map (fun e => F e.1 e.2)).sum := by
    intro y
    rw [evalForm_list_sum, List.map_map]
    rfl
  rw [key]
  refine htype _ ?_ ?_
  · refine (normForm_list_sum_le _ A ?_).trans ?_
    · intro G hG
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hG
      exact hF e (hE e he)
    · refine Nat.mul_le_mul_right _ ?_
      rw [List.length_map, List.length_zip, List.length_rotate, min_self]
      exact hlen
  · rw [← key]
    exact hg l hl hlen hE

end SPLP
