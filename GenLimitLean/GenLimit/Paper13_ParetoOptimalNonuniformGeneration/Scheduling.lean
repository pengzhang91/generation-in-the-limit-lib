import GenLimit.Paper13_ParetoOptimalNonuniformGeneration.Order
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Find
import Mathlib.Data.Set.Finite.Basic

/-!
# The finite-sublevel scheduler from Theorem 5

This file isolates and proves the exact scheduling argument used in Theorem 5
of arXiv:2510.02795v1.  If only finitely many languages have canonical
complexity at most each time budget, their largest index defines a
nondecreasing, unbounded scope.  Every language enters that scope no later
than its canonical generation time.
-/

namespace GenLimit.ParetoGeneration

/-- The sufficient condition printed in Theorem 5, with the paper's
`m⋆(L_i)+1` written as `complexity i + 1`. -/
def FiniteSublevels (complexity : ℕ → ℕ) : Prop :=
  ∀ t, ({i | complexity i + 1 ≤ t} : Set ℕ).Finite

/-- The finite set of indices eligible at budget `t`. -/
noncomputable def eligible
    (complexity : ℕ → ℕ) (hfinite : FiniteSublevels complexity)
    (t : ℕ) : Finset ℕ :=
  (hfinite t).toFinset

@[simp] theorem mem_eligible
    {complexity : ℕ → ℕ} {hfinite : FiniteSublevels complexity}
    {t i : ℕ} :
    i ∈ eligible complexity hfinite t ↔ complexity i + 1 ≤ t := by
  exact (hfinite t).mem_toFinset

/-- The paper's `f(t)`, with `0` inserted to make the empty-sublevel
convention explicit. -/
noncomputable def scope
    (complexity : ℕ → ℕ) (hfinite : FiniteSublevels complexity)
    (t : ℕ) : ℕ := by
  classical
  let candidates := insert 0 (eligible complexity hfinite t)
  exact candidates.max' ⟨0, Finset.mem_insert_self 0 _⟩

theorem le_scope_of_eligible
    {complexity : ℕ → ℕ} {hfinite : FiniteSublevels complexity}
    {t i : ℕ} (hi : complexity i + 1 ≤ t) :
    i ≤ scope complexity hfinite t := by
  classical
  let candidates := insert 0 (eligible complexity hfinite t)
  have himem : i ∈ candidates := by
    apply Finset.mem_insert_of_mem
    exact mem_eligible.mpr hi
  simpa [scope, candidates] using
    (Finset.le_max' candidates i himem)

theorem scope_mono
    {complexity : ℕ → ℕ} {hfinite : FiniteSublevels complexity}
    {s t : ℕ} (hst : s ≤ t) :
    scope complexity hfinite s ≤ scope complexity hfinite t := by
  classical
  let left := insert 0 (eligible complexity hfinite s)
  have hne : left.Nonempty := ⟨0, Finset.mem_insert_self 0 _⟩
  rw [show scope complexity hfinite s = left.max' hne by
    simp [scope, left]]
  apply Finset.max'_le
  intro i hi
  rcases Finset.mem_insert.mp hi with rfl | hi
  · exact Nat.zero_le _
  · exact le_scope_of_eligible
      (le_trans (mem_eligible.mp hi) hst)

/-- Every index is in scope by its canonical time. -/
theorem index_in_scope_by_complexity
    (complexity : ℕ → ℕ) (hfinite : FiniteSublevels complexity)
    (i : ℕ) :
    i ≤ scope complexity hfinite (complexity i + 1) :=
  le_scope_of_eligible (le_refl _)

theorem scope_unbounded
    (complexity : ℕ → ℕ) (hfinite : FiniteSublevels complexity) :
    ∀ i, ∃ t, i ≤ scope complexity hfinite t := by
  intro i
  exact ⟨complexity i + 1, index_in_scope_by_complexity complexity hfinite i⟩

/-- The paper's generalized inverse `g(i)`, the first time index `i` is in
scope. -/
noncomputable def entryTime
    (complexity : ℕ → ℕ) (hfinite : FiniteSublevels complexity)
    (i : ℕ) : ℕ :=
  Nat.find (scope_unbounded complexity hfinite i)

theorem entryTime_spec
    (complexity : ℕ → ℕ) (hfinite : FiniteSublevels complexity)
    (i : ℕ) :
    i ≤ scope complexity hfinite
      (entryTime complexity hfinite i) :=
  Nat.find_spec (scope_unbounded complexity hfinite i)

/-- Key inequality in Theorem 5: `g(i) ≤ m⋆(L_i)+1`. -/
theorem entryTime_le_complexity_add_one
    (complexity : ℕ → ℕ) (hfinite : FiniteSublevels complexity)
    (i : ℕ) :
    entryTime complexity hfinite i ≤ complexity i + 1 := by
  exact Nat.find_min' (H := scope_unbounded complexity hfinite i)
    (index_in_scope_by_complexity complexity hfinite i)

/-- Therefore the Section 3.2 bound
`max(g(i),m⋆(L_i)+1)` collapses to the canonical time. -/
theorem theorem_5_scheduling_identity
    (complexity : ℕ → ℕ) (hfinite : FiniteSublevels complexity)
    (i : ℕ) :
    max (entryTime complexity hfinite i) (complexity i + 1) =
      complexity i + 1 := by
  exact max_eq_right
    (entryTime_le_complexity_add_one complexity hfinite i)

end GenLimit.ParetoGeneration
