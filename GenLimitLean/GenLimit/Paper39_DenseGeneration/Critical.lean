import GenLimit.Core.TargetStability
import Mathlib.Data.Finset.Max

/-!
# Recursive criticality for the patient-scope algorithm

This file records Definition 3.2 of the patient-scope manuscript.  Its
recursive notion of criticality compares a language only with earlier
*critical* languages.  Its eventual target theorem is derived directly from
the shared finite-scope stability of consistency.  Comparisons with KM
criticality live in the explicit cross-development bridge module.

Indices are zero-based.  Thus a scope of size `s` contains precisely the
indices in `Finset.range s`.
-/

namespace GenLimit

/-- Definition 3.2: recursive criticality in increasing index order. -/
def RecursiveCritical (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) : ℕ → Prop
  | 0 => Consistent C stream t 0
  | n + 1 =>
      Consistent C stream t (n + 1) ∧
        ∀ j, j ≤ n → RecursiveCritical C stream t j → C (n + 1) ⊆ C j

theorem recursiveCritical_consistent
    {C : LanguageFamily} {stream : ℕ → ℕ} {t n : ℕ}
    (h : RecursiveCritical C stream t n) : Consistent C stream t n := by
  cases n with
  | zero => simpa [RecursiveCritical] using h
  | succ n =>
      have h' : Consistent C stream t (n + 1) ∧
          ∀ j, j ≤ n → RecursiveCritical C stream t j → C (n + 1) ⊆ C j := by
        simpa [RecursiveCritical] using h
      exact h'.1

/-- The critical languages form a descending inclusion chain (Remark 3.3). -/
theorem recursiveCritical_subset_of_le
    {C : LanguageFamily} {stream : ℕ → ℕ} {t i j : ℕ}
    (hij : i ≤ j)
    (hi : RecursiveCritical C stream t i)
    (hj : RecursiveCritical C stream t j) : C j ⊆ C i := by
  rcases eq_or_lt_of_le hij with rfl | hij
  · exact Set.Subset.rfl
  · cases j with
    | zero => omega
    | succ j =>
        have hj' : Consistent C stream t (j + 1) ∧
            ∀ k, k ≤ j → RecursiveCritical C stream t k → C (j + 1) ⊆ C k := by
          simpa [RecursiveCritical] using hj
        exact hj'.2 i (Nat.le_of_lt_succ hij) hi

/-- Lemma 3.4.  Once consistency in the target prefix has stabilized, every
earlier recursively critical language is consistent and hence contains the
target. -/
theorem target_eventually_recursiveCritical
    {C : LanguageFamily} {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (C z)) :
    ∃ T, ∀ t, T ≤ t → RecursiveCritical C stream t z := by
  obtain ⟨T, hT⟩ :=
    target_prefix_eventually_consistent_iff_target_subset hP
  refine ⟨T, ?_⟩
  intro t ht
  cases z with
  | zero =>
      simpa only [RecursiveCritical] using presents_consistent (t := t) hP
  | succ n =>
      rw [RecursiveCritical]
      refine ⟨presents_consistent hP, ?_⟩
      intro j hj hjcrit
      have hjz : j ≤ n + 1 := Nat.le_trans hj (Nat.le_succ n)
      exact (hT t ht j hjz).1 (recursiveCritical_consistent hjcrit)

/-- `f` is the highest-indexed critical language in the first `s` entries. -/
def IsFocus
    (C : LanguageFamily) (stream : ℕ → ℕ) (t s f : ℕ) : Prop :=
  f < s ∧ RecursiveCritical C stream t f ∧
    ∀ j, j < s → RecursiveCritical C stream t j → j ≤ f

/-- A focus exists whenever a critical language lies inside the scope. -/
theorem exists_focus_of_critical_in_scope
    {C : LanguageFamily} {stream : ℕ → ℕ} {t s z : ℕ}
    (hzs : z < s) (hz : RecursiveCritical C stream t z) :
    ∃ f, IsFocus C stream t s f := by
  classical
  let candidates := (Finset.range s).filter (RecursiveCritical C stream t)
  have hne : candidates.Nonempty := by
    refine ⟨z, ?_⟩
    simp [candidates, hzs, hz]
  refine ⟨candidates.max' hne, ?_⟩
  have hmem := candidates.max'_mem hne
  have hparts : candidates.max' hne < s ∧
      RecursiveCritical C stream t (candidates.max' hne) := by
    simpa [candidates] using hmem
  refine ⟨hparts.1, hparts.2, ?_⟩
  intro j hjs hj
  apply Finset.le_max' candidates j
  simp [candidates, hjs, hj]

/-- If a recursively critical index `z` lies inside the scope, the focus
language is contained in `C z`.  In the validity proof, `z` is instantiated
with the target index.  This is the set-theoretic step used in Lemma 3.11. -/
theorem focus_subset_target
    {C : LanguageFamily} {stream : ℕ → ℕ} {t s f z : ℕ}
    (hf : IsFocus C stream t s f)
    (hzs : z < s) (hz : RecursiveCritical C stream t z) :
    C f ⊆ C z := by
  have hzf : z ≤ f := hf.2.2 z hzs hz
  exact recursiveCritical_subset_of_le hzf hz hf.2.1

end GenLimit
