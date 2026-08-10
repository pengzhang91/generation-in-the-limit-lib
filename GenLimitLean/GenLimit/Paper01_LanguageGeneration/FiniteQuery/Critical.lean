import GenLimit.Paper01_LanguageGeneration.Critical

/-!
# #01 Language Generation: finite-prefix criticality

This module contains the cutoff approximation to semantic KM criticality used
by the finite membership-query implementation.  A cutoff `m` denotes the
strict universe prefix `{u | u < m}`. Candidate eligibility (`n < t`) remains
separate from criticality itself.
-/

namespace GenLimit

/-- Criticality restricted to the finite universe prefix `{u | u < m}`. -/
def FinitelyCritical
    (C : LanguageFamily) (stream : ℕ → ℕ) (t m n : ℕ) : Prop :=
  Consistent C stream t n ∧
    ∀ i, i ≤ n → Consistent C stream t i →
      ∀ u, u < m → u ∈ C n → u ∈ C i

theorem critical_finitelyCritical
    {C : LanguageFamily} {stream : ℕ → ℕ} {t n : ℕ}
    (h : Critical C stream t n) (m : ℕ) :
    FinitelyCritical C stream t m n := by
  rcases h with ⟨hncon, hmin⟩
  refine ⟨hncon, ?_⟩
  intro i hin hicon u _ hun
  exact hmin i hin hicon hun

/-- Equation (5.4), with a non-strict cutoff comparison. -/
theorem finitelyCritical_cutoff_mono
    {C : LanguageFamily} {stream : ℕ → ℕ} {t m m' n : ℕ}
    (hmm' : m' ≤ m) (h : FinitelyCritical C stream t m n) :
    FinitelyCritical C stream t m' n := by
  rcases h with ⟨hncon, hmin⟩
  refine ⟨hncon, ?_⟩
  intro i hin hicon u hum' hun
  exact hmin i hin hicon u (lt_of_lt_of_le hum' hmm') hun

/-- Equation (5.3): later finite-critical candidates have smaller prefixes. -/
theorem finitelyCritical_prefix_subset
    {C : LanguageFamily} {stream : ℕ → ℕ} {t m i j : ℕ}
    (hij : i ≤ j)
    (hi : FinitelyCritical C stream t m i)
    (hj : FinitelyCritical C stream t m j) :
    ∀ u, u < m → u ∈ C j → u ∈ C i := by
  exact hj.2 i hij hi.1

/-- The least consistent candidate is finite-critical at every cutoff. -/
theorem least_consistent_finitelyCritical
    {C : LanguageFamily} {stream : ℕ → ℕ} {t n : ℕ}
    (hn : Consistent C stream t n)
    (hleast : ∀ i, i < n → ¬ Consistent C stream t i) (m : ℕ) :
    FinitelyCritical C stream t m n := by
  exact critical_finitelyCritical (least_consistent_critical hn hleast) m

/-- Equation (5.2): the target is eventually finite-critical at every cutoff. -/
theorem target_eventually_finitelyCritical
    {C : LanguageFamily} {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (C z)) :
    ∃ T, ∀ t, T ≤ t → ∀ m, FinitelyCritical C stream t m z := by
  obtain ⟨T, hT⟩ := target_eventually_critical hP
  refine ⟨T, ?_⟩
  intro t ht m
  exact critical_finitelyCritical (hT t ht) m

end GenLimit
