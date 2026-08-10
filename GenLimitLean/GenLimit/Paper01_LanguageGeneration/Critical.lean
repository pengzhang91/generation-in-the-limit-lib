import GenLimit.Core.TargetStability

/-!
# #01 Language Generation: critical languages

This file contains KM's semantic notion of criticality and the theorem that the
target is eventually critical.  The finite-prefix approximation used by the
membership-query implementation lives in
`GenLimit.Paper01_LanguageGeneration.FiniteQuery.Critical`.
-/

namespace GenLimit

/-- Among candidates no later than `n`, every consistent language contains
the whole of `C n`. -/
def Critical (C : LanguageFamily) (stream : ℕ → ℕ) (t n : ℕ) : Prop :=
  Consistent C stream t n ∧
    ∀ i, i ≤ n → Consistent C stream t i → C n ⊆ C i

/-- KM-critical languages form a descending inclusion chain. -/
theorem critical_subset_of_le
    {C : LanguageFamily} {stream : ℕ → ℕ} {t i j : ℕ}
    (hij : i ≤ j) (hi : Critical C stream t i)
    (hj : Critical C stream t j) : C j ⊆ C i :=
  hj.2 i hij hi.1

/-- The least consistent candidate is KM-critical. -/
theorem least_consistent_critical
    {C : LanguageFamily} {stream : ℕ → ℕ} {t n : ℕ}
    (hn : Consistent C stream t n)
    (hleast : ∀ i, i < n → ¬ Consistent C stream t i) :
    Critical C stream t n := by
  refine ⟨hn, ?_⟩
  intro i hin hicon
  rcases eq_or_lt_of_le hin with rfl | hil
  · exact Set.Subset.rfl
  · exact False.elim ((hleast i hil) hicon)

/-- All earlier indices that fail to contain the target are eventually
inconsistent. The finite maximum is handled uniformly, including when there
are no such indices. -/
theorem bad_earlier_eventually_inconsistent
    {C : LanguageFamily} {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (C z)) :
    ∃ T, ∀ t, T ≤ t → ∀ i, i < z →
      ¬ C z ⊆ C i → ¬ Consistent C stream t i := by
  obtain ⟨T, hT⟩ :=
    target_prefix_eventually_consistent_iff_target_subset hP
  refine ⟨T, ?_⟩
  intro t ht i hiz hbad hcon
  exact hbad ((hT t ht i (Nat.le_of_lt hiz)).1 hcon)

/-- The target language is eventually critical. This is the semantic core of
equation (5.2). -/
theorem target_eventually_critical
    {C : LanguageFamily} {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (C z)) :
    ∃ T, ∀ t, T ≤ t → Critical C stream t z := by
  classical
  obtain ⟨T, hT⟩ := bad_earlier_eventually_inconsistent hP
  refine ⟨T, ?_⟩
  intro t ht
  refine ⟨presents_consistent hP, ?_⟩
  intro i hiz hicon
  rcases eq_or_lt_of_le hiz with rfl | hiz'
  · exact fun _ hu => hu
  · by_contra hIncl
    exact (hT t ht i hiz' hIncl) hicon

end GenLimit
