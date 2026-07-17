import GenLimit.Core.Basic

/-!
# Eventual stability of consistency under a target presentation

If `stream` presents `C z`, then a candidate which contains `C z` is
consistent at every time.  Conversely, every fixed candidate which does not
contain `C z` is eventually falsified by the stream.  This file makes the
second statement uniform over an arbitrary finite scope.

The resulting equivalence says that, after one finite threshold, consistency
inside the scope is a static property.  In particular, a candidate in the
scope which is consistent after that threshold remains consistent forever.
-/

namespace GenLimit

/-- For one fixed candidate, consistency eventually agrees with containment
of the presented target. -/
theorem candidate_eventually_consistent_iff_target_subset
    {C : LanguageFamily} {stream : ℕ → ℕ} {z i : ℕ}
    (hP : Presents stream (C z)) :
    ∃ T, ∀ t, T ≤ t →
      (Consistent C stream t i ↔ C z ⊆ C i) := by
  classical
  by_cases hsub : C z ⊆ C i
  · refine ⟨0, ?_⟩
    intro t _
    exact ⟨fun _ => hsub, fun _ => consistent_of_target_subset hP hsub⟩
  · obtain ⟨T, hT⟩ := eventually_not_consistent_of_not_subset hP hsub
    refine ⟨T, ?_⟩
    intro t ht
    constructor
    · intro hcon
      exact False.elim ((hT t ht) hcon)
    · intro hsub'
      exact False.elim (hsub hsub')

/-- Uniform finite-scope stabilization.  The scope `s` contains the indices
`i < s`; after one threshold, each such candidate is consistent exactly when
it contains the presented target. -/
theorem finite_scope_eventually_consistent_iff_target_subset
    {C : LanguageFamily} {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (C z)) (s : ℕ) :
    ∃ T, ∀ t, T ≤ t → ∀ i, i < s →
      (Consistent C stream t i ↔ C z ⊆ C i) := by
  induction s with
  | zero =>
      exact ⟨0, by omega⟩
  | succ s ih =>
      obtain ⟨Ts, hTs⟩ := ih
      obtain ⟨Ti, hTi⟩ :=
        candidate_eventually_consistent_iff_target_subset
          (C := C) (stream := stream) (z := z) (i := s) hP
      refine ⟨max Ts Ti, ?_⟩
      intro t ht i his
      have hTs_t : Ts ≤ t := le_trans (Nat.le_max_left Ts Ti) ht
      have hTi_t : Ti ≤ t := le_trans (Nat.le_max_right Ts Ti) ht
      rcases Nat.lt_succ_iff_lt_or_eq.mp his with his' | rfl
      · exact hTs t hTs_t i his'
      · exact hTi t hTi_t

/-- The stabilization statement requested for all candidates no later than
the target index. -/
theorem target_prefix_eventually_consistent_iff_target_subset
    {C : LanguageFamily} {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (C z)) :
    ∃ T, ∀ t, T ≤ t → ∀ i, i ≤ z →
      (Consistent C stream t i ↔ C z ⊆ C i) := by
  obtain ⟨T, hT⟩ :=
    finite_scope_eventually_consistent_iff_target_subset hP (z + 1)
  refine ⟨T, ?_⟩
  intro t ht i hiz
  exact hT t ht i (Nat.lt_succ_of_le hiz)

/-- Once finite-scope consistency has stabilized, any candidate which is
consistent at one time stays consistent at every later time. -/
theorem finite_scope_eventually_consistency_persistent
    {C : LanguageFamily} {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (C z)) (s : ℕ) :
    ∃ T, ∀ t, T ≤ t → ∀ u, t ≤ u → ∀ i, i < s →
      Consistent C stream t i → Consistent C stream u i := by
  obtain ⟨T, hT⟩ :=
    finite_scope_eventually_consistent_iff_target_subset hP s
  refine ⟨T, ?_⟩
  intro t ht u _ i his hcon
  have hsub : C z ⊆ C i := (hT t ht i his).1 hcon
  exact consistent_of_target_subset hP hsub

/-- After one finite threshold, any consistent candidate of index at most
`z` remains consistent at all later times. -/
theorem target_prefix_eventually_consistency_persistent
    {C : LanguageFamily} {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (C z)) :
    ∃ T, ∀ t, T ≤ t → ∀ u, t ≤ u → ∀ i, i ≤ z →
      Consistent C stream t i → Consistent C stream u i := by
  obtain ⟨T, hT⟩ :=
    finite_scope_eventually_consistency_persistent hP (z + 1)
  refine ⟨T, ?_⟩
  intro t ht u htu i hiz hcon
  exact hT t ht u htu i (Nat.lt_succ_of_le hiz) hcon

end GenLimit
