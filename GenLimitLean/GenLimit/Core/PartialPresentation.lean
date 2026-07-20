import GenLimit.Core.Basic

/-!
# Partial presentations

The partial-enumeration model presents an infinite set `E` contained in the
true language, but `E` need not itself occur in the indexed family. This
module records presentation-relative consistency facts without assuming that
the presented set has a family index.
-/

namespace GenLimit

/-- A candidate containing the presented set is consistent at every time. -/
theorem consistent_of_presented_subset
    {C : LanguageFamily} {stream : ℕ → ℕ} {E : Language} {i t : ℕ}
    (hP : Presents stream E) (hsub : E ⊆ C i) :
    Consistent C stream t i := by
  intro u hu
  exact hsub (mem_language_of_mem_sample_of_presents hP hu)

/-- A fixed candidate not containing the presented set is eventually
inconsistent. -/
theorem eventually_not_consistent_of_not_presented_subset
    {C : LanguageFamily} {stream : ℕ → ℕ} {E : Language} {i : ℕ}
    (hP : Presents stream E) (hbad : ¬ E ⊆ C i) :
    ∃ T, ∀ t, T ≤ t → ¬ Consistent C stream t i := by
  obtain ⟨u, huE, hui⟩ := Set.not_subset.mp hbad
  obtain ⟨T, hT⟩ := eventually_mem_sample_of_presents hP huE
  refine ⟨T, ?_⟩
  intro t ht hcon
  exact hui (hcon (hT t ht))

/-- For one fixed candidate, consistency eventually agrees with containment
of the presented set. -/
theorem candidate_eventually_consistent_iff_presented_subset
    {C : LanguageFamily} {stream : ℕ → ℕ} {E : Language} {i : ℕ}
    (hP : Presents stream E) :
    ∃ T, ∀ t, T ≤ t → (Consistent C stream t i ↔ E ⊆ C i) := by
  classical
  by_cases hsub : E ⊆ C i
  · exact ⟨0, fun _ _ =>
      ⟨fun _ => hsub, fun _ => consistent_of_presented_subset hP hsub⟩⟩
  · obtain ⟨T, hT⟩ :=
      eventually_not_consistent_of_not_presented_subset hP hsub
    refine ⟨T, ?_⟩
    intro t ht
    exact ⟨fun hcon => False.elim ((hT t ht) hcon),
      fun hsub' => False.elim (hsub hsub')⟩

/-- Uniform stabilization of consistency on a finite index prefix. -/
theorem finite_scope_eventually_consistent_iff_presented_subset
    {C : LanguageFamily} {stream : ℕ → ℕ} {E : Language}
    (hP : Presents stream E) (s : ℕ) :
    ∃ T, ∀ t, T ≤ t → ∀ i, i < s →
      (Consistent C stream t i ↔ E ⊆ C i) := by
  induction s with
  | zero => exact ⟨0, by omega⟩
  | succ s ih =>
      obtain ⟨Ts, hTs⟩ := ih
      obtain ⟨Ti, hTi⟩ :=
        candidate_eventually_consistent_iff_presented_subset
          (C := C) (stream := stream) (E := E) (i := s) hP
      refine ⟨max Ts Ti, ?_⟩
      intro t ht i his
      rcases Nat.lt_succ_iff_lt_or_eq.mp his with his' | rfl
      · exact hTs t (le_trans (Nat.le_max_left _ _) ht) i his'
      · exact hTi t (le_trans (Nat.le_max_right _ _) ht)

end GenLimit
