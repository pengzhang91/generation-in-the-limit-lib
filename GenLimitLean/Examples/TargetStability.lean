import GenLimit.Core.TargetStability

/-!
# Example: specialize finite-prefix stabilization

The Core theorem stabilizes every candidate up to the target index at once.
This example shows how a client can specialize that result to one fixed
candidate and obtain persistence at every later time.
-/

namespace GenLimit.Examples

theorem fixed_prefix_candidate_eventually_stays_consistent
    {C : LanguageFamily} {stream : ℕ → ℕ} {z i : ℕ}
    (hP : Presents stream (C z)) (hi : i ≤ z) :
    ∃ T, ∀ t, T ≤ t → ∀ u, t ≤ u →
      Consistent C stream t i → Consistent C stream u i := by
  obtain ⟨T, hstable⟩ :=
    target_prefix_eventually_consistency_persistent
      (C := C) (stream := stream) (z := z) hP
  refine ⟨T, ?_⟩
  intro t ht u htu
  exact hstable t ht u htu i hi

end GenLimit.Examples
