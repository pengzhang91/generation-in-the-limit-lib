import GenLimit.Paper12_NoiseLossAndFeedback.InfiniteOmissions
import GenLimit.Paper15_PartialEnumeration.FiniteScope

/-!
# Bridge from Paper 12 infinite omissions to Paper 15 partial enumeration

Paper 15 presents an infinite set contained in the true target, with
repetitions allowed. Paper 12's "enumeration with infinite omissions" is the
repetition-free special case: its stream is additionally injective. These
comparison theorems are kept outside both native paper developments.
-/

namespace GenLimit.Bridge.Paper12ToPaper15

/-- Paper 12's observation model is the injective fragment of the shared
infinite-partial-presentation model used by Paper 15. -/
theorem infiniteOmissionEnumeration_iff_injective_infinitePartialPresentation
    (stream : Generic.Stream ℕ) (K : Generic.Language ℕ) :
    NoiseLossFeedback.InfiniteOmissionEnumeration stream K ↔
      Function.Injective stream ∧ InfinitePartialPresentation stream K := by
  constructor
  · rintro ⟨hinjective, hsub⟩
    exact ⟨hinjective, Set.infinite_range_of_injective hinjective, hsub⟩
  · rintro ⟨hinjective, _hrange, hsub⟩
    exact ⟨hinjective, hsub⟩

/-- The same bridge in Paper 15's explicit named-sublanguage formulation. -/
theorem infiniteOmissionEnumeration_iff_injective_exists_presented_subset
    (stream : Generic.Stream ℕ) (K : Generic.Language ℕ) :
    NoiseLossFeedback.InfiniteOmissionEnumeration stream K ↔
      Function.Injective stream ∧
        ∃ E : Language,
          Presents stream E ∧ E.Infinite ∧ E ⊆ K := by
  rw [infiniteOmissionEnumeration_iff_injective_infinitePartialPresentation,
    infinitePartialPresentation_iff_exists_presented_subset]

end GenLimit.Bridge.Paper12ToPaper15
