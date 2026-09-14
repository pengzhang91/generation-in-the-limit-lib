import GenLimit.Paper05_HallucinationsBreadthAndStability.Definitions

/-!
# Semantic boundary of the raw support-validity predicate

The source-facing `IsLimitGenerator` predicate requires every generated
element to be valid and unseen, but it imposes no lower bound on the output
support.  The empty support therefore satisfies that raw predicate for every
language family.

The regression theorems below make this boundary executable and visible to
API users.  They do not change the source definition: exact breadth,
approximate breadth on an infinite target, and infinite coverage continue to
exclude the empty-support behavior.
-/

namespace GenLimit.BreadthCharacterizations

open GenLimit.Generic

/-- The diagnostic generator whose support is always empty. -/
def emptySupportAlgorithm : SupportAlgorithm α :=
  fun _history => ∅

@[simp] theorem supportAt_emptySupportAlgorithm
    (stream : Generic.Stream α) (t : ℕ) :
    supportAt emptySupportAlgorithm stream t = ∅ := by
  rfl

/-- Empty output satisfies the raw, validity-only stage predicate. -/
theorem emptySupportAlgorithm_generatesInLimitCorrectAt
    (K : Generic.Language α) (stream : Generic.Stream α) (t : ℕ) :
    GeneratesInLimitCorrectAt emptySupportAlgorithm K stream t := by
  simp [GeneratesInLimitCorrectAt]

/-- Semantic regression: the raw `IsLimitGenerator` predicate alone does not
require a generator to output anything. -/
theorem emptySupportAlgorithm_isLimitGenerator
    (F : Generic.LanguageFamily α) :
    IsLimitGenerator emptySupportAlgorithm F := by
  intro z stream _hP
  exact ⟨0, fun t _ht =>
    emptySupportAlgorithm_generatesInLimitCorrectAt (F z) stream t⟩

/-- On an infinite target, empty support cannot equal the unseen remainder of
the target after a finite sample. -/
theorem emptySupportAlgorithm_not_exactBreadthCorrectAt
    {K : Generic.Language α} (hK : K.Infinite)
    (stream : Generic.Stream α) (t : ℕ) :
    ¬ ExactBreadthCorrectAt emptySupportAlgorithm K stream t := by
  classical
  intro hExact
  obtain ⟨x, hxK, hxNotSample⟩ :=
    hK.exists_notMem_finset (Generic.sample stream t)
  have hxUnseen :
      x ∈ K \ (↑(Generic.sample stream t) : Set α) :=
    ⟨hxK, hxNotSample⟩
  have hxEmpty : x ∈ (∅ : Set α) := by
    rw [show (∅ : Set α) =
        K \ (↑(Generic.sample stream t) : Set α) by
      simpa [ExactBreadthCorrectAt] using hExact]
    exact hxUnseen
  exact hxEmpty

/-- On an infinite target, empty support cannot have approximate breadth:
it omits the entire infinite target. -/
theorem emptySupportAlgorithm_not_approximateBreadthCorrectAt
    {K : Generic.Language α} (hK : K.Infinite)
    (stream : Generic.Stream α) (t : ℕ) :
    ¬ ApproximateBreadthCorrectAt emptySupportAlgorithm K stream t := by
  intro hApprox
  apply hK
  simpa [ApproximateBreadthCorrectAt] using hApprox.2

/-- Empty support never has infinite coverage. -/
theorem emptySupportAlgorithm_not_infiniteCoverageCorrectAt
    (K : Generic.Language α) (stream : Generic.Stream α) (t : ℕ) :
    ¬ InfiniteCoverageCorrectAt emptySupportAlgorithm K stream t := by
  intro hCoverage
  simpa [InfiniteCoverageCorrectAt] using hCoverage.2.2

end GenLimit.BreadthCharacterizations
