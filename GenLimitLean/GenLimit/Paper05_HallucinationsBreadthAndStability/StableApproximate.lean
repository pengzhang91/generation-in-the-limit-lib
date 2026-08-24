import GenLimit.Paper05_HallucinationsBreadthAndStability.ExactBreadth
import GenLimit.Paper05_HallucinationsBreadthAndStability.Relationships

/-!
# Stable approximate breadth

The approximate-breadth clause of source Theorem 3.15 is coherent under the
literal arXiv-v2 definitions: approximate support may contain observed target
elements and can therefore become constant.  Its necessity direction reuses
P03's stable-approximate-to-identification reduction through the explicit
semantic adapter in `Relationships.lean`; its sufficiency direction reuses
P05 exact breadth after restoring the observed sample.
-/

namespace GenLimit.BreadthCharacterizations

open GenLimit.Generic

/-- Eventual whole-target support has approximate breadth. -/
theorem wholeTargetGenerator_implies_approximate
    {G : SupportAlgorithm α} {F : Generic.LanguageFamily α}
    (hWhole : IsWholeTargetGenerator G F) :
    IsApproximateBreadthGenerator G F := by
  intro z stream hP
  obtain ⟨T, hT⟩ := hWhole z stream hP
  refine ⟨T, ?_⟩
  intro t ht
  have hsupport : supportAt G stream t = F z := by
    simpa [WholeTargetCorrectAt] using hT t ht
  simp [ApproximateBreadthCorrectAt, hsupport]

/-- Angluin's condition gives a single raw-stable whole-target generator,
hence a stable approximate-breadth generator. -/
theorem conditionTwo_implies_stableApproximate
    {F : Generic.LanguageFamily α}
    (h : GenLimit.Angluin.ConditionTwo F) :
    ∃ G : SupportAlgorithm α,
      IsStableGenerator G F ∧ IsApproximateBreadthGenerator G F := by
  let G := restoreObserved (exactBreadthFromConditionTwo h)
  have hWhole : IsWholeTargetGenerator G F :=
    literalExact_implies_wholeTarget
      (conditionTwo_implies_literalExact h)
  refine ⟨G, ?_, wholeTargetGenerator_implies_approximate hWhole⟩
  intro z stream hP
  obtain ⟨T, hT⟩ := hWhole z stream hP
  refine ⟨T, ?_⟩
  intro n n' hn hn'
  rw [show supportAt G stream n = F z by
        simpa [WholeTargetCorrectAt] using hT n hn,
      show supportAt G stream n' = F z by
        simpa [WholeTargetCorrectAt] using hT n' hn']

/-- The coherent approximate-breadth equivalence in source Theorem 3.15,
at the library's semantic `ℕ`-universe level. -/
theorem stableApproximateGeneratable_iff_conditionTwo
    (F : Generic.LanguageFamily ℕ) :
    (∃ G : SupportAlgorithm ℕ,
        IsStableGenerator G F ∧ IsApproximateBreadthGenerator G F) ↔
      GenLimit.Angluin.ConditionTwo F := by
  constructor
  · rintro ⟨G, hStable, hApprox⟩
    exact GenLimit.Angluin.conditionTwo_of_semanticallyIdentifiable F
      (stableApproximate_implies_semanticallyInferrable hStable hApprox)
  · exact conditionTwo_implies_stableApproximate

end GenLimit.BreadthCharacterizations
