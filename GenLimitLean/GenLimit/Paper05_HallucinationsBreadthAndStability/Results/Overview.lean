import GenLimit.Paper05_HallucinationsBreadthAndStability.ApproximateBreadth
import GenLimit.Paper05_HallucinationsBreadthAndStability.CorrectedStability
import GenLimit.Paper05_HallucinationsBreadthAndStability.Relationships
import GenLimit.Paper05_HallucinationsBreadthAndStability.StabilityGap
import GenLimit.Paper05_HallucinationsBreadthAndStability.StableApproximate

/-!
# P05 source-facing overview

Paper-facing declarations for Kalavasis--Mehrotra--Velegkas,
*On Characterizations for Language Generation: Interplay of Hallucinations,
Breadth, and Stability*, arXiv:2412.18530v2.

The source works throughout with infinite languages.  The internal semantic
lemmas are sometimes more general; the wrappers below restore that standing
assumption.  Names ending in `_sufficiency_semantic`, `_inconsistent`, or
`_corrected` deliberately do not claim a complete literal formalization of
the corresponding printed theorem.
-/

namespace GenLimit.BreadthCharacterizations.Results

open GenLimit.Generic

/-- Semantic form of Theorem 3.3: exact breadth is characterized by
Angluin's condition. -/
theorem theorem_3_3_semantic
    [Nonempty α] [Countable α]
    (F : Generic.LanguageFamily α)
    (_hInfinite : ∀ i, (F i).Infinite) :
    ExactBreadthGeneratable F ↔ GenLimit.Angluin.ConditionTwo F :=
  exactBreadthGeneratable_iff_conditionTwo F

/-- The proved upper-bound direction of Theorem 3.8.  The finite
non-uniqueness lower bound, and hence the reverse implication, is not yet
formalized. -/
theorem theorem_3_8_sufficiency_semantic
    [Countable α]
    (F : Generic.LanguageFamily α)
    (_hInfinite : ∀ i, (F i).Infinite) :
    WeakAngluinCondition F → ApproximateBreadthGeneratable F :=
  weakAngluin_implies_approximateBreadthGeneratable

/-- The coherent approximate-breadth equivalence in Theorem 3.15, at the
semantic natural-number universe used by the existing P03 reduction. -/
theorem theorem_3_15_approximate_semantic
    (F : Generic.LanguageFamily ℕ)
    (_hInfinite : ∀ i, (F i).Infinite) :
    (∃ G : SupportAlgorithm ℕ,
        IsStableGenerator G F ∧ IsApproximateBreadthGenerator G F) ↔
      GenLimit.Angluin.ConditionTwo F :=
  stableApproximateGeneratable_iff_conditionTwo F

/-- Lean formalization finding for the exact-breadth clause of Theorem 3.15:
literal Definition 3.1 and raw-support stability in Definition 3.14 are
incompatible on complete presentations of infinite languages. -/
theorem theorem_3_15_literal_exact_inconsistent
    [Countable α]
    (F : Generic.LanguageFamily α)
    (hInfinite : ∀ i, (F i).Infinite) :
    ¬∃ G : SupportAlgorithm α,
      IsStableGenerator G F ∧ IsExactBreadthGenerator G F :=
  no_stable_exactBreadth_for_infinite_family F hInfinite

/-- A coherent repair of the exact-breadth clause of Theorem 3.15: restore
the observed sample and require eventual whole-target support.  This is a
library-proposed corrected statement, not the literal printed theorem. -/
theorem theorem_3_15_corrected_wholeTarget_semantic
    [Nonempty α] [Countable α]
    (F : Generic.LanguageFamily α)
    (_hInfinite : ∀ i, (F i).Infinite) :
    (∃ G : SupportAlgorithm α,
        IsWholeTargetGenerator G F ∧ IsStableGenerator G F) ↔
      GenLimit.Angluin.ConditionTwo F :=
  stableWholeTargetGeneratable_iff_conditionTwo F

/-- The same literal support/stability conflict applies to Proposition 8.10
and Corollary 8.11(2), independently of their additional closure-dimension
and oracle assumptions. -/
theorem proposition_8_10_literal_specification_inconsistent
    [Countable α]
    (F : Generic.LanguageFamily α)
    (hInfinite : ∀ i, (F i).Infinite) :
    ¬∃ G : SupportAlgorithm α,
      IsStableGenerator G F ∧ IsInfiniteCoverageGenerator G F :=
  no_stable_infiniteCoverage_for_infinite_family F hInfinite

end GenLimit.BreadthCharacterizations.Results
