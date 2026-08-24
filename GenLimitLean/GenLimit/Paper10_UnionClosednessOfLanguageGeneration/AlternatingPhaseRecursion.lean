import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Internal.AlternatingEngine

/-!
# Detailed Theorem 4.1 lower bound

The alternating phase construction is shared with detailed Theorem 4.3 in
`Internal.AlternatingEngine`.  Its cursor starts at zero and therefore
enumerates every negative integer.  That exact coverage is stronger than the
cofinite-negative invariant needed for Theorem 4.1.  The engine runs on a
common subfamily of both paper-facing pairs, so this file only restricts a
hypothetical Theorem 4.1 generator and packages the public result.
-/

namespace GenLimit.UnionClosedness

open GenLimit.Generic

/-- Detailed Theorem 4.1's union lower bound under the paper's injective
presentation convention. -/
theorem theorem_4_1_union_not_generatable_on_injective_presentations :
    ¬GeneratableInLimitOnInjectivePresentations
      (finiteNegativeInfinitePositiveClass ∪
        infiniteNegativeFinitePositiveClass) := by
  rintro ⟨G, hG⟩
  exact
    Internal.AlternatingEngine.alternatingCoreClass_not_generatable_on_injective_presentations
      ⟨G,
        Internal.AlternatingEngine.limitGeneratorOnCore_of_theorem41 hG⟩

/-- The same lower bound in the library's stronger all-presentations
semantics, where repetitions are also permitted. -/
theorem theorem_4_1_union_not_generatable :
    ¬GenLimit.Generic.GeneratableInLimit
      (finiteNegativeInfinitePositiveClass ∪
        infiniteNegativeFinitePositiveClass) :=
  not_generatableInLimit_of_not_generatableOnInjectivePresentations
    theorem_4_1_union_not_generatable_on_injective_presentations

/-- Detailed Theorem 4.1: both component classes are non-uniformly
generatable, while their union is not generatable in the limit on injective
presentations. -/
theorem theorem_4_1 :
    GenLimit.Generic.NonuniformlyGeneratable
        finiteNegativeInfinitePositiveClass ∧
      GenLimit.Generic.NonuniformlyGeneratable
        infiniteNegativeFinitePositiveClass ∧
      ¬GeneratableInLimitOnInjectivePresentations
        (finiteNegativeInfinitePositiveClass ∪
          infiniteNegativeFinitePositiveClass) :=
  ⟨theorem_4_1_individual_classes.1,
    theorem_4_1_individual_classes.2,
    theorem_4_1_union_not_generatable_on_injective_presentations⟩

end GenLimit.UnionClosedness
