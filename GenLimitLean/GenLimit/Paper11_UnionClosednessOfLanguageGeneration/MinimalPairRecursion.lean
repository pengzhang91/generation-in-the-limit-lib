import GenLimit.Paper11_UnionClosednessOfLanguageGeneration.Internal.AlternatingEngine

/-!
# Detailed Theorem 4.3 lower bound

This is the paper-facing wrapper around the single cursor-zero alternating
engine shared with detailed Theorem 4.1.  The engine is run on the common
hard subfamily and a hypothetical generator for the larger Theorem 4.3 union
is restricted to that subfamily.
-/

namespace GenLimit.UnionClosedness.MinimalPairCore

/-- Detailed Theorem 4.3's union lower bound under the paper's injective
presentation convention. -/
theorem theorem43_union_not_generatable_on_injective_presentations :
    ¬GenLimit.UnionClosedness.GeneratableInLimitOnInjectivePresentations
      (theorem43FirstClass ∪ theorem43SecondClass) := by
  rintro ⟨G, hG⟩
  exact
    GenLimit.UnionClosedness.Internal.AlternatingEngine.alternatingCoreClass_not_generatable_on_injective_presentations
      ⟨G,
        GenLimit.UnionClosedness.Internal.AlternatingEngine.limitGeneratorOnCore_of_theorem43 hG⟩

/-- The same lower bound in the library's stronger all-presentations
semantics, where repetitions are also permitted. -/
theorem theorem43_union_not_generatable :
    ¬GenLimit.Generic.GeneratableInLimit
      (theorem43FirstClass ∪ theorem43SecondClass) :=
  GenLimit.UnionClosedness.not_generatableInLimit_of_not_generatableOnInjectivePresentations
      theorem43_union_not_generatable_on_injective_presentations

end GenLimit.UnionClosedness.MinimalPairCore
