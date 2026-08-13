import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.Results.Detailed
import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.RegularRayEncoding
import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.Feedback

/-!
# Charikar--Pabbaraju: overview theorems

Source-facing facade for the completed overview results in
arXiv:2411.15364v2.  Overview Theorem 2 is not declared because its detailed
Theorem 7 lower bound is not yet fully formalized.
-/

namespace GenLimit.CharikarPabbaraju.Results

open GenLimit.Generic

/-- Overview Theorem 1. -/
theorem theorem_1 [Infinite α] [Countable α]
    (C : GenLimit.Generic.LanguageFamily α)
    (hInfinite : ∀ i, (C i).Infinite) :
    GenLimit.CharikarPabbaraju.NonuniformlyGeneratable C :=
  GenLimit.CharikarPabbaraju.countable_collections_nonuniformly_generatable
    C hInfinite

/-- Overview Theorem 3, including the finite alphabet and regularity claims. -/
theorem theorem_3 :
    ∃ C : GenLimit.Generic.LanguageClass (List Bool),
      C.Countable ∧
      (∀ K, K ∈ C → _root_.Language.IsRegular K) ∧
      ¬ GenLimit.CharikarPabbaraju.ExhaustivelyGeneratable C :=
  GenLimit.CharikarPabbaraju.theorem3_finiteAlphabet_regular_exhaustive_generation_lower_bound

/-- Overview Theorem 4. -/
theorem theorem_4 [Countable α]
    (F : GenLimit.Generic.LanguageFamily α)
    (hInfinite : ∀ i, (F i).Infinite) :
    GenLimit.CharikarPabbaraju.ExhaustivelyGeneratable (Set.range F) ↔
      GenLimit.CharikarPabbaraju.WeakAngluinExistence (Set.range F) :=
  GenLimit.CharikarPabbaraju.theorem4_exhaustive_generation_characterization
    F hInfinite

/-- Overview Theorem 5. -/
theorem theorem_5 [Countable α]
    {C : GenLimit.Generic.LanguageClass α}
    (hUUS : GenLimit.Generic.UUS C) :
    GenLimit.CharikarPabbaraju.UniformlyGeneratableWithFeedback C ↔
      GenLimit.CharikarPabbaraju.HasFiniteGFDimension C :=
  GenLimit.CharikarPabbaraju.theorem5_uniform_feedback_characterization hUUS

end GenLimit.CharikarPabbaraju.Results
