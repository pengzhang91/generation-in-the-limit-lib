import GenLimit.Paper02_LearningTheory.Definitions
import GenLimit.Paper02_LearningTheory.Hierarchy
import GenLimit.Paper02_LearningTheory.Closure
import GenLimit.Paper02_LearningTheory.UniformSampleComplexity
import GenLimit.Paper02_LearningTheory.NonuniformCharacterization
import GenLimit.Paper02_LearningTheory.GenerationInLimitCharacterization
import GenLimit.Paper02_LearningTheory.FiniteConeCover
import GenLimit.Paper02_LearningTheory.LimitVsNonuniformSeparation
import GenLimit.Paper02_LearningTheory.CountableUnionSeparation
import GenLimit.Paper02_LearningTheory.EarlierSectionThreeExamples
import GenLimit.Paper02_LearningTheory.Prediction
import GenLimit.Paper02_LearningTheory.EventuallyUnboundedClosure
import GenLimit.Paper02_LearningTheory.EventuallyUnboundedClosureDiagnostics
import GenLimit.Paper02_LearningTheory.FiniteEUCUnion
import GenLimit.Paper02_LearningTheory.PromptedDefinitions
import GenLimit.Paper02_LearningTheory.PromptedClosure
import GenLimit.Paper02_LearningTheory.PromptedNonuniform
import GenLimit.Paper02_LearningTheory.PromptedInfinitePromptExample

/-!
# #02 Learning Theory

Umbrella for *Generation through the Lens of Learning Theory* through all theorem-level
Section 3 results and the exact uniform-generation sample-complexity bounds,
Lemmas 4.2--4.3, Theorem 4.1's explicitly delimited
VC/Littlestone combinatorial core, the prompted-generation characterizations
and examples, and the completed Appendix C theorem paths together with the
diagnostic for the false prose equivalence preceding Theorem C.2.
-/

namespace GenLimit.LiRamanTewari

/-- Theorem 2.4: every countable class of infinite languages is generatable
in the limit.  The formal development proves the stronger intermediate
non-uniform conclusion in Corollary 3.6. -/
theorem theorem_2_4
    {α : Type*} [Nonempty α] [Countable α]
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : UUS H) (hCountable : H.Countable) :
    GeneratableInLimit H :=
  nonuniform_implies_limit hUUS
    (countable_classes_are_nonuniformly_generatable
      hUUS hCountable)

end GenLimit.LiRamanTewari
