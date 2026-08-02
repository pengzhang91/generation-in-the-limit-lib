import GenLimit.LiRamanTewari.Definitions
import GenLimit.LiRamanTewari.Hierarchy
import GenLimit.LiRamanTewari.Closure
import GenLimit.LiRamanTewari.UniformSampleComplexity
import GenLimit.LiRamanTewari.NonuniformCharacterization
import GenLimit.LiRamanTewari.GenerationInLimitCharacterization
import GenLimit.LiRamanTewari.FiniteConeCover
import GenLimit.LiRamanTewari.LimitVsNonuniformSeparation
import GenLimit.LiRamanTewari.CountableUnionSeparation
import GenLimit.LiRamanTewari.EarlierSectionThreeExamples
import GenLimit.LiRamanTewari.Prediction
import GenLimit.LiRamanTewari.EventuallyUnboundedClosure
import GenLimit.LiRamanTewari.EventuallyUnboundedClosureDiagnostics
import GenLimit.LiRamanTewari.FiniteEUCUnion
import GenLimit.LiRamanTewari.PromptedDefinitions
import GenLimit.LiRamanTewari.PromptedClosure
import GenLimit.LiRamanTewari.PromptedNonuniform
import GenLimit.LiRamanTewari.PromptedInfinitePromptExample

/-!
Umbrella for the Li--Raman--Tewari development through all theorem-level
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
