import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.Nonuniform
import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.NonuniformNoRepetition
import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.ExhaustiveCharacterization
import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.MembershipExhaustive
import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.Breadth
import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.BreadthClaim52
import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.NoFeedbackDimension
import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.Identification

/-!
# Charikar--Pabbaraju: detailed numbered results

Public facade for the detailed results supporting the overview theorems.
Theorem 7 is intentionally absent: its exact statement and partial diagonal
infrastructure live under the explicit `Experimental` entry point.
-/

namespace GenLimit.CharikarPabbaraju.Results

/-- Theorem 6: explicit non-uniform sample-complexity bound. -/
theorem theorem_6 [Infinite α]
    (C : GenLimit.Generic.LanguageFamily α) {i t : ℕ}
    (stream : GenLimit.Generic.Stream α)
    (hstream : GenLimit.Generic.StreamIn stream (C i))
    (hthreshold : max (i + 1)
        (GenLimit.CharikarPabbaraju.nonuniformComplexity C i + 1) ≤
      (GenLimit.Generic.sample stream t).card) :
    GenLimit.Generic.CorrectAt
      (GenLimit.CharikarPabbaraju.greedyGenerator C) (C i) stream t :=
  GenLimit.CharikarPabbaraju.nonuniform_upper_bound C stream hstream hthreshold

/-- Theorem 8: Angluin's effective identification characterization. -/
theorem theorem_8 (F : GenLimit.Angluin.EffectiveIndexedFamily) :
    GenLimit.CharikarPabbaraju.TheoremEightStatement F :=
  GenLimit.CharikarPabbaraju.theorem_8 F

end GenLimit.CharikarPabbaraju.Results
