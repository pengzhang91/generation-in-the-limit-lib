import GenLimit.Paper08_HallucinationDetection.AngluinCondition
import GenLimit.Paper08_HallucinationDetection.ExampleOne
import GenLimit.Paper08_HallucinationDetection.NegativeExamples
import GenLimit.Bridges.Paper02ToPaper08

/-!
# Paper 08: main-results overview

This is the public results facade for Karbasi--Montasser--Sous--Velegkas,
*(Im)possibility of Automated Hallucination Detection in Large Language
Models*.  The two main-text theorems below state their assumptions and
conclusions explicitly and delegate their proofs to the canonical modules.

The imports retain the supporting corollary, examples, and appendix results
for the paper entry point.  Theorem A.2 is proved in
`GenLimit.Bridges.Paper02ToPaper08` because it reuses Paper 02's countable-class
generation theorem; the native P08 proof modules remain independent of
substantive P02 results.
-/

namespace GenLimit.HallucinationDetection.Results

/-- Theorem 2.1: hallucination detection in the limit is equivalent to
language identification in the limit.

The nonempty countable domain supplies the fixed enumeration used by the
identification-to-detection reduction. -/
theorem theorem_2_1
    {α : Type*} [Nonempty α] [Countable α]
    (C : GenLimit.Generic.LanguageFamily α) :
    HallucinationDetectable C ↔ IdentifiableInLimit C :=
  GenLimit.HallucinationDetection.theorem_2_1 C

/-- Theorem 2.3: every indexed language family admits hallucination
detection with negative examples.

The correctness predicate assumes a complete, correctly labeled enumeration
of the domain; no additional typeclass assumptions are needed. -/
theorem theorem_2_3
    {α : Type*}
    (C : GenLimit.Generic.LanguageFamily α) :
    DetectableWithNegativeExamples C :=
  GenLimit.HallucinationDetection.theorem_2_3 C

end GenLimit.HallucinationDetection.Results
