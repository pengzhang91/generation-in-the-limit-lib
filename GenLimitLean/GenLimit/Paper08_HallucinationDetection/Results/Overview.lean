import GenLimit.Paper08_HallucinationDetection.AngluinCondition
import GenLimit.Paper08_HallucinationDetection.ExampleOne
import GenLimit.Paper08_HallucinationDetection.NegativeExamples
import GenLimit.Bridges.Paper02ToPaper08

/-!
# Paper 08: main-results overview

This is the public results facade for Karbasi--Montasser--Sous--Velegkas,
*(Im)possibility of Automated Hallucination Detection in Large Language
Models*.  The aliases below expose the paper's five numbered results without
duplicating their proofs.

Theorem A.2 is intentionally proved in `GenLimit.Bridges.Paper02ToPaper08`
because its proof reuses Paper 02's countable-class generation theorem.  The
native P08 proof modules therefore remain independent of substantive P02
results, while this complete paper-facing facade includes the bridge.
-/

namespace GenLimit.HallucinationDetection.Results

alias theorem_2_1 := GenLimit.HallucinationDetection.theorem_2_1
alias corollary_2_2 := GenLimit.HallucinationDetection.corollary_2_2
alias theorem_2_3 := GenLimit.HallucinationDetection.theorem_2_3
alias theorem_A_1 := GenLimit.HallucinationDetection.theorem_A_1
alias theorem_A_2 := GenLimit.HallucinationDetection.theorem_A_2

end GenLimit.HallucinationDetection.Results
