import GenLimit.Paper06_NoisyExamples.UniformIndependent
import GenLimit.Paper06_NoisyExamples.NoisyClosure
import GenLimit.Paper06_NoisyExamples.FiniteClasses
import GenLimit.Paper06_NoisyExamples.Nonuniform
import GenLimit.Paper06_NoisyExamples.NoiselessRobustification
import GenLimit.Paper06_NoisyExamples.FiniteUnionLimit
import GenLimit.Paper06_NoisyExamples.Separation
import GenLimit.Paper06_NoisyExamples.AlternatePositive
import GenLimit.Paper06_NoisyExamples.NonuniformIndependent

/-!
# Paper 06: main-results overview

This is the public results facade for Raman--Raman, *Generation from Noisy
Examples*.  The declarations below are aliases of the canonical proof
endpoints, so the source-numbered surface does not duplicate proofs.

The main characterizations and consequences are complete at the paper's
semantic interface.  Appendix Theorem C.3 uses the equivalent bounded-excess
form of noisy closure, and the development makes the source's noise convention
explicit.  No runtime or extracted implementation is claimed.
-/

namespace GenLimit.NoisyExamples.Results

alias theorem_3_1 := GenLimit.NoisyExamples.theorem_3_1
alias theorem_3_3 := GenLimit.NoisyExamples.theorem_3_3
alias corollary_3_4 := GenLimit.NoisyExamples.corollary_3_4
alias lemma_3_5 := GenLimit.NoisyExamples.lemma_3_5
alias lemma_3_6 := GenLimit.NoisyExamples.lemma_3_6
alias corollary_3_7 := GenLimit.NoisyExamples.corollary_3_7
alias lemma_3_8 := GenLimit.NoisyExamples.lemma_3_8
alias theorem_3_9 := GenLimit.NoisyExamples.theorem_3_9
alias theorem_3_10 := GenLimit.NoisyExamples.theorem_3_10
alias lemma_C_2 := GenLimit.NoisyExamples.lemma_C_2
alias theorem_C_3 := GenLimit.NoisyExamples.theorem_C_3
alias lemma_D_2 := GenLimit.NoisyExamples.lemma_D_2

end GenLimit.NoisyExamples.Results
