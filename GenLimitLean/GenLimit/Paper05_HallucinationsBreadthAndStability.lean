import GenLimit.Paper05_HallucinationsBreadthAndStability.ExhaustiveGeneration
import GenLimit.Paper05_HallucinationsBreadthAndStability.InfiniteCoverage
import GenLimit.Paper05_HallucinationsBreadthAndStability.StatisticalRates
import GenLimit.Paper05_HallucinationsBreadthAndStability.FrozenCoverage
import GenLimit.Paper05_HallucinationsBreadthAndStability.Uniqueness
import GenLimit.Paper05_HallucinationsBreadthAndStability.Results.Overview
import GenLimit.Paper05_HallucinationsBreadthAndStability.Results.Supporting
import GenLimit.Paper05_HallucinationsBreadthAndStability.SemanticBoundary

/-!
# Breadth characterizations

Paper-facing umbrella for Kalavasis--Mehrotra--Velegkas,
*On Characterizations for Language Generation: Interplay of Hallucinations,
Breadth, and Stability*, arXiv:2412.18530v2.

The Overview states the numbered original theorems and corollaries from
Sections 3–8. Results.Supporting collects the oracle lemmas, propositions,
figures, examples, and appendix results.
It distinguishes literal counterexamples from proofs under the whole-target
and sample-allowing conventions. The paper map also identifies the open
cells of Figure 4. `SemanticBoundary` checks the validity-only predicate
in Definition 2.1 on the empty-support algorithm.
-/
