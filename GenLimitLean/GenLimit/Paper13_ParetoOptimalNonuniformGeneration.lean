import GenLimit.Paper13_ParetoOptimalNonuniformGeneration.AdmissibleFrontier
import GenLimit.Paper13_ParetoOptimalNonuniformGeneration.Order
import GenLimit.Paper13_ParetoOptimalNonuniformGeneration.Scheduling
import GenLimit.Paper13_ParetoOptimalNonuniformGeneration.WitnessLowerBound
import GenLimit.Paper13_ParetoOptimalNonuniformGeneration.GlobalInvariant
import GenLimit.Paper13_ParetoOptimalNonuniformGeneration.ArbitraryScheduler
import GenLimit.Paper13_ParetoOptimalNonuniformGeneration.CoSingletonFrontier
import GenLimit.Paper13_ParetoOptimalNonuniformGeneration.ThresholdFrontier
import GenLimit.Paper13_ParetoOptimalNonuniformGeneration.ExactPareto
import GenLimit.Paper13_ParetoOptimalNonuniformGeneration.VariantExactPareto
import GenLimit.Paper13_ParetoOptimalNonuniformGeneration.NoisyWitness
import GenLimit.Paper13_ParetoOptimalNonuniformGeneration.NoisyProcedure
import GenLimit.Paper13_ParetoOptimalNonuniformGeneration.Results.Overview

/-!
# Pareto-optimal Non-uniform Language Generation

Paper-facing umbrella for Charikar--Pabbaraju, arXiv:2510.02795v1.  The
development covers the deterministic Procedure-1 construction and
Theorems 1, 4, and 5, the corrected totalized noisy Procedure 2 and
Theorems 6 and 8, and the common scheduler endgame used by Theorem 9.
The representative construction of Theorem 7 and its concrete Theorem-9
specialization remain open and are recorded explicitly in `Results.Overview`.
-/
