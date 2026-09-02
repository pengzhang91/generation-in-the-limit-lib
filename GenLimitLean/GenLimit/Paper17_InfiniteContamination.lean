import GenLimit.Paper17_InfiniteContamination.AlgorithmFour
import GenLimit.Paper17_InfiniteContamination.AlgorithmFive
import GenLimit.Paper17_InfiniteContamination.AlgorithmSixSeven
import GenLimit.Paper17_InfiniteContamination.AlgorithmEight
import GenLimit.Paper17_InfiniteContamination.AlgorithmNine
import GenLimit.Paper17_InfiniteContamination.BoundedDisplacement
import GenLimit.Paper17_InfiniteContamination.ConstantNoiseNecessity
import GenLimit.Paper17_InfiniteContamination.Definitions
import GenLimit.Paper17_InfiniteContamination.EvenDensity
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationNecessity
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency
import GenLimit.Paper17_InfiniteContamination.FiniteExpansionTransfer
import GenLimit.Paper17_InfiniteContamination.NoiselessSetDensity
import GenLimit.Paper17_InfiniteContamination.PriorityStabilization
import GenLimit.Paper17_InfiniteContamination.ProperSeparations
import GenLimit.Paper17_InfiniteContamination.Results.Overview
import GenLimit.Paper17_InfiniteContamination.SetDensityObstruction
import GenLimit.Paper17_InfiniteContamination.VanishingNoise

/-!
# Language generation with infinite contamination

Paper-facing umbrella for the kernel-checked deterministic and density
results from Mehrotra--Velegkas--Yu--Zhou, arXiv:2511.07417v1.

The development covers the principal separations, priority-stabilization
machinery, explicit-family forms of Theorems 5.1, 5.4, 6.1, 6.5, 6.11,
6.14 (for the justified strict range `c < 1`), the element-density transfer
through Theorem 6.18, and Algorithm 9 / Theorem 7.8. Source and abstraction
qualifications are recorded in `Results.Overview` and the paper map.
-/
