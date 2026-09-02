import GenLimit.Paper17_InfiniteContamination.AlgorithmFour
import GenLimit.Paper17_InfiniteContamination.BoundedDisplacement
import GenLimit.Paper17_InfiniteContamination.ConstantNoiseNecessity
import GenLimit.Paper17_InfiniteContamination.Definitions
import GenLimit.Paper17_InfiniteContamination.EvenDensity
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationNecessity
import GenLimit.Paper17_InfiniteContamination.FiniteExpansionTransfer
import GenLimit.Paper17_InfiniteContamination.PriorityStabilization
import GenLimit.Paper17_InfiniteContamination.ProperSeparations
import GenLimit.Paper17_InfiniteContamination.Results.Overview
import GenLimit.Paper17_InfiniteContamination.SetDensityObstruction
import GenLimit.Paper17_InfiniteContamination.VanishingNoise

/-!
# Language generation with infinite contamination

Paper-facing umbrella for the kernel-checked deterministic and density
results from Mehrotra--Velegkas--Yu--Zhou, arXiv:2511.07417v1.

The current development is intentionally marked partial: it covers the
principal separations, priority-stabilization machinery, explicit-family
forms of Theorems 5.1 and 5.4, the necessity-side density obstructions, and
the bounded-displacement density theorem.  The positive and element-density
results listed in `Results.Overview` remain future work.
-/
