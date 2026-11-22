import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.Results.Overview
import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.TowerStart
import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.FrozenFrame
import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.InfiniteRank.Levels
import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.InfiniteRank.PrefixCharge
import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.InfiniteRank.TwoTokenCharge
import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.InfiniteRank.HistoricalLedger
import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.InfiniteRank.RecursiveHistory
import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.InfiniteRank.RunTokenSource

/-!
# #07 Density Measures for Language Generation

Kleinberg and Wei, *Density Measures for Language Generation* (arXiv:2504.14370v1).
The overview includes all Section 2 results, the detailed minimax and density
theorems, and the finite-sample-set interpretation. The latter has a sharp
distinction between the minimax results and the positive accuracy or element
density guarantees. Further modules give the finite-rank and charging arguments.
-/
