import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.InfinitelyOften
import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.IndexLimsup
import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.Feasible
import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.Topology
import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.Fallback
import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.PersistenceCounterexample
import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.InfiniteRank.OneEighth
import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.InfiniteRank.CapacityCharge

/-!
# Paper 07: main-results overview

This facade collects the proved source-facing endpoints for Kleinberg--Wei,
*Density Measures for Language Generation*.  Exact aliases are used for the
complete Section 2 results.  Names containing `core`, `conditional`, or
`diagnostic` deliberately expose only the proved portion of a source result.

In particular, Theorems 2.3 and 2.5 remain open; Theorem 2.4 currently has its
feasibility core; Theorem 6.2 has the finite-rank endgame but not the missing
persistence premise; and Theorem 6.12 has conditional accounting endgames
rather than a complete unconditional construction.
-/

namespace GenLimit.KleinbergWei.DensityMeasures.Results

alias theorem_2_1 := GenLimit.KleinbergWei.DensityMeasures.theorem_2_1
alias corollary_2_2 := GenLimit.KleinbergWei.DensityMeasures.corollary_2_2
alias theorem_2_4_feasibility_core :=
  GenLimit.KleinbergWei.DensityMeasures.claim_4_7
alias claim_6_1 := GenLimit.KleinbergWei.DensityMeasures.claim_6_1
alias theorem_6_2_finite_rank_endgame :=
  GenLimit.KleinbergWei.DensityMeasures.FiniteRankFallback.corollary_6_10
alias theorem_6_2_persistence_diagnostic :=
  GenLimit.KleinbergWei.DensityMeasures.FiniteRankFallback.no_rankClimbWitness
alias theorem_6_12_finite_accounting :=
  GenLimit.KleinbergWei.DensityMeasures.InfiniteRank.theorem_6_12_finite_accounting
alias theorem_6_12_one_eighth_conditional :=
  GenLimit.KleinbergWei.DensityMeasures.InfiniteRank.theorem_6_12_one_eighth_of_counting
alias theorem_6_12_one_tenth_conditional :=
  GenLimit.KleinbergWei.DensityMeasures.InfiniteRank.orderedLowerDensity_one_tenth_of_longBadCapacityTwoCharge

end GenLimit.KleinbergWei.DensityMeasures.Results
