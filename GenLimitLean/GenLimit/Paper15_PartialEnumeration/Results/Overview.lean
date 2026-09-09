import GenLimit.Paper15_PartialEnumeration.FiniteScope
import GenLimit.Paper15_PartialEnumeration.SemiIndex
import GenLimit.Paper15_PartialEnumeration.AlgorithmOneRun
import GenLimit.Paper15_PartialEnumeration.WarmupPriorityRun
import GenLimit.Paper15_PartialEnumeration.DensityAccounting
import GenLimit.Paper15_PartialEnumeration.PodLimit
import GenLimit.Paper15_PartialEnumeration.FullTextIdentification
import GenLimit.Paper15_PartialEnumeration.FullTextSeparation
import GenLimit.Paper15_PartialEnumeration.PartialSeparationCounterexample

/-!
# Paper 15: main-results overview

This facade collects the source-numbered endpoints for Kleinberg--Wei,
*Language Generation and Identification From Partial Enumeration*.  All
declarations are aliases of canonical proofs.

Theorems 1.5/2.1, 1.7, 1.8, 2.2, 2.4, 4.9, and Corollary 4.11 are complete at
their stated semantic interfaces.  The Section 3 aliases expose the proved
validity and density-accounting components rather than claiming complete
Theorems 3.1 or 3.5.  Corollary 4.10 is complete for full exact texts; the
source's stronger arbitrary-partial-text version has a checked counterexample.
Theorems 1.10 and 1.11 remain open.
-/

namespace GenLimit.KleinbergWei.PartialEnumeration.Results

alias theorem_1_5 := GenLimit.KleinbergWei.PartialEnumeration.theorem_2_1
alias theorem_1_7 := GenLimit.KleinbergWei.PartialEnumeration.theorem_1_7
alias theorem_1_8 := GenLimit.KleinbergWei.PartialEnumeration.theorem_1_8
alias theorem_2_1 := GenLimit.KleinbergWei.PartialEnumeration.theorem_2_1
alias theorem_2_2 :=
  GenLimit.KleinbergWei.PartialEnumeration.theorem_2_2_accurate_conjunction
alias theorem_2_4 :=
  GenLimit.KleinbergWei.PartialEnumeration.theorem_2_4_semiIndex
alias theorem_3_1_eventual_validity :=
  GenLimit.KleinbergWei.PartialEnumeration.WarmupPriority.lemma_3_2_eventual_validity
alias theorem_3_1_density_certificate :=
  GenLimit.KleinbergWei.PartialEnumeration.WarmupChargeCertificate.theorem_3_1_alpha_third
alias theorem_3_5_fixed_pod_endgame :=
  GenLimit.KleinbergWei.PartialEnumeration.theorem_3_5_lowerDensity_of_fixedPodBounds
alias theorem_4_9 :=
  GenLimit.KleinbergWei.PartialEnumeration.FullTopology.theorem_4_9_fullText
alias corollary_4_10_full_text :=
  GenLimit.KleinbergWei.PartialEnumeration.FullTopology.corollary_4_10_fullText
alias corollary_4_10_partial_text_counterexample :=
  GenLimit.KleinbergWei.PartialEnumeration.FullTopology.PartialSeparationCounterexample.possiblySubset_corollary_4_10_counterexample
alias corollary_4_11 :=
  GenLimit.KleinbergWei.PartialEnumeration.FullTopology.corollary_4_11_fullText

end GenLimit.KleinbergWei.PartialEnumeration.Results
