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
# Paper 15: supporting results

These aliases preserve the detailed-number endpoints previously collected in
`Results.Overview`. The Section 3 results are validity and conditional density
components, not complete proofs of Theorems 3.1 or 3.5. Corollary 4.10 is proved
for full exact texts; the stronger arbitrary-partial-text statement has a
checked counterexample. The main theorem statements are in `Results.Overview`.
-/

namespace GenLimit.KleinbergWei.PartialEnumeration.Results

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
