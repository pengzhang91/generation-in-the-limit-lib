import GenLimit.Paper28_ContrastiveGeneration.Geometry
import GenLimit.Paper28_ContrastiveGeneration.IdentifierCharacterization
import GenLimit.Paper28_ContrastiveGeneration.GenerationCores
import GenLimit.Paper28_ContrastiveGeneration.ClosureDimension
import GenLimit.Paper28_ContrastiveGeneration.NonuniformClosure
import GenLimit.Paper28_ContrastiveGeneration.Hierarchy
import GenLimit.Paper28_ContrastiveGeneration.DisjointHierarchy
import GenLimit.Paper28_ContrastiveGeneration.CorruptedPresentations
import GenLimit.Paper28_ContrastiveGeneration.AbsenceCount
import GenLimit.Paper28_ContrastiveGeneration.CorruptedIncomparability
import GenLimit.Paper28_ContrastiveGeneration.DefectInfimum

/-!
# Paper 28: main-results overview

This is the public results facade for Li--Huang--Jiao--Ghoshal,
*Contrastive Identification and Generation in the Limit*.  The aliases below
collect the proved headline endpoints without duplicating proofs.

Theorem 4.3 and the clean-diamond direction of Theorem 5.13 retain the
qualifications documented in the paper map.  Theorem 5.14 is fully witnessed
by the punctured and disjoint examples.  Proposition B.1 and the Appendix D
membership-pattern classification remain open.
-/

namespace GenLimit.ContrastiveGeneration.Results

alias proposition_4_2 := GenLimit.ContrastiveGeneration.proposition_4_2
alias theorem_4_3 := GenLimit.ContrastiveGeneration.theorem_4_3
alias theorem_4_7 := GenLimit.ContrastiveGeneration.theorem_4_7
alias theorem_5_4 := GenLimit.ContrastiveGeneration.theorem_5_4
alias theorem_5_4_quantitative :=
  GenLimit.ContrastiveGeneration.theorem_5_4_quantitative
alias theorem_5_4_sharp_sample_complexity :=
  GenLimit.ContrastiveGeneration.theorem_5_4_sharp_sample_complexity
alias theorem_5_5 := GenLimit.ContrastiveGeneration.theorem_5_5
alias proposition_5_8 := GenLimit.ContrastiveGeneration.proposition_5_8
alias proposition_5_11 := GenLimit.ContrastiveGeneration.proposition_5_11
alias proposition_5_12 := GenLimit.ContrastiveGeneration.proposition_5_12
alias theorem_5_13_punctured_witness :=
  GenLimit.ContrastiveGeneration.theorem_5_13_5_14_punctured_witness
alias theorem_5_13_disjoint_witness :=
  GenLimit.ContrastiveGeneration.theorem_5_13_5_14_disjoint_witness
alias theorem_5_14_punctured_witness :=
  GenLimit.ContrastiveGeneration.theorem_5_13_5_14_punctured_witness
alias theorem_5_14_disjoint_witness :=
  GenLimit.ContrastiveGeneration.theorem_5_13_5_14_disjoint_witness
alias proposition_6_3_defect_infimum :=
  GenLimit.ContrastiveGeneration.proposition_6_3_defect_eq_forced_wrong_cut_infimum
alias proposition_6_3_zero_defect :=
  GenLimit.ContrastiveGeneration.proposition_6_3_notEliminable_iff_defectNumber_zero
alias theorem_6_5 := GenLimit.ContrastiveGeneration.theorem_6_5
alias theorem_6_6 := GenLimit.ContrastiveGeneration.theorem_6_6
alias theorem_6_8 := GenLimit.ContrastiveGeneration.theorem_6_8

end GenLimit.ContrastiveGeneration.Results
