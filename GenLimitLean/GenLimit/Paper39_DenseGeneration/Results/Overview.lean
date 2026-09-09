import GenLimit.Paper39_DenseGeneration.Abstract.NormalizedMain
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper39_DenseGeneration.Partial

/-!
# Paper 39: earlier-manuscript results overview

This facade covers only the earlier manuscript currently represented by the
Lean development.  It does **not** claim the public arXiv v1 main theorems,
whose criticality definition and theorem numbering differ materially.

For the earlier manuscript, the aliases expose patient-scope validity and the
one-half target-relative lower-density theorem, together with the partial
enumeration validity and density results.  No proof is duplicated here.
-/

namespace GenLimit.DenseGeneration.Results

alias theorem_3_14 := GenLimit.PatientMachine.patientScope_lowerDensity_half
alias theorem_3_14_with_generation :=
  GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
alias lemma_3_16 := GenLimit.PartialEnumeration.lemma_3_16_generation
alias theorem_3_17 := GenLimit.PartialEnumeration.theorem_3_17
alias theorem_3_17_with_generation :=
  GenLimit.PartialEnumeration.section_3_3_generation_and_lowerDensity

end GenLimit.DenseGeneration.Results
