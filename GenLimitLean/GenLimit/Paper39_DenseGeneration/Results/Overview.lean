import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper39_DenseGeneration.Partial.Main

/-!
# Paper 39: arXiv:2608.01320v2 results overview

Main theorems for the deterministic patient-scope machine:

- Theorem 3.15 (achievability): target-relative lower density at least `1/2`
  under full enumeration.
- Theorem B.3: under partial enumeration, the generator on the filtered family
  of infinite finite intersections achieves target-relative lower density at
  least `α / 2`, where `α` is the enumerated subset's relative lower density
  in the target.

Languages are indexed infinite subsets of `ℕ`. This is a semantic formalization,
with no finite-query implementation or complexity guarantees. Optimality, Remarks
3.16--3.17, randomized results, and multi-order results remain unformalized here.
See the PaperMap for more details.
-/

namespace GenLimit.DenseGeneration.Results

/-- Theorem 3.15, achievability: patient-scope generates with target-relative
lower density at least `1/2` for every exact presentation of an indexed
infinite target language. The optimality upper bound is not formalized here. -/
theorem theorem_3_15
    (O : OracleFamily) (stream : ℕ → ℕ) {z : ℕ}
    (hP : Presents stream (O.language z)) :
    (1 / 2 : ℝ) ≤ PatientMachine.patientLowerDensity O stream z :=
  PatientMachine.patientScope_lowerDensity_half O stream hP

/-- Theorem B.3: if the enumerated infinite subset has relative lower density
`α` in the target, patient-scope on the filtered finite-intersection closure
generates with target-relative lower density at least `α / 2`. -/
theorem theorem_B_3
    (O : OracleFamily) {stream : ℕ → ℕ} {E : Language} {z : ℕ}
    (hP : Presents stream E) (hE : E.Infinite)
    (hsub : E ⊆ O.language z) (α : ℝ)
    (hα : PatientScope.relativeLowerDensity E (O.language z) (O.infinite' z) = α) :
    α / 2 ≤ PartialEnumeration.partialPatientLowerDensity O stream z :=
  PartialEnumeration.theorem_B_3 O hP hE hsub α hα

end GenLimit.DenseGeneration.Results
