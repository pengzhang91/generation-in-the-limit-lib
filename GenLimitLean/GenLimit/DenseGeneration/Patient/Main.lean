import GenLimit.DenseGeneration.Patient.Charging
import GenLimit.DenseGeneration.Abstract.TargetMain

/-!
# Operational patient-scope lower-density theorem

This module states Theorem 3.14 directly for the semantic patient-scope
machine.  Its numerator is the ambient-prefix count of values first announced
by the generator which belong to the presented target.
-/

namespace GenLimit
namespace PatientMachine

/-- Lower density achieved by the concrete patient-scope output on target
`O.language z`. -/
noncomputable def patientLowerDensity
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ) : ℝ :=
  PatientScope.relativeLowerDensity
    (GeneratorFirst stream (output O stream) ∩ O.language z)
    (O.language z)

/-- The abstract certificate's target lower density is definitionally the
operational quantity above. -/
private theorem patientScopeCertificate_targetLowerDensity
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z))
    (Q : PatientScope.TargetSwitchChargingCertificate
      (O.language z) (settledSwitchLoss O stream z hP)) :
    (patientScopeCertificate O stream z hP Q).targetLowerDensity =
      patientLowerDensity O stream z := by
  rfl

/-- Operational form of Theorem 3.14.  It is uniform over the indexed family,
the target index, and every exact presentation of that target. -/
theorem patientScope_lowerDensity_half
    (O : OracleFamily) (stream : ℕ → ℕ) {z : ℕ}
    (hP : Presents stream (O.language z)) :
    (1 / 2 : ℝ) ≤ patientLowerDensity O stream z := by
  let Q := settledChargingCertificate O stream z hP
  let P := patientScopeCertificate O stream z hP Q
  have hInfinite : P.target.Infinite := by
    simpa [P] using O.infinite' z
  have hcharging :
      PatientScope.TargetSwitchChargingCertificate P.target P.switchLoss := by
    simpa [P] using Q
  have hhalf :=
    PatientScope.PatientScopeCertificate.theorem_3_14_target
      P hInfinite hcharging
  simpa [P, patientScopeCertificate_targetLowerDensity] using hhalf

/-- Definition 2.1 novelty together with Theorem 3.14 for the same run. -/
theorem patientScope_generation_and_lowerDensity
    (O : OracleFamily) (stream : ℕ → ℕ) {z : ℕ}
    (hP : Presents stream (O.language z)) :
    (∃ T, ∀ t, T ≤ t →
      output O stream t ∈ O.language z ∧
      (∀ s, s ≤ t → stream s ≠ output O stream t) ∧
      (∀ s, s < t → output O stream s ≠ output O stream t)) ∧
      (1 / 2 : ℝ) ≤ patientLowerDensity O stream z := by
  obtain ⟨T, hvalid⟩ := patient_validity O stream hP
  refine ⟨⟨T, ?_⟩, patientScope_lowerDensity_half O stream hP⟩
  intro t ht
  exact ⟨hvalid t ht, stream_ne_output O stream t,
    fun s hs => output_ne_of_lt O stream hs⟩

end PatientMachine
end GenLimit
