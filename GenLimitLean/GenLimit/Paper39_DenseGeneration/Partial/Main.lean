import GenLimit.Paper39_DenseGeneration.Partial.Certificate
import GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity

/-!
# Appendix B: partial enumeration

The adversary presents an infinite subset `E` of a true family member `K`.
The patient-scope machine is run on the filtered finite-intersection closure
of the original family.  Lemma B.2 supplies eventual validity, while the
partial-enumeration certificate gives the factor-`1/2` relative-density
guarantee of Theorem B.3.

The closure filters intersections by semantic infinitude. Consequently these
are semantic theorems; they do not claim that the transformed indexing can be
computed from the pointwise membership oracle.
-/

namespace GenLimit
namespace PartialEnumeration

/-- Target-relative lower density achieved by patient-scope on the filtered
finite-intersection closure. -/
noncomputable def partialPatientLowerDensity
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ) : ℝ :=
  PatientScope.relativeLowerDensity
    (GeneratorFirst stream
      (PatientMachine.output (closure O) stream) ∩ O.language z)
    (O.language z) (O.infinite' z)

/-- The abstract certificate density is the operational density of the same
patient-scope run. -/
private theorem StableTargetRun.partialCertificate_lowerDensity
    (O : OracleFamily) {stream : ℕ → ℕ} {E : Language} {z : ℕ}
    (S : StableTargetRun (closure O) stream (O.language z))
    (hP : Presents stream E) (hsub : E ⊆ O.language z) :
    (S.partialCertificate hP hsub).lowerDensity (O.infinite' z) =
      partialPatientLowerDensity O stream z := by
  rfl

/-- Intrinsic form of Theorem B.3, using the actual relative lower density
rather than introducing a separate parameter `α`. -/
theorem theorem_B_3_lowerDensity
    (O : OracleFamily) {stream : ℕ → ℕ} {E : Language} {z : ℕ}
    (hP : Presents stream E) (hE : E.Infinite)
    (hsub : E ⊆ O.language z) :
    (1 / 2 : ℝ) * PatientScope.relativeLowerDensity E (O.language z) (O.infinite' z) ≤
      partialPatientLowerDensity O stream z := by
  obtain ⟨S⟩ := stableTargetRun_nonempty O hP hE hsub
  let P := S.partialCertificate hP hsub
  have hInfinite : P.target.Infinite := by
    simpa [P] using O.infinite' z
  have hlog : ∀ n, PatientScope.prefixCount P.switchLoss n ≤
      Nat.log2 (P.targetCount n) := by
    intro n
    exact S.partialCertificate_switch_log hP hsub n
  have hDensity :=
    PatientScope.PartialEnumerationCertificate.theorem_B_3
      P hInfinite hlog
  simpa [P, StableTargetRun.partialCertificate_lowerDensity] using hDensity

/-- Paper-shaped form of Theorem B.3 with the relative lower density named
`α`. -/
theorem theorem_B_3
    (O : OracleFamily) {stream : ℕ → ℕ} {E : Language} {z : ℕ}
    (hP : Presents stream E) (hE : E.Infinite)
    (hsub : E ⊆ O.language z) (α : ℝ)
    (hα : PatientScope.relativeLowerDensity E (O.language z) (O.infinite' z) = α) :
    α / 2 ≤ partialPatientLowerDensity O stream z := by
  calc
    α / 2 = (1 / 2 : ℝ) *
        PatientScope.relativeLowerDensity E (O.language z) (O.infinite' z) := by
      rw [hα]
      ring
    _ ≤ partialPatientLowerDensity O stream z :=
      theorem_B_3_lowerDensity O hP hE hsub

/-- Lemma B.2 and Theorem B.3 for the same transformed patient-scope run. -/
theorem theorem_B_3_with_generation
    (O : OracleFamily) {stream : ℕ → ℕ} {E : Language} {z : ℕ}
    (hP : Presents stream E) (hE : E.Infinite)
    (hsub : E ⊆ O.language z) :
    (∃ T, ∀ t, T ≤ t →
      PatientMachine.output (closure O) stream t ∈ O.language z ∧
      (∀ s, s ≤ t →
        stream s ≠ PatientMachine.output (closure O) stream t) ∧
      (∀ s, s < t →
        PatientMachine.output (closure O) stream s ≠
          PatientMachine.output (closure O) stream t)) ∧
    (1 / 2 : ℝ) * PatientScope.relativeLowerDensity E (O.language z) (O.infinite' z) ≤
      partialPatientLowerDensity O stream z := by
  exact ⟨lemma_B_2_generation O hP hE hsub,
    theorem_B_3_lowerDensity O hP hE hsub⟩

end PartialEnumeration
end GenLimit
