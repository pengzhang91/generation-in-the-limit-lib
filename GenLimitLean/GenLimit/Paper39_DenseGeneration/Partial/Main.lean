import GenLimit.Paper39_DenseGeneration.Partial.Certificate
import GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity

/-!
# Section 3.3: partial enumeration

The adversary presents an infinite subset `E` of a true family member `K`.
The patient-scope machine is run on the filtered finite-intersection closure
of the original family.  Lemma 3.16 supplies eventual validity, while the
partial-enumeration certificate gives the factor-`1/2` relative-density
guarantee of Theorem 3.17.

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
    (O.language z)

/-- The abstract certificate density is the operational density of the same
patient-scope run. -/
private theorem StableTargetRun.partialCertificate_lowerDensity
    (O : OracleFamily) {stream : ℕ → ℕ} {E : Language} {z : ℕ}
    (S : StableTargetRun (closure O) stream (O.language z))
    (hP : Presents stream E) (hsub : E ⊆ O.language z) :
    (S.partialCertificate hP hsub).lowerDensity =
      partialPatientLowerDensity O stream z := by
  rfl

/-- Intrinsic form of Theorem 3.17, using the actual relative lower density
rather than introducing a separate parameter `α`. -/
theorem theorem_3_17_lowerDensity
    (O : OracleFamily) {stream : ℕ → ℕ} {E : Language} {z : ℕ}
    (hP : Presents stream E) (hE : E.Infinite)
    (hsub : E ⊆ O.language z) :
    (1 / 2 : ℝ) * PatientScope.relativeLowerDensity E (O.language z) ≤
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
    PatientScope.PartialEnumerationCertificate.theorem_3_17
      P hInfinite hlog
  simpa [P, StableTargetRun.partialCertificate_lowerDensity] using hDensity

/-- Paper-shaped form of Theorem 3.17 with the relative lower density named
`α`. -/
theorem theorem_3_17
    (O : OracleFamily) {stream : ℕ → ℕ} {E : Language} {z : ℕ}
    (hP : Presents stream E) (hE : E.Infinite)
    (hsub : E ⊆ O.language z) (α : ℝ)
    (hα : PatientScope.relativeLowerDensity E (O.language z) = α) :
    α / 2 ≤ partialPatientLowerDensity O stream z := by
  calc
    α / 2 = (1 / 2 : ℝ) *
        PatientScope.relativeLowerDensity E (O.language z) := by
      rw [hα]
      ring
    _ ≤ partialPatientLowerDensity O stream z :=
      theorem_3_17_lowerDensity O hP hE hsub

/-- Lemma 3.16 and Theorem 3.17 for the same transformed patient-scope run. -/
theorem section_3_3_generation_and_lowerDensity
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
    (1 / 2 : ℝ) * PatientScope.relativeLowerDensity E (O.language z) ≤
      partialPatientLowerDensity O stream z := by
  exact ⟨lemma_3_16_generation O hP hE hsub,
    theorem_3_17_lowerDensity O hP hE hsub⟩

end PartialEnumeration
end GenLimit
