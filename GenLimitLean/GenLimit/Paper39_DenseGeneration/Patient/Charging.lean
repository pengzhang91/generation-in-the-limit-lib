import GenLimit.Paper39_DenseGeneration.Patient.Certificate
import GenLimit.Paper39_DenseGeneration.Patient.StableTargetCharging

/-!
# Charging settled switch losses

This module instantiates the shared stable-target charging argument for an
exact presentation.  The settled target index is the permanent witness and
`settledThreshold` is the common stabilization threshold.
-/

namespace GenLimit
namespace PatientMachine

/-- The shared charging hypotheses supplied by an exact presentation after
the canonical settled threshold. -/
private noncomputable def settledStableTargetRun
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z)) :
    StableTargetRun O stream (O.language z) where
  witness := z
  threshold := settledThreshold O stream z hP
  onModel := onModel_of_presents O hP
  critical := fun _ ht => settled_target_critical O stream z hP ht
  inScope := fun _ ht => settled_target_in_scope O stream z hP ht
  witness_subset_target := Set.Subset.rfl
  adversary_target := by
    intro t
    rw [← hP]
    exact ⟨t, rfl⟩

/-- Concrete target-relative form of Lemma 3.14. -/
noncomputable def settledChargingCertificate
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z)) :
    PatientScope.TargetSwitchChargingCertificate
      (O.language z) (settledSwitchLoss O stream z hP) := by
  simpa [settledSwitchLoss, settledStableTargetRun] using
    (settledStableTargetRun O stream z hP).chargingCertificate

/-- Lemma 3.14 in ambient prefixes: the logarithm counts target elements,
so this also covers sparse targets without identifying the target with `ℕ`.
`settledSwitchLoss` excludes the finite initial segment before stabilization. -/
theorem lemma_3_14
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z)) (n : ℕ) :
    PatientScope.prefixCount (settledSwitchLoss O stream z hP) n ≤
      Nat.log2 (PatientScope.prefixCount (O.language z) n) :=
  (settledChargingCertificate O stream z hP).prefixCount_le_log2_targetCount n

end PatientMachine
end GenLimit
