import GenLimit.DenseGeneration.Partial.Trace
import GenLimit.DenseGeneration.Partial.Validity
import GenLimit.DenseGeneration.Patient.StableTargetCharging

/-!
# The Section 3.3 certificate

This module assembles the operational patient-scope run and the target-relative
charging construction into the abstract partial-enumeration certificate.  The
only facts about the transformed family used below are supplied by
`Partial.Critical` and `Partial.Validity`.
-/

namespace GenLimit
namespace PartialEnumeration

open PatientMachine

/-- Section 3.3 name for the shared stable-target run package. -/
abbrev StableTargetRun := PatientMachine.StableTargetRun

/-- The filtered finite-intersection closure has a permanently critical
witness which is contained in the true target and eventually lies in scope. -/
theorem stableTargetRun_nonempty
    (O : OracleFamily) {stream : ℕ → ℕ} {E : Language} {z : ℕ}
    (hP : Presents stream E) (hE : E.Infinite)
    (hsub : E ⊆ O.language z) :
    Nonempty (StableTargetRun (closure O) stream (O.language z)) := by
  obtain ⟨w, Tc, hwTarget, hcritical⟩ :=
    exists_eventually_critical_subset_target O hP hE hsub
  have hOn := closure_onModel O hP hsub
  obtain ⟨Ts, hinScope⟩ :=
    critical_witness_eventually_in_scope
      (closure O) stream hP hOn hcritical
  refine ⟨{
    witness := w
    threshold := max Tc Ts
    onModel := hOn
    critical := ?_
    inScope := ?_
    witness_subset_target := hwTarget
    adversary_target := ?_ }⟩
  · intro t ht
    exact hcritical t (le_trans (Nat.le_max_left _ _) ht)
  · intro t ht
    exact hinScope t (le_trans (Nat.le_max_right _ _) ht)
  · intro t
    apply hsub
    rw [← hP]
    exact ⟨t, rfl⟩

namespace StableTargetRun

variable {O : OracleFamily} {stream : ℕ → ℕ} {E K : Language}
    (S : StableTargetRun O stream K)

/-- The concrete Section 3.3 run, packaged for the abstract counting proof. -/
noncomputable def partialCertificate
    (hP : Presents stream E) (hsub : E ⊆ K) :
    PatientScope.PartialEnumerationCertificate := by
  let hvalid : ∀ t, S.threshold ≤ t → output O stream t ∈ K :=
    fun _ ht => PatientMachine.StableTargetRun.output_target S ht
  let G := machineTrace O stream E K S.threshold hP hsub hvalid
  let Q := PatientMachine.StableTargetRun.chargingCertificate S
  exact G.toCertificate
    (lateSwitchLoss O stream S.threshold)
    (by
      intro x hx
      exact ⟨hx.1, Q.switchLoss_subset hx⟩)
    (machineTrace_hasPredecessorComparison
      O stream E K S.threshold hP hsub hvalid)
    (fun n => Nat.log2 (PatientScope.prefixCount K n))
    Q.prefixCount_le_log2_targetCount

theorem partialCertificate_switch_log
    (hP : Presents stream E) (hsub : E ⊆ K) (n : ℕ) :
    PatientScope.prefixCount
        (S.partialCertificate hP hsub).switchLoss n ≤
      Nat.log2 ((S.partialCertificate hP hsub).targetCount n) := by
  simpa [partialCertificate, PatientScope.PartialEnumerationCertificate.targetCount]
    using
      (PatientMachine.StableTargetRun.chargingCertificate S).prefixCount_le_log2_targetCount n

end StableTargetRun
end PartialEnumeration
end GenLimit
