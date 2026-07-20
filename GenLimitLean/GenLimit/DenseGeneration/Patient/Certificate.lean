import GenLimit.DenseGeneration.Patient.Validity
import GenLimit.DenseGeneration.Patient.Fact312
import GenLimit.DenseGeneration.Abstract.TargetSwitchCharging

/-!
# Final patient-scope certificate assembly

This module chooses one canonical threshold at which the presented target is
both recursively critical and inside the patient scope.  The same threshold
controls eventual output validity, the finite early exception set, and the
late switch losses used in charging.

Given concrete target-relative charge data for those late switch losses, the
module assembles the `PatientScopeCertificate` consumed by Theorem 3.14.
-/

namespace GenLimit
namespace PatientMachine

/-- Canonical first threshold witnessing eventual target criticality. -/
noncomputable def criticalStart
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z)) : ℕ := by
  classical
  exact Nat.find (target_eventually_recursiveCritical hP)

theorem criticalStart_spec
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z)) :
    ∀ t, criticalStart O stream z hP ≤ t →
      RecursiveCritical O.language stream t z := by
  classical
  exact Nat.find_spec (target_eventually_recursiveCritical hP)

/-- Canonical first threshold witnessing eventual inclusion of the target
index in the scope. -/
noncomputable def scopeStart
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z)) : ℕ := by
  classical
  exact Nat.find (target_eventually_in_scope O stream hP)

theorem scopeStart_spec
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z)) :
    ∀ t, scopeStart O stream z hP ≤ t →
      z < (run O stream t).scope := by
  classical
  exact Nat.find_spec (target_eventually_in_scope O stream hP)

/-- Canonical common threshold for the settled patient-scope regime. -/
noncomputable def settledThreshold
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z)) : ℕ :=
  max (criticalStart O stream z hP) (scopeStart O stream z hP)

theorem settled_target_critical
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z))
    {t : ℕ} (ht : settledThreshold O stream z hP ≤ t) :
    RecursiveCritical O.language stream t z := by
  apply criticalStart_spec O stream z hP t
  exact le_trans (Nat.le_max_left _ _) ht

theorem settled_target_in_scope
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z))
    {t : ℕ} (ht : settledThreshold O stream z hP ≤ t) :
    z < (run O stream t).scope := by
  apply scopeStart_spec O stream z hP t
  exact le_trans (Nat.le_max_right _ _) ht

/-- Every output from the settled threshold onward lies in the target. -/
theorem settled_output_target
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z))
    {t : ℕ} (ht : settledThreshold O stream z hP ≤ t) :
    output O stream t ∈ O.language z := by
  have ht' : settledThreshold O stream z hP ≤ t + 1 := by omega
  have hfocus := run_focus_isFocus O hP (t + 1)
  have hsub : O.language (run O stream (t + 1)).focus ⊆ O.language z :=
    focus_subset_target hfocus
      (settled_target_in_scope O stream z hP ht')
      (settled_target_critical O stream z hP ht')
  exact hsub (output_mem_round_focus O stream t)

/-- The concrete game trace at the canonical settled threshold. -/
noncomputable def settledGameTrace
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z)) : PatientScope.GameTrace :=
  gameTrace O stream z (settledThreshold O stream z hP) hP
    (fun _ ht => settled_output_target O stream z hP ht)

/-- The post-validity switch-loss set used by the final certificate. -/
noncomputable def settledSwitchLoss
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z)) : Set ℕ :=
  lateSwitchLoss O stream (settledThreshold O stream z hP)

@[simp] theorem settledGameTrace_target
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z)) :
    (settledGameTrace O stream z hP).target = O.language z := rfl

@[simp] theorem settledGameTrace_validFrom
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z)) :
    (settledGameTrace O stream z hP).validFrom =
      settledThreshold O stream z hP := rfl

theorem settledSwitchLoss_subset
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z)) :
    settledSwitchLoss O stream z hP ⊆
      (settledGameTrace O stream z hP).attacker ∩
        (settledGameTrace O stream z hP).target := by
  simpa [settledSwitchLoss, settledGameTrace] using
    lateSwitchLoss_subset_attacker_target O hP
      (fun _ ht => settled_output_target O stream z hP ht)

/-- Assemble all non-charging parts of Theorem 3.14 with a supplied concrete
target-relative charging certificate.  Its budget is
`log2 (prefixCount target n)`, exactly the target-count form needed before the
paper's order-preserving normalization. -/
noncomputable def patientScopeCertificate
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z))
    (Q : PatientScope.TargetSwitchChargingCertificate
      (O.language z) (settledSwitchLoss O stream z hP)) :
    PatientScope.PatientScopeCertificate := by
  let G := settledGameTrace O stream z hP
  let losses := settledSwitchLoss O stream z hP
  exact G.toCertificate losses
    (settledSwitchLoss_subset O stream z hP)
    G.predecessorPartner
    (fun _ hx => predecessorPartner_mem_machine O stream z
      (settledThreshold O stream z hP) hP
      (fun _ ht => settled_output_target O stream z hP ht) hx)
    (fun _ hx => predecessorPartner_lt_machine O stream z
      (settledThreshold O stream z hP) hP
      (fun _ ht => settled_output_target O stream z hP ht) hx)
    (predecessorPartner_injective_machine O stream z
      (settledThreshold O stream z hP) hP
      (fun _ ht => settled_output_target O stream z hP ht))
    (fun n => Nat.log2 (PatientScope.prefixCount (O.language z) n))
    (fun n => Q.prefixCount_le_log2_targetCount n)

@[simp] theorem patientScopeCertificate_target
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z))
    (Q : PatientScope.TargetSwitchChargingCertificate
      (O.language z) (settledSwitchLoss O stream z hP)) :
    (patientScopeCertificate O stream z hP Q).target = O.language z := rfl

@[simp] theorem patientScopeCertificate_switchLoss
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z))
    (Q : PatientScope.TargetSwitchChargingCertificate
      (O.language z) (settledSwitchLoss O stream z hP)) :
    (patientScopeCertificate O stream z hP Q).switchLoss =
      settledSwitchLoss O stream z hP := rfl

@[simp] theorem patientScopeCertificate_validFrom
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z))
    (Q : PatientScope.TargetSwitchChargingCertificate
      (O.language z) (settledSwitchLoss O stream z hP)) :
    (patientScopeCertificate O stream z hP Q).validFrom =
      settledThreshold O stream z hP := rfl

/-- The assembled certificate carries the target-aware logarithmic switch
budget supplied by `Q`. -/
theorem patientScopeCertificate_switch_bound
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ)
    (hP : Presents stream (O.language z))
    (Q : PatientScope.TargetSwitchChargingCertificate
      (O.language z) (settledSwitchLoss O stream z hP)) (n : ℕ) :
    PatientScope.prefixCount
        (patientScopeCertificate O stream z hP Q).switchLoss n ≤
      Nat.log2
        ((patientScopeCertificate O stream z hP Q).targetCount n) := by
  simpa [PatientScope.PatientScopeCertificate.targetCount] using
    Q.prefixCount_le_log2_targetCount n

end PatientMachine
end GenLimit
