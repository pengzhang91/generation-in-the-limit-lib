import GenLimit.DenseGeneration.Abstract.TargetDensity
import GenLimit.DenseGeneration.Abstract.TargetSwitchCharging
import GenLimit.DenseGeneration.Abstract.PatientScope

/-!
# Theorem 3.14 for an arbitrary infinite target

This is the abstract assembly of the paper's lower-density theorem without
normalizing the target to `Set.univ`.  The denominator is the number of target
elements in the ambient prefix, exactly as in the paper's definition.
-/

namespace GenLimit
namespace PatientScope
namespace PatientScopeCertificate

/-- The paper's lower density of defender-first target elements, measured in
ambient natural-number prefixes.  The finitely many prefixes with denominator
zero do not affect the limit inferior for an infinite target. -/
noncomputable def targetLowerDensity (P : PatientScopeCertificate) : ℝ :=
  relativeLowerDensity (P.defender ∩ P.target) P.target

/-- Theorem 3.14 in its exact arbitrary-target form, assembled from the
ownership partition, Fact 3.12's partner injection, Lemma 3.13's target-aware
charging certificate, and the ambient-prefix asymptotic theorem. -/
theorem theorem_3_14_target
    (P : PatientScopeCertificate)
    (hInfinite : P.target.Infinite)
    (Q : TargetSwitchChargingCertificate P.target P.switchLoss) :
    (1 / 2 : ℝ) ≤ P.targetLowerDensity := by
  have hpartition : ∀ n,
      P.defenderCount n + P.attackerCount n = prefixCount P.target n := by
    intro n
    calc
      P.defenderCount n + P.attackerCount n =
          P.attackerCount n + P.defenderCount n := Nat.add_comm _ _
      _ = P.targetCount n := (P.targetCount_eq n).symm
      _ = prefixCount P.target n := rfl
  have hlog : ∀ n,
      prefixCount P.switchLoss n ≤ Nat.log2 (P.targetCount n) := by
    intro n
    simpa only [targetCount] using Q.prefixCount_le_log2_targetCount n
  have hcharge : ∀ n,
      P.attackerCount n ≤
        P.defenderCount n + P.earlyAttacker.card +
          Nat.log2 (prefixCount P.target n) := by
    intro n
    simpa only [targetCount] using P.attackerCount_le_log2 hlog n
  have h := lowerDensity_half_of_target_counting
    P.target hInfinite P.defenderCount P.attackerCount
    P.earlyAttacker.card hpartition hcharge
  simpa only [targetLowerDensity, relativeLowerDensity, defenderCount,
    targetCount] using h

end PatientScopeCertificate
end PatientScope
end GenLimit
