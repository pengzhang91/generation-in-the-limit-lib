import GenLimit.DenseGeneration.Abstract.Density
import GenLimit.DenseGeneration.Abstract.PatientScope
import GenLimit.DenseGeneration.Abstract.SwitchCharging

/-!
# Normalized Theorem 3.14 lower-density endgame

This module combines the three mathematical inputs isolated in the paper:

* the ownership partition of each normalized target prefix;
* Fact 3.12's order-decreasing injection, encoded by
  `PatientScopeCertificate.partner`;
* Lemma 3.13's logarithmic switch-loss bound.

The result below is the complete finite-counting and asymptotic proof of
Theorem 3.14.  Its argument does not assume convergence of the relevant ratio;
it proves the stated `Filter.liminf` inequality directly.

The certificate is an explicit interface to the still-separate operational
proof for the patient-scope state machine.  In particular, no theorem in this
file claims that exact inclusion between two infinite oracle languages is a
finite membership-oracle computation.
-/

open Filter

namespace GenLimit
namespace PatientScope

namespace PatientScopeCertificate

/-- Lower density after the paper's order-preserving normalization `K = ℕ`.
The value at `n = 0` is immaterial to the limit inferior. -/
noncomputable def normalizedLowerDensity (P : PatientScopeCertificate) : ℝ :=
  liminf (fun n : ℕ => (P.defenderCount n : ℝ) / (n : ℝ)) atTop

/-- Theorem 3.14, from Lemma 3.11, Fact 3.12, and Lemma 3.13 as exposed by a
`PatientScopeCertificate`.

`huniv` is the rank-map normalization of the target language.  `hcharging` is
the conclusion of Lemma 3.13.  The remaining hypotheses are named fields of
`P`, so none of the bridge assumptions is hidden in the proof.
-/
theorem theorem_3_14
    (P : PatientScopeCertificate)
    (huniv : P.target = Set.univ)
    (hcharging : ∀ n,
      prefixCount P.switchLoss n ≤ Nat.log2 (P.targetCount n)) :
    (1 / 2 : ℝ) ≤ P.normalizedLowerDensity := by
  exact lowerDensity_half_of_counting
    P.defenderCount P.attackerCount P.earlyAttacker.card
    (P.normalized_partition huniv)
    (P.normalized_attackerCount_le_log2 huniv hcharging)

/-- Theorem 3.14 with Lemma 3.13 discharged from explicit switch-loss charge
sets.  This version uses `SwitchChargingCertificate.prefixCount_le_log2`
rather than taking the logarithmic bound itself as a premise. -/
theorem theorem_3_14_of_charging_certificate
    (P : PatientScopeCertificate)
    (huniv : P.target = Set.univ)
    (Q : SwitchChargingCertificate P.switchLoss) :
    (1 / 2 : ℝ) ≤ P.normalizedLowerDensity := by
  apply P.theorem_3_14 huniv
  intro n
  have htarget : P.targetCount n = n := by
    simp [targetCount, prefixCount, prefixFinset, huniv]
  simpa [htarget] using Q.prefixCount_le_log2 n

end PatientScopeCertificate
end PatientScope
end GenLimit
