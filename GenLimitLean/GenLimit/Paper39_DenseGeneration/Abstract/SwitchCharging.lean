import GenLimit.Paper39_DenseGeneration.Abstract.Charging
import GenLimit.Paper39_DenseGeneration.Abstract.PatientScope

/-!
# Switch-loss certificates

This module turns the abstract finite charging lemma into the prefix bound
used by Theorem 3.14.  Each switch loss has a distinct positive `tau` label and
a charge set of at least `2 ^ tau` earlier values.
-/

namespace GenLimit
namespace PatientScope

/-- The static content of the charging construction in Lemma 3.13. -/
structure SwitchChargingCertificate (switchLoss : Set ℕ) where
  tau : ℕ → ℕ
  charge : ℕ → Finset ℕ
  tau_pos : ∀ ℓ, ℓ ∈ switchLoss → 0 < tau ℓ
  tau_injective : Set.InjOn tau switchLoss
  charge_size : ∀ ℓ, ℓ ∈ switchLoss → 2 ^ tau ℓ ≤ (charge ℓ).card
  /-- Charged generator-first values are smaller than the loss. -/
  charge_before_loss : ∀ ℓ, ℓ ∈ switchLoss → charge ℓ ⊆ Finset.range ℓ

namespace SwitchChargingCertificate

variable {switchLoss : Set ℕ} (Q : SwitchChargingCertificate switchLoss)

include Q

/-- Lemma 3.13: the number of certified switch losses in a prefix is at most
the base-two logarithm of the prefix length. -/
theorem prefixCount_le_log2 (n : ℕ) :
    prefixCount switchLoss n ≤ Nat.log2 n := by
  classical
  by_cases hn : n = 0
  · simp [hn, prefixCount, prefixFinset]
  · unfold prefixCount
    apply charging_card_le_log2
      (prefixFinset switchLoss n)
      (GenLimit.PatientScope.SwitchChargingCertificate.tau Q)
      (GenLimit.PatientScope.SwitchChargingCertificate.charge Q) n
    · intro ℓ hℓ
      exact GenLimit.PatientScope.SwitchChargingCertificate.tau_pos Q
        ℓ (mem_prefixFinset.mp hℓ).2
    · intro x hx y hy hxy
      exact GenLimit.PatientScope.SwitchChargingCertificate.tau_injective Q
        (mem_prefixFinset.mp hx).2 (mem_prefixFinset.mp hy).2 hxy
    · intro ℓ hℓ
      exact GenLimit.PatientScope.SwitchChargingCertificate.charge_size Q
        ℓ (mem_prefixFinset.mp hℓ).2
    · intro ℓ hℓ x hx
      have hxℓ : x < ℓ := Finset.mem_range.mp
        (GenLimit.PatientScope.SwitchChargingCertificate.charge_before_loss Q
          ℓ (mem_prefixFinset.mp hℓ).2 hx)
      exact Finset.mem_range.mpr
        (lt_trans hxℓ (mem_prefixFinset.mp hℓ).1)
    · exact Nat.pos_of_ne_zero hn

end SwitchChargingCertificate
end PatientScope
end GenLimit
