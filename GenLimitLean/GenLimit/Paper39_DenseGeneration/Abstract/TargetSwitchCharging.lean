import GenLimit.Paper39_DenseGeneration.Abstract.Charging
import GenLimit.Paper39_DenseGeneration.Abstract.PatientScope

/-!
# Switch-loss charging inside an arbitrary target

This is the target-relative form of Lemma 3.13.  A charge assigned to a loss
lies both in the target and strictly before the loss.  Hence a loss below a
raw prefix `n` has its whole charge inside the target portion of that prefix.
-/

namespace GenLimit
namespace PatientScope

/-- Charge data for switch losses in a possibly sparse target language. -/
structure TargetSwitchChargingCertificate
    (target switchLoss : Set ℕ) where
  tau : ℕ → ℕ
  charge : ℕ → Finset ℕ
  switchLoss_subset : switchLoss ⊆ target
  tau_pos : ∀ ℓ, ℓ ∈ switchLoss → 0 < tau ℓ
  tau_injective : Set.InjOn tau switchLoss
  charge_size : ∀ ℓ, ℓ ∈ switchLoss → 2 ^ tau ℓ ≤ (charge ℓ).card
  charge_target : ∀ ℓ, ℓ ∈ switchLoss → ↑(charge ℓ) ⊆ target
  charge_before_loss : ∀ ℓ, ℓ ∈ switchLoss → charge ℓ ⊆ Finset.range ℓ

namespace TargetSwitchChargingCertificate

variable {target switchLoss : Set ℕ}
    (Q : TargetSwitchChargingCertificate target switchLoss)

include Q

omit Q in
/-- Finite charging bound with an arbitrary finite container for the charge
sets. -/
private theorem charging_card_le_log2_finset
    {α : Type*} [DecidableEq α]
    (losses : Finset α) (tau : α → ℕ)
    (charge : α → Finset ℕ) (container : Finset ℕ)
    (hpos : ∀ ℓ ∈ losses, 0 < tau ℓ)
    (hinj : Set.InjOn tau losses)
    (hsize : ∀ ℓ ∈ losses, 2 ^ tau ℓ ≤ (charge ℓ).card)
    (hcontainer : ∀ ℓ ∈ losses, charge ℓ ⊆ container) :
    losses.card ≤ Nat.log2 container.card := by
  classical
  by_cases hne : losses.Nonempty
  · rw [Nat.log2_eq_log_two]
    apply Nat.le_log_of_pow_le Nat.one_lt_two
    obtain ⟨ℓ, hℓ, hcardTau⟩ :=
      exists_card_le_of_injOn_pos losses tau hpos hinj hne
    calc
      2 ^ losses.card ≤ 2 ^ tau ℓ :=
        Nat.pow_le_pow_right (by omega) hcardTau
      _ ≤ (charge ℓ).card := hsize ℓ hℓ
      _ ≤ container.card := Finset.card_le_card (hcontainer ℓ hℓ)
  · have hempty : losses = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [hempty]

/-- Lemma 3.13 for an arbitrary target: losses in a raw prefix are bounded by
the logarithm of the number of target values in that prefix. -/
theorem prefixCount_le_log2_targetCount (n : ℕ) :
    prefixCount switchLoss n ≤ Nat.log2 (prefixCount target n) := by
  classical
  let losses := prefixFinset switchLoss n
  let targetPrefix := prefixFinset target n
  change losses.card ≤ Nat.log2 targetPrefix.card
  apply charging_card_le_log2_finset losses Q.tau Q.charge targetPrefix
  · intro ℓ hℓ
    exact Q.tau_pos ℓ (mem_prefixFinset.mp hℓ).2
  · intro x hx y hy hxy
    exact Q.tau_injective
      (mem_prefixFinset.mp hx).2 (mem_prefixFinset.mp hy).2 hxy
  · intro ℓ hℓ
    exact Q.charge_size ℓ (mem_prefixFinset.mp hℓ).2
  · intro ℓ hℓ x hx
    have hℓparts := mem_prefixFinset.mp hℓ
    have hxTarget : x ∈ target := Q.charge_target ℓ hℓparts.2 hx
    have hxltℓ : x < ℓ := Finset.mem_range.mp
      (Q.charge_before_loss ℓ hℓparts.2 hx)
    exact mem_prefixFinset.mpr
      ⟨lt_trans hxltℓ hℓparts.1, hxTarget⟩

end TargetSwitchChargingCertificate
end PatientScope
end GenLimit
