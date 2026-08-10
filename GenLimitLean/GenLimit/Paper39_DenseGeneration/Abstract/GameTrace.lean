import GenLimit.Paper39_DenseGeneration.Abstract.Announcements
import GenLimit.Paper39_DenseGeneration.Abstract.PatientScope

/-!
# Concrete game traces and patient-scope certificates

This file connects the abstract ownership sets in `PatientScopeCertificate`
to two concrete round-by-round announcement sequences.  It discharges the
ownership partition, output-range, and freshness parts of the certificate.
The patient-scope-specific partner and switch-loss properties remain named
inputs.
-/

namespace GenLimit
namespace PatientScope

/-- A play of the announcement game.  The adversary speaks first in round
`t`, followed by the generator. -/
structure GameTrace where
  target : Language
  adversary : ℕ → ℕ
  generator : ℕ → ℕ
  presents : Presents adversary target
  /-- The round-`t` output has not appeared in the adversary sequence through
  that round. -/
  fresh_adversary : ∀ t s, s ≤ t → adversary s ≠ generator t
  /-- The generator does not repeat one of its earlier outputs. -/
  fresh_generator : ∀ t s, s < t → generator s ≠ generator t
  validFrom : ℕ
  eventual_target : ∀ t, validFrom ≤ t → generator t ∈ target

namespace GameTrace

variable (G : GameTrace)

/-- Concrete attacker ownership set. -/
def attacker : Set ℕ := AdversaryFirst G.adversary G.generator

/-- Concrete defender ownership set. -/
def defender : Set ℕ := GeneratorFirst G.adversary G.generator

/-- Every generator output is defender-first because outputs are fresh after
the adversary's announcement in the same round. -/
theorem output_range : Set.range G.generator = G.defender := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, rfl, G.fresh_adversary t⟩
  · rintro ⟨t, htx, -⟩
    exact ⟨t, htx⟩

theorem generator_injective : Function.Injective G.generator := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij' | hji'
  · exact G.fresh_generator j i hij' hij
  · exact G.fresh_generator i j hji' hij.symm

theorem target_covered : G.target ⊆ G.attacker ∪ G.defender := by
  intro x hx
  apply range_subset_first_announcements G.adversary G.generator
  rw [G.presents]
  exact hx

theorem ownership_disjoint : Disjoint G.attacker G.defender :=
  adversaryFirst_disjoint_generatorFirst G.adversary G.generator

/-- The full novelty statement supplied by the two freshness fields. -/
theorem eventual_validity_and_novelty :
    ∃ T, ∀ t, T ≤ t →
      G.generator t ∈ G.target ∧
      (∀ s, s ≤ t → G.adversary s ≠ G.generator t) ∧
      (∀ s, s < t → G.generator s ≠ G.generator t) := by
  exact ⟨G.validFrom, fun t ht =>
    ⟨G.eventual_target t ht, G.fresh_adversary t, G.fresh_generator t⟩⟩

/-- The finite exceptional set used in Theorem 3.14.  It includes attacker-first
values announced through the first valid round.  The extra round is needed
because Fact 3.12 pairs the round-`t` adversary value with the generator output
from round `t - 1`. -/
noncomputable def earlyAttacker : Finset ℕ := by
  classical
  exact (sample G.adversary (G.validFrom + 1)).filter
    (fun x => x ∈ G.attacker)

/-- Construct the theorem-level certificate from a concrete fresh trace.
Only Fact 3.12's partner and Lemma 3.13's switch budget remain to be supplied.
-/
noncomputable def toCertificate
    (switchLoss : Set ℕ)
    (hswitch : switchLoss ⊆ G.attacker ∩ G.target)
    (partner : ℕ → ℕ)
    (hpartnerMem : ∀ x,
      x ∈ ordinaryAttacker G.target G.attacker switchLoss G.earlyAttacker →
        partner x ∈ G.defender ∩ G.target)
    (hpartnerLt : ∀ x,
      x ∈ ordinaryAttacker G.target G.attacker switchLoss G.earlyAttacker →
        partner x < x)
    (hpartnerInj : Set.InjOn partner
      (ordinaryAttacker G.target G.attacker switchLoss G.earlyAttacker))
    (switchBudget : ℕ → ℕ)
    (hbudget : ∀ n, prefixCount switchLoss n ≤ switchBudget n) :
    PatientScopeCertificate where
  target := G.target
  attacker := G.attacker
  defender := G.defender
  output := G.generator
  output_range := G.output_range
  output_injective := G.generator_injective
  validFrom := G.validFrom
  eventual_target := G.eventual_target
  target_covered := G.target_covered
  ownership_disjoint := G.ownership_disjoint
  earlyAttacker := G.earlyAttacker
  switchLoss := switchLoss
  switchLoss_subset := hswitch
  partner := partner
  partner_mem := hpartnerMem
  partner_lt := hpartnerLt
  partner_injective := hpartnerInj
  switchBudget := switchBudget
  switch_prefix_le := hbudget

end GameTrace
end PatientScope
end GenLimit
