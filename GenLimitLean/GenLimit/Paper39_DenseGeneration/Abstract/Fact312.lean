import GenLimit.Paper39_DenseGeneration.Abstract.GameTrace
import Mathlib.Data.Nat.Find

/-!
# The predecessor pairing behind Fact 3.12

This file turns the local minimum-output comparison in a concrete game trace
into the global injective partner map used by the density count.  The finite
exception set includes the first valid round, so every paired predecessor is
already target-valid.
-/

namespace GenLimit
namespace PatientScope

namespace GameTrace

variable (G : GameTrace)

/-- First round in which the adversary announces `x`, defaulting to `0` for a
value outside the adversary range. -/
noncomputable def firstAdversaryTime (x : ℕ) : ℕ := by
  classical
  exact if h : ∃ t, G.adversary t = x then Nat.find h else 0

theorem firstAdversaryTime_spec {x : ℕ} (hx : x ∈ G.attacker) :
    G.adversary (G.firstAdversaryTime x) = x := by
  classical
  obtain ⟨t, htx, -⟩ := hx
  simp only [firstAdversaryTime]
  split
  · exact Nat.find_spec ‹∃ t, G.adversary t = x›
  · exact False.elim (‹¬ ∃ t, G.adversary t = x› ⟨t, htx⟩)

theorem firstAdversaryTime_min {x t : ℕ} (hx : x ∈ G.attacker)
    (ht : G.adversary t = x) : G.firstAdversaryTime x ≤ t := by
  classical
  obtain ⟨w, hw, -⟩ := hx
  simp only [firstAdversaryTime]
  split
  · exact Nat.find_min' ‹∃ q, G.adversary q = x› ht
  · exact False.elim (‹¬ ∃ q, G.adversary q = x› ⟨w, hw⟩)

theorem firstAdversaryTime_not_mem_sample {x : ℕ} (hx : x ∈ G.attacker) :
    x ∉ sample G.adversary (G.firstAdversaryTime x) := by
  intro hmem
  rw [mem_sample_iff] at hmem
  obtain ⟨s, hs, hseq⟩ := hmem
  exact (Nat.not_lt_of_ge (G.firstAdversaryTime_min hx hseq)) hs

theorem generator_ne_before_firstAdversaryTime
    {x s : ℕ} (hx : x ∈ G.attacker)
    (hs : s < G.firstAdversaryTime x) : G.generator s ≠ x := by
  have hxA := hx
  obtain ⟨t, htx, hnoGenerator⟩ := hx
  have hfirstLe : G.firstAdversaryTime x ≤ t :=
    G.firstAdversaryTime_min hxA htx
  exact hnoGenerator s (lt_of_lt_of_le hs hfirstLe)

/-- An ordinary attacker-first value occurs strictly after `validFrom`; this
is the one-round boundary adjustment needed by Fact 3.12. -/
theorem validFrom_lt_firstAdversaryTime
    {switchLoss : Set ℕ} {x : ℕ}
    (hx : x ∈ ordinaryAttacker
      G.target G.attacker switchLoss G.earlyAttacker) :
    G.validFrom < G.firstAdversaryTime x := by
  have hxA : x ∈ G.attacker := hx.1.1
  have hnotEarly : x ∉ G.earlyAttacker := by
    intro hearly
    exact hx.2 (Set.mem_union_left _ hearly)
  by_contra hnot
  have htime : G.firstAdversaryTime x < G.validFrom + 1 := by omega
  apply hnotEarly
  classical
  simp only [earlyAttacker, Finset.mem_filter]
  refine ⟨?_, hxA⟩
  rw [mem_sample_iff]
  exact ⟨G.firstAdversaryTime x, htime,
    G.firstAdversaryTime_spec hxA⟩

/-- Pair an attacker value with the generator output immediately before its
first adversary announcement. -/
noncomputable def predecessorPartner (x : ℕ) : ℕ :=
  G.generator (G.firstAdversaryTime x - 1)

/-- Local minimum-output fact required from a concrete patient-scope run. -/
def HasPredecessorComparison (switchLoss : Set ℕ) : Prop :=
  ∀ t, G.validFrom < t →
    G.adversary t ∈ G.attacker →
    G.adversary t ∉ sample G.adversary t →
    G.adversary t ∉ switchLoss →
    G.generator (t - 1) < G.adversary t

theorem predecessorPartner_mem
    {switchLoss : Set ℕ}
    {x : ℕ}
    (hx : x ∈ ordinaryAttacker
      G.target G.attacker switchLoss G.earlyAttacker) :
    G.predecessorPartner x ∈ G.defender ∩ G.target := by
  have htime := G.validFrom_lt_firstAdversaryTime hx
  refine ⟨?_, ?_⟩
  · rw [← G.output_range]
    exact ⟨G.firstAdversaryTime x - 1, rfl⟩
  · apply G.eventual_target
    omega

theorem predecessorPartner_lt
    {switchLoss : Set ℕ}
    (hcompare : G.HasPredecessorComparison switchLoss)
    {x : ℕ}
    (hx : x ∈ ordinaryAttacker
      G.target G.attacker switchLoss G.earlyAttacker) :
    G.predecessorPartner x < x := by
  have htime := G.validFrom_lt_firstAdversaryTime hx
  have hxA : x ∈ G.attacker := hx.1.1
  have hspec := G.firstAdversaryTime_spec hxA
  have hAat : G.adversary (G.firstAdversaryTime x) ∈ G.attacker := by
    rw [hspec]
    exact hxA
  have hnotSwitch : G.adversary (G.firstAdversaryTime x) ∉ switchLoss := by
    rw [hspec]
    intro hswitch
    exact hx.2 (Set.mem_union_right _ hswitch)
  have hfresh : G.adversary (G.firstAdversaryTime x) ∉
      sample G.adversary (G.firstAdversaryTime x) := by
    simpa [hspec] using G.firstAdversaryTime_not_mem_sample hxA
  have h := hcompare (G.firstAdversaryTime x) htime hAat hfresh hnotSwitch
  simpa [predecessorPartner, hspec] using h

theorem predecessorPartner_injective
    {switchLoss : Set ℕ} :
    Set.InjOn G.predecessorPartner
      (ordinaryAttacker G.target G.attacker switchLoss G.earlyAttacker) := by
  intro x hx y hy hxy
  have htx := G.validFrom_lt_firstAdversaryTime hx
  have hty := G.validFrom_lt_firstAdversaryTime hy
  have hpred : G.firstAdversaryTime x - 1 =
      G.firstAdversaryTime y - 1 := by
    apply G.generator_injective
    exact hxy
  have htime : G.firstAdversaryTime x = G.firstAdversaryTime y := by
    omega
  have hxA : x ∈ G.attacker := hx.1.1
  have hyA : y ∈ G.attacker := hy.1.1
  calc
    x = G.adversary (G.firstAdversaryTime x) :=
      (G.firstAdversaryTime_spec hxA).symm
    _ = G.adversary (G.firstAdversaryTime y) := by rw [htime]
    _ = y := G.firstAdversaryTime_spec hyA

end GameTrace
end PatientScope
end GenLimit
