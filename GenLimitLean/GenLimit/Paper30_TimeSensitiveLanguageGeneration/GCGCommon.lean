import GenLimit.Paper30_TimeSensitiveLanguageGeneration.AccurateBridge
import GenLimit.Core.OrderedDensity
import Mathlib.Tactic

/-!
# Shared infrastructure for Generation via Consistent Guessing

This module contains the queue-policy-independent data and greedy output operation
shared by the printed strict-rise GCG skeleton and the queue-totalized repair.
It deliberately contains no candidate-queue policy and no stage transition.
-/

namespace GenLimit.TimeSensitive

open GenLimit.KleinbergWei
open GenLimit.KleinbergWei.DensityMeasures

/-- A family together with the canonical order inherited by each language.
The coherence field rules out assigning two different orders to equal sets. -/
structure CanonicallyOrderedFamily where
  language : LanguageFamily
  order : ℕ → OrderedLanguage
  carrier_eq : ∀ i, (order i).carrier = language i
  order_eq_of_language_eq :
    ∀ {i j}, language i = language j → (order i).enumeration = (order j).enumeration

namespace CanonicallyOrderedFamily

variable (F : CanonicallyOrderedFamily)

/-- Every family member is infinite because its canonical order is an
injective enumeration by all natural ranks. -/
theorem language_infinite (i : ℕ) : (F.language i).Infinite := by
  rw [← F.carrier_eq i, ← (F.order i).range_enumeration]
  exact Set.infinite_range_of_injective (F.order i).enumeration_injective

/-- The P07 semantic selector used as Appendix E's `Accurate` subroutine. -/
noncomputable def guess (stream : ℕ → ℕ) (t : ℕ) : ℕ :=
  guessIndex F.language stream t

end CanonicallyOrderedFamily

/-- Ranks eligible for the source's `OnTimeUnused` operation. -/
def OnTimeUnusedRank
    (O : OrderedLanguage) (used : Finset ℕ) (t r : ℕ) : Prop :=
  t < r ∧ O.enumeration r ∉ used

/-- Among `used.card + 1` ranks strictly after `t`, at least one has an
unused image under an injective language enumeration. -/
theorem exists_onTimeUnusedRank
    (O : OrderedLanguage) (used : Finset ℕ) (t : ℕ) :
    ∃ r, OnTimeUnusedRank O used t r := by
  classical
  let ranks := Finset.Icc (t + 1) (t + used.card + 1)
  by_contra h
  push_neg at h
  have hmaps : ∀ r ∈ ranks, O.enumeration r ∈ used := by
    intro r hr
    by_contra hnot
    exact h r
      ⟨Nat.lt_of_succ_le (Finset.mem_Icc.mp hr).1, hnot⟩
  have hsubset : ranks.image O.enumeration ⊆ used := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
    exact hmaps r hr
  have hcardImage : (ranks.image O.enumeration).card = ranks.card := by
    exact Finset.card_image_iff.mpr fun a _ b _ hab =>
      O.enumeration_injective hab
  have hcardRanks : ranks.card = used.card + 1 := by
    simp only [ranks, Nat.card_Icc]
    omega
  have hle := Finset.card_le_card hsubset
  omega

/-- The least on-time rank whose language element has not been used. -/
noncomputable def onTimeUnusedRank
    (O : OrderedLanguage) (used : Finset ℕ) (t : ℕ) : ℕ :=
  by
    classical
    exact Nat.find (exists_onTimeUnusedRank O used t)

theorem onTimeUnusedRank_spec
    (O : OrderedLanguage) (used : Finset ℕ) (t : ℕ) :
    OnTimeUnusedRank O used t (onTimeUnusedRank O used t) :=
  by
    classical
    exact Nat.find_spec (exists_onTimeUnusedRank O used t)

theorem onTimeUnusedRank_min
    (O : OrderedLanguage) (used : Finset ℕ) (t : ℕ)
    {r : ℕ} (hr : OnTimeUnusedRank O used t r) :
    onTimeUnusedRank O used t ≤ r :=
  by
    classical
    exact Nat.find_min' (exists_onTimeUnusedRank O used t) hr

/-- Algorithm 2's first fresh member that has not missed its identity
deadline, expressed through the supplied canonical language order. -/
noncomputable def onTimeUnused
    (O : OrderedLanguage) (used : Finset ℕ) (t : ℕ) : ℕ :=
  O.enumeration (onTimeUnusedRank O used t)

theorem onTimeUnused_mem
    (O : OrderedLanguage) (used : Finset ℕ) (t : ℕ) :
    onTimeUnused O used t ∈ O.carrier := by
  rw [← O.range_enumeration]
  exact ⟨onTimeUnusedRank O used t, rfl⟩

theorem onTimeUnused_fresh
    (O : OrderedLanguage) (used : Finset ℕ) (t : ℕ) :
    onTimeUnused O used t ∉ used :=
  (onTimeUnusedRank_spec O used t).2

theorem onTimeUnused_onTime
    (O : OrderedLanguage) (used : Finset ℕ) (t : ℕ) :
    t < onTimeUnusedRank O used t :=
  (onTimeUnusedRank_spec O used t).1

/-- Values unavailable after the adversary has spoken in round `t`. -/
noncomputable def greedyUsed
    (stream : ℕ → ℕ) (t : ℕ) (outputs : List ℕ) : Finset ℕ :=
  sample stream (t + 1) ∪ outputs.toFinset

/-- Shared greedy output operation once a queue policy has selected the active
ordered language. -/
noncomputable def greedyRoundOutput
    (O : OrderedLanguage) (stream : ℕ → ℕ)
    (t : ℕ) (outputs : List ℕ) : ℕ :=
  onTimeUnused O (greedyUsed stream t outputs) t

/-- Turn a finite chronological output history into a total sequence.  Only
prefixes below `outputs.length` are semantically used by the machines. -/
def outputHistoryStream (outputs : List ℕ) : ℕ → ℕ :=
  fun t => outputs.getD t 0

end GenLimit.TimeSensitive
