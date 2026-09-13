import GenLimit.Paper32_InfinitelyManyHallucinations.Definitions

/-!
# Coverage-based recall

The paper observes that its coverage-based recall is the ordered relative
density introduced by Kleinberg--Wei.  This module uses the shared Core API
and proves Lemma 4.7 without duplicating the liminf/limsup complement
calculation.
-/

namespace GenLimit.InfinitelyManyHallucinations

open GenLimit.KleinbergWei

theorem lowerRecall_nonneg (target : OrderedLanguage) (guess : Language) :
    0 ≤ lowerRecall target guess :=
  target.lowerDensity_nonneg guess

theorem lowerRecall_le_one (target : OrderedLanguage) (guess : Language) :
    lowerRecall target guess ≤ 1 :=
  target.lowerDensity_le_one guess

theorem upperRecall_nonneg (target : OrderedLanguage) (guess : Language) :
    0 ≤ upperRecall target guess :=
  target.upperDensity_nonneg guess

theorem upperRecall_le_one (target : OrderedLanguage) (guess : Language) :
    upperRecall target guess ≤ 1 :=
  target.upperDensity_le_one guess

/-- Lemma 4.7.  If the guess eventually contains every target string never
revealed by the adversary, then its lower recall is at least one minus the
adversary's upper recall. -/
theorem lemma_4_7
    (target : OrderedLanguage) (adversary guess : Language)
    (hcoverage : target.carrier \ adversary ⊆ guess) :
    1 - upperRecall target adversary ≤ lowerRecall target guess := by
  rw [lowerRecall, upperRecall, ← target.lowerDensity_diff adversary]
  exact target.lowerDensity_mono hcoverage

/-- Equality form used when exploration enumerates the entire ambient
universe: perfect coverage has perfect recall. -/
theorem lowerRecall_eq_one_of_target_subset
    (target : OrderedLanguage) {guess : Language}
    (hcoverage : target.carrier ⊆ guess) :
    lowerRecall target guess = 1 := by
  apply le_antisymm (lowerRecall_le_one target guess)
  rw [lowerRecall, ← target.lowerDensity_carrier]
  exact target.lowerDensity_mono hcoverage

end GenLimit.InfinitelyManyHallucinations
