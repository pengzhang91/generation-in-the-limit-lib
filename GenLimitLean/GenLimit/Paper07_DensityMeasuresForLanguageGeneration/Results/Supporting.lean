import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.Feasible
import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.Topology
import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.Fallback
import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.PersistenceCounterexample
import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.InfiniteRank.OneEighth
import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.InfiniteRank.CapacityCharge

/-! # Supporting statements for the finite-rank and charging constructions -/

namespace GenLimit.KleinbergWei.DensityMeasures.Results

open Filter

/-- The proved feasibility core used toward Theorem 2.4: infinitely many
distinct languages in a feasible sequence contain any fixed finite subset
of its terminal language.  This is Claim 4.7, not the full index-breadth
characterization. -/
theorem theorem_2_4_feasibility_core
    {sequence : ℕ → Language} {terminal : Language}
    (h : FeasibleSequence sequence terminal)
    (F : Finset ℕ) (hF : (↑F : Set ℕ) ⊆ terminal) :
    (constrainedLanguages sequence F).Infinite :=
  GenLimit.KleinbergWei.DensityMeasures.claim_4_7 h F hF

/-- The proved finite-rank endgame toward Theorem 6.2: eventually, whenever
the selector changes language, its canonical fallback lies in the target.
This is Corollary 6.10. A separate generator proves the density conclusion. -/
theorem theorem_6_2_finite_rank_endgame
    {C : LanguageFamily} {stream : ℕ → ℕ} {r z : ℕ}
    (hr : TowerTopology.FiniteRankAtMost (FiniteRankParent.FamilySpace C) r)
    (hP : Presents stream (C z))
    (hfirst : FirstOccurrence C z) :
    ∃ T, ∀ round, T ≤ round →
      ∃ current : FiniteRankParent.RemainingPoint C stream round,
        ∃ next : FiniteRankParent.RemainingPoint C stream (round + 1),
          current.1 = FiniteRankParent.identifiedPointAt C stream round ∧
            next.1 = FiniteRankParent.identifiedPointAt C stream (round + 1) ∧
            (current.1.1 ≠ next.1.1 →
              ∃ fallback,
                FiniteRankFallback.fallbackChoice C stream r hr round current next =
                    some fallback ∧
                  fallback.1 ⊆ C z) :=
  GenLimit.KleinbergWei.DensityMeasures.FiniteRankFallback.corollary_6_10
    hr hP hfirst

/-- The proved conditional conclusions toward Theorem 6.12, combined in one
statement: finite eight-to-one accounting, the `1/8` lower-density bound from
uniform counting inequalities, and the corrected `1/10` ordered lower-density
bound from a capacity-two long-bad charge.

These hypotheses describe the paper's charging construction. The public Theorem 6.12
obtains the unconditional density guarantee by an independent proof. -/
theorem theorem_6_12_conditional :
    (∀ n o g s b eSingleton eGood eLong : ℕ,
      o + g + s + b = n →
      2 * s ≤ o + g + s + eSingleton →
      g ≤ 2 * o + eGood →
      b ≤ 2 * o + eLong →
      n ≤ 8 * o + eSingleton + 2 * eGood + eLong) ∧
    (∀ (O G Singleton Long : ℕ → ℕ) (eSingleton eGood eLong : ℕ),
      (∀ n, O n + G n + Singleton n + Long n = n) →
      (∀ n, 2 * Singleton n ≤ O n + G n + Singleton n + eSingleton) →
      (∀ n, G n ≤ 2 * O n + eGood) →
      (∀ n, Long n ≤ 2 * O n + eLong) →
      (1 / 8 : ℝ) ≤ liminf (fun n : ℕ => (O n : ℝ) / (n : ℝ)) atTop) ∧
    (∀ (K : OrderedLanguage) (Output Good Singleton Long : Language)
        (eSingleton eGood : ℕ),
      (∀ n,
        K.prefixCount Output n + K.prefixCount Good n +
          K.prefixCount Singleton n + K.prefixCount Long n = n) →
      (∀ᶠ n : ℕ in atTop,
        2 * K.prefixCount Singleton n ≤
          K.prefixCount Output n + K.prefixCount Good n +
            K.prefixCount Singleton n + eSingleton) →
      (∀ᶠ n : ℕ in atTop,
        K.prefixCount Good n ≤ 2 * K.prefixCount Output n + eGood) →
      InfiniteRank.LongBadCapacityTwoCharge K Output Long →
      (1 / 10 : ℝ) ≤ K.lowerDensity Output) :=
  ⟨GenLimit.KleinbergWei.DensityMeasures.InfiniteRank.theorem_6_12_finite_accounting,
    GenLimit.KleinbergWei.DensityMeasures.InfiniteRank.theorem_6_12_one_eighth_of_counting,
    GenLimit.KleinbergWei.DensityMeasures.InfiniteRank.orderedLowerDensity_one_tenth_of_longBadCapacityTwoCharge⟩

end GenLimit.KleinbergWei.DensityMeasures.Results
