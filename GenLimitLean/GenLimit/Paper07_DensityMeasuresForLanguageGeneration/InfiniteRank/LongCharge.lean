import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.InfiniteRank.OneEighth

/-!
# The long-bad-run charging interface

This file isolates the remaining dynamic input needed by the long-run part of
Kleinberg--Wei's infinite-rank density argument.  Positions are indices in the
fixed ordering of the target language.  A `LongBadCharge` retains enough long
bad positions and injectively sends every retained position to an earlier
position at which the generator did output.
-/

open Filter

namespace GenLimit.KleinbergWei.DensityMeasures.InfiniteRank

/-- Number of positions from `P` among `0, ..., n - 1`. -/
noncomputable def positionPrefixCount (P : Set ℕ) (n : ℕ) : ℕ := by
  classical
  exact ((Finset.range n).filter fun i => i ∈ P).card

/-- The precise finite-prefix interface for the backward charge of positions
in long bad runs.

`half_mass` permits a fixed finite error, accounting for an initial cutoff and
the possible boundary run at the end of a prefix.  The strict inequality in
`charge_earlier` ensures that restricting the charge to any prefix still lands
inside that prefix.  Here “earlier” means earlier in `K.enumeration`, not
merely earlier in generation time.
-/
structure LongBadCharge
    (K : OrderedLanguage) (Output Long : Language) where
  retained : Set ℕ
  charge : ℕ → ℕ
  longError : ℕ
  retained_long :
    ∀ ⦃i : ℕ⦄, i ∈ retained → K.enumeration i ∈ Long
  half_mass :
    ∀ᶠ n : ℕ in atTop,
      K.prefixCount Long n ≤
        2 * positionPrefixCount retained n + longError
  charge_earlier :
    ∀ ⦃i : ℕ⦄, i ∈ retained → charge i < i
  charge_output :
    ∀ ⦃i : ℕ⦄, i ∈ retained → K.enumeration (charge i) ∈ Output
  charge_injective :
    Set.InjOn charge retained

namespace LongBadCharge

/-- Every retained position is genuinely a long-bad position, prefix by
prefix. -/
theorem retainedPrefix_le_longPrefix
    {K : OrderedLanguage} {Output Long : Language}
    (C : LongBadCharge K Output Long) (n : ℕ) :
    positionPrefixCount C.retained n ≤ K.prefixCount Long n := by
  classical
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
  exact ⟨hi.1, C.retained_long hi.2⟩

/-- An earlier injective output charge embeds every retained prefix into the
output positions in the same prefix. -/
theorem retainedPrefix_le_outputPrefix
    {K : OrderedLanguage} {Output Long : Language}
    (C : LongBadCharge K Output Long) (n : ℕ) :
    positionPrefixCount C.retained n ≤ K.prefixCount Output n := by
  classical
  let source : Finset ℕ :=
    (Finset.range n).filter fun i => i ∈ C.retained
  let target : Finset ℕ :=
    (Finset.range n).filter fun i => K.enumeration i ∈ Output
  have hmaps : Set.MapsTo C.charge source target := by
    intro i hi
    have hi' : i ∈ Finset.range n ∧ i ∈ C.retained := by
      simpa [source] using hi
    have hcharge_lt_n : C.charge i < n :=
      lt_trans (C.charge_earlier hi'.2) (Finset.mem_range.mp hi'.1)
    have hcharge_output :
        K.enumeration (C.charge i) ∈ Output :=
      C.charge_output hi'.2
    simpa [target, hcharge_lt_n] using hcharge_output
  have hinj : Set.InjOn C.charge source := by
    intro i hi j hj hij
    apply C.charge_injective
    · have hi' : i < n ∧ i ∈ C.retained := by
        simpa [source] using hi
      exact hi'.2
    · have hj' : j < n ∧ j ∈ C.retained := by
        simpa [source] using hj
      exact hj'.2
    · exact hij
  have hcard : source.card ≤ target.card :=
    card_le_of_injective_charge source target C.charge hmaps hinj
  simpa [source, target, positionPrefixCount,
    OrderedLanguage.prefixCount] using hcard

/-- The retained-half estimate and the injective backward charge imply the
long-run inequality required by the one-eighth accounting lemma. -/
theorem eventually_long_le
    {K : OrderedLanguage} {Output Long : Language}
    (C : LongBadCharge K Output Long) :
    ∀ᶠ n : ℕ in atTop,
      K.prefixCount Long n ≤
        2 * K.prefixCount Output n + C.longError := by
  filter_upwards [C.half_mass] with n hn
  calc
    K.prefixCount Long n
        ≤ 2 * positionPrefixCount C.retained n + C.longError := hn
    _ ≤ 2 * K.prefixCount Output n + C.longError := by
      gcongr
      exact C.retainedPrefix_le_outputPrefix n

end LongBadCharge

/-- Once the singleton and good-position charges are available, a
`LongBadCharge` supplies the final hypothesis of the verified one-eighth
counting theorem. -/
theorem orderedLowerDensity_one_eighth_of_longBadCharge
    (K : OrderedLanguage)
    (Output Good Singleton Long : Language)
    (eSingleton eGood : ℕ)
    (hpartition : ∀ n,
      K.prefixCount Output n +
          K.prefixCount Good n +
          K.prefixCount Singleton n +
          K.prefixCount Long n = n)
    (hsingleton : ∀ᶠ n : ℕ in atTop,
      2 * K.prefixCount Singleton n ≤
        K.prefixCount Output n +
          K.prefixCount Good n +
          K.prefixCount Singleton n +
          eSingleton)
    (hgood : ∀ᶠ n : ℕ in atTop,
      K.prefixCount Good n ≤ 2 * K.prefixCount Output n + eGood)
    (C : LongBadCharge K Output Long) :
    (1 / 8 : ℝ) ≤ K.lowerDensity Output :=
  orderedLowerDensity_one_eighth_of_eventual_charges
    K Output Good Singleton Long
    eSingleton eGood C.longError
    hpartition hsingleton hgood C.eventually_long_le

end GenLimit.KleinbergWei.DensityMeasures.InfiniteRank
