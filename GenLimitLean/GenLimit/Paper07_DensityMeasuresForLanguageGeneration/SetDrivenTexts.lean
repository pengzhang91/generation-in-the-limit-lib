import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.SetDrivenDiagonal
import GenLimit.Paper12_NoiseLossAndFeedback.Repetitions

/-! # Set-driven observations along texts without repetitions

Taking first occurrences preserves the chain of distinct observed sets.
The two clocks are cofinal when the target is infinite. This allows the
unordered-sample obstruction to assume validity only on injective texts
and to produce an injective counterexample.
-/
namespace GenLimit.KleinbergWei.DensityMeasures.SetDriven
open Filter SquareTower NoiseLossFeedback

private theorem compressed_sample (s : ℕ → ℕ) (n : ℕ) :
    sample (firstOccurrenceStream s) (firstOccurrenceCount s n) = sample s n := by
  rw [← textPrefix_toFinset,textPrefix_eq_ofFn,← firstOccurrences_eq_firstOccurrenceStream_prefix]
  ext x
  rw [firstOccurrences_prefix_toFinset]
  exact Generic.mem_sample_iff.trans mem_sample_iff.symm

/-- Every eventual predicate of the finite sample has the same truth value
along an infinite-range text and its injective first-occurrence text. -/
private theorem eventual_compressed (s : ℕ → ℕ) (hi : (Set.range s).Infinite) (Q : Finset ℕ → Prop) :
    (∀ᶠ t in atTop, Q (sample (firstOccurrenceStream s) t)) ↔
      ∀ᶠ t in atTop, Q (sample s t) := by
  classical
  have hf := firstOccurrenceTimes_infinite hi
  have inv (n) : firstOccurrenceCount s (firstOccurrenceTime s n) = n :=
    Nat.count_nth_of_infinite hf n
  have mono : Monotone (firstOccurrenceCount s) := Nat.count_monotone _
  have times : Tendsto (firstOccurrenceTime s) atTop atTop :=
    (firstOccurrenceTime_strictMono hf).tendsto_atTop
  have counts : Tendsto (firstOccurrenceCount s) atTop atTop := by
    apply tendsto_atTop.mpr
    intro k
    filter_upwards [eventually_ge_atTop (firstOccurrenceTime s k)] with t ht
    exact inv k ▸ mono ht
  constructor
  · intro h
    simpa only [compressed_sample] using counts.eventually h
  · intro h
    filter_upwards [times.eventually h] with t ht
    rwa [← compressed_sample,inv] at ht

theorem injective_diagonal {Q : Finset ℕ → Prop}
    (stable : ∀ n s, Function.Injective s → Presents s (layer n) → ∀ᶠ t in atTop, Q (sample s t)) :
    ∃ s : ℕ → ℕ, Function.Injective s ∧ Presents s Set.univ ∧ ∀ᶠ t in atTop, Q (sample s t) := by
  obtain ⟨s,hs,hQ⟩ := diagonal (Q := Q) (by
    intro n s hs
    have hi : (layer n).Infinite := squares_infinite.mono Set.subset_union_left
    obtain ⟨inj,range⟩ := firstOccurrenceStream_exactEnumeration hi hs
    exact (eventual_compressed s (hs.symm ▸ hi) Q).mp (stable n _ inj range))
  obtain ⟨inj,range⟩ := firstOccurrenceStream_exactEnumeration Set.infinite_univ hs
  exact ⟨_,inj,range,(eventual_compressed s (hs.symm ▸ Set.infinite_univ) Q).mpr hQ⟩

end GenLimit.KleinbergWei.DensityMeasures.SetDriven
