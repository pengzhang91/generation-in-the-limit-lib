import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.VanishingBreadth
import GenLimit.Paper17_InfiniteContamination.ElementDensity
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation

/-! # A common stream forcing zero upper element density (Theorem 6.21) -/

namespace GenLimit.InfiniteContamination

open GenLimit.Generic GenLimit.KleinbergWei

/-- Once outputs must come from a sublanguage, their upper density in any
ambient ordering is bounded by that sublanguage's upper density. -/
theorem elementBasedUpperDensity_le_of_generates {gen : Generator ℕ}
    {s : Stream ℕ} {L : Set ℕ} (K : OrderedLanguage)
    (h : GeneratesElementInLimitOn gen L s) :
    elementBasedUpperDensity gen K s ≤ K.upperDensity L := by
  obtain ⟨T, hT⟩ := h
  let F := generatedBefore gen s T
  have hsub : elementOutputLanguage gen s ⊆ L ∪ (F : Set ℕ) := by
    rintro _ ⟨t, rfl⟩
    by_cases ht : t < T
    · exact Or.inr (mem_generatedBefore_iff.mpr ⟨t, ht, rfl⟩)
    · exact Or.inl (hT t (Nat.le_of_not_gt ht)).1
  exact (K.upperDensity_mono hsub).trans (by
    simpa only [K.upperDensity_eq_zero_of_finite F.finite_toSet, add_zero]
      using K.upperDensity_union_le L (F : Set ℕ))

/-- A single injective stream covers both targets without omissions. Every
generator valid for the smaller target has zero upper density in the larger. -/
theorem exists_zero_element_upperDensity :
    ∃ (small : Set ℕ) (large : OrderedLanguage) (s : Stream ℕ),
      small.Infinite ∧ small ⊂ large.carrier ∧
      VanishingNoiseEnumeration s small ∧ VanishingNoiseEnumeration s large.carrier ∧
      ∀ gen, GeneratesElementInLimitOn gen small s →
        elementBasedUpperDensity gen large s = 0 := by
  classical
  let L := DensityMeasures.SquareTower.squares
  let K := DensityMeasures.SquareTower.natOrder
  have hi : L.Infinite := DensityMeasures.SquareTower.squares_infinite
  have hz : K.upperDensity L = 0 := DensityMeasures.SquareTower.squares_upperDensity
  let s := sparseMergePresentation L Lᶜ hi
  have hinj : Function.Injective s := sparseMergePresentation_injective hi disjoint_compl_right
  have hr : Set.range s = Set.univ := (range_sparseMergePresentation hi).trans (Set.union_compl_self L)
  have henum (A : Set ℕ) (hA : L ⊆ A) : VanishingNoiseEnumeration s A := by
    refine ⟨hinj, ?_, sparseMergePresentation_vanishingNoise_of_core_subset hi hA⟩
    intro x hx
    exact hr.symm ▸ Set.mem_univ x
  refine ⟨L, K, s, hi, ⟨Set.subset_univ _, ?_⟩, henum _ (by rfl),
    henum _ (Set.subset_univ _), ?_⟩
  · intro h
    have hc := K.upperDensity_mono h
    rw [K.upperDensity_carrier, hz] at hc
    norm_num at hc
  · intro gen h
    exact le_antisymm ((elementBasedUpperDensity_le_of_generates K h).trans hz.le)
      (K.upperDensity_nonneg _)

end GenLimit.InfiniteContamination
