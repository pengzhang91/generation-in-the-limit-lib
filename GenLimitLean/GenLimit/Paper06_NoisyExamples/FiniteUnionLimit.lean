import GenLimit.Paper06_NoisyExamples.NonuniformDefinitions
import GenLimit.Paper06_NoisyExamples.UniformIndependent
import GenLimit.Core.ClassCovers
import GenLimit.Support.FiniteCandidateRace

/-!
# #06 Noisy Examples: finite unions and noisy generation in the limit

Source: Ananth Raman and Vinod Raman, *Generation from Noisy Examples*,
arXiv:2501.04179v2 / ICML 2025, Theorem 3.10 and Appendix G.

This module follows the paper's finite-family `arg max` construction.  Each
component has an infinite common intersection, which is enumerated without
repetition.  The generator selects the component whose enumeration has the
longest observed initial segment and emits its first unseen point.

The formal proof makes one detail in Appendix G explicit.  A selected
component can contain finitely many negative examples that were inserted by
the adversary.  They are harmless only after all such observed negative
values have entered the finite history.  The final threshold below therefore
dominates both the component-selection threshold and that finite-noise
threshold.

The printed theorem assumes only that the example space is countable.  An
empty class over an empty finite example space satisfies its hypotheses but
admits no total generator.  We record the paper's implicit infinite-universe
convention as `[Infinite α]`; this also supplies `[Nonempty α]`.
-/

namespace GenLimit.NoisyExamples

/-- A fixed equivalence between `ℕ` and an infinite subset of a countable
example space. -/
noncomputable def noisyInfiniteSetEquiv [Countable α]
    (C : Set α) (hC : C.Infinite) : ℕ ≃ C :=
  GenLimit.Support.infiniteSetEquiv C hC

/-- The fixed repetition-free enumeration used in Appendix G. -/
noncomputable def noisyInfiniteEnumeration [Countable α]
    (C : Set α) (hC : C.Infinite) : ℕ → α :=
  GenLimit.Support.infiniteEnumeration C hC

theorem noisyInfiniteEnumeration_mem [Countable α]
    (C : Set α) (hC : C.Infinite) (k : ℕ) :
    noisyInfiniteEnumeration C hC k ∈ C :=
  GenLimit.Support.infiniteEnumeration_mem C hC k

theorem noisyInfiniteEnumeration_injective [Countable α]
    (C : Set α) (hC : C.Infinite) :
    Function.Injective (noisyInfiniteEnumeration C hC) :=
  GenLimit.Support.infiniteEnumeration_injective C hC

theorem noisyInfiniteEnumeration_surjective [Countable α]
    (C : Set α) (hC : C.Infinite) {x : α} (hx : x ∈ C) :
    ∃ k, noisyInfiniteEnumeration C hC k = x :=
  GenLimit.Support.infiniteEnumeration_surjective C hC hx

theorem noisyEnumeration_misses_finset [Countable α]
    (C : Set α) (hC : C.Infinite) (S : Finset α) :
    ∃ k, noisyInfiniteEnumeration C hC k ∉ S :=
  GenLimit.Support.enumeration_misses_finset C hC S

/-- The first element of the fixed enumeration absent from the history. -/
noncomputable def noisyEnumerationProgress [Countable α]
    (C : Set α) (hC : C.Infinite) (S : Finset α) : ℕ :=
  GenLimit.Support.progress C hC S

theorem noisyEnumerationProgress_spec [Countable α]
    (C : Set α) (hC : C.Infinite) (S : Finset α) :
    noisyInfiniteEnumeration C hC (noisyEnumerationProgress C hC S) ∉ S :=
  GenLimit.Support.progress_spec C hC S

theorem noisy_mem_of_lt_progress [Countable α]
    (C : Set α) (hC : C.Infinite) (S : Finset α) {k : ℕ}
    (hk : k < noisyEnumerationProgress C hC S) :
    noisyInfiniteEnumeration C hC k ∈ S :=
  GenLimit.Support.mem_of_lt_progress C hC S hk

theorem noisy_progress_le_of_not_mem [Countable α]
    (C : Set α) (hC : C.Infinite) (S : Finset α) {k : ℕ}
    (hk : noisyInfiniteEnumeration C hC k ∉ S) :
    noisyEnumerationProgress C hC S ≤ k :=
  GenLimit.Support.progress_le_of_not_mem C hC S hk

/-- The paper's finite `arg max`, with `none` only for an empty family. -/
noncomputable def noisyWinningIndex [Countable α] {k : ℕ}
    (classes : Fin k → GenLimit.Generic.LanguageClass α)
    (hcores : ∀ i, (commonIntersection (classes i)).Infinite)
    (current : Finset α) : Option (Fin k) :=
  GenLimit.Support.winningIndexBy Finset.univ
    (fun i ↦ noisyEnumerationProgress
      (commonIntersection (classes i)) (hcores i) current)

theorem noisyWinningIndex_spec [Countable α] {k : ℕ}
    (classes : Fin k → GenLimit.Generic.LanguageClass α)
    (hcores : ∀ i, (commonIntersection (classes i)).Infinite)
    (current : Finset α)
    (hindices : (Finset.univ : Finset (Fin k)).Nonempty) :
    ∃ selected,
      noisyWinningIndex classes hcores current = some selected ∧
      ∀ i, noisyEnumerationProgress (commonIntersection (classes i))
          (hcores i) current ≤
        noisyEnumerationProgress (commonIntersection (classes selected))
          (hcores selected) current := by
  obtain ⟨selected, hselected, _hmem, hmax⟩ :=
    GenLimit.Support.winningIndexBy_spec
      (Finset.univ : Finset (Fin k))
      (fun i ↦ noisyEnumerationProgress
        (commonIntersection (classes i)) (hcores i) current) hindices
  refine ⟨selected, hselected, ?_⟩
  intro i
  exact hmax i (Finset.mem_univ i)

/-- The generator in Appendix G. -/
noncomputable def finiteUniformUnionNoisyGenerator
    [Countable α] [Nonempty α] {k : ℕ}
    (classes : Fin k → GenLimit.Generic.LanguageClass α)
    (hcores : ∀ i, (commonIntersection (classes i)).Infinite) :
    GenLimit.Generic.Generator α := by
  classical
  exact fun _ xs ↦
    let current := GenLimit.Generic.sequenceSample xs
    match noisyWinningIndex classes hcores current with
    | none => Classical.choice inferInstance
    | some i => noisyInfiniteEnumeration (commonIntersection (classes i))
        (hcores i)
        (noisyEnumerationProgress (commonIntersection (classes i))
          (hcores i) current)

private noncomputable def rangeGoodIndices [Countable α] {k : ℕ}
    (classes : Fin k → GenLimit.Generic.LanguageClass α)
    (stream : GenLimit.Generic.Stream α) : Finset (Fin k) := by
  classical
  exact Finset.univ.filter fun i ↦
    commonIntersection (classes i) ⊆ Set.range stream

private theorem mem_rangeGoodIndices_iff [Countable α] {k : ℕ}
    {classes : Fin k → GenLimit.Generic.LanguageClass α}
    {stream : GenLimit.Generic.Stream α} {i : Fin k} :
    i ∈ rangeGoodIndices classes stream ↔
      commonIntersection (classes i) ⊆ Set.range stream := by
  simp [rangeGoodIndices]

private theorem range_bad_obstruction_exists [Countable α] {k : ℕ}
    (classes : Fin k → GenLimit.Generic.LanguageClass α)
    (hcores : ∀ i, (commonIntersection (classes i)).Infinite)
    (stream : GenLimit.Generic.Stream α)
    {i : Fin k} (hi : i ∉ rangeGoodIndices classes stream) :
    ∃ p, noisyInfiniteEnumeration (commonIntersection (classes i))
      (hcores i) p ∉ Set.range stream := by
  have hnot : ¬ commonIntersection (classes i) ⊆ Set.range stream := by
    simpa only [mem_rangeGoodIndices_iff, not_iff_not] using hi
  obtain ⟨x, hxcore, hxrange⟩ := Set.not_subset.mp hnot
  obtain ⟨p, hp⟩ := noisyInfiniteEnumeration_surjective
    (commonIntersection (classes i)) (hcores i) hxcore
  exact ⟨p, hp.symm ▸ hxrange⟩

private noncomputable def rangeBadObstruction [Countable α] {k : ℕ}
    (classes : Fin k → GenLimit.Generic.LanguageClass α)
    (hcores : ∀ i, (commonIntersection (classes i)).Infinite)
    (stream : GenLimit.Generic.Stream α) (i : Fin k) : ℕ := by
  classical
  if hi : i ∉ rangeGoodIndices classes stream then
    exact Nat.find (range_bad_obstruction_exists classes hcores stream hi)
  else exact 0

private theorem rangeBadObstruction_spec [Countable α] {k : ℕ}
    (classes : Fin k → GenLimit.Generic.LanguageClass α)
    (hcores : ∀ i, (commonIntersection (classes i)).Infinite)
    (stream : GenLimit.Generic.Stream α) (i : Fin k)
    (hi : i ∉ rangeGoodIndices classes stream) :
    noisyInfiniteEnumeration (commonIntersection (classes i))
      (hcores i) (rangeBadObstruction classes hcores stream i) ∉
        Set.range stream := by
  classical
  simp only [rangeBadObstruction, dif_pos hi]
  exact Nat.find_spec (range_bad_obstruction_exists classes hcores stream hi)

private theorem component_uus_of_finite_cover {k : ℕ}
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : GenLimit.Generic.UUS H)
    (classes : Fin k → GenLimit.Generic.LanguageClass α)
    (hcover : GenLimit.Generic.IsFiniteCover H classes)
    (i : Fin k) : GenLimit.Generic.UUS (classes i) := by
  intro L hLi
  apply hUUS L
  rw [hcover]
  exact Set.mem_iUnion.mpr ⟨i, hLi⟩

/-- Theorem 3.10: a finite union of uniformly noise-independent generatable
classes is noisily generatable in the limit. -/
theorem theorem_3_10 [Countable α] [Infinite α]
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : GenLimit.Generic.UUS H)
    (hcover : ∃ k : ℕ,
      ∃ classes : Fin k → GenLimit.Generic.LanguageClass α,
        GenLimit.Generic.IsFiniteCover H classes ∧
        ∀ i, UniformNoiseIndependentGeneratable (classes i)) :
    NoisilyGeneratableInLimit H := by
  classical
  obtain ⟨k, classes, hclasses, hUniform⟩ := hcover
  have hcores : ∀ i, (commonIntersection (classes i)).Infinite := by
    intro i
    exact uniform_noiseIndependent_implies_infinite_commonIntersection
      (component_uus_of_finite_cover hUUS classes hclasses i) (hUniform i)
  let gen := finiteUniformUnionNoisyGenerator classes hcores
  refine ⟨gen, ?_⟩
  intro L hLH stream hP
  have hLUnion : L ∈ ⋃ i, classes i := by
    rw [← hclasses]
    exact hLH
  obtain ⟨target, hLTarget⟩ := Set.mem_iUnion.mp hLUnion
  have htargetCoreL : commonIntersection (classes target) ⊆ L :=
    commonIntersection_subset_of_mem hLTarget
  have htargetGood : target ∈ rangeGoodIndices classes stream := by
    apply mem_rangeGoodIndices_iff.mpr
    exact htargetCoreL.trans hP.1
  have hindices : (Finset.univ : Finset (Fin k)).Nonempty :=
    ⟨target, Finset.mem_univ target⟩
  let bad := (Finset.univ : Finset (Fin k)) \
    rangeGoodIndices classes stream
  let obstruction : Fin k → ℕ :=
    rangeBadObstruction classes hcores stream
  let badBound : ℕ := bad.sup obstruction
  let targetPrefix : Finset α :=
    (Finset.range (badBound + 1)).image
      (noisyInfiniteEnumeration (commonIntersection (classes target))
        (hcores target))
  have htargetPrefixRange : (targetPrefix : Set α) ⊆ Set.range stream := by
    intro x hx
    obtain ⟨p, _hp, hpx⟩ := Finset.mem_image.mp hx
    rw [← hpx]
    exact hP.1 (htargetCoreL
      (noisyInfiniteEnumeration_mem
        (commonIntersection (classes target)) (hcores target) p))
  obtain ⟨prefixTime, hPrefixTime⟩ :=
    GenLimit.Generic.finset_eventually_subset_sample
      (L := Set.range stream) (by rfl) targetPrefix htargetPrefixRange
  let noiseTimes : Finset ℕ := hP.2.toFinset
  let noiseValues : Finset α := noiseTimes.image stream
  have hnoiseValuesRange : (noiseValues : Set α) ⊆ Set.range stream := by
    rintro x hx
    obtain ⟨t, _ht, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨t, rfl⟩
  obtain ⟨noiseTime, hNoiseTime⟩ :=
    GenLimit.Generic.finset_eventually_subset_sample
      (L := Set.range stream) (by rfl) noiseValues hnoiseValuesRange
  refine ⟨max prefixTime noiseTime, ?_⟩
  intro s hs
  let current := GenLimit.Generic.sample stream s
  have hprefixCurrent : targetPrefix ⊆ current := by
    intro x hx
    exact GenLimit.Generic.sample_mono
      ((Nat.le_max_left _ _).trans hs) (hPrefixTime hx)
  have hnoiseCurrent : noiseValues ⊆ current := by
    intro x hx
    exact GenLimit.Generic.sample_mono
      ((Nat.le_max_right _ _).trans hs) (hNoiseTime hx)
  have htargetProgress : badBound <
      noisyEnumerationProgress (commonIntersection (classes target))
        (hcores target) current := by
    apply Nat.lt_of_not_ge
    intro hle
    have hmemPrefix :
        noisyInfiniteEnumeration (commonIntersection (classes target))
          (hcores target)
          (noisyEnumerationProgress (commonIntersection (classes target))
            (hcores target) current) ∈ targetPrefix := by
      apply Finset.mem_image.mpr
      refine ⟨noisyEnumerationProgress
        (commonIntersection (classes target)) (hcores target) current,
        ?_, rfl⟩
      simp only [Finset.mem_range, Nat.lt_add_one_iff]
      exact hle
    exact noisyEnumerationProgress_spec
      (commonIntersection (classes target)) (hcores target) current
      (hprefixCurrent hmemPrefix)
  obtain ⟨selected, hwin, hmax⟩ :=
    noisyWinningIndex_spec classes hcores current hindices
  have hselectedProgress : badBound <
      noisyEnumerationProgress (commonIntersection (classes selected))
        (hcores selected) current :=
    htargetProgress.trans_le (hmax target)
  have hselectedGood : selected ∈ rangeGoodIndices classes stream := by
    by_contra hnotGood
    have hbad : selected ∈ bad := by
      apply Finset.mem_sdiff.mpr
      exact ⟨Finset.mem_univ selected, hnotGood⟩
    have hobstructionRange := rangeBadObstruction_spec
      classes hcores stream selected hnotGood
    have hobstructionCurrent :
        noisyInfiniteEnumeration (commonIntersection (classes selected))
          (hcores selected) (obstruction selected) ∉ current := by
      intro hmem
      apply hobstructionRange
      obtain ⟨r, _hrs, hrx⟩ := GenLimit.Generic.mem_sample_iff.mp hmem
      exact ⟨r, hrx⟩
    have hprogressLe :
        noisyEnumerationProgress (commonIntersection (classes selected))
          (hcores selected) current ≤ obstruction selected :=
      noisy_progress_le_of_not_mem _ _ _ hobstructionCurrent
    have hobstructionLe : obstruction selected ≤ badBound :=
      Finset.le_sup (f := obstruction) hbad
    omega
  let out := noisyInfiniteEnumeration
    (commonIntersection (classes selected)) (hcores selected)
    (noisyEnumerationProgress (commonIntersection (classes selected))
      (hcores selected) current)
  have houtCore : out ∈ commonIntersection (classes selected) :=
    noisyInfiniteEnumeration_mem _ _ _
  have houtFresh : out ∉ current :=
    noisyEnumerationProgress_spec _ _ _
  have hrun : GenLimit.Generic.output gen stream s = out := by
    unfold GenLimit.Generic.output
    change finiteUniformUnionNoisyGenerator classes hcores s
      (fun i : Fin s ↦ stream i) = out
    simp only [finiteUniformUnionNoisyGenerator,
      GenLimit.Generic.sequenceSample_prefix]
    rw [hwin]
  constructor
  · rw [hrun]
    by_contra houtL
    have houtRange : out ∈ Set.range stream :=
      (mem_rangeGoodIndices_iff.mp hselectedGood) houtCore
    obtain ⟨r, hr⟩ := houtRange
    have hrNoise : r ∈ noiseTimes := by
      change r ∈ hP.2.toFinset
      rw [Set.Finite.mem_toFinset]
      change stream r ∉ L
      intro hrL
      apply houtL
      rw [← hr]
      exact hrL
    have houtNoiseValues : out ∈ noiseValues := by
      apply Finset.mem_image.mpr
      exact ⟨r, hrNoise, hr⟩
    exact houtFresh (hnoiseCurrent houtNoiseValues)
  · rw [hrun]
    exact houtFresh

end GenLimit.NoisyExamples
