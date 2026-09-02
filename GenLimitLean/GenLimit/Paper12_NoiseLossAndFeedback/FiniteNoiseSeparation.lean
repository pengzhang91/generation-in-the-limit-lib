import GenLimit.Paper12_NoiseLossAndFeedback.FiniteOmissionSeparation
import GenLimit.Paper12_NoiseLossAndFeedback.Projection

/-!
# Noise, Loss, and Feedback: the finite-noise hierarchy

Source: Bai--Panigrahi--Zhang, *Language Generation in the Limit:
Noise, Loss, and Feedback*, arXiv:2507.15319v2, Definitions 5.1--5.6,
Lemma 5.4, and Theorem 5.7.

This file uses the paper's injective, value-bounded noisy enumerations and
inclusive time convention.  The separating class is literally the class
`Cⁱ` from Theorem 4.15.  The upper-bound generator tests whether all `i+1`
markers have appeared; the lower bound constructs the equivalent direct
infinite diagonal, retaining those markers as exactly the allowed noisy
values of its final enumeration.
-/

namespace GenLimit.NoiseLossFeedback

open GenLimit.Generic

/-! ## Definitions 5.1--5.3 -/

/-- Definition 5.1, re-exported at the paper boundary. -/
abbrev NoisyEnumerationWithLevel
    (stream : Stream α) (L : GenLimit.Generic.Language α)
    (i : ℕ) : Prop :=
  GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost stream L i

/-- Definition 5.2 at a fixed generator.  The convergence time may depend
on both the target and the particular noisy enumeration. -/
def IsLimitGeneratorWithNoiseLevel
    (gen : Generator α) (C : LanguageClass α) (i : ℕ) : Prop :=
  ∀ L, L ∈ C → ∀ stream,
    NoisyEnumerationWithLevel stream L i →
      ∃ T, ∀ t, T ≤ t → CorrectAt gen L stream t

/-- Generatability in the limit at a known finite noise level. -/
def GeneratableInLimitWithNoiseLevel
    (C : LanguageClass α) (i : ℕ) : Prop :=
  ∃ gen : Generator α, IsLimitGeneratorWithNoiseLevel gen C i

/-- Definition 5.3 at a fixed generator. -/
def IsNonuniformGeneratorWithNoiseLevel
    (gen : Generator α) (C : LanguageClass α) (i : ℕ) : Prop :=
  ∀ L, L ∈ C → ∃ T, ∀ stream,
    NoisyEnumerationWithLevel stream L i →
      ∀ t, T ≤ t → CorrectAt gen L stream t

/-- Non-uniform generatability at a known finite noise level. -/
def NonuniformGeneratableWithNoiseLevel
    (C : LanguageClass α) (i : ℕ) : Prop :=
  ∃ gen : Generator α,
    IsNonuniformGeneratorWithNoiseLevel gen C i

theorem noisyEnumerationWithLevel_mono
    {stream : Stream α} {L : GenLimit.Generic.Language α}
    {i j : ℕ}
    (hij : i ≤ j)
    (h : NoisyEnumerationWithLevel stream L i) :
    NoisyEnumerationWithLevel stream L j :=
  GenLimit.Generic.injectiveValueContaminatedPresentationAtMost_mono hij h

/-! ## Definitions 5.5--5.6 -/

/-- Definition 5.5: pointwise image of a language. -/
def mappedLanguage (f : α → β) (L : Set α) : Set β :=
  f '' L

/-- Definition 5.5: pointwise image of a language collection. -/
def mappedLanguageClass
    (f : α → β) (C : LanguageClass α) : LanguageClass β :=
  mappedLanguage f '' C

/-- Definition 5.6: isomorphism of language collections. -/
def IsomorphicLanguageClasses
    (C : LanguageClass α) (C' : LanguageClass β) : Prop :=
  ∃ f : α → β,
    Function.Bijective f ∧ mappedLanguageClass f C = C'

/-! ## Lemma 5.4: projection after deleting at most `i` universe points -/

/-- Prefix a stream by every member of a finite set, in the canonical
`Finset.equivFin` order. -/
noncomputable def prependFinsetStream
    (F : Finset α) (stream : Stream α) : Stream α :=
  fun n =>
    if hn : n < F.card then
      (F.equivFin.symm ⟨n, hn⟩).1
    else
      stream (n - F.card)

theorem prependFinsetStream_prefix
    (F : Finset α) (stream : Stream α)
    {n : ℕ} (hn : n < F.card) :
    prependFinsetStream F stream n =
      (F.equivFin.symm ⟨n, hn⟩).1 := by
  simp [prependFinsetStream, hn]

theorem prependFinsetStream_tail
    (F : Finset α) (stream : Stream α) (n : ℕ) :
    prependFinsetStream F stream (F.card + n) =
      stream n := by
  have hnot : ¬F.card + n < F.card :=
    Nat.not_lt_of_ge (Nat.le_add_right F.card n)
  simp [prependFinsetStream, hnot]

theorem prependFinsetStream_injective
    (F : Finset α) {stream : Stream α}
    (hstream : Function.Injective stream)
    (hdisjoint : Disjoint (Set.range stream) (F : Set α)) :
    Function.Injective (prependFinsetStream F stream) := by
  intro m n hmn
  by_cases hm : m < F.card
  · by_cases hn : n < F.card
    · rw [prependFinsetStream_prefix F stream hm,
        prependFinsetStream_prefix F stream hn] at hmn
      have hsub :
          F.equivFin.symm ⟨m, hm⟩ =
            F.equivFin.symm ⟨n, hn⟩ :=
        Subtype.ext hmn
      exact congrArg Fin.val
        (F.equivFin.symm.injective hsub)
    · have hleft :
          prependFinsetStream F stream m ∈ F := by
        rw [prependFinsetStream_prefix F stream hm]
        exact (F.equivFin.symm ⟨m, hm⟩).2
      have hright :
          prependFinsetStream F stream n ∈ Set.range stream := by
        rw [prependFinsetStream, dif_neg hn]
        exact ⟨n - F.card, rfl⟩
      exact False.elim
        (Set.disjoint_left.mp hdisjoint hright (hmn ▸ hleft))
  · by_cases hn : n < F.card
    · have hleft :
          prependFinsetStream F stream m ∈ Set.range stream := by
        rw [prependFinsetStream, dif_neg hm]
        exact ⟨m - F.card, rfl⟩
      have hright :
          prependFinsetStream F stream n ∈ F := by
        rw [prependFinsetStream_prefix F stream hn]
        exact (F.equivFin.symm ⟨n, hn⟩).2
      exact False.elim
        (Set.disjoint_left.mp hdisjoint hleft (hmn ▸ hright))
    · rw [prependFinsetStream, dif_neg hm,
        prependFinsetStream, dif_neg hn] at hmn
      have hsub : m - F.card = n - F.card :=
        hstream hmn
      omega

theorem range_prependFinsetStream
    (F : Finset α) (stream : Stream α) :
    Set.range (prependFinsetStream F stream) =
      (F : Set α) ∪ Set.range stream := by
  apply Set.Subset.antisymm
  · rintro x ⟨n, rfl⟩
    by_cases hn : n < F.card
    · left
      rw [prependFinsetStream_prefix F stream hn]
      exact (F.equivFin.symm ⟨n, hn⟩).2
    · right
      rw [prependFinsetStream, dif_neg hn]
      exact ⟨n - F.card, rfl⟩
  · intro x hx
    rcases hx with hxF | hxRange
    · let k : Fin F.card := F.equivFin ⟨x, hxF⟩
      refine ⟨k, ?_⟩
      rw [prependFinsetStream_prefix F stream k.isLt]
      exact congrArg Subtype.val
        (F.equivFin.symm_apply_apply ⟨x, hxF⟩)
    · obtain ⟨n, rfl⟩ := hxRange
      exact ⟨F.card + n, prependFinsetStream_tail F stream n⟩

/-- Simulate a generator after placing the finite deleted universe prefix in
front of its current input. -/
noncomputable def prependFinsetGenerator
    (F : Finset α) (gen : Generator α) : Generator α :=
  fun n xs =>
    gen (F.card + n) fun k =>
      if hk : k.val < F.card then
        (F.equivFin.symm ⟨k, hk⟩).1
      else
        xs ⟨k - F.card, by omega⟩

theorem outputAt_prependFinsetGenerator
    (F : Finset α) (gen : Generator α)
    (stream : Stream α) (t : ℕ) :
    outputAt (prependFinsetGenerator F gen) stream t =
      outputAt gen (prependFinsetStream F stream)
        (F.card + t) := by
  unfold outputAt GenLimit.Generic.output
  congr 1

theorem finset_subset_observed_prepend
    (F : Finset α) (stream : Stream α) (t : ℕ) :
    F ⊆ observedThrough (prependFinsetStream F stream)
      (F.card + t) := by
  intro x hx
  let k : Fin F.card := F.equivFin ⟨x, hx⟩
  apply GenLimit.Generic.mem_sample_iff.mpr
  refine ⟨k, by omega, ?_⟩
  rw [prependFinsetStream_prefix F stream k.isLt]
  exact congrArg Subtype.val
    (F.equivFin.symm_apply_apply ⟨x, hx⟩)

theorem observed_subset_observed_prepend
    (F : Finset α) (stream : Stream α) (t : ℕ) :
    observedThrough stream t ⊆
      observedThrough (prependFinsetStream F stream)
        (F.card + t) := by
  intro x hx
  obtain ⟨n, hn, hnx⟩ :=
    GenLimit.Generic.mem_sample_iff.mp hx
  apply GenLimit.Generic.mem_sample_iff.mpr
  refine ⟨F.card + n, by omega, ?_⟩
  rw [prependFinsetStream_tail]
  exact hnx

/-- Lemma 5.4 in the literal injective-enumeration model.  The condition
`MissingAtMost univ U' i` is exactly `|U \ U'| ≤ i`. -/
theorem lemma_5_4
    {C : LanguageClass α} {U' : Set α} {i : ℕ}
    (hdeleted :
      GenLimit.Support.MissingAtMost
        (Set.univ : Set α) U' i)
    (hgen : GeneratableInLimitWithNoiseLevel C i) :
    GeneratableInLimitWithNoiseLevel
      (GenLimit.NoiseLossFeedback.classProjection C U') 0 := by
  classical
  obtain ⟨F, hF, hFcard⟩ := hdeleted
  obtain ⟨gen, hgen⟩ := hgen
  refine ⟨prependFinsetGenerator F gen, ?_⟩
  intro K' hK' stream henum
  obtain ⟨K, hKC, hK'eq, _hK'infinite⟩ := hK'
  have hrangeSubsetK' :
      Set.range stream ⊆ K' :=
    (GenLimit.Support.missingAtMost_zero_iff_subset
      _ _).mp henum.2.2
  have hrangeEq : Set.range stream = K' :=
    Set.Subset.antisymm hrangeSubsetK' henum.2.1
  have hK'subsetU' : K' ⊆ U' := by
    rw [hK'eq]
    exact Set.inter_subset_right
  have hstreamSubsetK : Set.range stream ⊆ K := by
    intro x hx
    have hxK' : x ∈ K' := hrangeSubsetK' hx
    rw [hK'eq] at hxK'
    exact hxK'.1
  have hstreamDisjoint :
      Disjoint (Set.range stream) (F : Set α) := by
    rw [Set.disjoint_left]
    intro x hxRange hxF
    have hxU' : x ∈ U' :=
      hK'subsetU' (hrangeEq ▸ hxRange)
    have hxDeleted : x ∈ (Set.univ : Set α) \ U' := by
      rw [← hF]
      exact hxF
    exact hxDeleted.2 hxU'
  let full := prependFinsetStream F stream
  have hfullInjective : Function.Injective full :=
    prependFinsetStream_injective F henum.1 hstreamDisjoint
  have hKsubsetRange : K ⊆ Set.range full := by
    intro x hxK
    rw [range_prependFinsetStream]
    by_cases hxU' : x ∈ U'
    · right
      rw [hrangeEq, hK'eq]
      exact ⟨hxK, hxU'⟩
    · left
      change x ∈ (F : Set α)
      rw [hF]
      exact ⟨Set.mem_univ x, hxU'⟩
  have hfullNoise :
      GenLimit.Support.MissingAtMost
        (Set.range full) K i := by
    let bad := F.filter fun x => x ∉ K
    refine ⟨bad, ?_, ?_⟩
    · ext x
      simp only [bad, Finset.mem_coe, Finset.mem_filter,
        Set.mem_diff]
      rw [range_prependFinsetStream]
      constructor
      · rintro ⟨hxF, hxNotK⟩
        exact ⟨Or.inl hxF, hxNotK⟩
      · rintro ⟨hxRange, hxNotK⟩
        rcases hxRange with hxF | hxStream
        · exact ⟨hxF, hxNotK⟩
        · exact False.elim
            (hxNotK (hstreamSubsetK hxStream))
    · exact (Finset.card_filter_le _ _).trans hFcard
  have hfullEnum :
      NoisyEnumerationWithLevel full K i :=
    ⟨hfullInjective, hKsubsetRange, hfullNoise⟩
  obtain ⟨T, hT⟩ := hgen K hKC full hfullEnum
  refine ⟨T, ?_⟩
  intro t ht
  have hcorrect :
      CorrectAt gen K full (F.card + t) :=
    hT (F.card + t) (ht.trans (Nat.le_add_left t F.card))
  have hout :
      outputAt (prependFinsetGenerator F gen) stream t =
        outputAt gen full (F.card + t) :=
    outputAt_prependFinsetGenerator F gen stream t
  have houtNotF :
      outputAt gen full (F.card + t) ∉ F := by
    intro houtF
    exact hcorrect.2
      (finset_subset_observed_prepend F stream t houtF)
  have houtU' :
      outputAt gen full (F.card + t) ∈ U' := by
    by_contra houtNotU'
    apply houtNotF
    change outputAt gen full (F.card + t) ∈ (F : Set α)
    rw [hF]
    exact ⟨Set.mem_univ _, houtNotU'⟩
  constructor
  · rw [hout, hK'eq]
    exact ⟨hcorrect.1, houtU'⟩
  · rw [hout]
    intro houtObserved
    exact hcorrect.2
      (observed_subset_observed_prepend F stream t houtObserved)

/-! ## The known-noise upper bound in Theorem 5.7 -/

private noncomputable def markerOccurrenceIndex
    {i : ℕ} {stream : Stream ℤ}
    {L : GenLimit.Generic.Language ℤ}
    (henum : NoisyEnumerationWithLevel stream L i)
    (hmarkers : (↑(omissionMarkerFinset i) : Set ℤ) ⊆ L)
    (z : ℤ) : ℕ :=
  if hz : z ∈ omissionMarkerFinset i then
    Classical.choose (henum.2.1 (hmarkers hz))
  else 0

private theorem markerOccurrenceIndex_spec
    {i : ℕ} {stream : Stream ℤ}
    {L : GenLimit.Generic.Language ℤ}
    (henum : NoisyEnumerationWithLevel stream L i)
    (hmarkers : (↑(omissionMarkerFinset i) : Set ℤ) ⊆ L)
    {z : ℤ} (hz : z ∈ omissionMarkerFinset i) :
    stream
        (markerOccurrenceIndex henum hmarkers z) =
      z := by
  classical
  simp only [markerOccurrenceIndex, dif_pos hz]
  exact Classical.choose_spec (henum.2.1 (hmarkers hz))

/-- Every target marker has appeared after one finite time. -/
theorem allMarkers_eventually_observed
    {i : ℕ} {stream : Stream ℤ}
    {L : GenLimit.Generic.Language ℤ}
    (henum : NoisyEnumerationWithLevel stream L i)
    (hmarkers : (↑(omissionMarkerFinset i) : Set ℤ) ⊆ L) :
    ∃ T, ∀ t, T ≤ t →
      omissionMarkerFinset i ⊆ observedThrough stream t := by
  classical
  let T :=
    (omissionMarkerFinset i).sup
      (markerOccurrenceIndex henum hmarkers)
  refine ⟨T, ?_⟩
  intro t hT z hz
  apply GenLimit.Generic.mem_sample_iff.mpr
  refine
    ⟨markerOccurrenceIndex henum hmarkers z, ?_,
      markerOccurrenceIndex_spec henum hmarkers hz⟩
  have hindex :
      markerOccurrenceIndex henum hmarkers z ≤ T :=
    Finset.le_sup (f := markerOccurrenceIndex henum hmarkers) hz
  omega

/-- A level-`i` noisy enumeration of a second-class target can never reveal
all `i+1` forbidden markers. -/
theorem not_allMarkers_observed_second
    {i : ℕ} {stream : Stream ℤ}
    {L : GenLimit.Generic.Language ℤ}
    (hL : L ∈ finiteOmissionSecondClass i)
    (henum : NoisyEnumerationWithLevel stream L i) :
    ∀ t, ¬omissionMarkerFinset i ⊆
      observedThrough stream t := by
  intro t hall
  obtain ⟨F, hF, hcard⟩ := henum.2.2
  have hsubset : omissionMarkerFinset i ⊆ F := by
    intro z hz
    have hzObserved := hall hz
    obtain ⟨k, _hk, hkz⟩ :=
      GenLimit.Generic.mem_sample_iff.mp hzObserved
    have hzRange : z ∈ Set.range stream := ⟨k, hkz⟩
    have hzNotL : z ∉ L := by
      intro hzL
      exact Set.disjoint_left.mp hL.2 hzL hz
    change z ∈ (F : Set ℤ)
    rw [hF]
    exact ⟨hzRange, hzNotL⟩
  have hmarkersCard :
      i + 1 ≤ F.card := by
    rw [← omissionMarkerFinset_card i]
    exact Finset.card_le_card hsubset
  omega

/-- The source's two-sided generator: switch to a positive sweep exactly
when all `i+1` markers have been observed. -/
noncomputable def finiteNoiseSweepGenerator
    (i : ℕ) : Generator ℤ :=
  fun n xs =>
    if omissionMarkerFinset i ⊆ sequenceSample xs then
      GenLimit.UnionClosedness.ascendingPositiveGenerator n xs
    else
      GenLimit.UnionClosedness.descendingNegativeGenerator n xs

theorem finiteNoiseSweepGenerator_first_correct
    {i : ℕ} {L : GenLimit.Generic.Language ℤ}
    (hL : L ∈ finiteOmissionFirstClass i)
    {stream : Stream ℤ}
    (henum : NoisyEnumerationWithLevel stream L i) :
    ∃ T, ∀ t, T ≤ t →
      CorrectAt (finiteNoiseSweepGenerator i) L stream t := by
  obtain ⟨hmarkers, j, htail⟩ := hL
  obtain ⟨Td, hTd⟩ :=
    allMarkers_eventually_observed henum hmarkers
  refine ⟨max Td j, ?_⟩
  intro t ht
  have hdetect :
      omissionMarkerFinset i ⊆ observedThrough stream t :=
    hTd t (le_trans (Nat.le_max_left _ _) ht)
  have hsample :
      sequenceSample (fun k : Fin (t + 1) => stream k) =
        observedThrough stream t :=
    sequenceSample_prefix stream (t + 1)
  obtain ⟨n, hnTime, hout, hfresh⟩ :=
    GenLimit.UnionClosedness.ascendingPositiveGenerator_spec
      (fun k : Fin (t + 1) => stream k)
  have hnTail : j ≤ n := by
    have hjt : j ≤ t := le_trans (Nat.le_max_right _ _) ht
    omega
  have hpositiveTail :
      GenLimit.UnionClosedness.positiveCode n ∈
        GenLimit.UnionClosedness.positiveTail j := by
    refine ⟨n - j, ?_⟩
    apply Int.ofNat_inj.mpr
    omega
  have hbranch :
      finiteNoiseSweepGenerator i (t + 1)
          (fun k : Fin (t + 1) => stream k) =
        GenLimit.UnionClosedness.ascendingPositiveGenerator
          (t + 1) (fun k : Fin (t + 1) => stream k) := by
    simp [finiteNoiseSweepGenerator, hsample, hdetect]
  constructor
  · rw [outputAt, GenLimit.Generic.output, hbranch, hout]
    exact htail hpositiveTail
  · rw [outputAt, GenLimit.Generic.output, hbranch, hout]
    rw [← hsample]
    simpa only [hout] using hfresh

theorem finiteNoiseSweepGenerator_second_correct
    {i : ℕ} {L : GenLimit.Generic.Language ℤ}
    (hL : L ∈ finiteOmissionSecondClass i)
    {stream : Stream ℤ}
    (henum : NoisyEnumerationWithLevel stream L i) :
    ∃ T, ∀ t, T ≤ t →
      CorrectAt (finiteNoiseSweepGenerator i) L stream t := by
  refine ⟨0, ?_⟩
  intro t _ht
  have hnoDetect :
      ¬omissionMarkerFinset i ⊆ observedThrough stream t :=
    not_allMarkers_observed_second hL henum t
  have hsample :
      sequenceSample (fun k : Fin (t + 1) => stream k) =
        observedThrough stream t :=
    sequenceSample_prefix stream (t + 1)
  obtain ⟨n, _hnTime, hout, hfresh⟩ :=
    GenLimit.UnionClosedness.descendingNegativeGenerator_spec
      (fun k : Fin (t + 1) => stream k)
  have hbranch :
      finiteNoiseSweepGenerator i (t + 1)
          (fun k : Fin (t + 1) => stream k) =
        GenLimit.UnionClosedness.descendingNegativeGenerator
          (t + 1) (fun k : Fin (t + 1) => stream k) := by
    simp [finiteNoiseSweepGenerator, hsample, hnoDetect]
  constructor
  · rw [outputAt, GenLimit.Generic.output, hbranch, hout]
    exact hL.1 (GenLimit.UnionClosedness.negativeCode_mem n)
  · rw [outputAt, GenLimit.Generic.output, hbranch, hout]
    rw [← hsample]
    simpa only [hout] using hfresh

/-- Upper-bound half of Theorem 5.7. -/
theorem finiteNoiseLevel_upper (i : ℕ) :
    GeneratableInLimitWithNoiseLevel
      (finiteOmissionClass i) i := by
  refine ⟨finiteNoiseSweepGenerator i, ?_⟩
  intro L hL stream henum
  rcases hL with hfirst | hsecond
  · exact finiteNoiseSweepGenerator_first_correct hfirst henum
  · exact finiteNoiseSweepGenerator_second_correct hsecond henum

/-! ## The direct infinite diagonal for the lower bound -/

private def noiseListInput (l : List α) : Fin l.length → α :=
  fun k => l.get k

private theorem sequenceSample_noiseListInput
    [DecidableEq α] (l : List α) :
    sequenceSample (noiseListInput l) = l.toFinset := by
  classical
  ext x
  rw [GenLimit.Generic.mem_sequenceSample_iff, List.mem_toFinset]
  exact List.mem_iff_get.symm

private theorem exists_positiveTail_disjoint_noiseFinset
    (S : Finset ℤ) :
    ∃ d, Disjoint
      (GenLimit.UnionClosedness.positiveTail d)
      (S : Set ℤ) := by
  let badIndices : Set ℕ :=
    GenLimit.UnionClosedness.positiveCode ⁻¹' (S : Set ℤ)
  have hbadFinite : badIndices.Finite := by
    apply S.finite_toSet.preimage
    exact Set.injOn_of_injective
      GenLimit.UnionClosedness.positiveCode_injective
  obtain ⟨d, hd⟩ :=
    Finset.exists_nat_subset_range hbadFinite.toFinset
  refine ⟨d, ?_⟩
  rw [Set.disjoint_left]
  intro z hzTail hzS
  obtain ⟨k, rfl⟩ := hzTail
  have hmem :
      d + k ∈ hbadFinite.toFinset := by
    rw [Set.Finite.mem_toFinset]
    exact hzS
  have hlt : d + k < d := by
    simpa using hd hmem
  omega

private theorem positiveTail_disjoint_negativeIntegers_noise
    (d : ℕ) :
    Disjoint
      (GenLimit.UnionClosedness.positiveTail d)
      GenLimit.UnionClosedness.negativeIntegers := by
  rw [Set.disjoint_left]
  intro z hzTail hzNeg
  obtain ⟨k, rfl⟩ := hzTail
  have hpos :=
    GenLimit.UnionClosedness.positiveCode_mem (d + k)
  exact (Int.not_lt_of_ge (Int.le_of_lt hpos)) hzNeg

/-- State after `n` lower-bound phases.  Every marker is retained in the
history; in the final noisy enumeration those are exactly the inserted
values. -/
structure FiniteNoisePhaseState (i n : ℕ) where
  history : List ℤ
  forbidden : Finset ℤ
  history_nodup : history.Nodup
  markers_subset_history :
    omissionMarkerFinset i ⊆ history.toFinset
  history_forbidden_disjoint :
    Disjoint history.toFinset forbidden
  forbidden_nonnegative :
    ∀ z, z ∈ forbidden → 0 ≤ z
  negative_mem_history_iff :
    ∀ k,
      GenLimit.UnionClosedness.negativeCode k ∈ history ↔
        k < n

/-- Initially reveal all `i+1` markers. -/
noncomputable def initialFiniteNoisePhaseState (i : ℕ) :
    FiniteNoisePhaseState i 0 where
  history := (omissionMarkerFinset i).toList
  forbidden := ∅
  history_nodup := Finset.nodup_toList _
  markers_subset_history := by simp
  history_forbidden_disjoint := by simp
  forbidden_nonnegative := by simp
  negative_mem_history_iff := by
    intro k
    constructor
    · intro hk
      have hkMarker :
          GenLimit.UnionClosedness.negativeCode k ∈
            omissionMarkerFinset i := by
        simpa using hk
      exact False.elim (negativeCode_not_marker i k hkMarker)
    · omega

structure SuccessfulFiniteNoisePhase
    (G : Generator ℤ) (i n : ℕ)
    (state : FiniteNoisePhaseState i n) where
  next : FiniteNoisePhaseState i (n + 1)
  extends_history : state.history <+: next.history
  strict_growth : state.history.length < next.history.length
  forbidden_subset : state.forbidden ⊆ next.forbidden
  failureTime : ℕ
  old_length_le_failureTime :
    state.history.length ≤ failureTime
  failureTime_lt_next : failureTime < next.history.length
  badOutput : ℤ
  bad_mem_forbidden : badOutput ∈ next.forbidden
  output_on_next :
    G (failureTime + 1)
        (fun k =>
          next.history.get
            ⟨k, lt_of_lt_of_le k.isLt
              (Nat.succ_le_iff.mpr failureTime_lt_next)⟩) =
      badOutput

private theorem exists_successfulFiniteNoisePhase
    (G : Generator ℤ) (i n : ℕ)
    (hG :
      IsLimitGeneratorWithNoiseLevel G
        (finiteOmissionClass i) (i + 1))
    (state : FiniteNoisePhaseState i n) :
    Nonempty (SuccessfulFiniteNoisePhase G i n state) := by
  classical
  let blocked :=
    state.history.toFinset ∪ state.forbidden
  obtain ⟨d, htailBlocked⟩ :=
    exists_positiveTail_disjoint_noiseFinset blocked
  let tail := GenLimit.UnionClosedness.positiveTail d
  have htailHistory :
      Disjoint tail (state.history.toFinset : Set ℤ) := by
    rw [Set.disjoint_left] at htailBlocked ⊢
    intro z hzTail hz
    apply htailBlocked hzTail
    change z ∈ blocked
    exact Finset.mem_union_left _ hz
  have htailForbidden :
      Disjoint tail (state.forbidden : Set ℤ) := by
    rw [Set.disjoint_left] at htailBlocked ⊢
    intro z hzTail hz
    apply htailBlocked hzTail
    change z ∈ blocked
    exact Finset.mem_union_right _ hz
  have hhistorySample :
      sequenceSample (noiseListInput state.history) =
        state.history.toFinset :=
    sequenceSample_noiseListInput state.history
  let hrest :
      (tail \
        (sequenceSample (noiseListInput state.history) :
          Set ℤ)).Infinite :=
    (GenLimit.UnionClosedness.positiveTail_infinite d).diff
      (sequenceSample
        (noiseListInput state.history)).finite_toSet
  let full : Stream ℤ :=
    prefixThenTarget (noiseListInput state.history) tail hrest
  have hhistoryGetInjective :
      Function.Injective (noiseListInput state.history) := by
    exact List.nodup_iff_injective_get.mp state.history_nodup
  have hfullInjective :
      Function.Injective full :=
    prefixThenTarget_injective hhistoryGetInjective tail hrest
  have hrange :
      Set.range full =
        (state.history.toFinset : Set ℤ) ∪ tail := by
    have h :=
      range_prefixThenTarget_eq_prefix_union
        (noiseListInput state.history) tail hrest
    simpa [full, hhistorySample] using h
  let target : Set ℤ :=
    (state.history.toFinset : Set ℤ) ∪ tail
  have htargetFirst :
      target ∈ finiteOmissionFirstClass i := by
    refine ⟨?_, d, ?_⟩
    · intro z hz
      exact Set.mem_union_left tail
        (state.markers_subset_history hz)
    · exact Set.subset_union_right
  have hrangeTarget : Set.range full = target := by
    simpa [target] using hrange
  have hfullEnum :
      NoisyEnumerationWithLevel full target (i + 1) := by
    refine ⟨hfullInjective, ?_, ?_⟩
    · rw [hrangeTarget]
    · refine ⟨∅, ?_, by simp⟩
      ext z
      simp [hrangeTarget]
  obtain ⟨T, hT⟩ :=
    hG target (Set.mem_union_left _ htargetFirst)
      full hfullEnum
  let t := max T state.history.length
  have hTt : T ≤ t := Nat.le_max_left _ _
  have hhistoryLenT : state.history.length ≤ t :=
    Nat.le_max_right _ _
  have hcorrect : CorrectAt G target full t :=
    hT t hTt
  let phasePrefix : List ℤ :=
    List.ofFn (fun k : Fin (t + 1) => full k)
  let y : ℤ := outputAt G full t
  let nextHistory : List ℤ :=
    phasePrefix ++ [GenLimit.UnionClosedness.negativeCode n]
  let nextForbidden : Finset ℤ :=
    insert y state.forbidden
  have hprefixLength : phasePrefix.length = t + 1 := by
    simp [phasePrefix]
  have hprefixNodup : phasePrefix.Nodup := by
    rw [List.nodup_iff_injective_getElem]
    intro a b hab
    apply Fin.ext
    apply hfullInjective
    simpa only [phasePrefix, List.getElem_ofFn] using hab
  have hhistoryPrefix : state.history <+: phasePrefix := by
    apply List.prefix_iff_getElem.mpr
    refine ⟨by rw [hprefixLength]; omega, ?_⟩
    intro k hk
    simp only [phasePrefix, List.getElem_ofFn]
    exact
      (prefixThenTarget_prefix
        (noiseListInput state.history) tail hrest
        ⟨k, hk⟩).symm
  have hprefixSubsetRange :
      (phasePrefix.toFinset : Set ℤ) ⊆ Set.range full := by
    intro z hz
    change z ∈ phasePrefix.toFinset at hz
    rw [List.mem_toFinset] at hz
    dsimp only [phasePrefix] at hz
    rw [List.mem_ofFn] at hz
    obtain ⟨k, hk⟩ := hz
    exact ⟨k, hk⟩
  have hyNotPrefix : y ∉ phasePrefix := by
    intro hy
    apply hcorrect.2
    rw [observedThrough, GenLimit.Generic.mem_sample_iff]
    dsimp only [phasePrefix] at hy
    rw [List.mem_ofFn] at hy
    obtain ⟨k, hk⟩ := hy
    exact ⟨k, k.isLt, hk⟩
  have hyTail : y ∈ tail := by
    rcases hcorrect.1 with hyHistory | hyTail
    · exact False.elim
        (hyNotPrefix
          (hhistoryPrefix.subset
            (List.mem_toFinset.mp hyHistory)))
    · exact hyTail
  have hyNonnegative : 0 ≤ y := by
    obtain ⟨k, hk⟩ := hyTail
    rw [← hk]
    exact Int.le_of_lt
      (GenLimit.UnionClosedness.positiveCode_mem (d + k))
  have hnextNegativeNotPrefix :
      GenLimit.UnionClosedness.negativeCode n ∉ phasePrefix := by
    intro hnegPrefix
    have hnegRange :=
      hprefixSubsetRange (List.mem_toFinset.mpr hnegPrefix)
    rw [hrange] at hnegRange
    rcases hnegRange with hnegHistory | hnegTail
    · have := (state.negative_mem_history_iff n).mp
        (List.mem_toFinset.mp hnegHistory)
      omega
    · exact
        Set.disjoint_left.mp
          (positiveTail_disjoint_negativeIntegers_noise d)
          hnegTail
          (GenLimit.UnionClosedness.negativeCode_mem n)
  have hnextHistoryNodup : nextHistory.Nodup := by
    dsimp only [nextHistory]
    rw [List.nodup_append]
    refine ⟨hprefixNodup, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst b
    exact fun hab => hnextNegativeNotPrefix (hab ▸ ha)
  have hfullForbiddenDisjoint :
      Disjoint (Set.range full)
        (state.forbidden : Set ℤ) := by
    rw [Set.disjoint_left]
    intro z hzRange hzForbidden
    rw [hrange] at hzRange
    rcases hzRange with hzHistory | hzTail
    · exact Finset.disjoint_left.mp
        state.history_forbidden_disjoint
        hzHistory hzForbidden
    · exact Set.disjoint_left.mp htailForbidden
        hzTail hzForbidden
  have hprefixOldForbidden :
      Disjoint phasePrefix.toFinset state.forbidden := by
    rw [Finset.disjoint_left]
    intro z hzPrefix hzForbidden
    exact Set.disjoint_left.mp hfullForbiddenDisjoint
      (hprefixSubsetRange hzPrefix) hzForbidden
  have hnegativeOldForbidden :
      GenLimit.UnionClosedness.negativeCode n ∉
        state.forbidden := by
    intro hmem
    have hnonneg := state.forbidden_nonnegative _ hmem
    exact (Int.not_lt_of_ge hnonneg)
      (GenLimit.UnionClosedness.negativeCode_mem n)
  have hnegativeNeY :
      GenLimit.UnionClosedness.negativeCode n ≠ y := by
    intro heq
    rw [← heq] at hyNonnegative
    exact (Int.not_lt_of_ge hyNonnegative)
      (GenLimit.UnionClosedness.negativeCode_mem n)
  have hnextForbiddenDisjoint :
      Disjoint nextHistory.toFinset nextForbidden := by
    rw [Finset.disjoint_left]
    intro z hzNext hzForbidden
    rw [Finset.mem_insert] at hzForbidden
    rw [List.mem_toFinset] at hzNext
    simp only [nextHistory, List.mem_append,
      List.mem_singleton] at hzNext
    rcases hzNext with hzPrefix | rfl
    · rcases hzForbidden with rfl | hzOld
      · exact hyNotPrefix hzPrefix
      · exact Finset.disjoint_left.mp hprefixOldForbidden
          (List.mem_toFinset.mpr hzPrefix) hzOld
    · rcases hzForbidden with heq | hzOld
      · exact hnegativeNeY heq
      · exact hnegativeOldForbidden hzOld
  have hnextMarkers :
      omissionMarkerFinset i ⊆ nextHistory.toFinset := by
    intro z hz
    apply List.mem_toFinset.mpr
    apply List.mem_append_left
    apply hhistoryPrefix.subset
    exact List.mem_toFinset.mp
      (state.markers_subset_history hz)
  have hnextNegativeIff :
      ∀ k,
        GenLimit.UnionClosedness.negativeCode k ∈
            nextHistory ↔
          k < n + 1 := by
    intro k
    constructor
    · intro hk
      simp only [nextHistory, List.mem_append,
        List.mem_singleton] at hk
      rcases hk with hkPrefix | hkEq
      · have hkRange :=
          hprefixSubsetRange
            (List.mem_toFinset.mpr hkPrefix)
        rw [hrange] at hkRange
        rcases hkRange with hkHistory | hkTail
        · have hkn :=
            (state.negative_mem_history_iff k).mp
              (List.mem_toFinset.mp hkHistory)
          omega
        · exact False.elim
            (Set.disjoint_left.mp
              (positiveTail_disjoint_negativeIntegers_noise d)
              hkTail
              (GenLimit.UnionClosedness.negativeCode_mem k))
      · have hkn : k = n :=
          GenLimit.UnionClosedness.negativeCode_injective hkEq
        omega
    · intro hk
      have hcases : k < n ∨ k = n := by omega
      rcases hcases with hlt | rfl
      · apply List.mem_append_left
        apply hhistoryPrefix.subset
        exact
          (state.negative_mem_history_iff k).mpr hlt
      · simp [nextHistory]
  let next : FiniteNoisePhaseState i (n + 1) :=
    { history := nextHistory
      forbidden := nextForbidden
      history_nodup := hnextHistoryNodup
      markers_subset_history := hnextMarkers
      history_forbidden_disjoint := hnextForbiddenDisjoint
      forbidden_nonnegative := by
        intro z hz
        rw [Finset.mem_insert] at hz
        exact hz.elim (fun h => h ▸ hyNonnegative)
          (state.forbidden_nonnegative z)
      negative_mem_history_iff := hnextNegativeIff }
  have houtputOnNext :
      G (t + 1)
          (fun k =>
            next.history.get
              ⟨k, by
                dsimp [next, nextHistory]
                simp [hprefixLength]
                omega⟩) =
        y := by
    change
      G (t + 1)
          (fun k =>
            nextHistory.get
              ⟨k, by
                simp [nextHistory, hprefixLength]
                omega⟩) =
        outputAt G full t
    unfold outputAt GenLimit.Generic.output
    congr 1
    funext k
    have hkPrefix : k.val < phasePrefix.length := by
      rw [hprefixLength]
      exact k.isLt
    simp only [nextHistory, List.get_eq_getElem]
    rw [List.getElem_append_left hkPrefix]
    simp only [phasePrefix, List.getElem_ofFn]
  refine ⟨{
    next := next
    extends_history :=
      hhistoryPrefix.trans
        (List.prefix_append phasePrefix _)
    strict_growth := by
      dsimp [next, nextHistory]
      simp [hprefixLength]
      omega
    forbidden_subset := by
      intro z hz
      exact Finset.mem_insert_of_mem hz
    failureTime := t
    old_length_le_failureTime := hhistoryLenT
    failureTime_lt_next := by
      dsimp [next, nextHistory]
      simp [hprefixLength]
      omega
    badOutput := y
    bad_mem_forbidden := by
      dsimp [next, nextForbidden]
      exact Finset.mem_insert_self _ _
    output_on_next := houtputOnNext
  }⟩

/-! ### Iteration and the limiting noisy enumeration -/

private noncomputable def chosenFiniteNoisePhase
    (G : Generator ℤ) (i n : ℕ)
    (hG :
      IsLimitGeneratorWithNoiseLevel G
        (finiteOmissionClass i) (i + 1))
    (state : FiniteNoisePhaseState i n) :
    SuccessfulFiniteNoisePhase G i n state :=
  Classical.choice
    (exists_successfulFiniteNoisePhase G i n hG state)

private noncomputable def iteratedFiniteNoiseState
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithNoiseLevel G
        (finiteOmissionClass i) (i + 1)) :
    (n : ℕ) → FiniteNoisePhaseState i n
  | 0 => initialFiniteNoisePhaseState i
  | n + 1 =>
      (chosenFiniteNoisePhase G i n hG
        (iteratedFiniteNoiseState G i hG n)).next

private theorem iteratedFiniteNoiseState_prefix_succ
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithNoiseLevel G
        (finiteOmissionClass i) (i + 1))
    (n : ℕ) :
    (iteratedFiniteNoiseState G i hG n).history <+:
      (iteratedFiniteNoiseState G i hG (n + 1)).history := by
  rw [iteratedFiniteNoiseState]
  exact
    (chosenFiniteNoisePhase G i n hG
      (iteratedFiniteNoiseState G i hG n)).extends_history

private theorem iteratedFiniteNoiseState_prefix
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithNoiseLevel G
        (finiteOmissionClass i) (i + 1))
    {n m : ℕ} (hnm : n ≤ m) :
    (iteratedFiniteNoiseState G i hG n).history <+:
      (iteratedFiniteNoiseState G i hG m).history := by
  induction m, hnm using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ m _ ih =>
      exact ih.trans
        (iteratedFiniteNoiseState_prefix_succ G i hG m)

private theorem iteratedFiniteNoiseState_length
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithNoiseLevel G
        (finiteOmissionClass i) (i + 1))
    (n : ℕ) :
    n ≤ (iteratedFiniteNoiseState G i hG n).history.length := by
  induction n with
  | zero =>
      simp [iteratedFiniteNoiseState,
        initialFiniteNoisePhaseState]
  | succ n ih =>
      have hstep :=
        (chosenFiniteNoisePhase G i n hG
          (iteratedFiniteNoiseState G i hG n)).strict_growth
      rw [iteratedFiniteNoiseState]
      omega

private theorem iteratedFiniteNoiseState_forbidden_succ
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithNoiseLevel G
        (finiteOmissionClass i) (i + 1))
    (n : ℕ) :
    (iteratedFiniteNoiseState G i hG n).forbidden ⊆
      (iteratedFiniteNoiseState G i hG
        (n + 1)).forbidden := by
  rw [iteratedFiniteNoiseState]
  exact
    (chosenFiniteNoisePhase G i n hG
      (iteratedFiniteNoiseState G i hG n)).forbidden_subset

private theorem iteratedFiniteNoiseState_forbidden_mono
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithNoiseLevel G
        (finiteOmissionClass i) (i + 1))
    {n m : ℕ} (hnm : n ≤ m) :
    (iteratedFiniteNoiseState G i hG n).forbidden ⊆
      (iteratedFiniteNoiseState G i hG m).forbidden := by
  induction m, hnm using Nat.le_induction with
  | base => exact fun _ hx => hx
  | succ m _ ih =>
      exact fun z hz =>
        iteratedFiniteNoiseState_forbidden_succ G i hG m
          (ih hz)

private noncomputable def finiteNoiseFailureTime
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithNoiseLevel G
        (finiteOmissionClass i) (i + 1))
    (n : ℕ) : ℕ :=
  (chosenFiniteNoisePhase G i n hG
    (iteratedFiniteNoiseState G i hG n)).failureTime

private noncomputable def finiteNoiseBadOutput
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithNoiseLevel G
        (finiteOmissionClass i) (i + 1))
    (n : ℕ) : ℤ :=
  (chosenFiniteNoisePhase G i n hG
    (iteratedFiniteNoiseState G i hG n)).badOutput

private theorem finiteNoiseFailureTime_ge_stage
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithNoiseLevel G
        (finiteOmissionClass i) (i + 1))
    (n : ℕ) :
    n ≤ finiteNoiseFailureTime G i hG n := by
  exact
    (iteratedFiniteNoiseState_length G i hG n).trans
      (chosenFiniteNoisePhase G i n hG
        (iteratedFiniteNoiseState G i hG n)).old_length_le_failureTime

private theorem finiteNoiseBadOutput_mem_nextForbidden
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithNoiseLevel G
        (finiteOmissionClass i) (i + 1))
    (n : ℕ) :
    finiteNoiseBadOutput G i hG n ∈
      (iteratedFiniteNoiseState G i hG
        (n + 1)).forbidden := by
  rw [iteratedFiniteNoiseState]
  exact
    (chosenFiniteNoisePhase G i n hG
      (iteratedFiniteNoiseState G i hG n)).bad_mem_forbidden

private theorem finiteNoiseBadOutput_not_mem_nextHistory
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithNoiseLevel G
        (finiteOmissionClass i) (i + 1))
    (n : ℕ) :
    finiteNoiseBadOutput G i hG n ∉
      (iteratedFiniteNoiseState G i hG
        (n + 1)).history := by
  intro hmem
  exact Finset.disjoint_left.mp
    (iteratedFiniteNoiseState G i hG
      (n + 1)).history_forbidden_disjoint
    (List.mem_toFinset.mpr hmem)
    (finiteNoiseBadOutput_mem_nextForbidden G i hG n)

private theorem finiteNoiseBadOutput_not_mem_laterHistory
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithNoiseLevel G
        (finiteOmissionClass i) (i + 1))
    (n m : ℕ) (hnm : n + 1 ≤ m) :
    finiteNoiseBadOutput G i hG n ∉
      (iteratedFiniteNoiseState G i hG m).history := by
  intro hmem
  have hbadForbidden :
      finiteNoiseBadOutput G i hG n ∈
        (iteratedFiniteNoiseState G i hG m).forbidden :=
    iteratedFiniteNoiseState_forbidden_mono G i hG hnm
      (finiteNoiseBadOutput_mem_nextForbidden G i hG n)
  exact Finset.disjoint_left.mp
    (iteratedFiniteNoiseState G i hG
      m).history_forbidden_disjoint
    (List.mem_toFinset.mpr hmem) hbadForbidden

private theorem finiteNoiseBadOutput_not_mem_history
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithNoiseLevel G
        (finiteOmissionClass i) (i + 1))
    (n m : ℕ) :
    finiteNoiseBadOutput G i hG n ∉
      (iteratedFiniteNoiseState G i hG m).history := by
  rcases le_total m (n + 1) with hmn | hnm
  · intro hmem
    exact finiteNoiseBadOutput_not_mem_nextHistory G i hG n
      ((iteratedFiniteNoiseState_prefix G i hG hmn).subset
        hmem)
  · exact finiteNoiseBadOutput_not_mem_laterHistory
      G i hG n m hnm

private noncomputable def finiteNoiseFinalStream
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithNoiseLevel G
        (finiteOmissionClass i) (i + 1)) :
    Stream ℤ :=
  fun k =>
    let history :=
      (iteratedFiniteNoiseState G i hG (k + 1)).history
    history.get ⟨k, by
      have hlen :=
        iteratedFiniteNoiseState_length G i hG (k + 1)
      exact lt_of_lt_of_le (Nat.lt_succ_self k) hlen⟩

private theorem finiteNoiseFinalStream_eq_history_get
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithNoiseLevel G
        (finiteOmissionClass i) (i + 1))
    (n k : ℕ)
    (hk :
      k <
        (iteratedFiniteNoiseState G i hG
          n).history.length) :
    finiteNoiseFinalStream G i hG k =
      (iteratedFiniteNoiseState G i hG n).history.get
        ⟨k, hk⟩ := by
  rw [finiteNoiseFinalStream]
  have hbound :
      k <
        (iteratedFiniteNoiseState G i hG
          (k + 1)).history.length := by
    have hlen :=
      iteratedFiniteNoiseState_length G i hG (k + 1)
    omega
  rw [List.get_eq_getElem, List.get_eq_getElem]
  rcases le_total (k + 1) n with hkn | hnk
  · exact
      (List.prefix_iff_getElem.mp
        (iteratedFiniteNoiseState_prefix G i hG hkn)).2
          k hbound
  · exact
      ((List.prefix_iff_getElem.mp
        (iteratedFiniteNoiseState_prefix G i hG hnk)).2
          k hk).symm

private theorem finiteNoiseHistory_subset_finalRange
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithNoiseLevel G
        (finiteOmissionClass i) (i + 1))
    (n : ℕ) :
    (↑(iteratedFiniteNoiseState G i hG n).history.toFinset :
        Set ℤ) ⊆
      Set.range (finiteNoiseFinalStream G i hG) := by
  intro x hx
  change
    x ∈ (iteratedFiniteNoiseState G i hG
      n).history.toFinset at hx
  rw [List.mem_toFinset] at hx
  obtain ⟨k, hk⟩ := List.mem_iff_get.mp hx
  refine ⟨k, ?_⟩
  exact
    (finiteNoiseFinalStream_eq_history_get
      G i hG n k k.isLt).trans hk

private theorem finiteNoiseFinalStream_injective
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithNoiseLevel G
        (finiteOmissionClass i) (i + 1)) :
    Function.Injective (finiteNoiseFinalStream G i hG) := by
  intro a b hab
  let n := max a b + 1
  have ha :
      a <
        (iteratedFiniteNoiseState G i hG
          n).history.length := by
    have hlen :=
      iteratedFiniteNoiseState_length G i hG n
    dsimp only [n] at hlen ⊢
    omega
  have hb :
      b <
        (iteratedFiniteNoiseState G i hG
          n).history.length := by
    have hlen :=
      iteratedFiniteNoiseState_length G i hG n
    dsimp only [n] at hlen ⊢
    omega
  have hget :
      (iteratedFiniteNoiseState G i hG n).history.get
          ⟨a, ha⟩ =
        (iteratedFiniteNoiseState G i hG n).history.get
          ⟨b, hb⟩ := by
    exact
      (finiteNoiseFinalStream_eq_history_get
        G i hG n a ha).symm.trans
        (hab.trans
          (finiteNoiseFinalStream_eq_history_get
            G i hG n b hb))
  have hfin :
      (⟨a, ha⟩ :
        Fin
          (iteratedFiniteNoiseState G i hG
            n).history.length) =
        ⟨b, hb⟩ :=
    (List.nodup_iff_injective_get.mp
      (iteratedFiniteNoiseState G i hG
        n).history_nodup) hget
  exact congrArg Fin.val hfin

private theorem finiteNoiseNegative_mem_nextHistory
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithNoiseLevel G
        (finiteOmissionClass i) (i + 1))
    (n : ℕ) :
    GenLimit.UnionClosedness.negativeCode n ∈
      (iteratedFiniteNoiseState G i hG
        (n + 1)).history := by
  exact
    ((iteratedFiniteNoiseState G i hG
      (n + 1)).negative_mem_history_iff n).mpr
        (Nat.lt_succ_self n)

private theorem finiteNoiseNegative_subset_finalRange
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithNoiseLevel G
        (finiteOmissionClass i) (i + 1)) :
    GenLimit.UnionClosedness.negativeIntegers ⊆
      Set.range (finiteNoiseFinalStream G i hG) := by
  rw [← GenLimit.UnionClosedness.range_negativeCode]
  rintro _ ⟨n, rfl⟩
  exact
    finiteNoiseHistory_subset_finalRange G i hG (n + 1)
      (List.mem_toFinset.mpr
        (finiteNoiseNegative_mem_nextHistory G i hG n))

private theorem finiteNoiseMarkers_subset_finalRange
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithNoiseLevel G
        (finiteOmissionClass i) (i + 1)) :
    (↑(omissionMarkerFinset i) : Set ℤ) ⊆
      Set.range (finiteNoiseFinalStream G i hG) := by
  intro z hz
  exact finiteNoiseHistory_subset_finalRange G i hG 0
    ((iteratedFiniteNoiseState G i hG
      0).markers_subset_history hz)

private theorem finiteNoiseBadOutput_not_mem_finalRange
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithNoiseLevel G
        (finiteOmissionClass i) (i + 1))
    (n : ℕ) :
    finiteNoiseBadOutput G i hG n ∉
      Set.range (finiteNoiseFinalStream G i hG) := by
  rintro ⟨k, hk⟩
  apply finiteNoiseBadOutput_not_mem_history
    G i hG n (k + 1)
  have hbound :
      k <
        (iteratedFiniteNoiseState G i hG
          (k + 1)).history.length := by
    have hlen :=
      iteratedFiniteNoiseState_length G i hG (k + 1)
    omega
  apply List.mem_iff_get.mpr
  refine ⟨⟨k, hbound⟩, ?_⟩
  exact
    (finiteNoiseFinalStream_eq_history_get
      G i hG (k + 1) k hbound).symm.trans hk

private noncomputable def finiteNoiseFinalTarget
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithNoiseLevel G
        (finiteOmissionClass i) (i + 1)) :
    Set ℤ :=
  Set.range (finiteNoiseFinalStream G i hG) \
    (omissionMarkerFinset i : Set ℤ)

private theorem finiteNoiseFinalTarget_mem_class
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithNoiseLevel G
        (finiteOmissionClass i) (i + 1)) :
    finiteNoiseFinalTarget G i hG ∈
      finiteOmissionClass i := by
  apply Set.mem_union_right
  constructor
  · intro z hzNegative
    refine
      ⟨finiteNoiseNegative_subset_finalRange
        G i hG hzNegative, ?_⟩
    intro hzMarker
    have hzNonnegative := omissionMarker_nonnegative hzMarker
    exact (Int.not_lt_of_ge hzNonnegative) hzNegative
  · rw [Set.disjoint_left]
    intro z hzTarget hzMarker
    exact hzTarget.2 hzMarker

private theorem finiteNoiseFinalStream_enumerates_target
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithNoiseLevel G
        (finiteOmissionClass i) (i + 1)) :
    NoisyEnumerationWithLevel
      (finiteNoiseFinalStream G i hG)
      (finiteNoiseFinalTarget G i hG) (i + 1) := by
  refine
    ⟨finiteNoiseFinalStream_injective G i hG, ?_, ?_⟩
  · exact fun _ hx => hx.1
  · refine ⟨omissionMarkerFinset i, ?_, ?_⟩
    · ext z
      constructor
      · intro hzMarker
        have hzRange :=
          finiteNoiseMarkers_subset_finalRange
            G i hG hzMarker
        exact
          ⟨hzRange, fun hzTarget =>
            hzTarget.2 hzMarker⟩
      · rintro ⟨hzRange, hzNotTarget⟩
        by_contra hzNotMarker
        exact hzNotTarget ⟨hzRange, hzNotMarker⟩
    · exact le_of_eq (omissionMarkerFinset_card i)

private theorem finiteNoiseFailureTime_lt_nextHistory
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithNoiseLevel G
        (finiteOmissionClass i) (i + 1))
    (n : ℕ) :
    finiteNoiseFailureTime G i hG n <
      (iteratedFiniteNoiseState G i hG
        (n + 1)).history.length := by
  rw [finiteNoiseFailureTime, iteratedFiniteNoiseState]
  exact
    (chosenFiniteNoisePhase G i n hG
      (iteratedFiniteNoiseState G i hG n)).failureTime_lt_next

private theorem finiteNoiseBadOutput_eq_outputAt_final
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithNoiseLevel G
        (finiteOmissionClass i) (i + 1))
    (n : ℕ) :
    outputAt G (finiteNoiseFinalStream G i hG)
        (finiteNoiseFailureTime G i hG n) =
      finiteNoiseBadOutput G i hG n := by
  unfold outputAt
  change
    G
        ((chosenFiniteNoisePhase G i n hG
          (iteratedFiniteNoiseState G i hG n)).failureTime + 1)
        (fun k => finiteNoiseFinalStream G i hG k) =
      (chosenFiniteNoisePhase G i n hG
        (iteratedFiniteNoiseState G i hG n)).badOutput
  convert
    (chosenFiniteNoisePhase G i n hG
      (iteratedFiniteNoiseState G i hG n)).output_on_next
      using 1
  congr 1
  funext k
  have hkHistory :
      k.val <
        (iteratedFiniteNoiseState G i hG
          (n + 1)).history.length := by
    exact lt_of_lt_of_le k.isLt
      (Nat.succ_le_iff.mpr
        (finiteNoiseFailureTime_lt_nextHistory
          G i hG n))
  exact
    finiteNoiseFinalStream_eq_history_get
      G i hG (n + 1) k hkHistory

/-! ## Theorem 5.7 -/

/-- Lower-bound half of Theorem 5.7.  The final enumeration contains every
target value and exactly the `i+1` marker values as noise. -/
theorem finiteNoiseLevel_lower (i : ℕ) :
    ¬GeneratableInLimitWithNoiseLevel
      (finiteOmissionClass i) (i + 1) := by
  rintro ⟨G, hG⟩
  let stream := finiteNoiseFinalStream G i hG
  let target := finiteNoiseFinalTarget G i hG
  have htarget :
      target ∈ finiteOmissionClass i :=
    finiteNoiseFinalTarget_mem_class G i hG
  have henum :
      NoisyEnumerationWithLevel stream target (i + 1) :=
    finiteNoiseFinalStream_enumerates_target G i hG
  obtain ⟨T, hT⟩ := hG target htarget stream henum
  have hlate :
      T ≤ finiteNoiseFailureTime G i hG T :=
    finiteNoiseFailureTime_ge_stage G i hG T
  have hcorrect :
      CorrectAt G target stream
        (finiteNoiseFailureTime G i hG T) :=
    hT _ hlate
  have houtput :
      outputAt G stream
          (finiteNoiseFailureTime G i hG T) =
        finiteNoiseBadOutput G i hG T :=
    finiteNoiseBadOutput_eq_outputAt_final G i hG T
  have hbad :
      finiteNoiseBadOutput G i hG T ∉ target := by
    intro hmem
    exact finiteNoiseBadOutput_not_mem_finalRange
      G i hG T hmem.1
  apply hbad
  rw [← houtput]
  exact hcorrect.1

/-- Theorem 5.7: every known finite noise level is strictly weaker than the
next one. -/
theorem theorem_5_7 :
    ∀ i : ℕ,
      ∃ C : LanguageClass ℤ,
        GenLimit.Generic.UUS C ∧
          GeneratableInLimitWithNoiseLevel C i ∧
            ¬GeneratableInLimitWithNoiseLevel C (i + 1) := by
  intro i
  exact
    ⟨finiteOmissionClass i,
      finiteOmissionClass_uus i,
      finiteNoiseLevel_upper i,
      finiteNoiseLevel_lower i⟩

/-- Summary Theorem 1.5: the same class witnesses the adjacent-level
separations for finite omissions and for known finite noise. -/
theorem theorem_1_5 :
    ∀ i : ℕ,
      ∃ C : LanguageClass ℤ,
        GenLimit.Generic.UUS C ∧
          GeneratableInLimitWithOmissions C i ∧
            ¬GeneratableInLimitWithOmissions C (i + 1) ∧
              GeneratableInLimitWithNoiseLevel C i ∧
                ¬GeneratableInLimitWithNoiseLevel C (i + 1) := by
  intro i
  exact
    ⟨finiteOmissionClass i,
      finiteOmissionClass_uus i,
      lemma_4_16 i,
      lemma_4_17 i,
      finiteNoiseLevel_upper i,
      finiteNoiseLevel_lower i⟩

/-- The `i = 0` consequence stated explicitly after Theorem 5.7. -/
theorem theorem_5_7_zero :
    ∃ C : LanguageClass ℤ,
      GenLimit.Generic.UUS C ∧
        GeneratableInLimitWithNoiseLevel C 0 ∧
          ¬GeneratableInLimitWithNoiseLevel C 1 :=
  theorem_5_7 0

end GenLimit.NoiseLossFeedback
