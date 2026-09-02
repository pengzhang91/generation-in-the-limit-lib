import GenLimit.Paper17_InfiniteContamination.AlgorithmFour
import GenLimit.Paper17_InfiniteContamination.NoiselessSetDensity
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation

/-!
# Algorithms 6 and 7: density under infinite contamination

Source: Mehrotra--Velegkas--Yu--Zhou,
*Language Generation with Infinite Contamination*,
arXiv:2511.07417v1, Theorems 6.11 and 6.14 and Algorithms 6 and 7.

This module first turns Algorithm 4's priority prefix into the set-valued
Algorithm 6 by returning its common core after deleting the observed sample.
The finite-family condition below is the indexed form of Condition 2.  The
necessity proof uses one common sparse presentation of the finite union,
constructed in `SharedVanishingPresentation`; the sufficiency proof uses the
maximal infinite prefix selected by Algorithm 6.

Algorithm 7 has a genuinely different stopping rule and is developed in the
second half of this file: the selected prefix itself must meet the prescribed
density bound in every selected language.
-/

namespace GenLimit.InfiniteContamination

open Filter
open GenLimit.KleinbergWei

/-! ## Shared set-generator infrastructure -/

/-- Set-valued version of Algorithm 4's selected common core. -/
noncomputable def priorityCoreSetGenerator
    (family : ℕ → GenLimit.Generic.Language ℕ)
    (threshold : ℕ → ℝ) (fallback : ℕ) : SetGenerator ℕ :=
  fun _ xs =>
    finiteCommonCore
        (indexedLanguages family
          (algorithmFourHistoryIndices family threshold fallback xs)) \
      (↑(GenLimit.Generic.sequenceSample xs) : Set ℕ)

@[simp] theorem priorityCoreSetGenerator_output
    (family : ℕ → GenLimit.Generic.Language ℕ)
    (threshold : ℕ → ℝ) (fallback : ℕ)
    (stream : GenLimit.Generic.Stream ℕ) (t : ℕ) :
    setOutput (priorityCoreSetGenerator family threshold fallback)
        stream t =
      finiteCommonCore
          (indexedLanguages family
            (algorithmFourIndices family
              (fun i =>
                thresholdPriorityTrace stream family threshold i t) t)) \
        (↑(GenLimit.Generic.sample stream t) : Set ℕ) := by
  simp only [setOutput, priorityCoreSetGenerator,
    GenLimit.Generic.sequenceSample_prefix]
  rw [algorithmFourHistoryIndices_eq_stream]

/-- The empty ranked prefix makes every output of the set-valued priority
generator infinite. -/
theorem priorityCoreSetGenerator_infinite
    (family : ℕ → GenLimit.Generic.Language ℕ)
    (hfamily : ∀ i, (family i).Infinite)
    (threshold : ℕ → ℝ) (fallback : ℕ) :
    IsInfiniteSetGenerator
      (priorityCoreSetGenerator family threshold fallback) := by
  intro t xs
  let stream := prefixCompletion fallback xs
  let score : ℕ → ℕ :=
    fun i => thresholdPriorityTrace stream family threshold i t
  have huniv : (Set.univ : Set ℕ).Infinite :=
    (hfamily 0).mono (Set.subset_univ _)
  have hzero :
      (finiteCommonCore
        (indexedLanguages family
          (rankedPrefix score t 0))).Infinite := by
    simpa [rankedPrefix, indexedLanguages] using huniv
  have hselected :
      (finiteCommonCore
        (indexedLanguages family
          (algorithmFourIndices family score t))).Infinite :=
    maximalInfinitePrefix_infinite_of_candidate
      family score (Nat.zero_le t) hzero
  have hindices :
      algorithmFourHistoryIndices family threshold fallback xs =
        algorithmFourIndices family score t := by
    unfold algorithmFourHistoryIndices score
    congr 1
  exact hselected.diff
    (GenLimit.Generic.sequenceSample xs).finite_toSet

/-! ## Theorem 6.11: vanishing noise -/

/-- Indexed form of Condition 2: every nonempty finite subfamily with
infinite common core has lower density at least `ρ` in each member's fixed
ordering. -/
def VanishingNoiseDenseSetCondition
    (family : ℕ → GenLimit.Generic.Language ℕ)
    (orders : ℕ → OrderedLanguage) (ρ : ℝ) : Prop :=
  ∀ S : Finset ℕ, S.Nonempty →
    (finiteCommonCore (indexedLanguages family S)).Infinite →
      ∀ i, i ∈ S →
        ρ ≤ (orders i).lowerDensity
          (finiteCommonCore (indexedLanguages family S))

/-- One set generator succeeds with lower density `ρ` on every indexed
target and every vanishing-noise arbitrary-omission presentation. -/
def GeneratesSetDensityUnderVanishingNoise
    (gen : SetGenerator ℕ)
    (family : ℕ → GenLimit.Generic.Language ℕ)
    (orders : ℕ → OrderedLanguage) (ρ : ℝ) : Prop :=
  IsInfiniteSetGenerator gen ∧
    ∀ target stream,
      VanishingNoiseArbitraryOmissionEnumeration
          stream (family target) →
        GeneratesSetInLimitOn gen (family target) stream ∧
          ρ ≤ setBasedLowerDensity gen (orders target) stream

/-- A finite set of indexed targets admits one common eventual correctness
time for a fixed set-valued run. -/
theorem eventually_set_correct_on_finite_indices
    (gen : SetGenerator ℕ)
    (family : ℕ → GenLimit.Generic.Language ℕ)
    (stream : GenLimit.Generic.Stream ℕ)
    (S : Finset ℕ)
    (hgen :
      ∀ i, i ∈ S → GeneratesSetInLimitOn gen (family i) stream) :
    ∃ T, ∀ i, i ∈ S → ∀ t, T ≤ t →
      SetCorrectAt gen (family i) stream t := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      exact ⟨0, by simp⟩
  | @insert i S hi ih =>
      obtain ⟨Ti, hTi⟩ := hgen i (Finset.mem_insert_self i S)
      obtain ⟨TS, hTS⟩ := ih (by
        intro j hj
        exact hgen j (Finset.mem_insert_of_mem hj))
      refine ⟨max Ti TS, ?_⟩
      intro j hj t ht
      rcases Finset.mem_insert.mp hj with rfl | hjS
      · exact hTi t ((Nat.le_max_left _ _).trans ht)
      · exact hTS j hjS t ((Nat.le_max_right _ _).trans ht)

/-- Necessity half of Theorem 6.11.  The common sparse presentation forces
one eventual output into the entire finite common core. -/
theorem theorem_6_11_necessity_enumerated
    (family : ℕ → GenLimit.Generic.Language ℕ)
    (orders : ℕ → OrderedLanguage) (ρ : ℝ)
    {gen : SetGenerator ℕ}
    (hgen : GeneratesSetDensityUnderVanishingNoise
      gen family orders ρ) :
    VanishingNoiseDenseSetCondition family orders ρ := by
  classical
  intro S hS hcore i hi
  obtain ⟨stream, _hinjective, hstream⟩ :=
    exists_common_vanishingNoise_presentation family S hS hcore
  have hrun :
      ∀ j, j ∈ S →
        GeneratesSetInLimitOn gen (family j) stream := by
    intro j hj
    exact (hgen.2 j stream (hstream j hj)).1
  obtain ⟨T, hT⟩ :=
    eventually_set_correct_on_finite_indices
      gen family stream S hrun
  have hsubset :
      ∀ᶠ t : ℕ in atTop,
        setOutput gen stream t ⊆
          finiteCommonCore (indexedLanguages family S) := by
    rw [eventually_atTop]
    refine ⟨T, ?_⟩
    intro t ht x hx L hL
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hL
    exact (hT j hj t ht).1 hx
  have hdensity := (hgen.2 i stream (hstream i hi)).2
  exact hdensity.trans
    (setBasedLowerDensity_le_of_frequently_subset
      gen (orders i) stream
      (finiteCommonCore (indexedLanguages family S))
      hsubset.frequently)

/-- Algorithm 6: Algorithm 4's geometric-priority common core, with the
observed finite sample removed. -/
noncomputable def algorithmSixGenerator
    (family : ℕ → GenLimit.Generic.Language ℕ)
    (fallback : ℕ) : SetGenerator ℕ :=
  priorityCoreSetGenerator family geometricThreshold fallback

/-- Sufficiency half of Theorem 6.11 for an explicitly indexed countable
family. -/
theorem theorem_6_11_sufficiency_enumerated
    (family : ℕ → GenLimit.Generic.Language ℕ)
    (hfamily : ∀ i, (family i).Infinite)
    (orders : ℕ → OrderedLanguage)
    (_hcarrier : ∀ i, (orders i).carrier = family i)
    (ρ : ℝ)
    (hcondition : VanishingNoiseDenseSetCondition family orders ρ) :
    ∃ gen : SetGenerator ℕ,
      GeneratesSetDensityUnderVanishingNoise gen family orders ρ := by
  let fallback : ℕ := Classical.choose (hfamily 0).nonempty
  let gen := algorithmSixGenerator family fallback
  refine ⟨gen, priorityCoreSetGenerator_infinite
    family hfamily geometricThreshold fallback, ?_⟩
  intro target stream hstream
  obtain ⟨p, htarget⟩ :=
    exists_boundedPriorityClass_of_vanishingNoise
      stream family geometricThreshold target
      (geometricThreshold_pos target) hstream.2.2
  have hstableInfinite :=
    theorem_5_1_geometric_stable_core_infinite
      stream family hstream.1 p
  obtain ⟨T, hT⟩ :=
    lemma_5_2_eventually_selects_stable_class
      family
      (thresholdPriorityTrace stream family geometricThreshold)
      (thresholdPriorityTrace_mono stream family geometricThreshold)
      (thresholdPriorityTrace_index_le stream family geometricThreshold)
      p hstableInfinite
  have hcorrect : GeneratesSetInLimitOn gen (family target) stream := by
    refine ⟨T, ?_⟩
    intro t ht
    have hselected := hT t ht
    have hvalid :
        finiteCommonCore
            (indexedLanguages family
              (algorithmFourIndices family
                (fun i =>
                  thresholdPriorityTrace
                    stream family geometricThreshold i t) t)) ⊆
          family target :=
      corollary_4_2_selected_core_subset_target
        family
        (thresholdPriorityTrace stream family geometricThreshold)
        p target _ hselected.1 htarget
    unfold SetCorrectAt
    rw [show setOutput gen stream t =
        finiteCommonCore
            (indexedLanguages family
              (algorithmFourIndices family
                (fun i => thresholdPriorityTrace
                  stream family geometricThreshold i t) t)) \
          (↑(GenLimit.Generic.sample stream t) : Set ℕ) by
      simpa [gen, algorithmSixGenerator] using
        priorityCoreSetGenerator_output
          family geometricThreshold fallback stream t]
    refine ⟨fun _ hx => hvalid hx.1, ?_⟩
    exact Set.disjoint_sdiff_left
  refine ⟨hcorrect, ?_⟩
  unfold setBasedLowerDensity
  apply le_liminf_of_le
  · exact isCoboundedUnder_ge_of_le atTop
      (fun t => (orders target).lowerDensity_le_one
        (setOutput gen stream t))
  · rw [eventually_atTop]
    refine ⟨T, ?_⟩
    intro t ht
    let selected :=
      algorithmFourIndices family
        (fun i => thresholdPriorityTrace
          stream family geometricThreshold i t) t
    have hselected := hT t ht
    have htargetSelected : target ∈ selected := hselected.1 htarget
    have hnonempty : selected.Nonempty := ⟨target, htargetSelected⟩
    have hbase :
        ρ ≤ (orders target).lowerDensity
          (finiteCommonCore (indexedLanguages family selected)) :=
      hcondition selected hnonempty hselected.2 target htargetSelected
    have hdelete :=
      (orders target).lowerDensity_diff_finite
        (finiteCommonCore (indexedLanguages family selected))
        (GenLimit.Generic.sample stream t).finite_toSet
    have hout :
        setOutput gen stream t =
          finiteCommonCore (indexedLanguages family selected) \
            (↑(GenLimit.Generic.sample stream t) : Set ℕ) := by
      simpa [gen, algorithmSixGenerator, selected] using
        priorityCoreSetGenerator_output
          family geometricThreshold fallback stream t
    rw [hout, hdelete]
    exact hbase

/-- Theorem 6.11, for an explicit enumeration of the paper's countable
collection. -/
theorem theorem_6_11_characterization_enumerated
    (family : ℕ → GenLimit.Generic.Language ℕ)
    (hfamily : ∀ i, (family i).Infinite)
    (orders : ℕ → OrderedLanguage)
    (hcarrier : ∀ i, (orders i).carrier = family i)
    (ρ : ℝ) :
    (∃ gen : SetGenerator ℕ,
        GeneratesSetDensityUnderVanishingNoise gen family orders ρ) ↔
      VanishingNoiseDenseSetCondition family orders ρ := by
  constructor
  · rintro ⟨gen, hgen⟩
    exact theorem_6_11_necessity_enumerated family orders ρ hgen
  · intro hcondition
    exact theorem_6_11_sufficiency_enumerated
      family hfamily orders hcarrier ρ hcondition

/-! ## Theorem 6.14: constant noise -/

/-- Algorithm 7's density stopping predicate for the first `k` current
languages in priority order. -/
def DensityPrefixAccepts
    (family : ℕ → GenLimit.Generic.Language ℕ)
    (orders : ℕ → OrderedLanguage) (ρ : ℝ)
    (score : ℕ → ℕ) (n k : ℕ) : Prop :=
  ∀ i, i ∈ rankedPrefix score n k →
    ρ ≤ (orders i).lowerDensity
      (finiteCommonCore
        (indexedLanguages family (rankedPrefix score n k)))

/-- Largest prefix accepted by Algorithm 7's density stopping rule. -/
noncomputable def maximalDensePrefixSize
    (family : ℕ → GenLimit.Generic.Language ℕ)
    (orders : ℕ → OrderedLanguage) (ρ : ℝ)
    (score : ℕ → ℕ) (n : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest
    (DensityPrefixAccepts family orders ρ score n) n

theorem le_maximalDensePrefixSize
    (family : ℕ → GenLimit.Generic.Language ℕ)
    (orders : ℕ → OrderedLanguage) (ρ : ℝ)
    (score : ℕ → ℕ) {n k : ℕ}
    (hkn : k ≤ n)
    (haccept : DensityPrefixAccepts family orders ρ score n k) :
    k ≤ maximalDensePrefixSize family orders ρ score n := by
  classical
  exact Nat.le_findGreatest hkn haccept

/-- Actual finite index prefix selected by Algorithm 7. -/
noncomputable def algorithmSevenIndices
    (family : ℕ → GenLimit.Generic.Language ℕ)
    (orders : ℕ → OrderedLanguage) (ρ : ℝ)
    (score : ℕ → ℕ) (n : ℕ) : Finset ℕ :=
  rankedPrefix score n
    (maximalDensePrefixSize family orders ρ score n)

theorem algorithmSevenIndices_accepts
    (family : ℕ → GenLimit.Generic.Language ℕ)
    (orders : ℕ → OrderedLanguage) (ρ : ℝ)
    (score : ℕ → ℕ) (n : ℕ) :
    ∀ i, i ∈ algorithmSevenIndices family orders ρ score n →
      ρ ≤ (orders i).lowerDensity
        (finiteCommonCore
          (indexedLanguages family
            (algorithmSevenIndices family orders ρ score n))) := by
  classical
  have hzero :
      DensityPrefixAccepts family orders ρ score n 0 := by
    simp [DensityPrefixAccepts, rankedPrefix]
  simpa [algorithmSevenIndices, maximalDensePrefixSize] using
    (Nat.findGreatest_spec
      (P := DensityPrefixAccepts family orders ρ score n)
      (Nat.zero_le n) hzero)

theorem rankedPrefix_subset_algorithmSevenIndices
    (family : ℕ → GenLimit.Generic.Language ℕ)
    (orders : ℕ → OrderedLanguage) (ρ : ℝ)
    (score : ℕ → ℕ) {n k : ℕ}
    (hkn : k ≤ n)
    (haccept : DensityPrefixAccepts family orders ρ score n k) :
    rankedPrefix score n k ⊆
      algorithmSevenIndices family orders ρ score n := by
  exact rankedPrefix_mono score n
    (le_maximalDensePrefixSize
      family orders ρ score hkn haccept)

/-- Indexed implication form of Condition 3.  The common stream is required
to be a valid constant-noise arbitrary-omission presentation for every
member, matching the adversaries on which a single generator must succeed.
-/
def ConstantNoiseDenseSetCondition
    (family : ℕ → GenLimit.Generic.Language ℕ)
    (orders : ℕ → OrderedLanguage) (c ρ : ℝ) : Prop :=
  ∀ S : Finset ℕ, S.Nonempty →
    ∀ stream,
      (∀ i, i ∈ S →
        ConstantNoiseArbitraryOmissionEnumeration
          stream (family i) c) →
      ∀ i, i ∈ S →
        ρ ≤ (orders i).lowerDensity
          (finiteCommonCore (indexedLanguages family S))

/-- Set-generation and density guarantee under constant noise. -/
def GeneratesSetDensityUnderConstantNoise
    (gen : SetGenerator ℕ)
    (family : ℕ → GenLimit.Generic.Language ℕ)
    (orders : ℕ → OrderedLanguage) (c ρ : ℝ) : Prop :=
  IsInfiniteSetGenerator gen ∧
    ∀ target stream,
      ConstantNoiseArbitraryOmissionEnumeration
          stream (family target) c →
        GeneratesSetInLimitOn gen (family target) stream ∧
          ρ ≤ setBasedLowerDensity gen (orders target) stream

/-- Necessity half of Theorem 6.14. -/
theorem theorem_6_14_necessity_enumerated
    (family : ℕ → GenLimit.Generic.Language ℕ)
    (orders : ℕ → OrderedLanguage) (c ρ : ℝ)
    {gen : SetGenerator ℕ}
    (hgen : GeneratesSetDensityUnderConstantNoise
      gen family orders c ρ) :
    ConstantNoiseDenseSetCondition family orders c ρ := by
  classical
  intro S hS stream hstream i hi
  have hrun :
      ∀ j, j ∈ S →
        GeneratesSetInLimitOn gen (family j) stream := by
    intro j hj
    exact (hgen.2 j stream (hstream j hj)).1
  obtain ⟨T, hT⟩ :=
    eventually_set_correct_on_finite_indices
      gen family stream S hrun
  have hsubset :
      ∀ᶠ t : ℕ in atTop,
        setOutput gen stream t ⊆
          finiteCommonCore (indexedLanguages family S) := by
    rw [eventually_atTop]
    refine ⟨T, ?_⟩
    intro t ht x hx L hL
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hL
    exact (hT j hj t ht).1 hx
  exact (hgen.2 i stream (hstream i hi)).2.trans
    (setBasedLowerDensity_le_of_frequently_subset
      gen (orders i) stream
      (finiteCommonCore (indexedLanguages family S))
      hsubset.frequently)

/-- Once the uniform-threshold stable class is separated in priority order,
Algorithm 7 contains it whenever it satisfies the density stopping rule. -/
theorem algorithmSeven_eventually_selects_stable_class
    (family : ℕ → GenLimit.Generic.Language ℕ)
    (orders : ℕ → OrderedLanguage) (ρ : ℝ)
    (trace : ℕ → ℕ → ℕ)
    (hmono : ∀ i, Monotone (trace i))
    (hlower : ∀ i n, i ≤ trace i n)
    (p : ℕ)
    (hstableAccepts :
      ∀ i, i ∈ boundedPriorityIndices trace p →
        ρ ≤ (orders i).lowerDensity
          (finiteCommonCore
            (indexedLanguages family
              (boundedPriorityIndices trace p)))) :
    ∃ T, ∀ n, T ≤ n →
      boundedPriorityIndices trace p ⊆
        algorithmSevenIndices family orders ρ
          (fun i => trace i n) n ∧
      (∀ i,
        i ∈ algorithmSevenIndices family orders ρ
            (fun j => trace j n) n →
          ρ ≤ (orders i).lowerDensity
            (finiteCommonCore
              (indexedLanguages family
                (algorithmSevenIndices family orders ρ
                  (fun j => trace j n) n)))) := by
  classical
  obtain ⟨N, _hpN, hN⟩ :=
    lemma_4_1_prefix_priority_stabilization
      trace hmono hlower p
  refine ⟨max N (p + 1), ?_⟩
  intro n hn
  have hnN : N ≤ n := (Nat.le_max_left N (p + 1)).trans hn
  have hpn : p + 1 ≤ n :=
    (Nat.le_max_right N (p + 1)).trans hn
  have hsep := hN n hnN
  let stable := boundedPriorityIndices trace p
  have hstableRange : stable ⊆ Finset.range n := by
    intro i hi
    exact Finset.mem_range.mpr
      ((mem_boundedPriorityIndices.mp hi).1.trans_lt (by omega))
  have hreorder :
      rankedPrefix (fun i => trace i n) n stable.card = stable := by
    apply rankedPrefix_card_eq_of_priority_separation
      (fun i => trace i n) n p stable hstableRange
    · exact hsep.1
    · intro i _hi hinot
      exact hsep.2.1 i hinot
  have hcard : stable.card ≤ n :=
    by simpa using Finset.card_le_card hstableRange
  have haccepts :
      DensityPrefixAccepts family orders ρ
        (fun i => trace i n) n stable.card := by
    unfold DensityPrefixAccepts
    rw [hreorder]
    intro i hi
    exact hstableAccepts i hi
  refine ⟨?_, algorithmSevenIndices_accepts
    family orders ρ (fun i => trace i n) n⟩
  change stable ⊆
    algorithmSevenIndices family orders ρ (fun i => trace i n) n
  rw [← hreorder]
  exact rankedPrefix_subset_algorithmSevenIndices
    family orders ρ (fun i => trace i n) hcard haccepts

/-- Algorithm 7's selected prefix, computed from a finite history. -/
noncomputable def algorithmSevenHistoryIndices
    (family : ℕ → GenLimit.Generic.Language ℕ)
    (orders : ℕ → OrderedLanguage) (c ρ : ℝ)
    (fallback : ℕ) {t : ℕ} (xs : Fin t → ℕ) : Finset ℕ :=
  algorithmSevenIndices family orders ρ
    (algorithmFourHistoryScore family (fun _ => c) fallback xs) t

theorem algorithmSevenHistoryIndices_eq_stream
    (family : ℕ → GenLimit.Generic.Language ℕ)
    (orders : ℕ → OrderedLanguage) (c ρ : ℝ)
    (fallback : ℕ)
    (stream : GenLimit.Generic.Stream ℕ) (t : ℕ) :
    algorithmSevenHistoryIndices family orders c ρ fallback
        (fun j : Fin t => stream j) =
      algorithmSevenIndices family orders ρ
        (fun i =>
          thresholdPriorityTrace stream family (fun _ => c) i t) t := by
  unfold algorithmSevenHistoryIndices
  congr 1
  funext i
  exact algorithmFourHistoryScore_eq_trace
    family (fun _ => c) fallback stream t i

/-- Literal finite-history implementation of Algorithm 7. -/
noncomputable def algorithmSevenGenerator
    (family : ℕ → GenLimit.Generic.Language ℕ)
    (orders : ℕ → OrderedLanguage) (c ρ : ℝ)
    (fallback : ℕ) : SetGenerator ℕ :=
  fun _ xs =>
    finiteCommonCore
        (indexedLanguages family
          (algorithmSevenHistoryIndices
            family orders c ρ fallback xs)) \
      (↑(GenLimit.Generic.sequenceSample xs) : Set ℕ)

@[simp] theorem algorithmSevenGenerator_output
    (family : ℕ → GenLimit.Generic.Language ℕ)
    (orders : ℕ → OrderedLanguage) (c ρ : ℝ)
    (fallback : ℕ)
    (stream : GenLimit.Generic.Stream ℕ) (t : ℕ) :
    setOutput (algorithmSevenGenerator family orders c ρ fallback)
        stream t =
      finiteCommonCore
          (indexedLanguages family
            (algorithmSevenIndices family orders ρ
              (fun i => thresholdPriorityTrace
                stream family (fun _ => c) i t) t)) \
        (↑(GenLimit.Generic.sample stream t) : Set ℕ) := by
  simp only [setOutput, algorithmSevenGenerator,
    GenLimit.Generic.sequenceSample_prefix]
  rw [algorithmSevenHistoryIndices_eq_stream]

/-- Positive density makes every Algorithm 7 output infinite. -/
theorem algorithmSevenGenerator_infinite
    (family : ℕ → GenLimit.Generic.Language ℕ)
    (hfamily : ∀ i, (family i).Infinite)
    (orders : ℕ → OrderedLanguage) (c ρ : ℝ)
    (hρ : 0 < ρ) (fallback : ℕ) :
    IsInfiniteSetGenerator
      (algorithmSevenGenerator family orders c ρ fallback) := by
  classical
  intro t xs
  let score := algorithmFourHistoryScore family (fun _ => c) fallback xs
  let selected := algorithmSevenIndices family orders ρ score t
  have haccepts :=
    algorithmSevenIndices_accepts family orders ρ score t
  have hcore :
      (finiteCommonCore (indexedLanguages family selected)).Infinite := by
    by_cases hempty : selected = ∅
    · have huniv : (Set.univ : Set ℕ).Infinite :=
        (hfamily 0).mono (Set.subset_univ _)
      simpa [hempty, indexedLanguages] using huniv
    · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      by_contra hnot
      have hfinite := Set.not_infinite.mp hnot
      have hdensity := haccepts i hi
      rw [(orders i).lowerDensity_eq_zero_of_finite hfinite] at hdensity
      exact (not_le_of_gt hρ) hdensity
  exact hcore.diff
    (GenLimit.Generic.sequenceSample xs).finite_toSet

/-- Sufficiency half of Theorem 6.14 for `0 < c < 1`.  The strict upper
bound is exactly what turns every bounded-priority candidate into a valid
arbitrary-omission presentation; the source's printed endpoint `c = 1`
does not justify that step. -/
theorem theorem_6_14_sufficiency_enumerated
    (family : ℕ → GenLimit.Generic.Language ℕ)
    (hfamily : ∀ i, (family i).Infinite)
    (orders : ℕ → OrderedLanguage)
    (_hcarrier : ∀ i, (orders i).carrier = family i)
    (c ρ : ℝ) (_hc0 : 0 < c) (hc1 : c < 1) (hρ : 0 < ρ)
    (hcondition : ConstantNoiseDenseSetCondition family orders c ρ) :
    ∃ gen : SetGenerator ℕ,
      GeneratesSetDensityUnderConstantNoise
        gen family orders c ρ := by
  classical
  let fallback : ℕ := Classical.choose (hfamily 0).nonempty
  let gen := algorithmSevenGenerator family orders c ρ fallback
  refine ⟨gen,
    algorithmSevenGenerator_infinite
      family hfamily orders c ρ hρ fallback, ?_⟩
  intro target stream hstream
  obtain ⟨p, htarget⟩ :=
    exists_boundedPriorityClass_of_eventually_le
      stream family (fun _ => c) target hstream.2.2
  let trace := thresholdPriorityTrace stream family (fun _ => c)
  let stable := boundedPriorityIndices trace p
  have hstableNonempty : stable.Nonempty := ⟨target, htarget⟩
  have hstablePresentations :
      ∀ i, i ∈ stable →
        ConstantNoiseArbitraryOmissionEnumeration
          stream (family i) c := by
    intro i hi
    have hconstant : ConstantNoise stream (family i) c :=
      ⟨p, fun n hn =>
        empiricalNoiseRate_le_threshold_of_boundedPriority
          stream family (fun _ => c) hi (by omega)⟩
    exact ⟨hstream.1,
      arbitraryOmissions_of_injective_constantNoise_lt_one
        hstream.1 hc1 hconstant,
      hconstant⟩
  have hstableAccepts :
      ∀ i, i ∈ stable →
        ρ ≤ (orders i).lowerDensity
          (finiteCommonCore (indexedLanguages family stable)) :=
    hcondition stable hstableNonempty stream hstablePresentations
  obtain ⟨T, hT⟩ :=
    algorithmSeven_eventually_selects_stable_class
      family orders ρ trace
      (thresholdPriorityTrace_mono stream family (fun _ => c))
      (thresholdPriorityTrace_index_le stream family (fun _ => c))
      p hstableAccepts
  have hcorrect : GeneratesSetInLimitOn gen (family target) stream := by
    refine ⟨T, ?_⟩
    intro t ht
    have hselected := hT t ht
    let selected :=
      algorithmSevenIndices family orders ρ
        (fun i => trace i t) t
    have hvalid :
        finiteCommonCore (indexedLanguages family selected) ⊆
          family target :=
      corollary_4_2_selected_core_subset_target
        family trace p target selected hselected.1 htarget
    unfold SetCorrectAt
    rw [show setOutput gen stream t =
        finiteCommonCore (indexedLanguages family selected) \
          (↑(GenLimit.Generic.sample stream t) : Set ℕ) by
      simpa [gen, trace, selected] using
        algorithmSevenGenerator_output
          family orders c ρ fallback stream t]
    exact ⟨fun _ hx => hvalid hx.1, Set.disjoint_sdiff_left⟩
  refine ⟨hcorrect, ?_⟩
  unfold setBasedLowerDensity
  apply le_liminf_of_le
  · exact isCoboundedUnder_ge_of_le atTop
      (fun t => (orders target).lowerDensity_le_one
        (setOutput gen stream t))
  · rw [eventually_atTop]
    refine ⟨T, ?_⟩
    intro t ht
    have hselected := hT t ht
    let selected :=
      algorithmSevenIndices family orders ρ
        (fun i => trace i t) t
    have htargetSelected : target ∈ selected := hselected.1 htarget
    have hbase :
        ρ ≤ (orders target).lowerDensity
          (finiteCommonCore (indexedLanguages family selected)) :=
      hselected.2 target htargetSelected
    have hdelete :=
      (orders target).lowerDensity_diff_finite
        (finiteCommonCore (indexedLanguages family selected))
        (GenLimit.Generic.sample stream t).finite_toSet
    have hout :
        setOutput gen stream t =
          finiteCommonCore (indexedLanguages family selected) \
            (↑(GenLimit.Generic.sample stream t) : Set ℕ) := by
      simpa [gen, trace, selected] using
        algorithmSevenGenerator_output
          family orders c ρ fallback stream t
    rw [hout, hdelete]
    exact hbase

/-- Theorem 6.14 characterization on the source-faithful range
`0 < c < 1`, for an explicit enumeration of the countable collection. -/
theorem theorem_6_14_characterization_enumerated
    (family : ℕ → GenLimit.Generic.Language ℕ)
    (hfamily : ∀ i, (family i).Infinite)
    (orders : ℕ → OrderedLanguage)
    (hcarrier : ∀ i, (orders i).carrier = family i)
    (c ρ : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (hρ : 0 < ρ) :
    (∃ gen : SetGenerator ℕ,
        GeneratesSetDensityUnderConstantNoise
          gen family orders c ρ) ↔
      ConstantNoiseDenseSetCondition family orders c ρ := by
  constructor
  · rintro ⟨gen, hgen⟩
    exact theorem_6_14_necessity_enumerated
      family orders c ρ hgen
  · intro hcondition
    exact theorem_6_14_sufficiency_enumerated
      family hfamily orders hcarrier c ρ hc0 hc1 hρ hcondition

end GenLimit.InfiniteContamination
