import GenLimit.Paper17_InfiniteContamination.AlgorithmEight

/-!
# Algorithm 9: set density under bounded displacement

Source: Mehrotra--Velegkas--Yu--Zhou,
*Language Generation with Infinite Contamination*,
arXiv:2511.07417v1, Algorithm 9 and Theorem 7.8.

The source's final pseudocode line returns the selected intersection itself,
although Definition 4 requires every set output to avoid the observed sample.
The generator below therefore removes that finite sample.  This does not
change ordered lower density and makes the implementation satisfy the
paper's declared set-generator interface literally.
-/

namespace GenLimit.InfiniteContamination

open Filter
open scoped Topology BigOperators
open GenLimit.KleinbergWei

/-! ## Priority diagnostics -/

/-- Zero-based form of Algorithm 9's summable error allocation
`ε / 2ⁱ`. -/
noncomputable def algorithmNineNoiseThreshold
    (ε : ℝ) (i : ℕ) : ℝ :=
  ε * (1 / 2 : ℝ) ^ (i + 1)

theorem algorithmNineNoiseThreshold_pos
    {ε : ℝ} (hε : 0 < ε) (i : ℕ) :
    0 < algorithmNineNoiseThreshold ε i := by
  unfold algorithmNineNoiseThreshold
  positivity

theorem sum_algorithmNineNoiseThreshold_range_le
    {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) :
    ∑ i ∈ Finset.range n, algorithmNineNoiseThreshold ε i ≤ ε := by
  have hsum := sum_geometricThreshold_range_le_half n
  calc
    ∑ i ∈ Finset.range n, algorithmNineNoiseThreshold ε i =
        (2 * ε) * ∑ i ∈ Finset.range n, geometricThreshold i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      simp [algorithmNineNoiseThreshold, geometricThreshold, pow_succ]
      ring
    _ ≤ (2 * ε) * (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ε := by ring

theorem sum_algorithmNineNoiseThreshold_le
    {ε : ℝ} (hε : 0 ≤ ε) {S : Finset ℕ} {n : ℕ}
    (hS : S ⊆ Finset.range n) :
    ∑ i ∈ S, algorithmNineNoiseThreshold ε i ≤ ε := by
  calc
    ∑ i ∈ S, algorithmNineNoiseThreshold ε i ≤
        ∑ i ∈ Finset.range n, algorithmNineNoiseThreshold ε i := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hS
        (fun i _hi _hinot =>
          mul_nonneg hε (by positivity))
    _ ≤ ε := sum_algorithmNineNoiseThreshold_range_le hε n

/-- Largest canonical rank, relative to `K`, among the first `n` input
positions. -/
noncomputable def prefixMaxCanonicalRank
    (K : OrderedLanguage)
    (stream : GenLimit.Generic.Stream ℕ) (n : ℕ) : ℕ :=
  (Finset.range n).sup fun j =>
    canonicalRank K K.carrier (stream j)

theorem canonicalRank_le_prefixMaxCanonicalRank
    (K : OrderedLanguage)
    (stream : GenLimit.Generic.Stream ℕ)
    {j n : ℕ} (hj : j < n) :
    canonicalRank K K.carrier (stream j) ≤
      prefixMaxCanonicalRank K stream n := by
  exact Finset.le_sup
    (f := fun r => canonicalRank K K.carrier (stream r))
    (Finset.mem_range.mpr hj)

/-- An eventual pointwise displacement bound also controls the maximum of
the whole observed prefix once the linear budget absorbs the finite initial
exception. -/
theorem eventually_prefixMaxCanonicalRank_le
    (K : OrderedLanguage)
    (stream : GenLimit.Generic.Stream ℕ)
    (M : ℝ) (hM : 0 < M)
    (hbounded : BoundedDisplacement K stream K.carrier M) :
    ∃ N, ∀ n, N ≤ n →
      (prefixMaxCanonicalRank K stream n : ℝ) ≤ M * n := by
  obtain ⟨T, hT⟩ := hbounded
  let B : ℕ :=
    (Finset.range T).sup fun j =>
      canonicalRank K K.carrier (stream j)
  let Nscale : ℕ := ⌈(B : ℝ) / M⌉₊
  refine ⟨max (max T Nscale) 1, ?_⟩
  intro n hn
  have hnT : T ≤ n :=
    (Nat.le_max_left T Nscale).trans
      (Nat.le_max_left (max T Nscale) 1) |>.trans hn
  have hnScale : Nscale ≤ n :=
    (Nat.le_max_right T Nscale).trans
      (Nat.le_max_left (max T Nscale) 1) |>.trans hn
  have hnpos : 0 < n := by
    have : 1 ≤ n :=
      (Nat.le_max_right (max T Nscale) 1).trans hn
    omega
  apply Finset.sup_mem
      {r : ℕ | (r : ℝ) ≤ M * n}
  · simp only [Set.mem_setOf_eq]
    have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    simpa using mul_nonneg hM.le hnnonneg
  · intro x hx y hy
    change (x : ℝ) ≤ M * n at hx
    change (y : ℝ) ≤ M * n at hy
    change ((max x y : ℕ) : ℝ) ≤ M * n
    simpa only [Nat.cast_max] using max_le hx hy
  · intro j hj
    have hjn : j < n := Finset.mem_range.mp hj
    by_cases hjT : j < T
    · have hjB : canonicalRank K K.carrier (stream j) ≤ B :=
        Finset.le_sup
          (f := fun r => canonicalRank K K.carrier (stream r))
          (Finset.mem_range.mpr hjT)
      have hdiv : (B : ℝ) / M ≤ Nscale := Nat.le_ceil _
      have hBN : (B : ℝ) ≤ M * Nscale :=
        by simpa [mul_comm] using (div_le_iff₀ hM).mp hdiv
      have hNn : (Nscale : ℝ) ≤ n := by exact_mod_cast hnScale
      have hjBReal :
          (canonicalRank K K.carrier (stream j) : ℝ) ≤ B := by
        exact_mod_cast hjB
      exact hjBReal.trans
        (hBN.trans (mul_le_mul_of_nonneg_left hNn hM.le))
    · have hTj : T ≤ j := Nat.le_of_not_gt hjT
      have hjbound := hT j hTj
      have hjnReal : (j + 1 : ℕ) ≤ n := Nat.succ_le_iff.mpr hjn
      exact hjbound.trans
        (mul_le_mul_of_nonneg_left
          (by exact_mod_cast hjnReal) hM.le)

/-- The two finite tests in Algorithm 9. -/
def AlgorithmNineGoodAt
    (stream : GenLimit.Generic.Stream ℕ)
    (family : ℕ → Set ℕ)
    (orders : ℕ → OrderedLanguage)
    (ε M : ℝ) (i n : ℕ) : Prop :=
  empiricalNoiseRate stream (family i) n ≤
      algorithmNineNoiseThreshold ε i ∧
    (prefixMaxCanonicalRank (orders i) stream n : ℝ) ≤ M * n

/-- A Boolean-valued real diagnostic lets the shared last-violation
priority kernel represent both Algorithm 9 tests at once. -/
noncomputable def algorithmNineDiagnostic
    (stream : GenLimit.Generic.Stream ℕ)
    (family : ℕ → Set ℕ)
    (orders : ℕ → OrderedLanguage)
    (ε M : ℝ) (i n : ℕ) : ℝ := by
  classical
  exact if AlgorithmNineGoodAt stream family orders ε M i n then 0 else 1

noncomputable def algorithmNinePriorityTrace
    (stream : GenLimit.Generic.Stream ℕ)
    (family : ℕ → Set ℕ)
    (orders : ℕ → OrderedLanguage)
    (ε M : ℝ) (i n : ℕ) : ℕ :=
  i + thresholdPenalty
    (algorithmNineDiagnostic stream family orders ε M i) 0 n

theorem algorithmNinePriorityTrace_mono
    (stream : GenLimit.Generic.Stream ℕ)
    (family : ℕ → Set ℕ)
    (orders : ℕ → OrderedLanguage)
    (ε M : ℝ) (i : ℕ) :
    Monotone (algorithmNinePriorityTrace
      stream family orders ε M i) := by
  intro m n hmn
  exact Nat.add_le_add_left
    (thresholdPenalty_mono
      (algorithmNineDiagnostic stream family orders ε M i) 0 hmn) i

theorem algorithmNinePriorityTrace_index_le
    (stream : GenLimit.Generic.Stream ℕ)
    (family : ℕ → Set ℕ)
    (orders : ℕ → OrderedLanguage)
    (ε M : ℝ) (i n : ℕ) :
    i ≤ algorithmNinePriorityTrace stream family orders ε M i n := by
  unfold algorithmNinePriorityTrace
  omega

theorem algorithmNineDiagnostic_le_zero_of_good
    (stream : GenLimit.Generic.Stream ℕ)
    (family : ℕ → Set ℕ)
    (orders : ℕ → OrderedLanguage)
    (ε M : ℝ) {i n : ℕ}
    (hgood : AlgorithmNineGoodAt stream family orders ε M i n) :
    algorithmNineDiagnostic stream family orders ε M i n ≤ 0 := by
  simp [algorithmNineDiagnostic, hgood]

theorem algorithmNinePriority_eventually_constant_of_good
    (stream : GenLimit.Generic.Stream ℕ)
    (family : ℕ → Set ℕ)
    (orders : ℕ → OrderedLanguage)
    (ε M : ℝ) (i : ℕ)
    (hgood : ∃ T, ∀ n, T ≤ n →
      AlgorithmNineGoodAt stream family orders ε M i n) :
    ∃ T, ∀ n, T ≤ n →
      algorithmNinePriorityTrace stream family orders ε M i n =
        algorithmNinePriorityTrace stream family orders ε M i T := by
  obtain ⟨T, hT⟩ := hgood
  refine ⟨T, ?_⟩
  intro n hn
  unfold algorithmNinePriorityTrace
  rw [thresholdPenalty_eq_of_eventually_le
    (algorithmNineDiagnostic stream family orders ε M i) 0
    (fun m hm => algorithmNineDiagnostic_le_zero_of_good
      stream family orders ε M (hT m hm)) hn]

theorem exists_algorithmNine_boundedPriorityClass
    (stream : GenLimit.Generic.Stream ℕ)
    (family : ℕ → Set ℕ)
    (orders : ℕ → OrderedLanguage)
    (ε M : ℝ) (target : ℕ)
    (hgood : ∃ T, ∀ n, T ≤ n →
      AlgorithmNineGoodAt stream family orders ε M target n) :
    ∃ p, target ∈ boundedPriorityIndices
      (algorithmNinePriorityTrace stream family orders ε M) p := by
  obtain ⟨T, hT⟩ :=
    algorithmNinePriority_eventually_constant_of_good
      stream family orders ε M target hgood
  let p := algorithmNinePriorityTrace
    stream family orders ε M target T
  refine ⟨p, mem_boundedPriorityIndices.mpr ⟨?_, ?_⟩⟩
  · exact algorithmNinePriorityTrace_index_le
      stream family orders ε M target T
  · intro n
    rcases le_total n T with hnT | hTn
    · exact algorithmNinePriorityTrace_mono
        stream family orders ε M target hnT
    · exact (hT n hTn).le

theorem algorithmNine_target_has_boundedPriority
    (stream : GenLimit.Generic.Stream ℕ)
    (family : ℕ → Set ℕ)
    (orders : ℕ → OrderedLanguage)
    (ε M : ℝ) (hε : 0 < ε) (hM : 0 < M)
    (target : ℕ)
    (hnoise : VanishingNoise stream (family target))
    (hbounded : BoundedDisplacement
      (orders target) stream (orders target).carrier M) :
    ∃ p, target ∈ boundedPriorityIndices
      (algorithmNinePriorityTrace stream family orders ε M) p := by
  have hnoiseEventually :
      ∀ᶠ n : ℕ in atTop,
        empiricalNoiseRate stream (family target) n ≤
          algorithmNineNoiseThreshold ε target :=
    ((tendsto_order.1 hnoise).2
      (algorithmNineNoiseThreshold ε target)
      (algorithmNineNoiseThreshold_pos hε target)).mono
        (fun _ h => h.le)
  obtain ⟨Nnoise, hNnoise⟩ := eventually_atTop.mp hnoiseEventually
  obtain ⟨Nrank, hNrank⟩ :=
    eventually_prefixMaxCanonicalRank_le
      (orders target) stream M hM hbounded
  apply exists_algorithmNine_boundedPriorityClass
  refine ⟨max Nnoise Nrank, ?_⟩
  intro n hn
  exact ⟨hNnoise n ((Nat.le_max_left _ _).trans hn),
    hNrank n ((Nat.le_max_right _ _).trans hn)⟩

/-! ## Consequences of a bounded priority class -/

theorem algorithmNineGoodAt_of_boundedPriority
    (stream : GenLimit.Generic.Stream ℕ)
    (family : ℕ → Set ℕ)
    (orders : ℕ → OrderedLanguage)
    (ε M : ℝ) {p i n : ℕ}
    (hi : i ∈ boundedPriorityIndices
      (algorithmNinePriorityTrace stream family orders ε M) p)
    (hpn : p < n + 1) :
    AlgorithmNineGoodAt stream family orders ε M i n := by
  by_contra hnot
  have hdiagnostic :
      algorithmNineDiagnostic stream family orders ε M i n = 1 := by
    simp [algorithmNineDiagnostic, hnot]
  have hviolation :
      0 < algorithmNineDiagnostic stream family orders ε M i n := by
    rw [hdiagnostic]
    norm_num
  have hpenalty := thresholdPenalty_eq_time_succ_of_violation
    (algorithmNineDiagnostic stream family orders ε M i) 0 hviolation
  have hbound := (mem_boundedPriorityIndices.mp hi).2 n
  unfold algorithmNinePriorityTrace at hbound
  rw [hpenalty] at hbound
  omega

theorem boundedDisplacement_of_algorithmNine_boundedPriority
    (stream : GenLimit.Generic.Stream ℕ)
    (family : ℕ → Set ℕ)
    (orders : ℕ → OrderedLanguage)
    (ε M : ℝ) {p i : ℕ}
    (hi : i ∈ boundedPriorityIndices
      (algorithmNinePriorityTrace stream family orders ε M) p) :
    BoundedDisplacement (orders i) stream (orders i).carrier M := by
  refine ⟨p, ?_⟩
  intro n hn
  have hgood := algorithmNineGoodAt_of_boundedPriority
    stream family orders ε M hi (n := n + 1) (by omega)
  have hrank :
      (canonicalRank (orders i) (orders i).carrier (stream n) : ℝ) ≤
        prefixMaxCanonicalRank (orders i) stream (n + 1) := by
    exact_mod_cast canonicalRank_le_prefixMaxCanonicalRank
      (orders i) stream (Nat.lt_succ_self n)
  simpa only [Nat.cast_add, Nat.cast_one] using hrank.trans hgood.2

theorem algorithmNineStableCore_noiseRate_le
    (stream : GenLimit.Generic.Stream ℕ)
    (family : ℕ → Set ℕ)
    (orders : ℕ → OrderedLanguage)
    (ε M : ℝ) (hε : 0 ≤ ε)
    (p n : ℕ) (hpn : p < n + 1) :
    empiricalNoiseRate stream
        (finiteCommonCore
          (boundedPriorityLanguages family
            (algorithmNinePriorityTrace stream family orders ε M) p)) n ≤
      ε := by
  classical
  let stable := boundedPriorityIndices
    (algorithmNinePriorityTrace stream family orders ε M) p
  change empiricalNoiseRate stream
      (finiteCommonCore (indexedLanguages family stable)) n ≤ ε
  calc
    empiricalNoiseRate stream
          (finiteCommonCore (indexedLanguages family stable)) n ≤
        ∑ i ∈ stable, empiricalNoiseRate stream (family i) n :=
      empiricalNoiseRate_indexedCommonCore_le_sum stream family stable n
    _ ≤ ∑ i ∈ stable, algorithmNineNoiseThreshold ε i := by
      exact Finset.sum_le_sum fun i hi =>
        (algorithmNineGoodAt_of_boundedPriority
          stream family orders ε M hi hpn).1
    _ ≤ ε := by
      apply sum_algorithmNineNoiseThreshold_le hε
      exact boundedPriorityIndices_subset_range
        (algorithmNinePriorityTrace stream family orders ε M) p

theorem empiricalTargetCount_eq_trueCount_of_injective
    (stream : GenLimit.Generic.Stream ℕ)
    (hinjective : Function.Injective stream)
    (L : Set ℕ) (n : ℕ) :
    empiricalTargetCount stream L n = trueCount stream L n := by
  classical
  letI : DecidableEq ℕ := Classical.decEq ℕ
  letI : DecidablePred (fun x : ℕ => x ∈ L) := Classical.decPred _
  unfold empiricalTargetCount trueCount GenLimit.Generic.sample
  rw [Finset.filter_image]
  exact Finset.card_image_of_injective _ hinjective

theorem empiricalTargetRatio_eq_one_sub_noise_of_injective
    (stream : GenLimit.Generic.Stream ℕ)
    (hinjective : Function.Injective stream)
    (L : Set ℕ) {n : ℕ} (hn : 0 < n) :
    empiricalTargetRatio stream L n =
      1 - empiricalNoiseRate stream L n := by
  have hcount := empiricalTargetCount_eq_trueCount_of_injective
    stream hinjective L n
  have hpartition := trueCount_add_noiseCount stream L n
  have hpartitionReal :
      (trueCount stream L n : ℝ) +
          (noiseCount stream L n : ℝ) = n := by
    exact_mod_cast hpartition
  simp only [empiricalTargetRatio, hn.ne', if_false,
    empiricalNoiseRate]
  rw [hcount]
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  field_simp [hnReal.ne']
  linarith

theorem algorithmNineStableCore_empirical_liminf
    (stream : GenLimit.Generic.Stream ℕ)
    (hinjective : Function.Injective stream)
    (family : ℕ → Set ℕ)
    (orders : ℕ → OrderedLanguage)
    (ε M : ℝ) (hε : 0 ≤ ε)
    (p : ℕ) :
    1 - ε ≤ liminf
      (empiricalTargetRatio stream
        (finiteCommonCore
          (boundedPriorityLanguages family
            (algorithmNinePriorityTrace stream family orders ε M) p)))
      atTop := by
  apply le_liminf_of_le
  · exact isCoboundedUnder_ge_of_le atTop fun n =>
      empiricalTargetRatio_le_one stream _ n
  · filter_upwards [eventually_ge_atTop (max (p + 1) 1)] with n hn
    have hnpos : 0 < n := (Nat.le_max_right (p + 1) 1).trans hn
    rw [empiricalTargetRatio_eq_one_sub_noise_of_injective
      stream hinjective _ hnpos]
    have hnoise := algorithmNineStableCore_noiseRate_le
      stream family orders ε M hε p n (by omega)
    linarith

/-- Every member of a stable Algorithm 9 priority class sees its common
core with lower density at least `(1 - ε) / M`. -/
theorem algorithmNineStableCore_lowerDensity
    (stream : GenLimit.Generic.Stream ℕ)
    (hinjective : Function.Injective stream)
    (family : ℕ → Set ℕ)
    (orders : ℕ → OrderedLanguage)
    (hcarrier : ∀ i, (orders i).carrier = family i)
    (ε M : ℝ) (hε0 : 0 ≤ ε) (hM : 0 < M)
    (p : ℕ) {i : ℕ}
    (hi : i ∈ boundedPriorityIndices
      (algorithmNinePriorityTrace stream family orders ε M) p) :
    (1 - ε) / M ≤
      (orders i).lowerDensity
        (finiteCommonCore
          (boundedPriorityLanguages family
            (algorithmNinePriorityTrace stream family orders ε M) p)) := by
  classical
  let core := finiteCommonCore
    (boundedPriorityLanguages family
      (algorithmNinePriorityTrace stream family orders ε M) p)
  have hcore : core ⊆ (orders i).carrier := by
    rw [hcarrier i]
    exact finiteCommonCore_subset_of_mem
      (show family i ∈ boundedPriorityLanguages family
          (algorithmNinePriorityTrace stream family orders ε M) p by
        exact Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  have hbounded := boundedDisplacement_of_algorithmNine_boundedPriority
    stream family orders ε M hi
  have hchange := lemma_7_5_lowerDensity
    (orders i) stream core hcore M hM hbounded
  have hliminf := algorithmNineStableCore_empirical_liminf
    stream hinjective family orders ε M hε0 p
  calc
    (1 - ε) / M = (1 / M) * (1 - ε) := by ring
    _ ≤ (1 / M) * liminf (empiricalTargetRatio stream core) atTop :=
      mul_le_mul_of_nonneg_left hliminf (one_div_nonneg.mpr hM.le)
    _ ≤ (orders i).lowerDensity core := hchange

/-! ## Algorithm 9's dense-prefix stopping rule -/

/-- The first `k` current priority-ranked languages have a common core of
the required density relative to every member of that prefix. -/
def AlgorithmNineDensePrefix
    (family : ℕ → Set ℕ)
    (orders : ℕ → OrderedLanguage)
    (c : ℝ) (score : ℕ → ℕ) (n k : ℕ) : Prop :=
  ∀ i, i ∈ rankedPrefix score n k →
    c ≤ (orders i).lowerDensity
      (finiteCommonCore
        (indexedLanguages family (rankedPrefix score n k)))

/-- Algorithm 9's finite set of selected language indices. -/
noncomputable def algorithmNineIndices
    (family : ℕ → Set ℕ)
    (orders : ℕ → OrderedLanguage)
    (c : ℝ) (score : ℕ → ℕ) (n : ℕ) : Finset ℕ :=
  algorithmSevenIndices family orders c score n

theorem algorithmNineIndices_dense
    (family : ℕ → Set ℕ)
    (orders : ℕ → OrderedLanguage)
    (c : ℝ) (score : ℕ → ℕ) (n : ℕ) :
    ∀ i, i ∈ algorithmNineIndices family orders c score n →
      c ≤ (orders i).lowerDensity
        (finiteCommonCore
          (indexedLanguages family
            (algorithmNineIndices family orders c score n))) := by
  exact algorithmSevenIndices_accepts family orders c score n

theorem rankedPrefix_subset_algorithmNineIndices
    (family : ℕ → Set ℕ)
    (orders : ℕ → OrderedLanguage)
    (c : ℝ) (score : ℕ → ℕ) {n k : ℕ}
    (hkn : k ≤ n)
    (hdense : AlgorithmNineDensePrefix
      family orders c score n k) :
    rankedPrefix score n k ⊆
      algorithmNineIndices family orders c score n := by
  apply rankedPrefix_subset_algorithmSevenIndices
    family orders c score hkn
  exact hdense

/-! ## Finite-history implementation -/

theorem prefixMaxCanonicalRank_eq_of_eq_on_prefix
    (K : OrderedLanguage)
    {stream₁ stream₂ : GenLimit.Generic.Stream ℕ} {n : ℕ}
    (h : ∀ i, i < n → stream₁ i = stream₂ i) :
    prefixMaxCanonicalRank K stream₁ n =
      prefixMaxCanonicalRank K stream₂ n := by
  unfold prefixMaxCanonicalRank
  apply Finset.sup_congr rfl
  intro i hi
  rw [h i (Finset.mem_range.mp hi)]

theorem algorithmNineDiagnostic_eq_of_eq_through
    (family : ℕ → Set ℕ)
    (orders : ℕ → OrderedLanguage)
    (ε M : ℝ) {stream₁ stream₂ : GenLimit.Generic.Stream ℕ}
    {i t : ℕ}
    (h : ∀ m, m ≤ t → ∀ r, r < m → stream₁ r = stream₂ r) :
    ∀ m, m ≤ t →
      algorithmNineDiagnostic stream₁ family orders ε M i m =
        algorithmNineDiagnostic stream₂ family orders ε M i m := by
  intro m hm
  have hnoise := empiricalNoiseRate_eq_of_eq_on_prefix
    (family i) (h m hm)
  have hrank := prefixMaxCanonicalRank_eq_of_eq_on_prefix
    (orders i) (h m hm)
  unfold algorithmNineDiagnostic AlgorithmNineGoodAt
  rw [hnoise, hrank]

/-- Algorithm 9's priority score computed only from a finite history. -/
noncomputable def algorithmNineHistoryScore
    (family : ℕ → Set ℕ)
    (orders : ℕ → OrderedLanguage)
    (ε M : ℝ) {t : ℕ} (xs : Fin t → ℕ) (i : ℕ) : ℕ :=
  algorithmNinePriorityTrace
    (prefixCompletion 0 xs) family orders ε M i t

theorem algorithmNineHistoryScore_eq_trace
    (family : ℕ → Set ℕ)
    (orders : ℕ → OrderedLanguage)
    (ε M : ℝ) (stream : GenLimit.Generic.Stream ℕ)
    (t i : ℕ) :
    algorithmNineHistoryScore family orders ε M
        (fun j : Fin t => stream j) i =
      algorithmNinePriorityTrace stream family orders ε M i t := by
  unfold algorithmNineHistoryScore algorithmNinePriorityTrace
  congr 1
  apply thresholdPenalty_eq_of_eq_through
  exact algorithmNineDiagnostic_eq_of_eq_through
    family orders ε M (i := i)
      (fun m hm r hr => by
        simp [prefixCompletion, hr.trans_le hm])

/-- Algorithm 9's selected prefix computed only from a finite history. -/
noncomputable def algorithmNineHistoryIndices
    (family : ℕ → Set ℕ)
    (orders : ℕ → OrderedLanguage)
    (ε M : ℝ) {t : ℕ} (xs : Fin t → ℕ) : Finset ℕ :=
  algorithmNineIndices family orders ((1 - ε) / M)
    (algorithmNineHistoryScore family orders ε M xs) t

theorem algorithmNineHistoryIndices_eq_stream
    (family : ℕ → Set ℕ)
    (orders : ℕ → OrderedLanguage)
    (ε M : ℝ) (stream : GenLimit.Generic.Stream ℕ)
    (t : ℕ) :
    algorithmNineHistoryIndices family orders ε M
        (fun j : Fin t => stream j) =
      algorithmNineIndices family orders ((1 - ε) / M)
        (fun i =>
          algorithmNinePriorityTrace stream family orders ε M i t) t := by
  have hscores :
      algorithmNineHistoryScore family orders ε M
          (fun j : Fin t => stream j) =
        fun i => algorithmNinePriorityTrace
          stream family orders ε M i t := by
    funext i
    exact algorithmNineHistoryScore_eq_trace
      family orders ε M stream t i
  exact congrArg
    (fun score => algorithmNineIndices
      family orders ((1 - ε) / M) score t) hscores

/-! ## Stable-prefix selection -/

theorem algorithmNine_eventually_selects_stable_class
    (stream : GenLimit.Generic.Stream ℕ)
    (family : ℕ → Set ℕ)
    (orders : ℕ → OrderedLanguage)
    (ε M c : ℝ) (p : ℕ)
    (hstableDense : ∀ i, i ∈ boundedPriorityIndices
        (algorithmNinePriorityTrace stream family orders ε M) p →
      c ≤ (orders i).lowerDensity
        (finiteCommonCore
          (boundedPriorityLanguages family
            (algorithmNinePriorityTrace stream family orders ε M) p))) :
    ∃ T, ∀ n, T ≤ n →
      boundedPriorityIndices
          (algorithmNinePriorityTrace stream family orders ε M) p ⊆
        algorithmNineIndices family orders c
          (fun i => algorithmNinePriorityTrace
            stream family orders ε M i n) n := by
  classical
  let trace := algorithmNinePriorityTrace stream family orders ε M
  let stable := boundedPriorityIndices trace p
  obtain ⟨N, hpN, hN⟩ := lemma_4_1_prefix_priority_stabilization
    trace
    (fun i => algorithmNinePriorityTrace_mono
      stream family orders ε M i)
    (algorithmNinePriorityTrace_index_le
      stream family orders ε M) p
  refine ⟨max N (p + 1), ?_⟩
  intro n hn
  have hnN : N ≤ n := (Nat.le_max_left N (p + 1)).trans hn
  have hpn : p + 1 ≤ n :=
    (Nat.le_max_right N (p + 1)).trans hn
  have hsep := hN n hnN
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
  have hdense : AlgorithmNineDensePrefix
      family orders c (fun i => trace i n) n stable.card := by
    intro i hi
    rw [hreorder] at hi ⊢
    simpa [stable, trace, boundedPriorityLanguages] using
      hstableDense i hi
  have hsub := rankedPrefix_subset_algorithmNineIndices
    family orders c (fun i => trace i n) hcard hdense
  rw [hreorder] at hsub
  simpa [stable, trace] using hsub

/-! ## Literal set generator and Theorem 7.8 -/

/-- The raw selected intersection before enforcing Definition 4 freshness. -/
noncomputable def algorithmNineRawCore
    (family : ℕ → Set ℕ)
    (orders : ℕ → OrderedLanguage)
    (ε M : ℝ) {t : ℕ} (xs : Fin t → ℕ) : Set ℕ :=
  finiteCommonCore
    (indexedLanguages family
      (algorithmNineHistoryIndices family orders ε M xs))

/-- Source-faithful Algorithm 9 output, with the observed finite sample
removed as required by Definition 4. -/
noncomputable def algorithmNineSetGenerator
    (family : ℕ → Set ℕ)
    (orders : ℕ → OrderedLanguage)
    (ε M : ℝ) : SetGenerator ℕ :=
  fun _t xs => algorithmNineRawCore family orders ε M xs \
    (↑(GenLimit.Generic.sequenceSample xs) : Set ℕ)

theorem algorithmNineRawCore_eq_stream
    (family : ℕ → Set ℕ)
    (orders : ℕ → OrderedLanguage)
    (ε M : ℝ) (stream : GenLimit.Generic.Stream ℕ) (t : ℕ) :
    algorithmNineRawCore family orders ε M
        (fun i : Fin t => stream i) =
      finiteCommonCore
        (indexedLanguages family
          (algorithmNineIndices family orders ((1 - ε) / M)
            (fun i => algorithmNinePriorityTrace
              stream family orders ε M i t) t)) := by
  unfold algorithmNineRawCore
  rw [algorithmNineHistoryIndices_eq_stream]

theorem algorithmNineRawCore_infinite
    (family : ℕ → Set ℕ)
    (hfamily : ∀ i, (family i).Infinite)
    (orders : ℕ → OrderedLanguage)
    (ε M : ℝ) (hε1 : ε < 1) (hM : 0 < M)
    {t : ℕ} (xs : Fin t → ℕ) :
    (algorithmNineRawCore family orders ε M xs).Infinite := by
  classical
  let selected := algorithmNineHistoryIndices family orders ε M xs
  by_cases hempty : selected = ∅
  · have huniv : (Set.univ : Set ℕ).Infinite :=
      (hfamily 0).mono (Set.subset_univ _)
    simpa [algorithmNineRawCore, selected, hempty, indexedLanguages] using
      huniv
  · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hdense := algorithmNineIndices_dense family orders
      ((1 - ε) / M)
      (algorithmNineHistoryScore family orders ε M xs) t i
      (show i ∈ algorithmNineIndices family orders ((1 - ε) / M)
          (algorithmNineHistoryScore family orders ε M xs) t by
        exact hi)
    have hcpos : 0 < (1 - ε) / M :=
      div_pos (sub_pos.mpr hε1) hM
    by_contra hnot
    have hfinite :
        (algorithmNineRawCore family orders ε M xs).Finite :=
      Set.not_infinite.mp hnot
    have hzero := (orders i).lowerDensity_eq_zero_of_finite hfinite
    unfold algorithmNineRawCore algorithmNineHistoryIndices at hzero
    rw [hzero] at hdense
    linarith

theorem algorithmNineSetGenerator_infinite
    (family : ℕ → Set ℕ)
    (hfamily : ∀ i, (family i).Infinite)
    (orders : ℕ → OrderedLanguage)
    (ε M : ℝ) (hε1 : ε < 1) (hM : 0 < M) :
    IsInfiniteSetGenerator
      (algorithmNineSetGenerator family orders ε M) := by
  intro t xs
  exact (algorithmNineRawCore_infinite
    family hfamily orders ε M hε1 hM xs).diff
      (GenLimit.Generic.sequenceSample xs).finite_toSet

/-- Theorem 7.8 for an explicitly indexed countable family.  The result
includes the literal finite-history generator, global infinite outputs,
eventual Definition 4 correctness, and the eventual `(1 - ε) / M`
set-density guarantee. -/
theorem theorem_7_8_algorithmNine
    (family : ℕ → Set ℕ)
    (hfamily : ∀ i, (family i).Infinite)
    (orders : ℕ → OrderedLanguage)
    (hcarrier : ∀ i, (orders i).carrier = family i)
    (ε M : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hM : 0 < M)
    (target : ℕ) (stream : GenLimit.Generic.Stream ℕ)
    (hinjective : Function.Injective stream)
    (hnoise : VanishingNoise stream (family target))
    (hbounded : BoundedDisplacement
      (orders target) stream (orders target).carrier M) :
    GeneratesInfiniteSetInLimitOn
        (algorithmNineSetGenerator family orders ε M)
        (family target) stream ∧
      ∃ T, ∀ t, T ≤ t →
        (1 - ε) / M ≤
          (orders target).lowerDensity
            (setOutput
              (algorithmNineSetGenerator family orders ε M) stream t) := by
  classical
  let trace := algorithmNinePriorityTrace stream family orders ε M
  obtain ⟨p, htargetStable⟩ :=
    algorithmNine_target_has_boundedPriority
      stream family orders ε M hε0 hM target hnoise hbounded
  have hstableDense : ∀ i, i ∈ boundedPriorityIndices trace p →
      (1 - ε) / M ≤ (orders i).lowerDensity
        (finiteCommonCore
          (boundedPriorityLanguages family trace p)) := by
    intro i hi
    exact algorithmNineStableCore_lowerDensity
      stream hinjective family orders hcarrier ε M hε0.le hM p hi
  obtain ⟨T, hT⟩ := algorithmNine_eventually_selects_stable_class
    stream family orders ε M ((1 - ε) / M) p hstableDense
  have hinfinite := algorithmNineSetGenerator_infinite
    family hfamily orders ε M hε1 hM
  have heventual : ∀ t, T ≤ t →
      SetCorrectAt
          (algorithmNineSetGenerator family orders ε M)
          (family target) stream t ∧
        (1 - ε) / M ≤
          (orders target).lowerDensity
            (setOutput
              (algorithmNineSetGenerator family orders ε M) stream t) := by
    intro t ht
    let selected := algorithmNineIndices family orders ((1 - ε) / M)
      (fun i => trace i t) t
    have htargetSelected : target ∈ selected :=
      hT t ht htargetStable
    have hraw :
        algorithmNineRawCore family orders ε M
            (fun i : Fin t => stream i) =
          finiteCommonCore (indexedLanguages family selected) := by
      simpa [selected, trace] using algorithmNineRawCore_eq_stream
        family orders ε M stream t
    have hrawSubset :
        algorithmNineRawCore family orders ε M
            (fun i : Fin t => stream i) ⊆ family target := by
      rw [hraw]
      exact finiteCommonCore_subset_of_mem
        (Finset.mem_image.mpr ⟨target, htargetSelected, rfl⟩)
    have hdenseRaw :
        (1 - ε) / M ≤
          (orders target).lowerDensity
            (algorithmNineRawCore family orders ε M
              (fun i : Fin t => stream i)) := by
      rw [hraw]
      exact algorithmNineIndices_dense family orders
        ((1 - ε) / M) (fun i => trace i t) t
        target htargetSelected
    constructor
    · constructor
      · intro x hx
        exact hrawSubset hx.1
      · change Disjoint
          (algorithmNineRawCore family orders ε M
              (fun i : Fin t => stream i) \
            (↑(GenLimit.Generic.sequenceSample
              (fun i : Fin t => stream i)) : Set ℕ))
          (↑(GenLimit.Generic.sample stream t) : Set ℕ)
        rw [← GenLimit.Generic.sequenceSample_prefix stream t]
        exact Set.disjoint_sdiff_left
    · change (1 - ε) / M ≤
        (orders target).lowerDensity
          (algorithmNineRawCore family orders ε M
            (fun i : Fin t => stream i) \
              (↑(GenLimit.Generic.sequenceSample
                (fun i : Fin t => stream i)) : Set ℕ))
      rw [(orders target).lowerDensity_diff_finite _
        (GenLimit.Generic.sequenceSample
          (fun i : Fin t => stream i)).finite_toSet]
      exact hdenseRaw
  refine ⟨⟨hinfinite, ⟨T, fun t ht => (heventual t ht).1⟩⟩, ?_⟩
  exact ⟨T, fun t ht => (heventual t ht).2⟩

end GenLimit.InfiniteContamination
