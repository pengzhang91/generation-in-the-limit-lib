import GenLimit.Paper17_InfiniteContamination.PriorityStabilization
import GenLimit.Paper17_InfiniteContamination.ConstantNoiseNecessity
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Algorithm 4: priority ordering and maximal infinite prefixes

Source: Mehrotra--Velegkas--Yu--Zhou,
*Language Generation with Infinite Contamination*,
arXiv:2511.07417v1, Algorithm 4, Lemma 5.2, and Theorems 5.1 and 5.4.

This module supplies the concrete deterministic assembly left after
`PriorityStabilization`:

* the current languages are ordered lexicographically by priority and index;
* `rankedPrefix` is the first `k` indices in that order;
* `maximalInfinitePrefixSize` implements Algorithm 4's largest prefix with
  infinite common intersection;
* after Lemma 4.1 stabilizes a cutoff class, that whole class lies in the
  selected maximal prefix; and
* the geometric thresholds used in Theorem 5.1 make the stable common core
  infinite.

The resulting recursive finite-history generator proves all of Theorem 5.1.
With uniform thresholds, the same construction proves Theorem 5.4's
sufficiency direction and, together with the existing necessity theorem, its
full characterization for an explicitly enumerated countable collection.

The source's proof prints the final common-core containment in the wrong
direction.  The endgame here uses the corrected direction already proved in
`PriorityStabilization`: an intersection containing the target language is a
subset of that target.
-/

namespace GenLimit.InfiniteContamination

open scoped BigOperators

/-! ## Lexicographic priority ranks -/

/-- Strict lexicographic order by current priority, tie-breaking by index. -/
def PriorityBefore (score : ℕ → ℕ) (i j : ℕ) : Prop :=
  score i < score j ∨
    score i = score j ∧ i < j

theorem priorityBefore_irrefl
    (score : ℕ → ℕ) (i : ℕ) :
    ¬ PriorityBefore score i i := by
  simp [PriorityBefore]

theorem priorityBefore_of_le_lt
    {score : ℕ → ℕ} {i j p : ℕ}
    (hi : score i ≤ p) (hj : p < score j) :
    PriorityBefore score i j := by
  exact Or.inl (hi.trans_lt hj)

/-- Indices among the first `n` languages ranked strictly before `i`. -/
noncomputable def priorityPredecessors
    (score : ℕ → ℕ) (n i : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range n).filter fun j =>
    PriorityBefore score j i

/-- Zero-based rank of `i` among the first `n` languages. -/
noncomputable def priorityRank
    (score : ℕ → ℕ) (n i : ℕ) : ℕ :=
  (priorityPredecessors score n i).card

/-- The first `k` of the first `n` language indices in increasing priority,
with ties broken by index. -/
noncomputable def rankedPrefix
    (score : ℕ → ℕ) (n k : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range n).filter fun i =>
    priorityRank score n i < k

theorem rankedPrefix_subset_range
    (score : ℕ → ℕ) (n k : ℕ) :
    rankedPrefix score n k ⊆ Finset.range n := by
  intro i hi
  exact (Finset.mem_filter.mp hi).1

theorem rankedPrefix_mono
    (score : ℕ → ℕ) (n : ℕ) {k l : ℕ}
    (hkl : k ≤ l) :
    rankedPrefix score n k ⊆ rankedPrefix score n l := by
  intro i hi
  exact Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp hi).1,
      (Finset.mem_filter.mp hi).2.trans_le hkl⟩

/-- Once a finite class has priority at most `p` and every other current
index has priority above `p`, it is literally the corresponding ranked
prefix.  This is the concrete reordering step between Lemma 4.1 and
Lemma 5.2. -/
theorem rankedPrefix_card_eq_of_priority_separation
    (score : ℕ → ℕ) (n p : ℕ) (stable : Finset ℕ)
    (hrange : stable ⊆ Finset.range n)
    (hle : ∀ i, i ∈ stable → score i ≤ p)
    (hgt : ∀ i, i ∈ Finset.range n → i ∉ stable →
      p < score i) :
    rankedPrefix score n stable.card = stable := by
  classical
  ext i
  constructor
  · intro hi
    have hirange : i ∈ Finset.range n :=
      (Finset.mem_filter.mp hi).1
    by_contra hinot
    have hstablePred :
        stable ⊆ priorityPredecessors score n i := by
      intro j hj
      exact Finset.mem_filter.mpr
        ⟨hrange hj,
          priorityBefore_of_le_lt (hle j hj)
            (hgt i hirange hinot)⟩
    have hcard :
        stable.card ≤ (priorityPredecessors score n i).card :=
      Finset.card_le_card hstablePred
    exact (Nat.not_lt_of_ge hcard) (Finset.mem_filter.mp hi).2
  · intro hi
    have hpredSub :
        priorityPredecessors score n i ⊆ stable := by
      intro j hj
      have hjrange : j ∈ Finset.range n :=
        (Finset.mem_filter.mp hj).1
      by_contra hjnot
      have hpi := hle i hi
      have hpj := hgt j hjrange hjnot
      rcases (Finset.mem_filter.mp hj).2 with hlt | ⟨heq, hij⟩
      · exact (Nat.lt_asymm hlt (hpi.trans_lt hpj)).elim
      · exact (not_lt_of_ge (heq.le.trans hpi)) hpj
    have hinotPred :
        i ∉ priorityPredecessors score n i := by
      simp [priorityPredecessors, priorityBefore_irrefl]
    have hins :
        insert i (priorityPredecessors score n i) ⊆ stable := by
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hi
      · exact hpredSub hj
    have hcard :
        (insert i (priorityPredecessors score n i)).card ≤
          stable.card :=
      Finset.card_le_card hins
    rw [Finset.card_insert_of_notMem hinotPred] at hcard
    exact Finset.mem_filter.mpr
      ⟨hrange hi, by
        change (priorityPredecessors score n i).card < stable.card
        omega⟩

/-! ## Algorithm 4's maximal infinite prefix -/

/-- The largest `k ≤ n` for which the first `k` current languages have an
infinite common intersection.  `Nat.findGreatest` returns zero if no such
prefix exists; correctness is only used once a known infinite prefix has
entered the current window. -/
noncomputable def maximalInfinitePrefixSize
    (family : ℕ → GenLimit.Generic.Language α)
    (score : ℕ → ℕ) (n : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest
    (fun k =>
      (finiteCommonCore
        (indexedLanguages family
          (rankedPrefix score n k))).Infinite)
    n

theorem maximalInfinitePrefixSize_le
    (family : ℕ → GenLimit.Generic.Language α)
    (score : ℕ → ℕ) (n : ℕ) :
    maximalInfinitePrefixSize family score n ≤ n := by
  classical
  exact Nat.findGreatest_le n

theorem le_maximalInfinitePrefixSize
    (family : ℕ → GenLimit.Generic.Language α)
    (score : ℕ → ℕ) {n k : ℕ}
    (hkn : k ≤ n)
    (hinfinite :
      (finiteCommonCore
        (indexedLanguages family
          (rankedPrefix score n k))).Infinite) :
    k ≤ maximalInfinitePrefixSize family score n := by
  classical
  exact Nat.le_findGreatest hkn hinfinite

theorem maximalInfinitePrefix_infinite_of_candidate
    (family : ℕ → GenLimit.Generic.Language α)
    (score : ℕ → ℕ) {n k : ℕ}
    (hkn : k ≤ n)
    (hinfinite :
      (finiteCommonCore
        (indexedLanguages family
          (rankedPrefix score n k))).Infinite) :
    (finiteCommonCore
      (indexedLanguages family
        (rankedPrefix score n
          (maximalInfinitePrefixSize family score n)))).Infinite := by
  classical
  simpa [maximalInfinitePrefixSize] using
    (Nat.findGreatest_spec
      (P := fun j =>
        (finiteCommonCore
          (indexedLanguages family
            (rankedPrefix score n j))).Infinite)
      hkn hinfinite)

/-- The actual finite language-index set selected by Algorithm 4. -/
noncomputable def algorithmFourIndices
    (family : ℕ → GenLimit.Generic.Language α)
    (score : ℕ → ℕ) (n : ℕ) : Finset ℕ :=
  rankedPrefix score n
    (maximalInfinitePrefixSize family score n)

/-- Lemma 5.2's stopping-rule argument: every known infinite prefix is
contained in Algorithm 4's maximal infinite prefix. -/
theorem rankedPrefix_subset_algorithmFourIndices
    (family : ℕ → GenLimit.Generic.Language α)
    (score : ℕ → ℕ) {n k : ℕ}
    (hkn : k ≤ n)
    (hinfinite :
      (finiteCommonCore
        (indexedLanguages family
          (rankedPrefix score n k))).Infinite) :
    rankedPrefix score n k ⊆
      algorithmFourIndices family score n := by
  exact rankedPrefix_mono score n
    (le_maximalInfinitePrefixSize family score hkn hinfinite)

/-! ## Geometric thresholds and the stable common core -/

/-- Zero-based form of the source thresholds
`cᵢ = 1 / 2^(i+1)`: source index `i=1` corresponds to Lean index `0`. -/
noncomputable def geometricThreshold (i : ℕ) : ℝ :=
  (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ i

theorem geometricThreshold_pos (i : ℕ) :
    0 < geometricThreshold i := by
  unfold geometricThreshold
  positivity

theorem geometricThreshold_eq (i : ℕ) :
    geometricThreshold i =
      1 / (2 : ℝ) ^ (i + 2) := by
  rw [geometricThreshold, pow_add]
  norm_num [div_pow]

theorem sum_geometricThreshold_range_le_half (n : ℕ) :
    ∑ i ∈ Finset.range n, geometricThreshold i ≤ (1 / 2 : ℝ) := by
  simp_rw [geometricThreshold]
  rw [← Finset.mul_sum]
  rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
  have hpow : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
  norm_num [div_eq_mul_inv]
  nlinarith

theorem sum_geometricThreshold_le_half
    {S : Finset ℕ} {n : ℕ}
    (hS : S ⊆ Finset.range n) :
    ∑ i ∈ S, geometricThreshold i ≤ (1 / 2 : ℝ) := by
  calc
    ∑ i ∈ S, geometricThreshold i
        ≤ ∑ i ∈ Finset.range n, geometricThreshold i := by
          exact Finset.sum_le_sum_of_subset_of_nonneg hS
            (fun i _hi _hinot => (geometricThreshold_pos i).le)
    _ ≤ (1 / 2 : ℝ) :=
      sum_geometricThreshold_range_le_half n

/-! ## Theorem 5.1's finite geometric union bound -/

@[simp] theorem finiteCommonCore_indexedLanguages_empty
    (family : ℕ → GenLimit.Generic.Language α) :
    finiteCommonCore
        (indexedLanguages family (∅ : Finset ℕ)) =
      Set.univ := by
  classical
  simp [indexedLanguages]

@[simp] theorem finiteCommonCore_indexedLanguages_insert
    (family : ℕ → GenLimit.Generic.Language α)
    (i : ℕ) (S : Finset ℕ) :
    finiteCommonCore
        (indexedLanguages family (insert i S)) =
      family i ∩
        finiteCommonCore (indexedLanguages family S) := by
  classical
  simp [indexedLanguages]

/-- The empirical union bound indexed by languages rather than by distinct
language sets.  Repeated languages merely duplicate a nonnegative summand,
so the indexed form is the one needed for the source's geometric thresholds.
-/
theorem empiricalNoiseRate_indexedCommonCore_le_sum
    (stream : GenLimit.Generic.Stream α)
    (family : ℕ → GenLimit.Generic.Language α)
    (S : Finset ℕ) (n : ℕ) :
    empiricalNoiseRate stream
        (finiteCommonCore (indexedLanguages family S)) n ≤
      ∑ i ∈ S, empiricalNoiseRate stream (family i) n := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp [indexedLanguages, empiricalNoiseRate, noiseCount]
  | @insert i S hi ih =>
      rw [finiteCommonCore_indexedLanguages_insert]
      calc
        empiricalNoiseRate stream
              (family i ∩
                finiteCommonCore (indexedLanguages family S)) n
            ≤ empiricalNoiseRate stream (family i) n +
                empiricalNoiseRate stream
                  (finiteCommonCore
                    (indexedLanguages family S)) n :=
          empiricalNoiseRate_inter_le_add stream _ _ n
        _ ≤ empiricalNoiseRate stream (family i) n +
              ∑ j ∈ S,
                empiricalNoiseRate stream (family j) n :=
          add_le_add_left ih _
        _ = ∑ j ∈ insert i S,
              empiricalNoiseRate stream (family j) n := by
          simp [hi]

/-- Membership in a bounded Algorithm 4 priority class forces every
sufficiently late empirical rate below its assigned threshold. -/
theorem empiricalNoiseRate_le_threshold_of_boundedPriority
    (stream : GenLimit.Generic.Stream α)
    (family : ℕ → GenLimit.Generic.Language α)
    (threshold : ℕ → ℝ) {p i n : ℕ}
    (hi :
      i ∈ boundedPriorityIndices
        (thresholdPriorityTrace stream family threshold) p)
    (hpn : p < n + 1) :
    empiricalNoiseRate stream (family i) n ≤ threshold i := by
  by_contra hnot
  have hviolation :
      threshold i <
        empiricalNoiseRate stream (family i) n :=
    lt_of_not_ge hnot
  have hbound :=
    (mem_boundedPriorityIndices.mp hi).2 n
  unfold thresholdPriorityTrace at hbound
  rw [thresholdPenalty_eq_time_succ_of_violation
    _ _ hviolation] at hbound
  omega

/-- At every time at least the cutoff, the empirical noise rate of the
stable common core is at most one half.  This is the exact finite geometric
count in the proof of Theorem 5.1. -/
theorem geometricStableCore_noiseRate_le_half
    (stream : GenLimit.Generic.Stream α)
    (family : ℕ → GenLimit.Generic.Language α)
    (p n : ℕ) (hpn : p ≤ n) :
    empiricalNoiseRate stream
        (finiteCommonCore
          (boundedPriorityLanguages family
            (thresholdPriorityTrace stream family geometricThreshold)
            p)) n ≤
      (1 / 2 : ℝ) := by
  classical
  let stable :=
    boundedPriorityIndices
      (thresholdPriorityTrace stream family geometricThreshold) p
  have hlanguages :
      boundedPriorityLanguages family
          (thresholdPriorityTrace stream family geometricThreshold) p =
        indexedLanguages family stable := by
    rfl
  rw [hlanguages]
  calc
    empiricalNoiseRate stream
          (finiteCommonCore (indexedLanguages family stable)) n
        ≤ ∑ i ∈ stable,
            empiricalNoiseRate stream (family i) n :=
      empiricalNoiseRate_indexedCommonCore_le_sum
        stream family stable n
    _ ≤ ∑ i ∈ stable, geometricThreshold i := by
      exact Finset.sum_le_sum fun i hi =>
        empiricalNoiseRate_le_threshold_of_boundedPriority
          stream family geometricThreshold hi (by omega)
    _ ≤ (1 / 2 : ℝ) := by
      apply sum_geometricThreshold_le_half
      exact boundedPriorityIndices_subset_range
        (thresholdPriorityTrace stream family geometricThreshold) p

/-- A repetition-free stream cannot have eventual empirical noise rate at
most one half relative to a finite language. -/
theorem infinite_of_injective_eventually_noiseRate_le_half
    {stream : GenLimit.Generic.Stream α}
    (hinjective : Function.Injective stream)
    {L : GenLimit.Generic.Language α}
    (hhalf :
      ∃ N, ∀ n, N ≤ n →
        empiricalNoiseRate stream L n ≤ (1 / 2 : ℝ)) :
    L.Infinite := by
  classical
  by_contra hnot
  have hfinite : L.Finite := Set.not_infinite.mp hnot
  obtain ⟨N, hN⟩ := hhalf
  let B := hfinite.toFinset.card
  let n := max N (2 * B + 1)
  have hnN : N ≤ n := Nat.le_max_left _ _
  have hnB : 2 * B + 1 ≤ n := Nat.le_max_right _ _
  have hnpos : 0 < n := by omega
  have hrate := hN n hnN
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hnoiseR :
      2 * (noiseCount stream L n : ℝ) ≤ (n : ℝ) := by
    simp only [empiricalNoiseRate, Nat.ne_of_gt hnpos, if_false] at hrate
    rw [div_le_iff₀ hnR] at hrate
    nlinarith
  have hpartitionR :
      (trueCount stream L n : ℝ) +
        (noiseCount stream L n : ℝ) = (n : ℝ) := by
    exact_mod_cast trueCount_add_noiseCount stream L n
  have htrueB : B < trueCount stream L n := by
    have hnBR : (2 * B + 1 : ℕ) ≤ n := hnB
    have hnBR' : (2 * (B : ℝ) + 1 : ℝ) ≤ n := by
      exact_mod_cast hnBR
    have : (B : ℝ) < trueCount stream L n := by
      nlinarith
    exact_mod_cast this
  exact (Nat.not_lt_of_ge
    (trueCount_le_finite_card hinjective hfinite n)) htrueB

/-- The geometric stable prefix in Theorem 5.1 has infinite intersection.
Unlike `theorem_5_1_finite_prefix_core`, this theorem does not assume each
stable language has vanishing noise: its indexed threshold may be positive,
and summability of all thresholds is the essential argument. -/
theorem theorem_5_1_geometric_stable_core_infinite
    (stream : GenLimit.Generic.Stream α)
    (family : ℕ → GenLimit.Generic.Language α)
    (hinjective : Function.Injective stream)
    (p : ℕ) :
    (finiteCommonCore
      (boundedPriorityLanguages family
        (thresholdPriorityTrace stream family geometricThreshold)
        p)).Infinite := by
  apply infinite_of_injective_eventually_noiseRate_le_half hinjective
  exact ⟨p, fun n hn =>
    geometricStableCore_noiseRate_le_half
      stream family p n hn⟩

/-! ## Constant-noise support for Theorem 5.4 -/

/-- An eventually satisfied threshold gives the target a bounded Algorithm 4
priority, without requiring convergence of the empirical rate. -/
theorem exists_boundedPriorityClass_of_eventually_le
    (stream : GenLimit.Generic.Stream α)
    (family : ℕ → GenLimit.Generic.Language α)
    (threshold : ℕ → ℝ) (target : ℕ)
    (heventually :
      ∃ T, ∀ n, T ≤ n →
        empiricalNoiseRate stream (family target) n ≤
          threshold target) :
    ∃ p,
      target ∈ boundedPriorityIndices
        (thresholdPriorityTrace stream family threshold) p := by
  obtain ⟨T, hT⟩ := heventually
  have hconstant :
      ∀ n, T ≤ n →
        thresholdPriorityTrace stream family threshold target n =
          thresholdPriorityTrace stream family threshold target T := by
    intro n hn
    unfold thresholdPriorityTrace
    rw [thresholdPenalty_eq_of_eventually_le
      (empiricalNoiseRate stream (family target))
      (threshold target) hT hn]
  let p :=
    thresholdPriorityTrace stream family threshold target T
  refine ⟨p, mem_boundedPriorityIndices.mpr ⟨?_, ?_⟩⟩
  · exact thresholdPriorityTrace_index_le
      stream family threshold target T
  · intro n
    rcases le_total n T with hnT | hTn
    · exact thresholdPriorityTrace_mono
        stream family threshold target hnT
    · exact (hconstant n hTn).le

/-- If an injective stream has eventual noise rate strictly below one, it
contains infinitely many displayed elements of the language.  Thus the
paper's arbitrary-omission side condition follows automatically for every
stable candidate in Theorem 5.4. -/
theorem arbitraryOmissions_of_injective_constantNoise_lt_one
    {stream : GenLimit.Generic.Stream α}
    {L : GenLimit.Generic.Language α} {c : ℝ}
    (hinjective : Function.Injective stream)
    (hc : c < 1)
    (hnoise : ConstantNoise stream L c) :
    ArbitraryOmissions stream L := by
  classical
  by_contra hnot
  have hfinite :
      (Set.range stream ∩ L).Finite :=
    Set.not_infinite.mp hnot
  obtain ⟨N, hN⟩ := hnoise
  let B := hfinite.toFinset.card
  have hden : 0 < 1 - c := sub_pos.mpr hc
  obtain ⟨m : ℕ, hm⟩ :=
    exists_nat_gt ((B : ℝ) / (1 - c))
  let n := max N m
  have hnN : N ≤ n := Nat.le_max_left _ _
  have hmn : m ≤ n := Nat.le_max_right _ _
  have hratioNonneg : 0 ≤ (B : ℝ) / (1 - c) :=
    div_nonneg (Nat.cast_nonneg _) hden.le
  have hmpos : 0 < m := by
    exact_mod_cast hratioNonneg.trans_lt hm
  have hnpos : 0 < n := hmpos.trans_le hmn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hBlinear : (B : ℝ) < (1 - c) * n := by
    have hBm : (B : ℝ) < (1 - c) * m := by
      have := (div_lt_iff₀ hden).mp hm
      nlinarith
    have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
    nlinarith
  have hrate := hN n hnN
  have hnoiseR :
      (noiseCount stream L n : ℝ) ≤ c * n := by
    simp only [empiricalNoiseRate, Nat.ne_of_gt hnpos, if_false] at hrate
    rwa [div_le_iff₀ hnR] at hrate
  have hpartitionR :
      (trueCount stream L n : ℝ) +
        (noiseCount stream L n : ℝ) = (n : ℝ) := by
    exact_mod_cast trueCount_add_noiseCount stream L n
  have htrueB : B < trueCount stream L n := by
    have : (B : ℝ) < trueCount stream L n := by
      nlinarith
    exact_mod_cast this
  have htrueEq :
      trueCount stream L n =
        trueCount stream (Set.range stream ∩ L) n := by
    unfold trueCount
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Set.mem_inter_iff]
    constructor
    · rintro ⟨hi, hiL⟩
      exact ⟨hi, ⟨⟨i, rfl⟩, hiL⟩⟩
    · rintro ⟨hi, _hirange, hiL⟩
      exact ⟨hi, hiL⟩
  have hbound :
      trueCount stream (Set.range stream ∩ L) n ≤ B := by
    simpa [B] using
      trueCount_le_finite_card hinjective hfinite n
  rw [htrueEq] at htrueB
  exact (Nat.not_lt_of_ge hbound) htrueB

/-! ## Lemma 5.2 assembled with the concrete stopping rule -/

/-- Once Lemma 4.1 separates the stable cutoff class, Algorithm 4's maximal
infinite prefix contains the entire stable class and itself has infinite
intersection. -/
theorem lemma_5_2_eventually_selects_stable_class
    (family : ℕ → GenLimit.Generic.Language α)
    (trace : ℕ → ℕ → ℕ)
    (hmono : ∀ i, Monotone (trace i))
    (hlower : ∀ i n, i ≤ trace i n)
    (p : ℕ)
    (hstableInfinite :
      (finiteCommonCore
        (boundedPriorityLanguages family trace p)).Infinite) :
    ∃ T, ∀ n, T ≤ n →
      boundedPriorityIndices trace p ⊆
        algorithmFourIndices family (fun i => trace i n) n ∧
      (finiteCommonCore
        (indexedLanguages family
          (algorithmFourIndices family
            (fun i => trace i n) n))).Infinite := by
  classical
  obtain ⟨N, hpN, hN⟩ :=
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
      ((mem_boundedPriorityIndices.mp hi).1.trans_lt
        (by omega))
  have hreorder :
      rankedPrefix (fun i => trace i n) n stable.card = stable := by
    apply rankedPrefix_card_eq_of_priority_separation
      (fun i => trace i n) n p stable hstableRange
    · exact hsep.1
    · intro i _hi hinot
      exact hsep.2.1 i hinot
  have hcard : stable.card ≤ n :=
    by simpa using Finset.card_le_card hstableRange
  have hprefixInfinite :
      (finiteCommonCore
        (indexedLanguages family
          (rankedPrefix (fun i => trace i n) n stable.card))).Infinite := by
    rw [hreorder]
    simpa [stable, boundedPriorityLanguages, indexedLanguages] using
      hstableInfinite
  have hcontains :
      stable ⊆
        algorithmFourIndices family (fun i => trace i n) n := by
    rw [← hreorder]
    exact rankedPrefix_subset_algorithmFourIndices
      family (fun i => trace i n) hcard hprefixInfinite
  refine ⟨hcontains, ?_⟩
  exact maximalInfinitePrefix_infinite_of_candidate
    family (fun i => trace i n) hcard hprefixInfinite

/-- Lemma 5.2's corrected target-validity endgame for the concrete selected
prefix. -/
theorem lemma_5_2_eventually_selected_core_subset_target
    (family : ℕ → GenLimit.Generic.Language α)
    (trace : ℕ → ℕ → ℕ)
    (hmono : ∀ i, Monotone (trace i))
    (hlower : ∀ i n, i ≤ trace i n)
    (p target : ℕ)
    (htarget : target ∈ boundedPriorityIndices trace p)
    (hstableInfinite :
      (finiteCommonCore
        (boundedPriorityLanguages family trace p)).Infinite) :
    ∃ T, ∀ n, T ≤ n →
      finiteCommonCore
          (indexedLanguages family
            (algorithmFourIndices family
              (fun i => trace i n) n)) ⊆
        family target := by
  obtain ⟨T, hT⟩ :=
    lemma_5_2_eventually_selects_stable_class
      family trace hmono hlower p hstableInfinite
  refine ⟨T, ?_⟩
  intro n hn
  exact corollary_4_2_selected_core_subset_target
    family trace p target
    (algorithmFourIndices family (fun i => trace i n) n)
    (hT n hn).1 htarget

/-! ## A literal finite-history generator -/

/-- Extend a finite history by a fixed fallback value.  Quantities computed
from prefixes of length at most `t` are independent of the fallback. -/
def prefixCompletion
    (fallback : α) {t : ℕ} (xs : Fin t → α) :
    GenLimit.Generic.Stream α :=
  fun n => if h : n < t then xs ⟨n, h⟩ else fallback

@[simp] theorem prefixCompletion_eq
    (fallback : α) {t : ℕ} (xs : Fin t → α)
    {n : ℕ} (hn : n < t) :
    prefixCompletion fallback xs n = xs ⟨n, hn⟩ := by
  simp [prefixCompletion, hn]

theorem noiseCount_eq_of_eq_on_prefix
    {stream₁ stream₂ : GenLimit.Generic.Stream α}
    (L : GenLimit.Generic.Language α) {n : ℕ}
    (h : ∀ i, i < n → stream₁ i = stream₂ i) :
    noiseCount stream₁ L n = noiseCount stream₂ L n := by
  classical
  unfold noiseCount
  congr 1
  apply Finset.filter_congr
  intro i hi
  rw [h i (Finset.mem_range.mp hi)]

theorem empiricalNoiseRate_eq_of_eq_on_prefix
    {stream₁ stream₂ : GenLimit.Generic.Stream α}
    (L : GenLimit.Generic.Language α) {n : ℕ}
    (h : ∀ i, i < n → stream₁ i = stream₂ i) :
    empiricalNoiseRate stream₁ L n =
      empiricalNoiseRate stream₂ L n := by
  unfold empiricalNoiseRate
  rw [noiseCount_eq_of_eq_on_prefix L h]

theorem thresholdPenalty_eq_of_eq_through
    {rate₁ rate₂ : ℕ → ℝ} (threshold : ℝ) {n : ℕ}
    (h : ∀ m, m ≤ n → rate₁ m = rate₂ m) :
    thresholdPenalty rate₁ threshold n =
      thresholdPenalty rate₂ threshold n := by
  classical
  have hsets :
      (Finset.range (n + 1)).filter
          (fun m => threshold < rate₁ m) =
        (Finset.range (n + 1)).filter
          (fun m => threshold < rate₂ m) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hm, hbad⟩
      exact ⟨hm, by
        rw [← h m (Nat.le_of_lt_succ hm)]
        exact hbad⟩
    · rintro ⟨hm, hbad⟩
      exact ⟨hm, by
        rw [h m (Nat.le_of_lt_succ hm)]
        exact hbad⟩
  unfold thresholdPenalty
  rw [hsets]

/-- Algorithm 4's score computed from one finite history. -/
noncomputable def algorithmFourHistoryScore
    (family : ℕ → GenLimit.Generic.Language α)
    (threshold : ℕ → ℝ) (fallback : α)
    {t : ℕ} (xs : Fin t → α) (i : ℕ) : ℕ :=
  thresholdPriorityTrace
    (prefixCompletion fallback xs) family threshold i t

/-- The finite-history score agrees exactly with the stream score on the
corresponding prefix. -/
theorem algorithmFourHistoryScore_eq_trace
    (family : ℕ → GenLimit.Generic.Language α)
    (threshold : ℕ → ℝ) (fallback : α)
    (stream : GenLimit.Generic.Stream α) (t i : ℕ) :
    algorithmFourHistoryScore family threshold fallback
        (fun j : Fin t => stream j) i =
      thresholdPriorityTrace stream family threshold i t := by
  unfold algorithmFourHistoryScore thresholdPriorityTrace
  congr 1
  apply thresholdPenalty_eq_of_eq_through
  intro m hm
  apply empiricalNoiseRate_eq_of_eq_on_prefix
  intro r hr
  simp [prefixCompletion, hr.trans_le hm]

/-- Algorithm 4's selected index prefix, computed solely from the supplied
finite history. -/
noncomputable def algorithmFourHistoryIndices
    (family : ℕ → GenLimit.Generic.Language α)
    (threshold : ℕ → ℝ) (fallback : α)
    {t : ℕ} (xs : Fin t → α) : Finset ℕ :=
  algorithmFourIndices family
    (algorithmFourHistoryScore family threshold fallback xs) t

theorem algorithmFourHistoryIndices_eq_stream
    (family : ℕ → GenLimit.Generic.Language α)
    (threshold : ℕ → ℝ) (fallback : α)
    (stream : GenLimit.Generic.Stream α) (t : ℕ) :
    algorithmFourHistoryIndices family threshold fallback
        (fun j : Fin t => stream j) =
      algorithmFourIndices family
        (fun i =>
          thresholdPriorityTrace stream family threshold i t) t := by
  have hscores :
      algorithmFourHistoryScore family threshold fallback
          (fun j : Fin t => stream j) =
        fun i =>
          thresholdPriorityTrace stream family threshold i t := by
    funext i
    exact algorithmFourHistoryScore_eq_trace
      family threshold fallback stream t i
  exact congrArg
    (fun score => algorithmFourIndices family score t) hscores

/-- Literal recursive output rule for Algorithm 4.

At time `t`, the rule chooses from the maximal infinite prefix core while
avoiding both the observed finite history and every output produced on a
strict prefix of that same history.  The fallback branch makes the definition
total for arbitrary families.  For the paper's families of infinite
languages, `algorithmFourGenerator_fresh_every_round` below shows that the
selected core is infinite and the fallback is never used at any round. -/
noncomputable def algorithmFourOutput
    (family : ℕ → GenLimit.Generic.Language α)
    (threshold : ℕ → ℝ) (fallback : α)
    (t : ℕ) (xs : Fin t → α) : α := by
  classical
  let selected :=
    algorithmFourHistoryIndices family threshold fallback xs
  let previous : Finset α :=
    Finset.univ.image fun s : Fin t =>
      algorithmFourOutput family threshold fallback s
        (fun j : Fin s =>
          xs ⟨j, j.isLt.trans s.isLt⟩)
  let forbidden :=
    GenLimit.Generic.sequenceSample xs ∪ previous
  let core :=
    finiteCommonCore (indexedLanguages family selected)
  exact if h : ∃ x, x ∈ core ∧ x ∉ forbidden then
    Classical.choose h
  else fallback
termination_by t
decreasing_by exact s.isLt

/-- Paper-level generator obtained from the recursive finite-history rule. -/
noncomputable def algorithmFourGenerator
    (family : ℕ → GenLimit.Generic.Language α)
    (threshold : ℕ → ℝ) (fallback : α) :
    GenLimit.Generic.Generator α :=
  algorithmFourOutput family threshold fallback

theorem algorithmFourOutput_spec_of_infinite
    (family : ℕ → GenLimit.Generic.Language α)
    (threshold : ℕ → ℝ) (fallback : α)
    {t : ℕ} (xs : Fin t → α)
    (hinfinite :
      (finiteCommonCore
        (indexedLanguages family
          (algorithmFourHistoryIndices
            family threshold fallback xs))).Infinite) :
    let output :=
      algorithmFourOutput family threshold fallback t xs
    output ∈
        finiteCommonCore
          (indexedLanguages family
            (algorithmFourHistoryIndices
              family threshold fallback xs)) ∧
      output ∉ GenLimit.Generic.sequenceSample xs ∧
      ∀ s : Fin t,
        output ≠
          algorithmFourOutput family threshold fallback s
            (fun j : Fin s =>
              xs ⟨j, j.isLt.trans s.isLt⟩) := by
  classical
  let selected :=
    algorithmFourHistoryIndices family threshold fallback xs
  let previous : Finset α :=
    Finset.univ.image fun s : Fin t =>
      algorithmFourOutput family threshold fallback s
        (fun j : Fin s =>
          xs ⟨j, j.isLt.trans s.isLt⟩)
  let forbidden :=
    GenLimit.Generic.sequenceSample xs ∪ previous
  let core :=
    finiteCommonCore (indexedLanguages family selected)
  have hnotSubset : ¬core ⊆ (forbidden : Set α) := by
    intro hsubset
    exact hinfinite (forbidden.finite_toSet.subset hsubset)
  obtain ⟨x, hxcore, hxfresh⟩ := Set.not_subset.mp hnotSubset
  have hex : ∃ x, x ∈ core ∧ x ∉ forbidden :=
    ⟨x, hxcore, hxfresh⟩
  have hexFull :
      ∃ x,
        x ∈
          finiteCommonCore
            (indexedLanguages family
              (algorithmFourHistoryIndices
                family threshold fallback xs)) ∧
        x ∉
          GenLimit.Generic.sequenceSample xs ∪
            (Finset.univ.image fun s : Fin t =>
              algorithmFourOutput family threshold fallback s
                (fun j : Fin s =>
                  xs ⟨j, j.isLt.trans s.isLt⟩)) := by
    simpa [core, forbidden, previous, selected] using hex
  have hchosen := Classical.choose_spec hexFull
  have hout :
      algorithmFourOutput family threshold fallback t xs =
        Classical.choose hexFull := by
    rw [algorithmFourOutput]
    exact dif_pos hexFull
  rw [hout]
  refine ⟨hchosen.1, ?_, ?_⟩
  · intro hsample
    exact hchosen.2
      (Finset.mem_union_left _ hsample)
  · intro s heq
    exact hchosen.2
      (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨s, Finset.mem_univ s, heq.symm⟩))

/-- Definition 3's global element-generator condition for the concrete
Algorithm 4: on every stream and at every round, the output avoids both the
entire observed prefix and all earlier outputs.

The source requires this before its separate eventual target-validity
condition.  It holds at every round, not merely after priority stabilization:
the empty ranked prefix has common core `univ`, which is infinite because the
paper assumes every language (in particular `family 0`) is infinite.
-/
theorem algorithmFourGenerator_fresh_every_round
    (family : ℕ → GenLimit.Generic.Language α)
    (hfamily : ∀ i, (family i).Infinite)
    (threshold : ℕ → ℝ) (fallback : α) :
    ∀ stream t,
      GenLimit.Generic.output
          (algorithmFourGenerator family threshold fallback) stream t ∉
        GenLimit.Generic.sample stream t ∧
      GenLimit.Generic.output
          (algorithmFourGenerator family threshold fallback) stream t ∉
        generatedBefore
          (algorithmFourGenerator family threshold fallback) stream t := by
  intro stream t
  let score : ℕ → ℕ :=
    fun i => thresholdPriorityTrace stream family threshold i t
  have huniv : (Set.univ : Set α).Infinite :=
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
  let xs : Fin t → α := fun j => stream j
  have hindices :=
    algorithmFourHistoryIndices_eq_stream
      family threshold fallback stream t
  have hhistoryInfinite :
      (finiteCommonCore
        (indexedLanguages family
          (algorithmFourHistoryIndices
            family threshold fallback xs))).Infinite := by
    rw [hindices]
    simpa [score] using hselected
  have hspec :=
    algorithmFourOutput_spec_of_infinite
      family threshold fallback xs hhistoryInfinite
  change
    algorithmFourOutput family threshold fallback t xs ∉
        GenLimit.Generic.sample stream t ∧
      algorithmFourOutput family threshold fallback t xs ∉
        generatedBefore
          (algorithmFourGenerator family threshold fallback)
          stream t
  refine ⟨?_, ?_⟩
  · rw [← GenLimit.Generic.sequenceSample_prefix stream t]
    exact hspec.2.1
  · rw [mem_generatedBefore_iff]
    rintro ⟨s, hst, heq⟩
    let sf : Fin t := ⟨s, hst⟩
    have hne := hspec.2.2 sf
    apply hne
    change
      algorithmFourOutput family threshold fallback t xs =
        algorithmFourOutput family threshold fallback s
          (fun j : Fin s => stream j)
    simpa [xs, sf, algorithmFourGenerator] using heq.symm

/-- If Algorithm 4's selected core is infinite and target-valid at one
stream time, its literal recursive output satisfies all three freshness
requirements at that time. -/
theorem algorithmFourGenerator_freshAt_of_selected
    (family : ℕ → GenLimit.Generic.Language α)
    (threshold : ℕ → ℝ) (fallback : α)
    (target : GenLimit.Generic.Language α)
    (stream : GenLimit.Generic.Stream α) (t : ℕ)
    (hinfinite :
      (finiteCommonCore
        (indexedLanguages family
          (algorithmFourIndices family
            (fun i =>
              thresholdPriorityTrace
                stream family threshold i t) t))).Infinite)
    (hvalid :
      finiteCommonCore
          (indexedLanguages family
            (algorithmFourIndices family
              (fun i =>
                thresholdPriorityTrace
                  stream family threshold i t) t)) ⊆
        target) :
    FreshElementCorrectAt
      (algorithmFourGenerator family threshold fallback)
      target stream t := by
  let xs : Fin t → α := fun j => stream j
  have hindices :=
    algorithmFourHistoryIndices_eq_stream
      family threshold fallback stream t
  have hhistoryInfinite :
      (finiteCommonCore
        (indexedLanguages family
          (algorithmFourHistoryIndices
            family threshold fallback xs))).Infinite := by
    rw [hindices]
    exact hinfinite
  have hspec :=
    algorithmFourOutput_spec_of_infinite
      family threshold fallback xs hhistoryInfinite
  change
    algorithmFourOutput family threshold fallback t xs ∈ target ∧
      algorithmFourOutput family threshold fallback t xs ∉
        GenLimit.Generic.sample stream t ∧
      algorithmFourOutput family threshold fallback t xs ∉
        generatedBefore
          (algorithmFourGenerator family threshold fallback)
          stream t
  refine ⟨?_, ?_, ?_⟩
  · apply hvalid
    rw [← hindices]
    exact hspec.1
  · rw [← GenLimit.Generic.sequenceSample_prefix stream t]
    exact hspec.2.1
  · rw [mem_generatedBefore_iff]
    rintro ⟨s, hst, heq⟩
    let sf : Fin t := ⟨s, hst⟩
    have hne := hspec.2.2 sf
    apply hne
    change
      algorithmFourOutput family threshold fallback t xs =
        algorithmFourOutput family threshold fallback s
          (fun j : Fin s => stream j)
    simpa [xs, sf, algorithmFourGenerator] using heq.symm

/-! ## Full deterministic Theorem 5.1 -/

/-- Theorem 5.1, with the source's Algorithm 4 fully assembled.

For every countable family of infinite languages there is one finite-history
generator that succeeds on every target under every repetition-free stream
with vanishing noise and arbitrary omissions.  The proof is deterministic;
no probability space is involved.  The separate theorem
`algorithmFourGenerator_fresh_every_round` verifies Definition 3's global
sample/output freshness condition for this same concrete generator. -/
theorem theorem_5_1_algorithmFour
    (family : ℕ → GenLimit.Generic.Language α)
    (hfamily : ∀ i, (family i).Infinite) :
    ∃ gen : GenLimit.Generic.Generator α,
      ∀ target stream,
        VanishingNoiseArbitraryOmissionEnumeration
            stream (family target) →
          GeneratesElementInLimitOn gen (family target) stream := by
  classical
  let fallback : α :=
    Classical.choose (hfamily 0).nonempty
  let gen :=
    algorithmFourGenerator family geometricThreshold fallback
  refine ⟨gen, ?_⟩
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
      (thresholdPriorityTrace
        stream family geometricThreshold)
      (thresholdPriorityTrace_mono
        stream family geometricThreshold)
      (thresholdPriorityTrace_index_le
        stream family geometricThreshold)
      p hstableInfinite
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
      (thresholdPriorityTrace
        stream family geometricThreshold)
      p target
      (algorithmFourIndices family
        (fun i =>
          thresholdPriorityTrace
            stream family geometricThreshold i t) t)
      hselected.1 htarget
  exact algorithmFourGenerator_freshAt_of_selected
    family geometricThreshold fallback
    (family target) stream t hselected.2 hvalid

/-! ## Theorem 5.4 sufficiency and characterization -/

/-- Under the constant-noise generation property, every bounded uniform-
threshold priority class has infinite common core. -/
theorem theorem_5_4_uniform_stable_core_infinite
    (C : GenLimit.Generic.LanguageClass α) (c : ℝ)
    (hc : c < 1)
    (family : ℕ → GenLimit.Generic.Language α)
    (hfamilyC : ∀ i, family i ∈ C)
    (hproperty : ConstantNoiseGenerationProperty C c)
    (stream : GenLimit.Generic.Stream α)
    (hinjective : Function.Injective stream)
    (p target : ℕ)
    (htarget :
      target ∈ boundedPriorityIndices
        (thresholdPriorityTrace stream family (fun _ => c)) p) :
    (finiteCommonCore
      (boundedPriorityLanguages family
        (thresholdPriorityTrace stream family (fun _ => c))
        p)).Infinite := by
  classical
  let stable :=
    boundedPriorityIndices
      (thresholdPriorityTrace stream family (fun _ => c)) p
  let S :=
    boundedPriorityLanguages family
      (thresholdPriorityTrace stream family (fun _ => c)) p
  have hSne : S.Nonempty := by
    refine ⟨family target, ?_⟩
    exact Finset.mem_image.mpr ⟨target, htarget, rfl⟩
  have hSC : (↑S : Set (GenLimit.Generic.Language α)) ⊆ C := by
    intro L hL
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hL
    exact hfamilyC i
  apply hproperty S hSne hSC stream
  intro L hL
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hL
  have hconstant :
      ConstantNoise stream (family i) c := by
    exact ⟨p, fun n hn =>
      empiricalNoiseRate_le_threshold_of_boundedPriority
        stream family (fun _ => c) hi (by omega)⟩
  exact
    ⟨hinjective,
      arbitraryOmissions_of_injective_constantNoise_lt_one
        hinjective hc hconstant,
      hconstant⟩

/-- Sufficiency direction of Theorem 5.4 for an explicit enumeration of the
countable collection.  The family hypotheses are the representation data
needed to turn the set-valued collection in the theorem statement into
Algorithm 4's indexed input. -/
theorem theorem_5_4_sufficiency_enumerated
    (C : GenLimit.Generic.LanguageClass α) (c : ℝ)
    (_hc0 : 0 < c) (hc1 : c < 1)
    (family : ℕ → GenLimit.Generic.Language α)
    (hfamilyInfinite : ∀ i, (family i).Infinite)
    (hfamilyC : ∀ i, family i ∈ C)
    (hcovers : ∀ L, L ∈ C → ∃ i, family i = L)
    (hproperty : ConstantNoiseGenerationProperty C c) :
    ∃ gen : GenLimit.Generic.Generator α,
      GeneratesUnderConstantNoise gen C c := by
  classical
  let fallback : α :=
    Classical.choose (hfamilyInfinite 0).nonempty
  let threshold : ℕ → ℝ := fun _ => c
  let gen :=
    algorithmFourGenerator family threshold fallback
  refine ⟨gen, ?_⟩
  intro L hLC stream hstream
  obtain ⟨target, htargetL⟩ := hcovers L hLC
  subst L
  obtain ⟨p, htarget⟩ :=
    exists_boundedPriorityClass_of_eventually_le
      stream family threshold target hstream.2.2
  have hstableInfinite :
      (finiteCommonCore
        (boundedPriorityLanguages family
          (thresholdPriorityTrace stream family threshold) p)).Infinite := by
    simpa [threshold] using
      theorem_5_4_uniform_stable_core_infinite
        C c hc1 family hfamilyC hproperty
        stream hstream.1 p target (by simpa [threshold] using htarget)
  obtain ⟨T, hT⟩ :=
    lemma_5_2_eventually_selects_stable_class
      family
      (thresholdPriorityTrace stream family threshold)
      (thresholdPriorityTrace_mono stream family threshold)
      (thresholdPriorityTrace_index_le stream family threshold)
      p hstableInfinite
  refine ⟨T, ?_⟩
  intro t ht
  have hselected := hT t ht
  have hvalid :
      finiteCommonCore
          (indexedLanguages family
            (algorithmFourIndices family
              (fun i =>
                thresholdPriorityTrace
                  stream family threshold i t) t)) ⊆
        family target :=
    corollary_4_2_selected_core_subset_target
      family
      (thresholdPriorityTrace stream family threshold)
      p target
      (algorithmFourIndices family
        (fun i =>
          thresholdPriorityTrace
            stream family threshold i t) t)
      hselected.1 htarget
  exact algorithmFourGenerator_freshAt_of_selected
    family threshold fallback
    (family target) stream t hselected.2 hvalid

/-- Full Theorem 5.4, for an explicit enumeration of a countable collection
of infinite languages. -/
theorem theorem_5_4_characterization_enumerated
    (C : GenLimit.Generic.LanguageClass α) (c : ℝ)
    (hc0 : 0 < c) (hc1 : c < 1)
    (family : ℕ → GenLimit.Generic.Language α)
    (hfamilyInfinite : ∀ i, (family i).Infinite)
    (hfamilyC : ∀ i, family i ∈ C)
    (hcovers : ∀ L, L ∈ C → ∃ i, family i = L) :
    (∃ gen : GenLimit.Generic.Generator α,
        GeneratesUnderConstantNoise gen C c) ↔
      ConstantNoiseGenerationProperty C c := by
  constructor
  · rintro ⟨gen, hgen⟩
    exact theorem_5_4_necessity hgen
  · intro hproperty
    exact theorem_5_4_sufficiency_enumerated
      C c hc0 hc1 family hfamilyInfinite
      hfamilyC hcovers hproperty

end GenLimit.InfiniteContamination
