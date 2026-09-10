import GenLimit.Paper30_TimeSensitiveLanguageGeneration.MeasureZeroExamples
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# Density-zero completion of the dyadic chain

This file supplies the logarithmic counting argument omitted from the first
Appendix-B slice of Ganju--McVoy--Dughmi--Teng.  Positive naturals are ordered
as `1,2,3,...`.  At the prefix ending at `2^M`, a fixed dyadic-chain level
contains only its fixed initial segment and at most the first `M+1`
distinguished powers of two.  The resulting linear-over-exponential ratio
tends to zero along a cofinal subsequence, which is enough for lower density
zero.
-/

namespace GenLimit.TimeSensitive

open Filter
open GenLimit.KleinbergWei

/-- The source's natural order on the positive integers. -/
def positiveNaturalsOrder : OrderedLanguage where
  carrier := positiveNaturals
  enumeration := fun n => n + 1
  enumeration_injective := fun _ _ h => Nat.add_right_cancel h
  range_enumeration := by
    ext n
    constructor
    · rintro ⟨k, rfl⟩
      exact Nat.succ_pos k
    · intro hn
      have hnpos : 0 < n := hn
      exact
        ⟨n - 1,
          Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hnpos.ne')⟩

/-- Candidate index set covering all points of level `j` in the first
`2^M` positions: a fixed initial segment plus at most `M+1` power indices. -/
noncomputable def dyadicPrefixIndexCover (j M : ℕ) : Finset ℕ := by
  classical
  exact
    Finset.range (2 ^ (j + 1)) ∪
      (Finset.range (M + 1)).image (fun m => 2 ^ m - 1)

noncomputable def dyadicPrefixFilter (j M : ℕ) : Finset ℕ := by
  classical
  exact
    (Finset.range (2 ^ M)).filter
      (fun i => positiveNaturalsOrder.enumeration i ∈
        dyadicBlockLanguage j)

theorem dyadic_prefix_filter_subset_cover (j M : ℕ) :
    dyadicPrefixFilter j M ⊆
      dyadicPrefixIndexCover j M := by
  classical
  intro i hi
  rw [dyadicPrefixFilter] at hi
  obtain ⟨hiM, hipos, hismall | ⟨m, hm⟩⟩ :=
    Finset.mem_filter.mp hi
  · apply Finset.mem_union_left
    simp only [Finset.mem_range]
    change i + 1 < 2 ^ (j + 1) at hismall
    omega
  · apply Finset.mem_union_right
    rw [Finset.mem_image]
    have hiM' : i < 2 ^ M := Finset.mem_range.mp hiM
    change i + 1 = 2 ^ m at hm
    have hpowLe : 2 ^ m ≤ 2 ^ M := by
      rw [← hm]
      exact Nat.succ_le_iff.mpr hiM'
    have hmM : m ≤ M :=
      (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hpowLe
    refine ⟨m, Finset.mem_range.mpr (Nat.lt_succ_of_le hmM), ?_⟩
    change 2 ^ m - 1 = i
    omega

theorem dyadic_prefixCount_pow_le (j M : ℕ) :
    positiveNaturalsOrder.prefixCount
        (dyadicBlockLanguage j) (2 ^ M) ≤
      2 ^ (j + 1) + (M + 1) := by
  classical
  change (dyadicPrefixFilter j M).card ≤ _
  calc
    (dyadicPrefixFilter j M).card
      ≤ (dyadicPrefixIndexCover j M).card :=
        Finset.card_le_card (dyadic_prefix_filter_subset_cover j M)
    _ ≤
        (Finset.range (2 ^ (j + 1))).card +
          ((Finset.range (M + 1)).image
            (fun m => 2 ^ m - 1)).card := by
              exact Finset.card_union_le _ _
    _ ≤ 2 ^ (j + 1) + (M + 1) := by
      simpa using
        Nat.add_le_add_left
          (Finset.card_image_le :
            ((Finset.range (M + 1)).image
              (fun m => 2 ^ m - 1)).card ≤
                (Finset.range (M + 1)).card)
          (2 ^ (j + 1))

/-- A cofinal subsequence with ratio tending to zero forces ordered lower
density zero. -/
theorem lowerDensity_eq_zero_of_cofinal_subsequence
    (K : OrderedLanguage) (A : Set ℕ)
    (positions : ℕ → ℕ)
    (hpositions : Tendsto positions atTop atTop)
    (hsubsequence :
      Tendsto
        (fun n => K.prefixRatio A (positions n))
        atTop (nhds 0)) :
    K.lowerDensity A = 0 := by
  apply le_antisymm
  · by_contra hnot
    have hpositive : 0 < K.lowerDensity A := lt_of_not_ge hnot
    let ε := K.lowerDensity A / 2
    have hε : 0 < ε := by
      dsimp [ε]
      linarith
    have hfrequent :
        ∃ᶠ n : ℕ in atTop, K.prefixRatio A n ≤ ε := by
      rw [Filter.frequently_atTop]
      intro cutoff
      have hpositionEventually :
          ∀ᶠ m : ℕ in atTop, cutoff ≤ positions m :=
        hpositions.eventually (Ici_mem_atTop cutoff)
      have hratioEventually :
          ∀ᶠ m : ℕ in atTop,
            K.prefixRatio A (positions m) < ε :=
        (tendsto_order.1 hsubsequence).2 ε hε
      obtain ⟨m, hmPosition, hmRatio⟩ :=
        (hpositionEventually.and hratioEventually).exists
      exact ⟨positions m, hmPosition, hmRatio.le⟩
    have hliminf :
        K.lowerDensity A ≤ ε := by
      unfold OrderedLanguage.lowerDensity
      exact liminf_le_of_frequently_le hfrequent
        (isBoundedUnder_of
          ⟨0, fun n => K.prefixRatio_nonneg A n⟩)
    dsimp [ε] at hliminf
    linarith
  · unfold OrderedLanguage.lowerDensity
    apply le_liminf_of_le
    · exact isCoboundedUnder_ge_of_le atTop
        (fun n => K.prefixRatio_le_one A n)
    · exact Filter.Eventually.of_forall
        (fun n => K.prefixRatio_nonneg A n)

theorem tendsto_dyadic_prefixRatio_pow (j : ℕ) :
    Tendsto
      (fun M =>
        positiveNaturalsOrder.prefixRatio
          (dyadicBlockLanguage j) (2 ^ M))
      atTop (nhds 0) := by
  let upper : ℕ → ℝ :=
    fun M => ((2 ^ (j + 1) + (M + 1) : ℕ) : ℝ) / (2 : ℝ) ^ M
  have hlinear :
      Tendsto (fun M : ℕ => (M : ℝ) / (2 : ℝ) ^ M)
        atTop (nhds 0) := by
    simpa using
      (tendsto_pow_const_div_const_pow_of_one_lt
        1 (by norm_num : (1 : ℝ) < 2))
  have hone :
      Tendsto (fun M : ℕ => (1 : ℝ) / (2 : ℝ) ^ M)
        atTop (nhds 0) := by
    simpa using
      (tendsto_pow_const_div_const_pow_of_one_lt
        0 (by norm_num : (1 : ℝ) < 2))
  have hconstant :
      Tendsto
        (fun M : ℕ =>
          ((2 ^ (j + 1) : ℕ) : ℝ) / (2 : ℝ) ^ M)
        atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul
        (by
          simpa [div_eq_mul_inv] using hone :
          Tendsto (fun M : ℕ => ((2 : ℝ) ^ M)⁻¹)
            atTop (nhds 0)))
  have hupper : Tendsto upper atTop (nhds 0) := by
    have hadd := hconstant.add (hlinear.add hone)
    simpa [upper, add_div] using hadd
  exact @squeeze_zero' ℕ
    (fun M =>
      positiveNaturalsOrder.prefixRatio
        (dyadicBlockLanguage j) (2 ^ M))
    upper atTop
    (Filter.Eventually.of_forall fun M =>
      positiveNaturalsOrder.prefixRatio_nonneg
        (dyadicBlockLanguage j) (2 ^ M))
    (Filter.Eventually.of_forall fun M => by
      change
        (if 2 ^ M = 0 then 0
          else
            (positiveNaturalsOrder.prefixCount
              (dyadicBlockLanguage j) (2 ^ M) : ℝ) / (2 ^ M : ℕ)) ≤
          upper M
      rw [if_neg (pow_ne_zero M (by norm_num : (2 : ℕ) ≠ 0))]
      have hcount :=
        dyadic_prefixCount_pow_le j M
      have hcountReal :
          (positiveNaturalsOrder.prefixCount
              (dyadicBlockLanguage j) (2 ^ M) : ℝ) ≤
            (2 ^ (j + 1) + (M + 1) : ℕ) := by
        exact_mod_cast hcount
      change
        (positiveNaturalsOrder.prefixCount
            (dyadicBlockLanguage j) (2 ^ M) : ℝ) /
              (2 ^ M : ℕ) ≤ upper M
      rw [show ((2 ^ M : ℕ) : ℝ) = (2 : ℝ) ^ M by norm_num]
      exact div_le_div_of_nonneg_right hcountReal (by positivity))
    hupper

/-- Appendix-B Example 1 completed as an actual measure-zero chain in the
paper's natural positive-integer order. -/
def dyadicMeasureZeroChain : MeasureZeroChain where
  limit := positiveNaturalsOrder
  level := dyadicBlockLanguage
  nested := dyadicBlockLanguage_nested
  union_eq := iUnion_dyadicBlockLanguage
  sparse := by
    intro j
    apply lowerDensity_eq_zero_of_cofinal_subsequence
      positiveNaturalsOrder (dyadicBlockLanguage j) (fun M => 2 ^ M)
    · exact
        (Nat.tendsto_pow_atTop_atTop_of_one_lt
          (by norm_num : 1 < (2 : ℕ)))
    · exact tendsto_dyadic_prefixRatio_pow j

/-! ## Appendix-B Example 2 -/

/-- The canonical order on all naturals.  Example 2 includes the source's
zero marker, so its limiting carrier is `Set.univ`, unlike Example 1's
positive-natural carrier. -/
def naturalNumbersOrder : OrderedLanguage where
  carrier := Set.univ
  enumeration := id
  enumeration_injective := Function.injective_id
  range_enumeration := Set.range_id

/-- Candidate indices for the first `3^M` positions of the marker-interval
language.  Every one of the first `M+1` markers contributes at most `j+1`
indices. -/
noncomputable def markerPrefixIndexCover (j M : ℕ) : Finset ℕ := by
  classical
  exact
    (Finset.range (M + 1)).biUnion fun k =>
      (Finset.range (j + 1)).image
        (fun r => marker k + r)

noncomputable def markerPrefixFilter (j M : ℕ) : Finset ℕ := by
  classical
  exact
    (Finset.range (3 ^ M)).filter
      (fun i => naturalNumbersOrder.enumeration i ∈
        markerIntervalLanguage j)

theorem marker_prefix_filter_subset_cover (j M : ℕ) :
    markerPrefixFilter j M ⊆ markerPrefixIndexCover j M := by
  classical
  intro x hx
  rw [markerPrefixFilter] at hx
  obtain ⟨hxM, k, hklower, hkupper⟩ :=
    Finset.mem_filter.mp hx
  have hxM' : x < 3 ^ M := Finset.mem_range.mp hxM
  change marker k ≤ x at hklower
  change x ≤ marker k + j at hkupper
  have hkM : k ≤ M := by
    by_cases hk : k = 0
    · omega
    · have hpow : 3 ^ k ≤ 3 ^ M := by
        have hmarker : marker k = 3 ^ k := by
          simp [marker, hk]
        rw [← hmarker]
        exact hklower.trans hxM'.le
      exact
        (Nat.pow_le_pow_iff_right
          (by decide : 1 < (3 : ℕ))).mp hpow
  let r := x - marker k
  have hrj : r ≤ j := by
    dsimp [r]
    omega
  rw [markerPrefixIndexCover, Finset.mem_biUnion]
  refine ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hkM), ?_⟩
  rw [Finset.mem_image]
  refine ⟨r, Finset.mem_range.mpr (Nat.lt_succ_of_le hrj), ?_⟩
  dsimp [r]
  omega

theorem marker_prefixCount_pow_le (j M : ℕ) :
    naturalNumbersOrder.prefixCount
        (markerIntervalLanguage j) (3 ^ M) ≤
      (M + 1) * (j + 1) := by
  classical
  change (markerPrefixFilter j M).card ≤ _
  calc
    (markerPrefixFilter j M).card
      ≤ (markerPrefixIndexCover j M).card :=
        Finset.card_le_card (marker_prefix_filter_subset_cover j M)
    _ ≤ (M + 1) * (j + 1) := by
      rw [markerPrefixIndexCover]
      simpa using
        (Finset.card_biUnion_le_card_mul
          (Finset.range (M + 1))
          (fun k =>
            (Finset.range (j + 1)).image
              (fun r => marker k + r))
          (j + 1)
          (by
            intro k hk
            simpa using
              (Finset.card_image_le :
                ((Finset.range (j + 1)).image
                  (fun r => marker k + r)).card ≤
                    (Finset.range (j + 1)).card)))

theorem tendsto_marker_prefixRatio_pow (j : ℕ) :
    Tendsto
      (fun M =>
        naturalNumbersOrder.prefixRatio
          (markerIntervalLanguage j) (3 ^ M))
      atTop (nhds 0) := by
  let upper : ℕ → ℝ :=
    fun M => (((M + 1) * (j + 1) : ℕ) : ℝ) / (3 : ℝ) ^ M
  have hlinear :
      Tendsto (fun M : ℕ => (M : ℝ) / (3 : ℝ) ^ M)
        atTop (nhds 0) := by
    simpa using
      (tendsto_pow_const_div_const_pow_of_one_lt
        1 (by norm_num : (1 : ℝ) < 3))
  have hone :
      Tendsto (fun M : ℕ => (1 : ℝ) / (3 : ℝ) ^ M)
        atTop (nhds 0) := by
    simpa using
      (tendsto_pow_const_div_const_pow_of_one_lt
        0 (by norm_num : (1 : ℝ) < 3))
  have hupper : Tendsto upper atTop (nhds 0) := by
    have hsum :
        Tendsto
          (fun M : ℕ =>
            ((M : ℝ) / (3 : ℝ) ^ M +
              (1 : ℝ) / (3 : ℝ) ^ M) *
                ((j + 1 : ℕ) : ℝ))
          atTop (nhds 0) := by
      simpa using
        (hlinear.add hone).mul_const (((j + 1 : ℕ) : ℝ))
    convert hsum using 1
    · funext M
      simp only [upper]
      push_cast
      ring
  exact @squeeze_zero' ℕ
    (fun M =>
      naturalNumbersOrder.prefixRatio
        (markerIntervalLanguage j) (3 ^ M))
    upper atTop
    (Filter.Eventually.of_forall fun M =>
      naturalNumbersOrder.prefixRatio_nonneg
        (markerIntervalLanguage j) (3 ^ M))
    (Filter.Eventually.of_forall fun M => by
      change
        (if 3 ^ M = 0 then 0
          else
            (naturalNumbersOrder.prefixCount
              (markerIntervalLanguage j) (3 ^ M) : ℝ) / (3 ^ M : ℕ)) ≤
          upper M
      rw [if_neg (pow_ne_zero M (by norm_num : (3 : ℕ) ≠ 0))]
      have hcount := marker_prefixCount_pow_le j M
      have hcountReal :
          (naturalNumbersOrder.prefixCount
              (markerIntervalLanguage j) (3 ^ M) : ℝ) ≤
            ((M + 1) * (j + 1) : ℕ) := by
        exact_mod_cast hcount
      change
        (naturalNumbersOrder.prefixCount
            (markerIntervalLanguage j) (3 ^ M) : ℝ) /
              (3 ^ M : ℕ) ≤ upper M
      rw [show ((3 ^ M : ℕ) : ℝ) = (3 : ℝ) ^ M by norm_num]
      exact div_le_div_of_nonneg_right hcountReal (by positivity))
    hupper

/-- Appendix-B Example 2 completed as a measure-zero chain in the canonical
all-natural order, retaining the source's zero marker. -/
def markerMeasureZeroChain : MeasureZeroChain where
  limit := naturalNumbersOrder
  level := markerIntervalLanguage
  nested := markerIntervalLanguage_nested
  union_eq := iUnion_markerIntervalLanguage
  sparse := by
    intro j
    apply lowerDensity_eq_zero_of_cofinal_subsequence
      naturalNumbersOrder (markerIntervalLanguage j) (fun M => 3 ^ M)
    · exact
        (Nat.tendsto_pow_atTop_atTop_of_one_lt
          (by norm_num : 1 < (3 : ℕ)))
    · exact tendsto_marker_prefixRatio_pow j

end GenLimit.TimeSensitive
