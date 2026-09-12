import GenLimit.Paper21_GenerationInMetricSpaces.ScaleMonotonicity
import GenLimit.Paper02_LearningTheory.Definitions

/-!
# Recovering the countable discrete framework

This file formalizes Proposition D.1 of Li--Raman--Tewari,
*On Generation in Metric Spaces*, arXiv:2602.07710v1.

For the `{0,1}` discrete metric and any scale in `[0,1)`, closed
neighbourhoods are the original sets and covering number is ordinary finite
cardinality.  The resulting three generation notions coincide with the
paper's earlier countable-space semantics.
-/

namespace GenLimit.MetricSpaces

/-- The source's `{0,1}` discrete metric, kept as an explicit distance
kernel. -/
def discreteDistance [DecidableEq α] : Distance α :=
  fun x y ↦ if x = y then 0 else 1

@[simp] theorem discreteDistance_self [DecidableEq α] (x : α) :
    discreteDistance x x = 0 := by
  simp [discreteDistance]

theorem discreteDistance_eq_one [DecidableEq α]
    {x y : α} (hxy : x ≠ y) :
    discreteDistance x y = 1 := by
  simp [discreteDistance, hxy]

/-- Below scale one, the closed neighbourhood of a set in the discrete
metric is exactly that set. -/
theorem discrete_closedNeighborhood_eq
    [DecidableEq α] {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (A : Set α) :
    closedNeighborhood (discreteDistance (α := α)) A ε = A := by
  ext y
  constructor
  · intro hy
    let η := (ε + 1) / 2
    have hεη : ε < η := by
      dsimp [η]
      linarith
    have hη1 : η < 1 := by
      dsimp [η]
      linarith
    obtain ⟨x, hxA, hxy⟩ := hy η hεη
    have hxyEq : x = y := by
      by_contra hne
      rw [discreteDistance_eq_one hne] at hxy
      exact (not_lt_of_ge hη1.le) hxy
    simpa [hxyEq] using hxA
  · intro hy η hεη
    refine ⟨y, hy, ?_⟩
    rw [discreteDistance_self]
    exact lt_of_le_of_lt hε0 hεη

theorem discrete_hasFiniteCover_iff
    [DecidableEq α] {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    {A : Set α} :
    HasFiniteCover (discreteDistance (α := α)) ε A ↔ A.Finite := by
  constructor
  · rintro ⟨centers, hcover⟩
    have hsubset : A ⊆ (centers : Set α) := by
      simpa [discrete_closedNeighborhood_eq hε0 hε1] using hcover
    exact (centers.finite_toSet).subset hsubset
  · intro hA
    classical
    refine ⟨hA.toFinset, ?_⟩
    simp [discrete_closedNeighborhood_eq hε0 hε1]

theorem discrete_coveringNumberAtLeast_finset_iff
    [DecidableEq α] {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (S : Finset α) (d : ℕ) :
    CoveringNumberAtLeast (discreteDistance (α := α)) ε
        (S : Set α) d ↔
      d ≤ S.card := by
  constructor
  · intro h
    apply h S
    simp [discrete_closedNeighborhood_eq hε0 hε1]
  · intro hd centers hcover
    have hsubset : S ⊆ centers := by
      intro x hx
      have hx' : x ∈
          closedNeighborhood (discreteDistance (α := α))
            (centers : Set α) ε :=
        hcover hx
      simpa [discrete_closedNeighborhood_eq hε0 hε1] using hx'
    exact hd.trans (Finset.card_le_card hsubset)

theorem discrete_metricPresentation_iff
    [DecidableEq α] {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    {stream : GenLimit.Generic.Stream α}
    {L : GenLimit.Generic.Language α} :
    MetricPresentation (discreteDistance (α := α)) ε stream L ↔
      GenLimit.Generic.Presents stream L := by
  constructor
  · rintro ⟨hstream, hcover⟩
    apply Set.Subset.antisymm
    · exact hstream
    · simpa [discrete_closedNeighborhood_eq hε0 hε1] using hcover
  · intro hpresents
    constructor
    · exact GenLimit.Generic.streamIn_of_presents hpresents
    · rw [← hpresents]
      simp [discrete_closedNeighborhood_eq hε0 hε1]

theorem discrete_metricCorrectAt_iff
    [DecidableEq α] {ε' : ℝ} (hε'0 : 0 ≤ ε') (hε'1 : ε' < 1)
    {gen : GenLimit.Generic.Generator α}
    {L : GenLimit.Generic.Language α}
    {stream : GenLimit.Generic.Stream α} {t : ℕ} :
    MetricCorrectAt (discreteDistance (α := α)) ε'
        gen L stream t ↔
      GenLimit.Generic.CorrectAt gen L stream t := by
  simp only [MetricCorrectAt, GenLimit.Generic.CorrectAt]
  rw [discrete_closedNeighborhood_eq hε'0 hε'1]
  simp only [Finset.mem_coe]

/-- Limit-generation part of Proposition D.1, at the generator level. -/
theorem discrete_isLimitGeneratorAt_iff
    [DecidableEq α] {ε ε' : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hε'0 : 0 ≤ ε') (hε'1 : ε' < 1)
    {gen : GenLimit.Generic.Generator α}
    {H : GenLimit.Generic.LanguageClass α} :
    IsLimitGeneratorAt (discreteDistance (α := α)) ε ε' gen H ↔
      GenLimit.LiRamanTewari.IsLimitGenerator gen H := by
  constructor
  · intro hgen L hLH stream hpresents
    obtain ⟨T, hT⟩ :=
      hgen L hLH stream
        ((discrete_metricPresentation_iff hε0 hε1).mpr hpresents)
    exact
      ⟨T, fun t ht ↦
        (discrete_metricCorrectAt_iff hε'0 hε'1).mp (hT t ht)⟩
  · intro hgen L hLH stream hpresentation
    obtain ⟨T, hT⟩ :=
      hgen L hLH stream
        ((discrete_metricPresentation_iff hε0 hε1).mp hpresentation)
    exact
      ⟨T, fun t ht ↦
        (discrete_metricCorrectAt_iff hε'0 hε'1).mpr (hT t ht)⟩

/-- Generation-in-the-limit part of Proposition D.1. -/
theorem proposition_D_1_limit
    [DecidableEq α] {ε ε' : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hε'0 : 0 ≤ ε') (hε'1 : ε' < 1)
    {H : GenLimit.Generic.LanguageClass α} :
    GeneratableInLimitAt (discreteDistance (α := α)) ε ε' H ↔
      GenLimit.LiRamanTewari.GeneratableInLimit H := by
  constructor
  · rintro ⟨gen, hgen⟩
    exact ⟨gen,
      (discrete_isLimitGeneratorAt_iff hε0 hε1 hε'0 hε'1).mp hgen⟩
  · rintro ⟨gen, hgen⟩
    exact ⟨gen,
      (discrete_isLimitGeneratorAt_iff hε0 hε1 hε'0 hε'1).mpr hgen⟩

/-- Uniform-generation part of Proposition D.1, at a fixed generator and
threshold. -/
theorem discrete_isUniformGeneratorAt_iff
    [DecidableEq α] {ε ε' : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hε'0 : 0 ≤ ε') (hε'1 : ε' < 1)
    {gen : GenLimit.Generic.Generator α}
    {H : GenLimit.Generic.LanguageClass α} {d : ℕ} :
    IsUniformGeneratorAt (discreteDistance (α := α)) ε ε' gen H d ↔
      GenLimit.LiRamanTewari.IsUniformGeneratorAt gen H d := by
  constructor
  · intro hgen L hLH stream hstream t ht s hts
    apply (discrete_metricCorrectAt_iff hε'0 hε'1).mp
    apply hgen L hLH stream hstream t
    exact
      (discrete_coveringNumberAtLeast_finset_iff hε0 hε1
        (GenLimit.Generic.sample stream t) d).mpr ht.ge
    exact hts
  · intro hgen L hLH stream hstream t htrigger s hts
    have hd :
        d ≤ (GenLimit.Generic.sample stream t).card :=
      (discrete_coveringNumberAtLeast_finset_iff hε0 hε1
        (GenLimit.Generic.sample stream t) d).mp htrigger
    obtain ⟨r, hrt, hr⟩ :=
      GenLimit.Generic.exists_sample_card_eq_of_le hd
    apply (discrete_metricCorrectAt_iff hε'0 hε'1).mpr
    exact hgen L hLH stream hstream r hr s (hrt.trans hts)

/-- Uniform-generation part of Proposition D.1. -/
theorem proposition_D_1_uniform
    [DecidableEq α] {ε ε' : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hε'0 : 0 ≤ ε') (hε'1 : ε' < 1)
    {H : GenLimit.Generic.LanguageClass α} :
    UniformlyGeneratableAt (discreteDistance (α := α)) ε ε' H ↔
      GenLimit.LiRamanTewari.UniformlyGeneratable H := by
  constructor
  · rintro ⟨gen, d, hgen⟩
    exact ⟨gen, d,
      (discrete_isUniformGeneratorAt_iff hε0 hε1 hε'0 hε'1).mp hgen⟩
  · rintro ⟨gen, d, hgen⟩
    exact ⟨gen, d,
      (discrete_isUniformGeneratorAt_iff hε0 hε1 hε'0 hε'1).mpr hgen⟩

/-- Non-uniform-generation part of Proposition D.1, at a fixed generator. -/
theorem discrete_isNonuniformGeneratorAt_iff
    [DecidableEq α] {ε ε' : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hε'0 : 0 ≤ ε') (hε'1 : ε' < 1)
    {gen : GenLimit.Generic.Generator α}
    {H : GenLimit.Generic.LanguageClass α} :
    IsNonuniformGeneratorAt (discreteDistance (α := α)) ε ε' gen H ↔
      GenLimit.LiRamanTewari.IsNonuniformGenerator gen H := by
  constructor
  · intro hgen L hLH
    obtain ⟨d, hd⟩ := hgen L hLH
    refine ⟨d, ?_⟩
    intro stream hstream t ht s hts
    apply (discrete_metricCorrectAt_iff hε'0 hε'1).mp
    apply hd stream hstream t
    exact
      (discrete_coveringNumberAtLeast_finset_iff hε0 hε1
        (GenLimit.Generic.sample stream t) d).mpr ht.ge
    exact hts
  · intro hgen L hLH
    obtain ⟨d, hd⟩ := hgen L hLH
    refine ⟨d, ?_⟩
    intro stream hstream t htrigger s hts
    have hcard :
        d ≤ (GenLimit.Generic.sample stream t).card :=
      (discrete_coveringNumberAtLeast_finset_iff hε0 hε1
        (GenLimit.Generic.sample stream t) d).mp htrigger
    obtain ⟨r, hrt, hr⟩ :=
      GenLimit.Generic.exists_sample_card_eq_of_le hcard
    apply (discrete_metricCorrectAt_iff hε'0 hε'1).mpr
    exact hd stream hstream r hr s (hrt.trans hts)

/-- Non-uniform-generation part of Proposition D.1. -/
theorem proposition_D_1_nonuniform
    [DecidableEq α] {ε ε' : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hε'0 : 0 ≤ ε') (hε'1 : ε' < 1)
    {H : GenLimit.Generic.LanguageClass α} :
    NonuniformlyGeneratableAt (discreteDistance (α := α)) ε ε' H ↔
      GenLimit.LiRamanTewari.NonuniformlyGeneratable H := by
  constructor
  · rintro ⟨gen, hgen⟩
    exact ⟨gen,
      (discrete_isNonuniformGeneratorAt_iff hε0 hε1 hε'0 hε'1).mp hgen⟩
  · rintro ⟨gen, hgen⟩
    exact ⟨gen,
      (discrete_isNonuniformGeneratorAt_iff hε0 hε1 hε'0 hε'1).mpr hgen⟩

end GenLimit.MetricSpaces
