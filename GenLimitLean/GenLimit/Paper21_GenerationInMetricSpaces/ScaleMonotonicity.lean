import GenLimit.Paper21_GenerationInMetricSpaces.Definitions

/-!
# Monotonicity in the novelty scales

This file formalizes Lemma 2.1 and Theorems 4.6--4.7 of
Li--Raman--Tewari, *On Generation in Metric Spaces*,
arXiv:2602.07710v1.

The proofs retain the source's generators and thresholds.  No compactness,
separability, or choice of nearest points is needed.
-/

namespace GenLimit.MetricSpaces

/-- Lemma 2.1: infinite covering number at radius `r` implies infinite
covering number at every smaller positive radius. -/
theorem lemma_2_1_uus_mono
    {ρ : Distance α} {H : GenLimit.Generic.LanguageClass α}
    {δ r : ℝ} (_hδ : 0 < δ) (hδr : δ < r)
    (hUUS : UniformlyUnboundedSupportAt ρ r H) :
    UniformlyUnboundedSupportAt ρ δ H := by
  intro L hLH hfinite
  exact hUUS L hLH (finiteCover_mono_radius hδr.le hfinite)

theorem metricPresentation_mono_adversary_scale
    {ρ : Distance α} {stream : GenLimit.Generic.Stream α}
    {L : GenLimit.Generic.Language α} {δ ε : ℝ}
    (hδε : δ ≤ ε) :
    MetricPresentation ρ δ stream L →
      MetricPresentation ρ ε stream L := by
  rintro ⟨hstream, hcover⟩
  exact
    ⟨hstream,
      hcover.trans (inClosedNeighborhood_mono_radius hδε)⟩

theorem metricCorrectAt_mono_generator_scale
    {ρ : Distance α} {gen : GenLimit.Generic.Generator α}
    {L : GenLimit.Generic.Language α}
    {stream : GenLimit.Generic.Stream α} {t : ℕ}
    {δ' ε' : ℝ} (hδε : δ' ≤ ε') :
    MetricCorrectAt ρ ε' gen L stream t →
      MetricCorrectAt ρ δ' gen L stream t := by
  rintro ⟨hvalid, hfresh⟩
  exact
    ⟨hvalid,
      not_inClosedNeighborhood_anti_radius hδε hfresh⟩

/-- Generator-level form of Theorem 4.6. -/
theorem isLimitGeneratorAt_mono
    {ρ : Distance α} {H : GenLimit.Generic.LanguageClass α}
    {gen : GenLimit.Generic.Generator α}
    {δ δ' ε ε' : ℝ}
    (hδε : δ ≤ ε) (hδ'ε' : δ' ≤ ε')
    (hgen : IsLimitGeneratorAt ρ ε ε' gen H) :
    IsLimitGeneratorAt ρ δ δ' gen H := by
  intro L hLH stream hpresentation
  obtain ⟨T, hT⟩ :=
    hgen L hLH stream
      (metricPresentation_mono_adversary_scale hδε hpresentation)
  exact
    ⟨T, fun t ht ↦
      metricCorrectAt_mono_generator_scale hδ'ε' (hT t ht)⟩

/-- Theorem 4.6: generation in the limit is preserved when both novelty
scales are decreased. -/
theorem theorem_4_6_limit_scale_monotonicity
    {ρ : Distance α} {H : GenLimit.Generic.LanguageClass α}
    {δ δ' ε ε' : ℝ}
    (hδε : δ ≤ ε) (hδ'ε' : δ' ≤ ε')
    (hgen : GeneratableInLimitAt ρ ε ε' H) :
    GeneratableInLimitAt ρ δ δ' H := by
  obtain ⟨gen, hgen⟩ := hgen
  exact ⟨gen, isLimitGeneratorAt_mono hδε hδ'ε' hgen⟩

/-- Generator-level uniform part of Theorem 4.7.  Increasing the
adversary's scale can only increase the covering-number trigger, while
decreasing the generator's scale weakens freshness. -/
theorem isUniformGeneratorAt_mono
    {ρ : Distance α} {H : GenLimit.Generic.LanguageClass α}
    {gen : GenLimit.Generic.Generator α} {d : ℕ}
    {ε ε' δ δ' : ℝ}
    (hεδ : ε ≤ δ) (hδ'ε' : δ' ≤ ε')
    (hgen : IsUniformGeneratorAt ρ ε ε' gen H d) :
    IsUniformGeneratorAt ρ δ δ' gen H d := by
  intro L hLH stream hstream t htrigger s hts
  have htrigger' :
      CoveringNumberAtLeast ρ ε
        (GenLimit.Generic.sample stream t : Set α) d :=
    coveringNumberAtLeast_anti_radius hεδ htrigger
  exact metricCorrectAt_mono_generator_scale hδ'ε'
    (hgen L hLH stream hstream t htrigger' s hts)

/-- Uniform half of Theorem 4.7. -/
theorem theorem_4_7_uniform_scale_monotonicity
    {ρ : Distance α} {H : GenLimit.Generic.LanguageClass α}
    {ε ε' δ δ' : ℝ}
    (hεδ : ε ≤ δ) (hδ'ε' : δ' ≤ ε')
    (hgen : UniformlyGeneratableAt ρ ε ε' H) :
    UniformlyGeneratableAt ρ δ δ' H := by
  obtain ⟨gen, d, hgen⟩ := hgen
  exact ⟨gen, d, isUniformGeneratorAt_mono hεδ hδ'ε' hgen⟩

/-- Generator-level non-uniform part of Theorem 4.7. -/
theorem isNonuniformGeneratorAt_mono
    {ρ : Distance α} {H : GenLimit.Generic.LanguageClass α}
    {gen : GenLimit.Generic.Generator α}
    {ε ε' δ δ' : ℝ}
    (hεδ : ε ≤ δ) (hδ'ε' : δ' ≤ ε')
    (hgen : IsNonuniformGeneratorAt ρ ε ε' gen H) :
    IsNonuniformGeneratorAt ρ δ δ' gen H := by
  intro L hLH
  obtain ⟨d, hd⟩ := hgen L hLH
  refine ⟨d, ?_⟩
  intro stream hstream t htrigger s hts
  have htrigger' :
      CoveringNumberAtLeast ρ ε
        (GenLimit.Generic.sample stream t : Set α) d :=
    coveringNumberAtLeast_anti_radius hεδ htrigger
  exact metricCorrectAt_mono_generator_scale hδ'ε'
    (hd stream hstream t htrigger' s hts)

/-- Non-uniform half of Theorem 4.7. -/
theorem theorem_4_7_nonuniform_scale_monotonicity
    {ρ : Distance α} {H : GenLimit.Generic.LanguageClass α}
    {ε ε' δ δ' : ℝ}
    (hεδ : ε ≤ δ) (hδ'ε' : δ' ≤ ε')
    (hgen : NonuniformlyGeneratableAt ρ ε ε' H) :
    NonuniformlyGeneratableAt ρ δ δ' H := by
  obtain ⟨gen, hgen⟩ := hgen
  exact ⟨gen, isNonuniformGeneratorAt_mono hεδ hδ'ε' hgen⟩

end GenLimit.MetricSpaces
