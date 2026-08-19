import GenLimit.Paper09_RepresentativeLanguageGeneration.Definitions

/-!
# Relationships to ordinary generation

Representative generation uses the same histories and eventual-consistency
quantifiers as the shared Core predicates, but returns a distribution rather
than one point.  Selecting a fixed point of nonzero mass converts any
consistent representative output distribution into an ordinary fresh,
correct output.  This module records the resulting hierarchy without moving
paper-specific probability or group notions into Core.
-/

namespace GenLimit.RepresentativeGeneration

/-- Published Definition 2.3 is exactly Core's positive version space. -/
theorem consistentHypotheses_eq_versionSpace
    (H : GenLimit.Generic.LanguageClass α) (S : Finset α) :
    consistentHypotheses H S = GenLimit.Generic.versionSpace H S :=
  rfl

/-- The paper's common core is Core's canonical version-space
intersection. -/
theorem commonCore_eq_genericCommonCore
    (H : GenLimit.Generic.LanguageClass α) (S : Finset α) :
    commonCore H S = GenLimit.Generic.commonCore H S :=
  rfl

/-- Published Definition 2.4 is exactly Core's positive closure. -/
theorem closure_eq_genericClosure
    (H : GenLimit.Generic.LanguageClass α) (S : Finset α) :
    closure H S = GenLimit.Generic.closure H S :=
  rfl

/-! ## The representative hierarchy -/

theorem isAlphaRepresentative_mono
    {gen : RandomizedGenerator α} {groups : ℕ → Set α}
    {alpha beta : ℝ} (hab : alpha ≤ beta)
    (h : IsAlphaRepresentative gen groups alpha) :
    IsAlphaRepresentative gen groups beta := by
  intro stream t ht
  exact (h stream t ht).trans (ENNReal.ofReal_le_ofReal hab)

theorem alpha_uniform_implies_nonuniform
    {H : GenLimit.Generic.LanguageClass α}
    {groups : ℕ → Set α} {alpha : ℝ}
    (h : AlphaRepresentativeUniformlyGeneratable H groups alpha) :
    ∃ gen : RandomizedGenerator α,
      IsAlphaRepresentative gen groups alpha ∧
      ∀ L, L ∈ H → ∃ d : ℕ,
        ∀ stream : GenLimit.Generic.Stream α,
          GenLimit.Generic.StreamIn stream L →
          ∀ t, (GenLimit.Generic.sample stream t).card = d →
            IsConsistentFrom gen L stream t := by
  obtain ⟨gen, hrep, d, hd⟩ := h
  exact ⟨gen, hrep, fun L hLH => ⟨d, hd L hLH⟩⟩

theorem representative_uniform_implies_nonuniform
    {H : GenLimit.Generic.LanguageClass α}
    {groups : ℕ → Set α}
    (h : RepresentativelyUniformlyGeneratable H groups) :
    RepresentativelyNonuniformlyGeneratable H groups := by
  intro alpha halpha
  by_cases ha : alpha ≤ 1
  · exact alpha_uniform_implies_nonuniform (h alpha halpha ha)
  · obtain ⟨gen, hrep, d, hd⟩ := h 1 (by norm_num) le_rfl
    refine ⟨gen, isAlphaRepresentative_mono (le_of_not_ge ha) hrep, ?_⟩
    intro L hLH
    exact ⟨d, hd L hLH⟩

/-- Representative non-uniform generation implies representative generation
in the limit for UUS classes. -/
theorem representative_nonuniform_implies_limit
    {H : GenLimit.Generic.LanguageClass α}
    {groups : ℕ → Set α}
    (hUUS : GenLimit.Generic.UUS H)
    (h : RepresentativelyNonuniformlyGeneratable H groups) :
    RepresentativelyGeneratableInLimit H groups := by
  intro alpha halpha
  obtain ⟨gen, hrep, hgen⟩ := h alpha halpha
  refine ⟨gen, hrep, ?_⟩
  intro L hLH stream hP
  obtain ⟨d, hd⟩ := hgen L hLH
  obtain ⟨T, hT⟩ :=
    GenLimit.Generic.exists_sample_card_eq_of_presents_infinite
      hP (hUUS L hLH) d
  exact ⟨T, hd stream (GenLimit.Generic.streamIn_of_presents hP) T hT⟩

/-- Determinize a randomized generator by choosing one point of nonzero mass
from each output distribution.  The choice is semantic and need not be
computable. -/
noncomputable def supportPointGenerator
    (gen : RandomizedGenerator α) : GenLimit.Generic.Generator α :=
  fun t xs => (gen t xs).supportPoint

theorem supportPointGenerator_correctAt
    {gen : RandomizedGenerator α}
    {L : GenLimit.Generic.Language α}
    {stream : GenLimit.Generic.Stream α} {t : ℕ}
    (hconsistent : IsConsistentAt gen L stream t) :
    GenLimit.Generic.CorrectAt
      (supportPointGenerator gen) L stream t := by
  have hsupported :=
    isConsistentAt_iff_supportedOn.mp hconsistent
  have hmem := hsupported
    (distributionAt gen stream t).supportPoint
    (distributionAt gen stream t).supportPoint_mass_ne_zero
  simpa [GenLimit.Generic.CorrectAt, GenLimit.Generic.output,
    supportPointGenerator, distributionAt] using hmem

/-- Fixed-scale representative uniform generation implies ordinary uniform
generation by choosing a support point at every history. -/
theorem alphaRepresentativeUniform_implies_uniform
    {H : GenLimit.Generic.LanguageClass α}
    {groups : ℕ → Set α} {alpha : ℝ}
    (h : AlphaRepresentativeUniformlyGeneratable H groups alpha) :
    GenLimit.Generic.UniformlyGeneratable H := by
  obtain ⟨gen, _hrepresentative, d, hconsistent⟩ := h
  refine ⟨supportPointGenerator gen, d, ?_⟩
  intro L hLH stream hstream t hcard s hts
  exact supportPointGenerator_correctAt
    (hconsistent L hLH stream hstream t hcard s hts)

/-- Representative uniform generation is stronger than ordinary uniform
generation. -/
theorem representativeUniform_implies_uniform
    {H : GenLimit.Generic.LanguageClass α}
    {groups : ℕ → Set α}
    (h : RepresentativelyUniformlyGeneratable H groups) :
    GenLimit.Generic.UniformlyGeneratable H :=
  alphaRepresentativeUniform_implies_uniform
    (h 1 (by norm_num) le_rfl)

/-- Representative non-uniform generation is stronger than ordinary
non-uniform generation. -/
theorem representativeNonuniform_implies_nonuniform
    {H : GenLimit.Generic.LanguageClass α}
    {groups : ℕ → Set α}
    (h : RepresentativelyNonuniformlyGeneratable H groups) :
    GenLimit.Generic.NonuniformlyGeneratable H := by
  obtain ⟨gen, _hrepresentative, hconsistent⟩ :=
    h 1 (by norm_num)
  refine ⟨supportPointGenerator gen, ?_⟩
  intro L hLH
  obtain ⟨d, hd⟩ := hconsistent L hLH
  refine ⟨d, ?_⟩
  intro stream hstream t hcard s hts
  exact supportPointGenerator_correctAt
    (hd stream hstream t hcard s hts)

/-- Representative generation in the limit is stronger than ordinary
generation in the limit. -/
theorem representativeLimit_implies_limit
    {H : GenLimit.Generic.LanguageClass α}
    {groups : ℕ → Set α}
    (h : RepresentativelyGeneratableInLimit H groups) :
    GenLimit.Generic.GeneratableInLimit H := by
  obtain ⟨gen, _hrepresentative, hconsistent⟩ :=
    h 1 (by norm_num)
  refine ⟨supportPointGenerator gen, ?_⟩
  intro L hLH stream hpresents
  obtain ⟨T, hT⟩ := hconsistent L hLH stream hpresents
  exact ⟨T, fun t ht => supportPointGenerator_correctAt (hT t ht)⟩

end GenLimit.RepresentativeGeneration
