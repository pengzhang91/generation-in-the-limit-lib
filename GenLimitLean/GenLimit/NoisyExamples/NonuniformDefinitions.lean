import GenLimit.NoisyExamples.NoisyClosure

/-!
# Raman--Raman: non-uniform noisy generation and noisy generation in the limit

Source: Ananth Raman and Vinod Raman, *Generation from Noisy Examples*,
arXiv:2501.04179v2 / ICML 2025, Definitions 2.6--2.7.

The quantifier order below is the paper's literal order.  In particular, in
Definition 2.6 the threshold may depend on the noise level and the target
language, but not on the noisy stream.  A `NoisyPresentation` is the paper's
"noisy enumeration": every positive example occurs, while only finitely many
stream positions contain negative examples.  This is strictly weaker than
requiring the range of the stream to equal the target.
-/

namespace GenLimit.NoisyExamples

/-- Definition 2.6 at a fixed generator.  The quantifier order is
`for every noise level, for every target, there exists a threshold, for every
stream ...`. -/
def IsNonuniformNoiseDependentGenerator
    (gen : GenLimit.Generic.Generator α)
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  ∀ n : ℕ, ∀ L, L ∈ H → ∃ d : ℕ,
    ∀ stream : GenLimit.Generic.Stream α, HasNoiseAtMost stream L n →
      ∀ t, (GenLimit.Generic.sample stream t).card = d →
        ∀ s, t ≤ s → GenLimit.Generic.CorrectAt gen L stream s

/-- Non-uniform noise-dependent generatability, Definition 2.6. -/
def NonuniformNoiseDependentGeneratable
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  ∃ gen : GenLimit.Generic.Generator α,
    IsNonuniformNoiseDependentGenerator gen H

/-- The paper's noisy enumeration of `L`: the stream still enumerates every
member of `L`, and it has only finitely many negative occurrences. -/
def NoisyPresentation
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) : Prop :=
  L ⊆ Set.range stream ∧ HasFiniteNoise stream L

/-- Definition 2.7 at a fixed generator. -/
def IsNoisyLimitGenerator
    (gen : GenLimit.Generic.Generator α)
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  ∀ L, L ∈ H → ∀ stream : GenLimit.Generic.Stream α,
    NoisyPresentation stream L →
      ∃ T : ℕ, ∀ s, T ≤ s → GenLimit.Generic.CorrectAt gen L stream s

/-- Noisy generatability in the limit, Definition 2.7. -/
def NoisilyGeneratableInLimit
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  ∃ gen : GenLimit.Generic.Generator α, IsNoisyLimitGenerator gen H

theorem noisyPresentation_range_infinite
    {stream : GenLimit.Generic.Stream α}
    {L : GenLimit.Generic.Language α}
    (hL : L.Infinite) (hP : NoisyPresentation stream L) :
    (Set.range stream).Infinite := by
  exact hL.mono hP.1

/-- Any stream with infinite range passes through every finite distinct-sample
count.  This is the noisy-presentation counterpart of the generic exact-
presentation lemma. -/
theorem exists_sample_card_eq_of_range_infinite
    {stream : GenLimit.Generic.Stream α}
    (hrange : (Set.range stream).Infinite) (d : ℕ) :
    ∃ t, (GenLimit.Generic.sample stream t).card = d := by
  exact GenLimit.Generic.exists_sample_card_eq_of_presents_infinite
    (L := Set.range stream) (by rfl) hrange d

/-- Every bounded-noise stream has finite noise. -/
theorem hasFiniteNoise_of_hasNoiseAtMost
    {stream : GenLimit.Generic.Stream α}
    {L : GenLimit.Generic.Language α} {n : ℕ}
    (hnoise : HasNoiseAtMost stream L n) :
    HasFiniteNoise stream L := by
  obtain ⟨F, _hFcard, hF⟩ := hnoise
  have heq : {t | stream t ∉ L} = (↑F : Set ℕ) := by
    ext t
    simp [hF t]
  change {t | stream t ∉ L}.Finite
  rw [heq]
  exact F.finite_toSet

/-- A finite-noise stream has some finite noise bound. -/
theorem exists_hasNoiseAtMost_of_hasFiniteNoise
    {stream : GenLimit.Generic.Stream α}
    {L : GenLimit.Generic.Language α}
    (hnoise : HasFiniteNoise stream L) :
    ∃ n, HasNoiseAtMost stream L n := by
  classical
  let F : Finset ℕ := hnoise.toFinset
  refine ⟨F.card, F, le_rfl, ?_⟩
  intro t
  change t ∈ hnoise.toFinset ↔ _
  rw [Set.Finite.mem_toFinset]
  rfl

/-- Uniform noise-dependent generation implies its non-uniform version. -/
theorem uniform_noiseDependent_implies_nonuniform_noiseDependent
    {H : GenLimit.Generic.LanguageClass α}
    (h : UniformNoiseDependentGeneratable H) :
    NonuniformNoiseDependentGeneratable H := by
  obtain ⟨gen, hgen⟩ := h
  refine ⟨gen, ?_⟩
  intro n L hLH
  obtain ⟨d, hd⟩ := hgen n
  exact ⟨d, hd L hLH⟩

/-- Definition 2.6 implies Definition 2.7, as used in Corollary 3.7. -/
theorem nonuniform_noiseDependent_implies_noisy_limit
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : GenLimit.Generic.UUS H)
    (h : NonuniformNoiseDependentGeneratable H) :
    NoisilyGeneratableInLimit H := by
  obtain ⟨gen, hgen⟩ := h
  refine ⟨gen, ?_⟩
  intro L hLH stream hP
  obtain ⟨n, hnoise⟩ := exists_hasNoiseAtMost_of_hasFiniteNoise hP.2
  obtain ⟨d, hd⟩ := hgen n L hLH
  obtain ⟨T, hT⟩ := exists_sample_card_eq_of_range_infinite
    (noisyPresentation_range_infinite (hUUS L hLH) hP) d
  exact ⟨T, fun s hTs ↦ hd stream hnoise T hT s hTs⟩

end GenLimit.NoisyExamples
