import GenLimit.Paper12_NoiseLossAndFeedback.NoisyWithoutSamples
import GenLimit.Paper06_NoisyExamples.UniformIndependent

/-!
# Bridge to Generation from Noisy Examples

Paper06 permits repeated observations and counts noisy occurrences.  Paper12
uses injective enumerations and therefore counts noisy values.  Under the
injectivity hypothesis the two presentation predicates agree; without it,
Paper06's convention is strictly stronger and the definitions must remain
distinct.
-/

namespace GenLimit.NoiseLossFeedback

open GenLimit.Generic

theorem finite_range_diff_iff_hasFiniteNoise_of_injective
    {stream : Stream α} {L : Language α}
    (hinjective : Function.Injective stream) :
    (Set.range stream \ L).Finite ↔
      GenLimit.NoisyExamples.HasFiniteNoise stream L := by
  constructor
  · intro hvalues
    change {t | stream t ∉ L}.Finite
    have hpreimage :
        {t | stream t ∉ L} =
          stream ⁻¹' (Set.range stream \ L) := by
      ext t
      simp
    rw [hpreimage]
    apply hvalues.preimage
    exact Set.injOn_of_injective hinjective
  · intro htimes
    change {t | stream t ∉ L}.Finite at htimes
    have himage :
        Set.range stream \ L =
          stream '' {t | stream t ∉ L} := by
      ext x
      constructor
      · rintro ⟨⟨t, rfl⟩, ht⟩
        exact ⟨t, ht, rfl⟩
      · rintro ⟨t, ht, rfl⟩
        exact ⟨⟨t, rfl⟩, ht⟩
    rw [himage]
    exact htimes.image stream

/-- Exact relationship between the two papers' noisy presentations. -/
theorem noisyEnumeration_iff_injective_noisyPresentation
    (stream : Stream α) (L : Language α) :
    NoisyEnumeration stream L ↔
      Function.Injective stream ∧
        GenLimit.NoisyExamples.NoisyPresentation stream L := by
  constructor
  · rintro ⟨hinjective, hcover, hfinite⟩
    exact
      ⟨hinjective, hcover,
        (finite_range_diff_iff_hasFiniteNoise_of_injective
          hinjective).mp hfinite⟩
  · rintro ⟨hinjective, hcover, hnoise⟩
    exact
      ⟨hinjective, hcover,
        (finite_range_diff_iff_hasFiniteNoise_of_injective
          hinjective).mpr hnoise⟩

/-- Paper06's repetition-robust noisy-limit guarantee implies Paper12's
injective-enumeration guarantee.  The converse is intentionally not stated. -/
theorem p06_noisyLimit_implies_p12_noisyLimit
    {C : LanguageClass α}
    (h : GenLimit.NoisyExamples.NoisilyGeneratableInLimit C) :
    GenLimit.NoiseLossFeedback.NoisilyGeneratableInLimit C := by
  obtain ⟨gen, hgen⟩ := h
  refine ⟨gen, ?_⟩
  intro L hLC stream henumeration
  have hpresentation :
      GenLimit.NoisyExamples.NoisyPresentation stream L :=
    (noisyEnumeration_iff_injective_noisyPresentation stream L).mp
      henumeration |>.2
  obtain ⟨T, hT⟩ := hgen L hLC stream hpresentation
  refine ⟨T, ?_⟩
  intro t ht
  exact
    (correctAt_iff_generic_succ gen L stream t).mpr
      (hT (t + 1) (by omega))

/-- Theorem 4.6 of Paper12 and Theorem 3.1 of Paper06 have the same
class-intersection invariant. -/
theorem uniformlyWithoutSamples_iff_uniformNoiseIndependent
    [Countable α] [Infinite α]
    (C : LanguageClass α) (hUUS : UUS C) :
    UniformlyGeneratableWithoutSamples C ↔
      GenLimit.NoisyExamples.UniformNoiseIndependentGeneratable C :=
  (theorem_4_6 C).trans
    (GenLimit.NoisyExamples.theorem_3_1 hUUS).symm

end GenLimit.NoiseLossFeedback
