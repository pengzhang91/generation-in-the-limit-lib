import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import GenLimit.Paper19_EffectOfNoise.Definitions

/-!
# Papers 12 and 19: the shared fixed-noise interface

Paper 12 and Paper 19 use the same injective, value-bounded noisy
enumerations and the same inclusive-time correctness predicate.  Their
target-uniform fixed-level generator notions are therefore definitionally
the same.  The papers package the surrounding hierarchies differently, so
the bridge is kept here instead of making either paper depend on the other.
-/

namespace GenLimit.Bridge.Paper12ToPaper19

theorem noisyEnumerationWithLevel_iff
    (stream : Generic.Stream α) (L : Generic.Language α) (i : ℕ) :
    NoiseLossFeedback.NoisyEnumerationWithLevel stream L i ↔
      QuantifyingNoise.EnumerationWithNoiseAtMost stream L i :=
  Iff.rfl

theorem correctAt_iff
    (gen : Generic.Generator α) (L : Generic.Language α)
    (stream : Generic.Stream α) (t : ℕ) :
    NoiseLossFeedback.CorrectAt gen L stream t ↔
      QuantifyingNoise.CorrectAt gen L stream t :=
  Iff.rfl

theorem isNonuniformGeneratorWithNoiseLevel_iff
    (gen : Generic.Generator α) (C : Generic.LanguageClass α) (i : ℕ) :
    NoiseLossFeedback.IsNonuniformGeneratorWithNoiseLevel gen C i ↔
      QuantifyingNoise.IsNonuniformGeneratorAtNoiseLevel gen C i :=
  Iff.rfl

theorem nonuniformGeneratableWithNoiseLevel_iff
    (C : Generic.LanguageClass α) (i : ℕ) :
    NoiseLossFeedback.NonuniformGeneratableWithNoiseLevel C i ↔
      QuantifyingNoise.NonuniformGeneratableAtNoiseLevel C i :=
  Iff.rfl

end GenLimit.Bridge.Paper12ToPaper19
