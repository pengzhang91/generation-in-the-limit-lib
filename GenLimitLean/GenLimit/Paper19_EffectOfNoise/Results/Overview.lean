import GenLimit.Paper19_EffectOfNoise.Nonuniform
import GenLimit.Paper19_EffectOfNoise.EquivTransport

/-!
# Paper 19: main-results overview

This module is the public results facade for Li--Zhang,
*Characterizing the Effect of Noise in Language Generation in the Limit*
(arXiv:2601.21237v2).  It exposes one stable, source-numbered declaration for
each headline theorem.  Every declaration below is a thin wrapper around the
canonical proof modules; no proof is duplicated here.

## Scope and qualifications

The source works with infinite languages over a countable universe.  The
generic wrappers therefore expose `[Countable α]`, `[Nonempty α]`, and
`AllLanguagesInfinite C` explicitly.  The development is semantic and uses
classical choice; it does not claim an extracted executable implementation or
running-time bound.

Theorems 2.18 and 2.19 each combine two kinds of claim in the source: three
equivalent conditions for an arbitrary class, followed by existence of a
noiseless/noisy separating class.  Their wrappers preserve that packaging by
conjoining the generic equivalences with an existential witness on the
paper's literal universe `ℕ × ℕ`.

Theorem 2.17 uses the version of Algorithm 1 that retains rejected scan
iterations, then transports the resulting column construction to the exact
source universe.  The accepted-update compression remains available in the
canonical proof modules as an equivalent semantic proof.
-/

namespace GenLimit.QuantifyingNoise.Results

open GenLimit.Generic

/-- Theorem 2.16: all positive finite noise levels collapse to level one for
both uniform and non-uniform generation. -/
theorem theorem_2_16
    [Countable α] [Nonempty α]
    {C : LanguageClass α}
    (hInfinite : AllLanguagesInfinite C)
    {i : ℕ} (hi : 1 ≤ i) :
    (UniformGeneratableAtNoiseLevel C i ↔
        UniformGeneratableAtNoiseLevel C 1) ∧
      (NonuniformGeneratableAtNoiseLevel C i ↔
        NonuniformGeneratableAtNoiseLevel C 1) :=
  GenLimit.QuantifyingNoise.theorem_2_16 hInfinite hi

/-- Theorem 2.17: a class over the paper's literal universe is uniformly
generatable without noise but not non-uniformly generatable with one noisy
value.  The witness uses the full rejected-iteration scan for Algorithm 1. -/
theorem theorem_2_17 :
    ∃ C : LanguageClass PaperColumnPoint,
      UniformGeneratableAtNoiseLevel C 0 ∧
        ¬NonuniformGeneratableAtNoiseLevel C 1 :=
  ⟨paperColumnUnionClass,
    GenLimit.QuantifyingNoise.theorem_2_17_paper_rejectedScan⟩

/-- Theorem 2.18: the three uniform noisy-generation conditions are
equivalent, and noiseless uniform generation is strictly stronger. -/
theorem theorem_2_18
    [Countable α] [Nonempty α]
    {C : LanguageClass α}
    (hInfinite : AllLanguagesInfinite C) :
    ((FiniteNoisyClosureDimensionAt C 1 ↔
        ∀ i : ℕ, 1 ≤ i → UniformGeneratableAtNoiseLevel C i) ∧
      (FiniteNoisyClosureDimensionAt C 1 ↔
        UniformNoiseDependentGeneratable C)) ∧
      ∃ D : LanguageClass PaperColumnPoint,
        UniformGeneratableAtNoiseLevel D 0 ∧
          ¬UniformGeneratableAtNoiseLevel D 1 :=
  ⟨GenLimit.QuantifyingNoise.theorem_2_18_uniform_equivalences_full
      hInfinite,
    ⟨paperColumnUnionClass,
      GenLimit.QuantifyingNoise.theorem_2_18_separation_clause_paper⟩⟩

/-- Theorem 2.19: the three non-uniform noisy-generation conditions are
equivalent, and noiseless non-uniform generation is strictly stronger. -/
theorem theorem_2_19
    [Countable α] [Nonempty α]
    {C : LanguageClass α}
    (hInfinite : AllLanguagesInfinite C) :
    ((HasFiniteDimensionExhaustionAt C 1 ↔
        ∀ i : ℕ, 1 ≤ i → NonuniformGeneratableAtNoiseLevel C i) ∧
      (HasFiniteDimensionExhaustionAt C 1 ↔
        NonuniformNoiseDependentGeneratable C)) ∧
      ∃ D : LanguageClass PaperColumnPoint,
        NonuniformGeneratableAtNoiseLevel D 0 ∧
          ¬NonuniformGeneratableAtNoiseLevel D 1 :=
  ⟨GenLimit.QuantifyingNoise.theorem_2_19_nonuniform_equivalences_full
      hInfinite,
    ⟨paperColumnUnionClass,
      GenLimit.QuantifyingNoise.theorem_2_19_separation_clause_paper⟩⟩

end GenLimit.QuantifyingNoise.Results
