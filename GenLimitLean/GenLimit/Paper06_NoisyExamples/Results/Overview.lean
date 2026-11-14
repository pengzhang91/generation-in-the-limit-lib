import GenLimit.Paper06_NoisyExamples.UniformIndependent
import GenLimit.Paper06_NoisyExamples.NoisyClosure
import GenLimit.Paper06_NoisyExamples.FiniteClasses
import GenLimit.Paper06_NoisyExamples.Nonuniform
import GenLimit.Paper06_NoisyExamples.NoiselessRobustification
import GenLimit.Paper06_NoisyExamples.FiniteUnionLimit
import GenLimit.Paper06_NoisyExamples.Separation
import GenLimit.Paper06_NoisyExamples.AlternatePositive
import GenLimit.Paper06_NoisyExamples.NonuniformIndependent

/-!
# Paper 06: main-results overview

This is the public results facade for Raman--Raman, *Generation from Noisy
Examples*.  The four main-text theorems below state their assumptions and
conclusions explicitly and delegate their proofs to the canonical modules.

The statements use the paper's semantic interface and make the ambient-space
assumptions explicit.  No runtime or extracted implementation is claimed.
-/

namespace GenLimit.NoisyExamples.Results

/-- Theorem 3.1: uniform noise-independent generation is equivalent to an
infinite intersection of all languages in the class.

`[Infinite α]` makes explicit the ambient-space assumption used by the
necessity proof. -/
theorem theorem_3_1
    {α : Type*} [Countable α] [Infinite α]
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : GenLimit.Generic.UUS H) :
    UniformNoiseIndependentGeneratable H ↔
      (commonIntersection H).Infinite :=
  GenLimit.NoisyExamples.theorem_3_1 hUUS

/-- Theorem 3.3: uniform noise-dependent generation is equivalent to finite
noisy closure dimension at every noise level.

`[Nonempty α]` ensures that a total generator can return an example even
when the language class is empty. -/
theorem theorem_3_3
    {α : Type*} [Countable α] [Nonempty α]
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : GenLimit.Generic.UUS H) :
    UniformNoiseDependentGeneratable H ↔
      ∀ n : ℕ, FiniteNoisyClosureDimensionAt H n :=
  GenLimit.NoisyExamples.theorem_3_3 hUUS

/-- Theorem 3.9: noiseless non-uniform generation implies noisy generation
in the limit. -/
theorem theorem_3_9
    {α : Type*} [Countable α]
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : GenLimit.Generic.UUS H)
    (hNonuniform : GenLimit.Generic.NonuniformlyGeneratable H) :
    NoisilyGeneratableInLimit H :=
  GenLimit.NoisyExamples.theorem_3_9 hUUS hNonuniform

/-- Theorem 3.10: a finite union of uniformly noise-independent generatable
classes is noisily generatable in the limit.

`[Infinite α]` records the ambient-space assumption used to obtain each
component's infinite common intersection. -/
theorem theorem_3_10
    {α : Type*} [Countable α] [Infinite α]
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : GenLimit.Generic.UUS H)
    (hcover : ∃ k : ℕ,
      ∃ classes : Fin k → GenLimit.Generic.LanguageClass α,
        GenLimit.Generic.IsFiniteCover H classes ∧
        ∀ i, UniformNoiseIndependentGeneratable (classes i)) :
    NoisilyGeneratableInLimit H :=
  GenLimit.NoisyExamples.theorem_3_10 hUUS hcover

end GenLimit.NoisyExamples.Results
