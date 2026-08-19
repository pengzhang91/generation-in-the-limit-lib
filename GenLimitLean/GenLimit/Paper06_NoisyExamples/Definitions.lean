import GenLimit.Support.ClassIntersection
import GenLimit.Core.ClassGeneration

/-!
# #06 Noisy Examples: semantic definitions

Paper-local definitions used across the formalization of Ananth Raman and
Vinod Raman, *Generation from Noisy Examples* (ICML 2025 /
arXiv:2501.04179v2).
-/

namespace GenLimit.NoisyExamples

/-- The set of examples common to every hypothesis in the class. -/
abbrev commonIntersection
    (H : GenLimit.Generic.LanguageClass α) : GenLimit.Generic.Language α :=
  GenLimit.Support.classIntersection H

/-- A stream has finite noise relative to `L` when it contains only finitely
many examples outside `L`. -/
def HasFiniteNoise
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) : Prop :=
  {t | stream t ∉ L}.Finite

/-- `G` satisfies Definition 2.4 at the distinct-example threshold `d`. -/
def IsUniformNoiseIndependentGeneratorAt
    (gen : GenLimit.Generic.Generator α)
    (H : GenLimit.Generic.LanguageClass α) (d : ℕ) : Prop :=
  ∀ L, L ∈ H → ∀ stream : GenLimit.Generic.Stream α,
    HasFiniteNoise stream L →
    ∀ t, (GenLimit.Generic.sample stream t).card = d →
      ∀ s, t ≤ s → GenLimit.Generic.CorrectAt gen L stream s

/-- Uniform noise-independent generatability, Definition 2.4. -/
def UniformNoiseIndependentGeneratable
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  ∃ gen : GenLimit.Generic.Generator α, ∃ d : ℕ,
    IsUniformNoiseIndependentGeneratorAt gen H d

/-- The examples of `S` that belong to `L`. -/
noncomputable def positivePart
    (S : Finset α) (L : GenLimit.Generic.Language α) : Finset α := by
  classical
  exact S.filter fun x => x ∈ L

/-- The examples of `S` that do not belong to `L`. -/
noncomputable def negativePart
    (S : Finset α) (L : GenLimit.Generic.Language α) : Finset α := by
  classical
  exact S.filter fun x => x ∉ L

/-- The hypotheses that disagree with at most `n` distinct examples in `S`.
This is `H(x_1:d; n)` from the preliminaries, for a distinct sequence with
underlying set `S`. -/
def noisyVersionSpace
    (H : GenLimit.Generic.LanguageClass α) (S : Finset α) (n : ℕ) :
    Set (GenLimit.Generic.Language α) :=
  {L | L ∈ H ∧ S.card ≤ (positivePart S L).card + n}

/-- The intersection of the supports in a nonempty noisy version space. -/
def noisyCommonCore
    (H : GenLimit.Generic.LanguageClass α) (S : Finset α) (n : ℕ) :
    GenLimit.Generic.Language α :=
  {x | ∀ L, L ∈ noisyVersionSpace H S n → x ∈ L}

/-- The paper's noisy closure, with `none` representing `bot`. -/
noncomputable def noisyClosure
    (H : GenLimit.Generic.LanguageClass α) (S : Finset α) (n : ℕ) :
    Option (GenLimit.Generic.Language α) := by
  classical
  exact if (noisyVersionSpace H S n).Nonempty then
    some (noisyCommonCore H S n)
  else none

/-- A witness that the `n`-noisy closure dimension is at least `d`, using a
finset as the underlying set of the paper's `d` distinct examples. -/
def NoisyClosureWitnessAt
    (H : GenLimit.Generic.LanguageClass α) (n d : ℕ) : Prop :=
  ∃ S : Finset α, S.card = d ∧
    (noisyVersionSpace H S n).Nonempty ∧
    (noisyCommonCore H S n).Finite

/-- Definition 3.2's assertion `NC_n(H) < infinity`. -/
def FiniteNoisyClosureDimensionAt
    (H : GenLimit.Generic.LanguageClass α) (n : ℕ) : Prop :=
  ∃ D : ℕ, ∀ d : ℕ, D < d → ¬NoisyClosureWitnessAt H n d

/-- A stream has at most `n` noisy occurrences relative to `L`.  The finset
`F` is exactly the set of time indices whose examples lie outside `L`, so
this is the finite indicator sum in Definition 2.5. -/
def HasNoiseAtMost
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) (n : ℕ) : Prop :=
  ∃ F : Finset ℕ, F.card ≤ n ∧ ∀ t, t ∈ F ↔ stream t ∉ L

/-- Definition 2.5 at a fixed generator.  The quantifier order is
`for every n, there exists d, for every target and every stream ...`. -/
def IsUniformNoiseDependentGenerator
    (gen : GenLimit.Generic.Generator α)
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  ∀ n : ℕ, ∃ d : ℕ, ∀ L, L ∈ H →
    ∀ stream : GenLimit.Generic.Stream α, HasNoiseAtMost stream L n →
      ∀ t, (GenLimit.Generic.sample stream t).card = d →
        ∀ s, t ≤ s → GenLimit.Generic.CorrectAt gen L stream s

/-- Uniform noise-dependent generatability, Definition 2.5. -/
def UniformNoiseDependentGeneratable
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  ∃ gen : GenLimit.Generic.Generator α,
    IsUniformNoiseDependentGenerator gen H

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

end GenLimit.NoisyExamples
