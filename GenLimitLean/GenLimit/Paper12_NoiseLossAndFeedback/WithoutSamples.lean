import GenLimit.Paper12_NoiseLossAndFeedback.Common

/-!
# Noise, Loss, and Feedback: generation without samples

Source: Bai--Panigrahi--Zhang, *Language Generation in the Limit:
Noise, Loss, and Feedback*, arXiv:2507.15319v2, Definitions 4.1--4.3 and
Theorem 4.6.

The paper's generator without samples is an injective stream.  `output` below
is therefore not an arbitrary stream accompanied by a later side condition:
injectivity is part of the structure, exactly as in Definition 4.1.
-/

namespace GenLimit.NoiseLossFeedback

open GenLimit.Generic

/-- Definition 4.1: a generator without samples is an injective output
sequence. -/
structure WithoutSamplesGenerator (α : Type*) where
  output : ℕ → α
  injective' : Function.Injective output

/-- Definition 4.2 at a fixed generator. -/
def UniformlyGeneratesWithoutSamples
    (gen : WithoutSamplesGenerator α)
    (C : LanguageClass α) : Prop :=
  ∃ T : ℕ, ∀ L, L ∈ C → ∀ t, T ≤ t → gen.output t ∈ L

/-- Uniform generation without samples, existentially quantified over the
generator. -/
def UniformlyGeneratableWithoutSamples
    (C : LanguageClass α) : Prop :=
  ∃ gen : WithoutSamplesGenerator α,
    UniformlyGeneratesWithoutSamples gen C

/-- Definition 4.3 at a fixed generator.  The threshold may depend on the
target language. -/
def GeneratesInLimitWithoutSamples
    (gen : WithoutSamplesGenerator α)
    (C : LanguageClass α) : Prop :=
  ∀ L, L ∈ C → ∃ T : ℕ, ∀ t, T ≤ t → gen.output t ∈ L

/-- Generation in the limit without samples. -/
def GeneratableInLimitWithoutSamples
    (C : LanguageClass α) : Prop :=
  ∃ gen : WithoutSamplesGenerator α,
    GeneratesInLimitWithoutSamples gen C

/-- The paper's common intersection `⋂_{L ∈ C} L`. -/
abbrev languageIntersection (C : LanguageClass α) : Set α :=
  GenLimit.Support.classIntersection C

/-- The range of the output tail beginning at `T`. -/
def outputTail
    (gen : WithoutSamplesGenerator α) (T : ℕ) : Set α :=
  Set.range fun n => gen.output (T + n)

theorem outputTail_infinite
    (gen : WithoutSamplesGenerator α) (T : ℕ) :
    (outputTail gen T).Infinite := by
  apply Set.infinite_range_of_injective
  intro m n hmn
  have hadd : T + m = T + n := gen.injective' hmn
  omega

theorem outputTail_subset_languageIntersection
    {gen : WithoutSamplesGenerator α}
    {C : LanguageClass α} {T : ℕ}
    (hT : ∀ L, L ∈ C → ∀ t, T ≤ t → gen.output t ∈ L) :
    outputTail gen T ⊆ languageIntersection C := by
  rintro x ⟨n, rfl⟩
  intro L hLC
  exact hT L hLC (T + n) (Nat.le_add_right T n)

/-- Necessity in Theorem 4.6. -/
theorem uniform_withoutSamples_implies_infinite_intersection
    {C : LanguageClass α}
    (h : UniformlyGeneratableWithoutSamples C) :
    (languageIntersection C).Infinite := by
  obtain ⟨gen, T, hT⟩ := h
  exact (outputTail_infinite gen T).mono
    (outputTail_subset_languageIntersection hT)

/-- Sufficiency in Theorem 4.6.  The fixed repetition-free enumeration of the
common intersection works from time zero. -/
theorem infinite_intersection_implies_uniform_withoutSamples
    [Countable α]
    {C : LanguageClass α}
    (h : (languageIntersection C).Infinite) :
    UniformlyGeneratableWithoutSamples C := by
  let gen : WithoutSamplesGenerator α :=
    { output :=
        GenLimit.Support.infiniteEnumeration
          (languageIntersection C) h
      injective' :=
        GenLimit.Support.infiniteEnumeration_injective
          (languageIntersection C) h }
  refine ⟨gen, 0, ?_⟩
  intro L hLC t _ht
  exact
    (GenLimit.Support.infiniteEnumeration_mem
      (languageIntersection C) h t) L hLC

/-- Theorem 4.6: uniform generation without samples is equivalent to an
infinite common intersection. -/
theorem theorem_4_6
    [Countable α]
    (C : LanguageClass α) :
    UniformlyGeneratableWithoutSamples C ↔
      (languageIntersection C).Infinite :=
  ⟨uniform_withoutSamples_implies_infinite_intersection,
    infinite_intersection_implies_uniform_withoutSamples⟩

end GenLimit.NoiseLossFeedback
