import GenLimit.Paper12_NoiseLossAndFeedback.Results.Witnesses
import GenLimit.Paper12_NoiseLossAndFeedback.Bridges.NoisyExamples
import GenLimit.Paper12_NoiseLossAndFeedback.NoSampleCharacterization
import GenLimit.Paper12_NoiseLossAndFeedback.UnknownFiniteNoiseSeparation
import GenLimit.Paper12_NoiseLossAndFeedback.FeedbackIdentification

/-!
# Main theorems for Noise, Loss, and Feedback

This overview contains only the paper's main summary Theorems 1.1--1.8,
with explicit statements and proofs delegated to the detailed modules.
Supporting witness constructions for Theorems 1.1 and 1.7 are in
`Results.Witnesses`. Theorem 1.8 concerns identification rather than generation
and is proved in `FeedbackIdentification`.
-/

namespace GenLimit.NoiseLossFeedback.Results

open GenLimit.Generic

/-- Summary Theorem 1.1: the first class is non-uniformly generatable
(also without samples), the second is uniformly generatable (also without
samples), but their union is not generatable in the limit.

The with-sample clauses use the paper's standard repetition-free model.
`GeneratableInLimitWithoutSamples` expresses non-uniform generation without
samples: there is no input enumeration on which the threshold could depend.
The paper's integer universe is encoded bijectively by `ℕ`. -/
theorem theorem_1_1 :
    ∃ C₁ C₂ : LanguageClass ℕ,
      (NonuniformlyGeneratableWithoutRepetitions C₁ ∧
        GeneratableInLimitWithoutSamples C₁) ∧
      (UniformlyGeneratableWithoutRepetitions C₂ ∧
        UniformlyGeneratableWithoutSamples C₂) ∧
      ¬GeneratableInLimitWithoutRepetitions (C₁ ∪ C₂) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hUnion⟩ :=
    GenLimit.NoiseLossFeedback.theorem_1_1_with_and_without_samples
  exact ⟨C₁, C₂, ⟨hC₁.2, hC₁.1⟩, ⟨hC₂.2, hC₂.1⟩, hUnion⟩

/-- Summary Theorem 1.2: finite-noise generation is equivalent to generation
without samples, in the uniform and non-uniform settings. -/
theorem theorem_1_2
    (C : LanguageClass ℕ) (hUUS : UUS C) :
    (UniformlyNoisilyGeneratable C ↔
        UniformlyGeneratableWithoutSamples C) ∧
      (NonuniformlyNoisilyGeneratable C ↔
        GeneratableInLimitWithoutSamples C) :=
  ⟨theorem_4_4 C hUUS, theorem_4_5 C hUUS⟩

/-- Summary Theorem 1.3: no-sample generation is characterized by an
increasing cover with infinite common cores. -/
theorem theorem_1_3
    [Countable α]
    (C : LanguageClass α) :
    GeneratableInLimitWithoutSamples C ↔
      HasIncreasingInfiniteCoreCover C :=
  GenLimit.NoiseLossFeedback.theorem_1_3 C

/-- Summary Theorem 1.4: ordinary generators remain correct under arbitrary
infinite omissions. -/
theorem theorem_1_4
    [Countable α] {C : LanguageClass α} (hUUS : UUS C) :
    (∀ gen, IsUniformGenerator gen C →
        IsUniformInfiniteOmissionGenerator gen C) ∧
      (∀ gen, IsNonuniformGenerator gen C →
        IsNonuniformInfiniteOmissionGenerator gen C) := by
  constructor
  · intro gen hgen
    exact theorem_4_11 hUUS hgen
  · intro gen hgen
    exact theorem_4_12 hUUS hgen

/-- Summary Theorem 1.5: one class realizes both adjacent finite-omission and
adjacent known-finite-noise separations. -/
theorem theorem_1_5 :
    ∀ i : ℕ,
      ∃ C : LanguageClass ℤ,
        UUS C ∧
          GeneratableInLimitWithOmissions C i ∧
            ¬GeneratableInLimitWithOmissions C (i + 1) ∧
              GeneratableInLimitWithNoiseLevel C i ∧
                ¬GeneratableInLimitWithNoiseLevel C (i + 1) :=
  GenLimit.NoiseLossFeedback.theorem_1_5

/-- Summary Theorem 1.6: success at every known finite noise level does not
imply generation under an unknown finite amount of noise. -/
theorem theorem_1_6 :
    ∃ C : LanguageClass ℤ,
      (∀ i : ℕ, GeneratableInLimitWithNoiseLevel C i) ∧
        ¬NoisilyGeneratableInLimit C :=
  GenLimit.NoiseLossFeedback.theorem_1_6

/-- Summary Theorem 1.7 in Definition 6.1's literal interface: infinite
mandatory-query feedback is strictly stronger than every fixed finite query
budget. -/
theorem theorem_1_7 :
    ∃ C : LanguageClass ℕ,
      GeneratableInLimitWithTotalFeedback C ∧
        ¬GeneratableInLimitWithoutRepetitions C ∧
        ∀ budget : ℕ, ¬GeneratableInLimitWithQueries C budget :=
  ⟨theoremOneFirstClass ∪ theoremOneSecondClass,
    theorem_1_7_total_feedback_witness⟩

/-- Summary Theorem 1.8: every explicitly indexed countable language family
is non-uniformly identifiable with membership feedback. -/
theorem theorem_1_8 (C : GenLimit.Generic.LanguageFamily ℕ) :
    NonuniformlyIdentifiableWithFeedback C :=
  GenLimit.NoiseLossFeedback.theorem_1_8 C

end GenLimit.NoiseLossFeedback.Results
