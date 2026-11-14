import GenLimit.Paper12_NoiseLossAndFeedback.Relationships
import GenLimit.Paper12_NoiseLossAndFeedback.InfiniteFeedback
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteFeedback
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Results.Overview
import Mathlib.Logic.Equiv.Nat

/-!
# Witnesses for Noise, Loss, and Feedback

Supporting constructions and proofs for summary Theorems 1.1 and 1.7.
They reuse the concurrent Paper10 witness, transported from `ℤ` to the
equivalent universe `ℕ`, without duplicating the diagonal construction.
The main theorem statements are collected in `Results.Overview`.
-/

namespace GenLimit.NoiseLossFeedback

open GenLimit.Generic

/-! ## Theorem 1.1 from the concurrent Paper10 witness -/

/-- The countable non-uniform component of the fixed Theorem 1.1 witness. -/
def theoremOneFirstClass : LanguageClass ℕ :=
  GenLimit.Support.renameLanguageClass Equiv.intEquivNat
    GenLimit.UnionClosedness.theorem43SecondClass

/-- The uncountable uniform component of the fixed Theorem 1.1 witness. -/
def theoremOneSecondClass : LanguageClass ℕ :=
  GenLimit.Support.renameLanguageClass Equiv.intEquivNat
    GenLimit.UnionClosedness.theorem43FirstClass

/-- A strengthened fixed witness for Theorem 1.1, including the cardinality
properties inherited from the concurrent Paper10 construction. -/
theorem theorem_1_1_strong_witness :
    theoremOneFirstClass.Countable ∧
      GeneratableInLimitWithoutSamples theoremOneFirstClass ∧
      ¬theoremOneSecondClass.Countable ∧
      UniformlyGeneratableWithoutSamples theoremOneSecondClass ∧
      ¬GeneratableInLimitWithoutRepetitions
        (theoremOneFirstClass ∪ theoremOneSecondClass) := by
  let e : ℤ ≃ ℕ := Equiv.intEquivNat
  have hsource := GenLimit.UnionClosedness.theorem_3_2_witness
  have hfirstAutonomous :
      GenLimit.UnionClosedness.NonuniformlyGeneratableWithoutAdversaryInput
        theoremOneFirstClass := by
    exact nonuniformWithoutAdversaryInput_rename e hsource.2.1
  have hsecondAutonomous :
      GenLimit.UnionClosedness.UniformlyGeneratableWithoutAdversaryInput
        theoremOneSecondClass := by
    exact uniformWithoutAdversaryInput_rename e hsource.2.2.2.1
  have hlowerRenamed :
      ¬GenLimit.UnionClosedness.GeneratableInLimitOnInjectivePresentations
        (theoremOneFirstClass ∪ theoremOneSecondClass) := by
    have h :=
      not_generatableOnInjectivePresentations_rename e
        hsource.2.2.2.2
    rw [GenLimit.Support.renameLanguageClass_union] at h
    exact h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact
      (GenLimit.Support.renameLanguageClass_countable_iff e
        GenLimit.UnionClosedness.theorem43SecondClass).mpr hsource.1
  · exact
      (generatableInLimitWithoutSamples_iff_withoutAdversaryInput
        theoremOneFirstClass).mpr hfirstAutonomous
  · intro hcountable
    exact hsource.2.2.1
      ((GenLimit.Support.renameLanguageClass_countable_iff e
        GenLimit.UnionClosedness.theorem43FirstClass).mp hcountable)
  · exact
      (uniformlyGeneratableWithoutSamples_iff_withoutAdversaryInput
        theoremOneSecondClass).mpr hsecondAutonomous
  · intro hgen
    exact hlowerRenamed
      ((generatableInLimitWithoutRepetitions_iff_onInjectivePresentations
        (theoremOneFirstClass ∪ theoremOneSecondClass)).mp hgen)

/-- A consequence of Theorem 1.1 making both positive guarantees explicit:
each component is generatable both without samples and in the standard model
with adversarial samples.  The union lower bound already holds in the latter,
more permissive model. -/
theorem theorem_1_1_with_and_without_samples :
    ∃ C₁ C₂ : LanguageClass ℕ,
      (GeneratableInLimitWithoutSamples C₁ ∧
        NonuniformlyGeneratableWithoutRepetitions C₁) ∧
      (UniformlyGeneratableWithoutSamples C₂ ∧
        UniformlyGeneratableWithoutRepetitions C₂) ∧
      ¬GeneratableInLimitWithoutRepetitions (C₁ ∪ C₂) := by
  exact
    ⟨theoremOneFirstClass, theoremOneSecondClass,
      ⟨theorem_1_1_strong_witness.2.1,
        generatableInLimitWithoutSamples_implies_withSamples
          theorem_1_1_strong_witness.2.1⟩,
      ⟨theorem_1_1_strong_witness.2.2.2.1,
        uniformlyGeneratableWithoutSamples_implies_withSamples
          theorem_1_1_strong_witness.2.2.2.1⟩,
      theorem_1_1_strong_witness.2.2.2.2⟩

/-! ## Theorem 1.7: infinite feedback is strictly stronger -/

/-- A two-component sequence realizing a countable cover. -/
def twoClassFeedbackCover
    (C₁ C₂ : LanguageClass ℕ) : ℕ → LanguageClass ℕ :=
  fun i => if i = 0 then C₁ else C₂

theorem twoClassFeedbackCover_isCover
    (C₁ C₂ : LanguageClass ℕ) :
    IsCountableFeedbackCover (C₁ ∪ C₂)
      (twoClassFeedbackCover C₁ C₂) := by
  unfold IsCountableFeedbackCover
  ext L
  constructor
  · rintro (hL | hL)
    · exact Set.mem_iUnion.mpr ⟨0, by simpa [twoClassFeedbackCover]⟩
    · exact Set.mem_iUnion.mpr ⟨1, by simpa [twoClassFeedbackCover]⟩
  · intro hL
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hL
    by_cases hzero : i = 0
    · left
      simpa [twoClassFeedbackCover, hzero] using hi
    · right
      simpa [twoClassFeedbackCover, hzero] using hi

/-- The fixed Theorem 1.1 union has an infinite-feedback generator, but no
generator using any fixed finite membership-query budget. -/
theorem theorem_1_7_witness :
    GeneratableInLimitWithFeedback
        (theoremOneFirstClass ∪ theoremOneSecondClass) ∧
      ¬GeneratableInLimitWithoutRepetitions
        (theoremOneFirstClass ∪ theoremOneSecondClass) ∧
      ∀ budget : ℕ,
        ¬GeneratableInLimitWithQueries
          (theoremOneFirstClass ∪ theoremOneSecondClass) budget := by
  let e : ℤ ≃ ℕ := Equiv.intEquivNat
  have hsource := GenLimit.UnionClosedness.theorem_3_2_witness
  have hfirstAutonomous :
      GenLimit.UnionClosedness.NonuniformlyGeneratableWithoutAdversaryInput
        theoremOneFirstClass :=
    nonuniformWithoutAdversaryInput_rename e hsource.2.1
  have hsecondAutonomous :
      GenLimit.UnionClosedness.UniformlyGeneratableWithoutAdversaryInput
        theoremOneSecondClass :=
    uniformWithoutAdversaryInput_rename e hsource.2.2.2.1
  have hfirstNonuniform :
      NonuniformlyGeneratable theoremOneFirstClass :=
    GenLimit.UnionClosedness.nonuniformlyGeneratable_of_withoutAdversaryInput
      hfirstAutonomous
  have hsecondNonuniform :
      NonuniformlyGeneratable theoremOneSecondClass :=
    uniform_implies_nonuniform
      (GenLimit.UnionClosedness.uniformlyGeneratable_of_withoutAdversaryInput
        hsecondAutonomous)
  have hUUS : UUS (theoremOneFirstClass ∪ theoremOneSecondClass) := by
    intro L hL
    rcases hL with hL | hL
    · exact
        ((GenLimit.Support.renameLanguageClass_uus_iff e
          GenLimit.UnionClosedness.theorem43SecondClass).mpr
          GenLimit.UnionClosedness.theorem_3_2_witness_uus.1) L hL
    · exact
        ((GenLimit.Support.renameLanguageClass_uus_iff e
          GenLimit.UnionClosedness.theorem43FirstClass).mpr
          GenLimit.UnionClosedness.theorem_3_2_witness_uus.2) L hL
  have hcomponents :
      ∀ i,
        NonuniformlyGeneratable
          (twoClassFeedbackCover theoremOneFirstClass
            theoremOneSecondClass i) := by
    intro i
    by_cases hzero : i = 0
    · simpa [twoClassFeedbackCover, hzero] using hfirstNonuniform
    · simpa [twoClassFeedbackCover, hzero] using hsecondNonuniform
  have hfeedback :
      GeneratableInLimitWithFeedback
        (theoremOneFirstClass ∪ theoremOneSecondClass) :=
    corollary_6_4 hUUS
      (twoClassFeedbackCover_isCover
        theoremOneFirstClass theoremOneSecondClass)
      hcomponents
  have hnoFeedback := theorem_1_1_strong_witness.2.2.2.2
  refine ⟨hfeedback, hnoFeedback, ?_⟩
  intro budget hfinite
  exact hnoFeedback
    ((finiteFeedback_iff_noFeedback
      (theoremOneFirstClass ∪ theoremOneSecondClass) budget).mp hfinite)

/-- The fixed Theorem 1.7 witness in Definition 6.1's literal interface:
the positive generator asks one membership query on every round. -/
theorem theorem_1_7_total_feedback_witness :
    GeneratableInLimitWithTotalFeedback
        (theoremOneFirstClass ∪ theoremOneSecondClass) ∧
      ¬GeneratableInLimitWithoutRepetitions
        (theoremOneFirstClass ∪ theoremOneSecondClass) ∧
      ∀ budget : ℕ,
        ¬GeneratableInLimitWithQueries
          (theoremOneFirstClass ∪ theoremOneSecondClass) budget := by
  refine ⟨?_, theorem_1_7_witness.2⟩
  exact generatableInLimitWithTotalFeedback_of_optional
    (theoremOneFirstClass ∪ theoremOneSecondClass) 0
    theorem_1_7_witness.1

end GenLimit.NoiseLossFeedback
