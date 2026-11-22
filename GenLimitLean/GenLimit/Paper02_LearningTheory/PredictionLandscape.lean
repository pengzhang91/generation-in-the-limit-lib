import GenLimit.Paper02_LearningTheory.OnlinePrediction
import GenLimit.Paper02_LearningTheory.PACLower
import GenLimit.Paper02_LearningTheory.PACUpper

/-! # Theorem 4.1 in its two learning models -/

namespace GenLimit.LiRamanTewari

/-- The six witness classes of Appendix A satisfy the distribution-free
IID and causal online predicates of Definitions 2.8 and 2.10. -/
theorem theorem_4_1 :
    (∃ H : Generic.LanguageClass ℤ, H.Countable ∧ UniformlyGeneratable H ∧ ¬PACLearnable H) ∧
    (∃ H : Generic.LanguageClass BlockUniverse, H.Countable ∧ OnlineLearnable H ∧ ¬UniformlyGeneratable H) ∧
    (∃ H : Generic.LanguageClass ℤ, H.Countable ∧ OnlineLearnable H ∧ UniformlyGeneratable H) ∧
    (∃ H : Generic.LanguageClass ThresholdBlockUniverse,
      H.Countable ∧ PACLearnable H ∧ ¬OnlineLearnable H ∧ ¬UniformlyGeneratable H) ∧
    (∃ H : Generic.LanguageClass ℕ, H.Countable ∧ PACLearnable H ∧ UniformlyGeneratable H ∧ ¬OnlineLearnable H) ∧
    (∃ H : Generic.LanguageClass ℕ, H.Countable ∧ ¬PACLearnable H ∧ ¬UniformlyGeneratable H) := by
  obtain ⟨H₂,h₂c,h₂o,h₂g⟩ := theorem_4_1_ii_combinatorial_core
  obtain ⟨H₃,h₃c,h₃o,h₃g⟩ := theorem_4_1_iii_combinatorial_core
  exact ⟨⟨_,finiteAugmentationClass_countable,finiteAugmentationClass_uus_and_uniform.2,
        not_pacLearnable_of_infiniteVC finiteAugmentationClass_infiniteVC⟩,
    ⟨H₂,h₂c,onlineLearnable_of_finiteLittlestone h₂o,h₂g⟩,
    ⟨H₃,h₃c,onlineLearnable_of_finiteLittlestone h₃o,h₃g⟩,
    ⟨_,thresholdBlockClass_countable,thresholdBlockClass_pacLearnable,
      fun h => thresholdBlockClass_not_online ((onlineLearnable_iff_finiteLittlestone _).mp h),
      thresholdBlockClass_not_uniform⟩,
    ⟨_,thresholdClass_countable,thresholdClass_pacLearnable,thresholdClass_uniform,
      fun h => thresholdClass_not_onlineViaLittlestone ((onlineLearnable_iff_finiteLittlestone _).mp h)⟩,
    ⟨_,cofiniteClass_countable,not_pacLearnable_of_infiniteVC cofiniteClass_infiniteVC,
      cofiniteClass_not_uniform⟩⟩

end GenLimit.LiRamanTewari
