import GenLimit.Paper02_LearningTheory.EventuallyUnboundedClosure
import GenLimit.Paper02_LearningTheory.PromptedDefinitions

/-! # Finite-universe boundary of the separation theorems -/

namespace GenLimit.LiRamanTewari

/-- On a finite universe the class-wide threshold one greater than the
universe cardinality is unreachable on every stream. -/
theorem finiteUniverse_uniform [Nonempty α] [Finite α] (H : Generic.LanguageClass α) :
    UniformlyGeneratable H := by
  classical
  letI := Fintype.ofFinite α
  refine ⟨fun _ _ => Classical.arbitrary α, Fintype.card α + 1, ?_⟩
  intro L _ s _ t ht
  have hle := Finset.card_le_univ (Generic.sample s t)
  omega

/-- The prompted threshold has the same finite-universe obstruction for
every prompt type, even when the space of prompts is infinite. -/
theorem finiteUniverse_promptedUniform [Nonempty α] [Finite α] (H : MulticlassHypothesisClass α ι) :
    PromptedUniformlyGeneratable H := by
  classical
  letI := Fintype.ofFinite α
  refine ⟨fun _ _ => Classical.arbitrary α, Fintype.card α + 1, ?_⟩
  intro h _ s _ y t ht
  have hle := Finset.card_le_univ (promptedSample h s y t)
  omega

/-- Under the standing UUS hypothesis a finite universe forces the class
to be empty, and Definition C.1 then holds vacuously. -/
theorem finiteUniverse_euc [Finite α] (H : Generic.LanguageClass α) (h : UUS H) :
    EventuallyUnboundedClosure H := by
  intro L hL
  exact (h L hL L.toFinite).elim

end GenLimit.LiRamanTewari
