import GenLimit.Paper00A_PositiveDataInference.Semantic.Characterization
import GenLimit.Paper00A_PositiveDataInference.Effective

/-!
# Paper 0A: main-results overview

This public facade exposes thin wrappers for the completed main results of
Dana Angluin, *Inductive Inference of Formal Languages from Positive Data*
(1980). The effective wrappers retain uniform computability of the indexed
family, learner, and Condition 1 enumeration.

The semantic characterization allows arbitrary learners and nonuniform finite
tell-tales. Theorems 2–4 give counterexample families. Theorem 5 proves
identification, consistency, responsiveness, and conservativeness for one
effective machine under Conditions 3 and 5.
-/

namespace GenLimit.Angluin.Results

/-- The non-effective finite-tell-tale characterization underlying the
paper's semantic layer. -/
theorem semantic_characterization
    {α : Type*} [Nonempty α] [Countable α]
    (C : GenLimit.Generic.LanguageFamily α) :
    SemanticallyInferrable C ↔ ConditionTwo C :=
  semanticallyInferrable_iff_conditionTwo C

/-- Theorem 1. An indexed family is effectively inferable exactly when one
computable procedure enumerates a finite tell-tale for each language index. -/
theorem theorem_1 (F : EffectiveIndexedFamily) :
    EffectiveInferrable F ↔ ConditionOne F :=
  theoremOne F

/-- Nonuniform tell-tales can exist for an effectively unlearnable family. -/
theorem theorem_2 :
    ∃ F : EffectiveIndexedFamily, ConditionTwo F.language ∧ ¬ EffectiveInferrable F :=
  theoremTwo

/-- An inferable family can lack uniformly terminating tell-tale output. -/
theorem theorem_3 : ∃ F : EffectiveIndexedFamily,
    EffectiveInferrable F ∧ ¬ ConditionOnePrime F := theoremThree

/-- A family admitting ordinary effective inference can defeat every
conservative inference machine. -/
theorem theorem_4 : ∃ F : EffectiveIndexedFamily, EffectiveInferrable F ∧
    ¬ ∃ M : InferenceMachine, M.Identifies F ∧ M.Conservative F := theoremFour

/-- Conditions 3 and 5 give one machine with all four guarantees. -/
theorem theorem_5 (F : EffectiveIndexedFamily)
    (h3 : ConditionThree F.language) (h5 : ConditionFive F) :
    ∃ M : InferenceMachine, M.Identifies F ∧ M.Consistent F ∧ M.Responsive F ∧
      M.Conservative F := theoremFive F h3 h5

/-- Corollary 1. In an effectively inferable family, every language has a finite tell-tale. -/
theorem corollary_1 (F : EffectiveIndexedFamily) :
    EffectiveInferrable F → ConditionTwo F.language :=
  corollaryOne F

/-- Corollary 2. Finite thickness suffices for effective inference. -/
theorem corollary_2 (F : EffectiveIndexedFamily) :
    ConditionThree F.language → EffectiveInferrable F :=
  corollaryTwo F

/-- Corollary 3. Finite tell-tales and uniformly computable language inclusion
suffice for effective inference. -/
theorem corollary_3 (F : EffectiveIndexedFamily) :
    ConditionTwo F.language → ConditionFour F → EffectiveInferrable F :=
  corollaryThree F

end GenLimit.Angluin.Results
