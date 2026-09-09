import GenLimit.Paper00A_PositiveDataInference.Semantic.Characterization
import GenLimit.Paper00A_PositiveDataInference.Effective.Corollaries

/-!
# Paper 0A: main-results overview

This public facade exposes thin wrappers for the completed main results of
Dana Angluin, *Inductive Inference of Formal Languages from Positive Data*
(1980). The effective wrappers retain uniform computability of the indexed
family, learner, and Condition 1 enumeration.

The semantic characterization is deliberately separate: it is a useful
non-effective analogue of Theorem 1, not another source theorem. Effective
Theorem 1 and Corollaries 1--3 are complete. The separation results in
Theorems 2--4 and the conservative learner of Theorem 5 remain open.

The Corollary 2 and 3 proofs construct extensionally equivalent uniform
tell-tale enumerators rather than reproducing the source's stage pseudocode
line by line. Their assumptions and conclusions match the journal statements.
-/

namespace GenLimit.Angluin.Results

/-- The non-effective finite-tell-tale characterization underlying the
paper's semantic layer. -/
theorem semantic_characterization
    {α : Type*} [Nonempty α] [Countable α]
    (C : GenLimit.Generic.LanguageFamily α) :
    SemanticallyInferrable C ↔ ConditionTwo C :=
  semanticallyInferrable_iff_conditionTwo C

/-- Angluin's effective Theorem 1. -/
theorem theorem_1 (F : EffectiveIndexedFamily) :
    TheoremOneStatement F :=
  theoremOne F

/-- Angluin's Corollary 1. -/
theorem corollary_1 (F : EffectiveIndexedFamily) :
    CorollaryOneStatement F :=
  corollaryOne F

/-- Angluin's Corollary 2. -/
theorem corollary_2 (F : EffectiveIndexedFamily) :
    CorollaryTwoStatement F :=
  corollaryTwo F

/-- Angluin's Corollary 3. -/
theorem corollary_3 (F : EffectiveIndexedFamily) :
    CorollaryThreeStatement F :=
  corollaryThree F

end GenLimit.Angluin.Results
