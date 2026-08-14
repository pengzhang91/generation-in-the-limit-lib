import GenLimit.Paper00A_PositiveDataInference

/-!
# Charikar--Pabbaraju: identification in the limit

This module pins Definition 7 and Theorem 8 in the numbering of
arXiv:2411.15364v2 to the repository's source-facing Angluin development.
The paper cites Angluin's effective characterization rather than reproving it.
The complete effective biconditional is reused directly from the current
Angluin development.
-/

namespace GenLimit.CharikarPabbaraju

open GenLimit.Generic

/-- Definition 7, using Angluin's total computable list-machine interface. -/
abbrev IdentifiableInLimit :=
  GenLimit.Angluin.EffectiveInferrable

/-- The finite uniformly enumerable tell-tale condition printed in Theorem 8. -/
abbrev AngluinIdentificationCondition :=
  GenLimit.Angluin.ConditionOne

/-- Theorem 8 (`thm:angluin-characterization`) exactly. -/
def TheoremEightStatement
    (F : GenLimit.Angluin.EffectiveIndexedFamily) : Prop :=
  IdentifiableInLimit F ↔ AngluinIdentificationCondition F

theorem theoremEightStatement_eq_angluin
    (F : GenLimit.Angluin.EffectiveIndexedFamily) :
    TheoremEightStatement F =
      GenLimit.Angluin.TheoremOneStatement F :=
  rfl

/-- Theorem 8, proved by the formalized Angluin Theorem 1. -/
theorem theorem_8 (F : GenLimit.Angluin.EffectiveIndexedFamily) :
    TheoremEightStatement F :=
  GenLimit.Angluin.theoremOne F

/-- Semantic projection of Theorem 8's sufficient direction. -/
theorem theorem8_condition_semantic_sufficiency
    {F : GenLimit.Angluin.EffectiveIndexedFamily}
    (h : AngluinIdentificationCondition F) :
    ∃ M : GenLimit.Angluin.SemanticIdentifier ℕ,
      GenLimit.Angluin.SemanticallyIdentifies M F.language :=
  GenLimit.Angluin.ConditionOne.semantic_sufficiency h

/-- The weaker non-effective tell-tale consequence of Theorem 8. -/
theorem theorem8_effective_identification_implies_finite_telltales
    {F : GenLimit.Angluin.EffectiveIndexedFamily}
    (h : IdentifiableInLimit F) :
    GenLimit.Angluin.ConditionTwo F.language :=
  GenLimit.Angluin.effectiveInferrable_conditionTwo h

end GenLimit.CharikarPabbaraju
