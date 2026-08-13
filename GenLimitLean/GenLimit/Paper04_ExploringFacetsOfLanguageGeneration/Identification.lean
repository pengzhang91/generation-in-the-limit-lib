import GenLimit.Paper00A_PositiveDataInference

/-!
# Charikar--Pabbaraju: identification in the limit

This module pins Definition 7 and Theorem 8 in the numbering of
arXiv:2411.15364v2 to the repository's source-facing Angluin development.
The paper cites Angluin's effective characterization rather than reproving it.
Accordingly, the exact biconditional below is a proposition alias, while the
two already kernel-checked dependency slices are exposed with names that
cannot be confused with the still-unproved effective biconditional.
-/

namespace GenLimit.CharikarPabbaraju

open GenLimit.Generic

/-- Definition 7, using Angluin's total computable list-machine interface. -/
abbrev IdentifiableInLimit :=
  GenLimit.Angluin.EffectiveInferrable

/-- The finite uniformly enumerable tell-tale condition printed in Theorem 8. -/
abbrev AngluinIdentificationCondition :=
  GenLimit.Angluin.ConditionOne

/-- Theorem 8 (`thm:angluin-characterization`) exactly, as the imported
Angluin Theorem 1 proposition.  This is a statement alias, not a proof. -/
def TheoremEightStatement
    (F : GenLimit.Angluin.EffectiveIndexedFamily) : Prop :=
  IdentifiableInLimit F ↔ AngluinIdentificationCondition F

theorem theoremEightStatement_eq_angluin
    (F : GenLimit.Angluin.EffectiveIndexedFamily) :
    TheoremEightStatement F =
      GenLimit.Angluin.TheoremOneStatement F :=
  rfl

/-- Kernel-checked semantic correctness of the learner constructed from the
effective tell-tale hypothesis.  It deliberately omits the missing proof that
the constructed learner is computable. -/
theorem theorem8_condition_semantic_sufficiency
    {F : GenLimit.Angluin.EffectiveIndexedFamily}
    (h : AngluinIdentificationCondition F) :
    ∃ M : GenLimit.Angluin.SemanticIdentifier ℕ,
      GenLimit.Angluin.SemanticallyIdentifies M F.language :=
  GenLimit.Angluin.ConditionOne.semantic_sufficiency h

/-- Kernel-checked necessity consequence available from the imported locking
argument: effective identification gives a finite tell-tale for every member.
This is Condition 2, not the uniform effective enumeration in Condition 1. -/
theorem theorem8_effective_identification_implies_finite_telltales
    {F : GenLimit.Angluin.EffectiveIndexedFamily}
    (h : IdentifiableInLimit F) :
    GenLimit.Angluin.ConditionTwo F.language :=
  GenLimit.Angluin.effectiveInferrable_conditionTwo h

end GenLimit.CharikarPabbaraju
