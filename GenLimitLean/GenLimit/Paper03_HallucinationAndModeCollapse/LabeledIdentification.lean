import GenLimit.Paper03_HallucinationAndModeCollapse.LabeledIdentificationRates
import GenLimit.Paper03_HallucinationAndModeCollapse.LabeledIdentificationLowerBound

/-!
# Theorem 3.13: optimal exponential labeled identification

Source: arXiv:2411.09642v3, Definition 16 and Theorem 3.13. The upper
bound holds for every indexed countable family under the standing membership
oracle. The lower bound retains the source's identification nontriviality
assumption and applies to every randomized learner. Constants in the upper
bound may depend on the fixed valid law. The lower bound fixes one valid law
before taking infinitely many sample sizes.
-/

namespace GenLimit.HallucinationModeCollapse

/-- The full labeled-data theorem, including an explicit membership-only
learner and its ordinary computability specialization. -/
theorem theorem_3_13 (C : GenLimit.Generic.LanguageFamily ℕ) (O : GenLimit.MembershipOracle C) :
    ExponentialLabeledIdentifies C (deterministicLabeledIdentifier (labeledEnumerationLearner O)) ∧
      (Computable₂ O.query → Computable (labeledEnumerationLearner O)) ∧
      (NontrivialCollection C → ∀ A : LabeledIdentifier,
        ∃ i p, ValidLabeledDistribution C i p ∧
          ∃ᶠ n : ℕ in Filter.atTop,
            Real.exp (-2 * (n : ℝ)) ≤ labeledIdentificationError C A p i n) :=
  ⟨(theorem_3_13_upper C O).1, (theorem_3_13_upper C O).2, lemma_8_2 C⟩

end GenLimit.HallucinationModeCollapse
