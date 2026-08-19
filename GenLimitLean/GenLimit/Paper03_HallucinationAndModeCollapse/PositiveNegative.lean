import GenLimit.Core.GenericGeneration
import GenLimit.Paper00_LanguageIdentification.Informant.Enumeration

/-!
# Positive and negative examples

This file records the qualitative online ingredient used in the upper-bound
direction of Theorem 3.13: every indexed countable family is identifiable
from complete, correctly labelled informants.

The result is a thin paper-facing wrapper around the shared Gold informant
development.  The statistical exponential-rate statement and its converse
remain outside the present probability-free scope.
-/

namespace GenLimit.HallucinationModeCollapse

/-- Existence of a semantic learner identifying an indexed family from every
complete, correctly labelled positive/negative presentation. -/
abbrev IdentifiableFromPositiveNegative
    (C : Generic.LanguageFamily ℕ) : Prop :=
  ∃ M : Gold.Informant.InformantLearner ℕ,
    Gold.Informant.IdentifiesFamilyFromInformant C M

/-- Qualitative online ingredient for the upper-bound direction of source
Theorem 3.13.  The learner and its correctness theorem are supplied by the
shared Gold informant formalization. -/
theorem theorem_3_13_online_core
    (C : Generic.LanguageFamily ℕ) :
    IdentifiableFromPositiveNegative C :=
  ⟨Gold.Informant.informantEnumerationLearner C,
    Gold.Informant.informantEnumerationLearner_identifiesFamily C⟩

end GenLimit.HallucinationModeCollapse
