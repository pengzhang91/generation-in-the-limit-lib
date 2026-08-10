import GenLimit.HallucinationDetection.Reductions
import GenLimit.Angluin.Semantic.Characterization

/-!
# Angluin's condition and hallucination detection

This module proves Corollary 2.2 of Karbasi--Montasser--Sous--Velegkas at
the paper's semantic oracle level. Its Angluin condition is exactly finite
tell-tale existence (`ConditionTwo` in the shared Angluin development).

The semantic necessity direction is supplied by
`GenLimit.Angluin.Semantic.Necessity`, which reduces the countable-domain
statement to Gold's positive-text finite-tell-tale theorem.
-/

namespace GenLimit.HallucinationDetection

open GenLimit.Generic

theorem identifiable_of_conditionTwo
    (C : GenLimit.Generic.LanguageFamily α)
    (h : GenLimit.Angluin.ConditionTwo C) :
    IdentifiableInLimit C :=
  GenLimit.Angluin.semanticallyInferrable_of_conditionTwo C h

theorem conditionTwo_of_identifiable
    [Nonempty α] [Countable α]
    (C : GenLimit.Generic.LanguageFamily α)
    (hID : IdentifiableInLimit C) :
    GenLimit.Angluin.ConditionTwo C :=
  GenLimit.Angluin.conditionTwo_of_semanticallyIdentifiable C hID

/-- Corollary 2.2. The shared name `ConditionTwo` is the finite-tell-tale
condition printed as Definition 4 in the hallucination-detection paper. -/
theorem corollary_2_2
    [Nonempty α] [Countable α]
    (C : GenLimit.Generic.LanguageFamily α) :
    HallucinationDetectable C ↔ GenLimit.Angluin.ConditionTwo C := by
  rw [theorem_2_1 C]
  constructor
  · exact conditionTwo_of_identifiable C
  · exact identifiable_of_conditionTwo C

end GenLimit.HallucinationDetection
