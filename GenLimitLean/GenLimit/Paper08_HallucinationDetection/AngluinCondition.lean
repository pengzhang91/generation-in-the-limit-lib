import GenLimit.Paper08_HallucinationDetection.Reductions
import GenLimit.Paper00A_PositiveDataInference.Semantic.Characterization

/-!
# Angluin's condition and hallucination detection

This module proves Corollary 2.2 of Karbasi--Montasser--Sous--Velegkas at
the paper's semantic oracle level. Its Angluin condition is exactly finite
tell-tale existence (`ConditionTwo` in the shared Angluin development).

The source-facing corollary combines Paper08 Theorem 2.1 directly with the
canonical semantic Angluin characterization.  The tell-tale construction and
its necessity proof remain owned by the shared Angluin development rather than
being duplicated here.
-/

namespace GenLimit.HallucinationDetection

open GenLimit.Generic

/-- Corollary 2.2. The shared name `ConditionTwo` is the finite-tell-tale
condition printed as Definition 4 in the hallucination-detection paper. -/
theorem corollary_2_2
    [Nonempty α] [Countable α]
    (C : GenLimit.Generic.LanguageFamily α) :
    HallucinationDetectable C ↔ GenLimit.Angluin.ConditionTwo C := by
  rw [theorem_2_1 C]
  exact GenLimit.Angluin.semanticallyInferrable_iff_conditionTwo C

end GenLimit.HallucinationDetection
