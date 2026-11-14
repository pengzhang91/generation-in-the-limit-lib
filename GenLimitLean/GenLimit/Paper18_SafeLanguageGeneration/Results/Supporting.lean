import GenLimit.Paper18_SafeLanguageGeneration.DiffEmpty

/-!
# Paper 18: supporting results for Theorem 6.1

The encoded hard subclass and representation-transport theorem are retained
under their existing names. The main machine-code statement is in
`Results.Overview`.
-/

namespace GenLimit.SafeGeneration.Results

/-- The encoded hard subclass used internally to prove Theorem 6.1. -/
theorem theorem_6_1_restricted :
    ¬ComputablePred DiffEmpty.DiffEmptyInstance :=
  DiffEmpty.theorem_6_1_restricted

/-- Representation-independent transport form of Theorem 6.1. -/
theorem theorem_6_1_of_hard_embedding
    {Rep : Type*} [Primcodable Rep]
    (left right : Rep → Set ℕ)
    (encode : Nat.Partrec.Code → Rep)
    (hencode : Computable encode)
    (hcorrect :
      ∀ c,
        left (encode c) \ right (encode c) = ∅ ↔
          DiffEmpty.DiffEmptyInstance c) :
    ¬ComputablePred
      (fun r => left r \ right r = ∅) :=
  DiffEmpty.diffEmpty_not_computable_of_hard_embedding
    left right encode hencode hcorrect

end GenLimit.SafeGeneration.Results
