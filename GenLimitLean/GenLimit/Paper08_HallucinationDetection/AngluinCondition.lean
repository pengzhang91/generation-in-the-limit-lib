import GenLimit.Paper08_HallucinationDetection.Reductions
import GenLimit.Paper00A_PositiveDataInference.Semantic.Characterization

/-!
# Angluin's condition and hallucination detection

This module proves Corollary 2.2 of Karbasi--Montasser--Sous--Velegkas at
the paper's semantic oracle level. Its Angluin condition is exactly finite
tell-tale existence (`ConditionTwo` in the shared Angluin development).

The source describes an enumeration as an infinite sequence all of whose
entries lie in the language. Consequently an empty language has no legal
enumeration. The public equivalence below handles that edge case exactly:
identification is vacuous there, and the empty set is a tell-tale. Nonempty
targets use the generic locking-sequence argument in
`GenLimit.Paper00A_PositiveDataInference.Semantic.Characterization`.
-/

namespace GenLimit.HallucinationDetection

open GenLimit.Generic

noncomputable local instance angluinConditionPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-! ## Tell-tales suffice semantically -/

/-- Choose one finite tell-tale for each indexed language. -/
noncomputable def chosenTellTale
    (C : GenLimit.Generic.LanguageFamily α)
    (h : GenLimit.Angluin.ConditionTwo C) (i : ℕ) : Finset α :=
  Classical.choose (h i)

theorem chosenTellTale_spec
    (C : GenLimit.Generic.LanguageFamily α)
    (h : GenLimit.Angluin.ConditionTwo C) (i : ℕ) :
    GenLimit.Angluin.IsTellTale C i (chosenTellTale C h i) :=
  Classical.choose_spec (h i)

/-- A fixed tell-tale is a constant finite-stage approximation. -/
noncomputable def constantTellTaleApproximation
    (C : GenLimit.Generic.LanguageFamily α)
    (h : GenLimit.Angluin.ConditionTwo C) :
    ℕ → ℕ → Finset α :=
  fun i _stage => chosenTellTale C h i

theorem constantTellTaleApproximation_spec
    (C : GenLimit.Generic.LanguageFamily α)
    (h : GenLimit.Angluin.ConditionTwo C) :
    GenLimit.Angluin.IsTellTaleApproximation C
      (constantTellTaleApproximation C h) := by
  constructor
  · intro i n m _hnm
    exact Finset.Subset.refl _
  · intro i
    refine ⟨chosenTellTale C h i, chosenTellTale_spec C h i, 0, ?_⟩
    intro n _hn
    rfl

theorem identifiable_of_conditionTwo
    (C : GenLimit.Generic.LanguageFamily α)
    (h : GenLimit.Angluin.ConditionTwo C) :
    IdentifiableInLimit C := by
  let A := constantTellTaleApproximation C h
  exact ⟨GenLimit.Angluin.semanticLearner C A,
    GenLimit.Angluin.semanticLearner_semanticallyIdentifies
      (constantTellTaleApproximation_spec C h)⟩

/-! ## Tell-tale necessity

The #0A semantic characterization now derives necessity through Gold's
positive-text theorem.  The earlier #08-local locking-sequence adapter layer
is therefore no longer duplicated here.
-/

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
