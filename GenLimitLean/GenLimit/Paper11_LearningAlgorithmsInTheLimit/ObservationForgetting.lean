import GenLimit.Paper11_LearningAlgorithmsInTheLimit.CharacteristicSets

/-!
# Forgetting observations and characteristic-set bounds

Corollary 18 orders the paper's observation models by information content:
input-output observations are obtained from time-bound observations by
forgetting the time bound, and time-bound observations are in turn obtained
from policy-trajectory observations by forgetting the trajectory.

This file checks the deterministic semantic implication used by that
corollary.  A learner for poorer observations induces a learner for richer
observations by erasing the extra information.  The induced learner uses
exactly the same characteristic cores, so every bound measured solely from
the core is preserved.

No declaration below asserts the machine-level non-IPTD premise of
Corollary 18; that premise still depends on Theorem 17's computability and
Halting-Problem reduction.
-/

namespace GenLimit.LearningAlgorithmsLimit

/-- Apply an observation-erasing map pointwise to a set of examples. -/
def forgetExamples
    (forget : Rich → Poor)
    (examples : Set (Input × Rich)) :
    Set (Input × Poor) :=
  {z | ∃ observation,
    (z.1, observation) ∈ examples ∧
      z.2 = forget observation}

/-- Forgetting the observations in a model's example set gives exactly the
example set for the composed poorer observation map. -/
theorem forgetExamples_exampleSet
    (rich : Model → Input → Rich)
    (forget : Rich → Poor)
    (m : Model) (inputs : Set Input) :
    forgetExamples forget (exampleSet rich m inputs) =
      exampleSet (fun model input => forget (rich model input))
        m inputs := by
  ext z
  simp [forgetExamples, exampleSet]

/-- A learner for poorer observations can consume richer observations by
erasing the additional information before invoking the original learner. -/
def liftLearnerAlongForget
    (learner : Set (Input × Poor) → Rep)
    (forget : Rich → Poor) :
    Set (Input × Rich) → Rep :=
  fun examples => learner (forgetExamples forget examples)

/-- Every characteristic core for the poorer observation model is the same
characteristic core for the induced richer-observation learner. -/
theorem isCharacteristicSet_lift_along_forget
    (learner : Set (Input × Poor) → Rep)
    (rich : Model → Input → Rich)
    (forget : Rich → Poor)
    (modelSemantics : Model → Input → Option Output)
    (representationSemantics : Rep → Input → Option Output)
    (source core : Set Input) (m : Model)
    (hcore : IsCharacteristicSet learner
      (fun model input => forget (rich model input))
      modelSemantics representationSemantics source m core) :
    IsCharacteristicSet
      (liftLearnerAlongForget learner forget)
      rich modelSemantics representationSemantics source m core := by
  refine ⟨hcore.1, ?_⟩
  intro inputs hcoreInputs hinputsSource
  change CorrectOn representationSemantics (modelSemantics m) source
    (learner (forgetExamples forget (exampleSet rich m inputs)))
  rw [forgetExamples_exampleSet]
  exact hcore.2 inputs hcoreInputs hinputsSource

/-- Corollary 18's exact characteristic-set information-order implication.

If a learner using poorer observations has characteristic cores bounded by
an arbitrary core measure, then erasing information gives a
richer-observation learner with the identical bound.  Consequently, any
impossibility for the richer observation model transfers contrapositively
to the poorer one once the source-specific machine impossibility is
available. -/
theorem corollary_18_characteristic_bound_lifts_to_richer_observations
    (learner : Set (Input × Poor) → Rep)
    (rich : Model → Input → Rich)
    (forget : Rich → Poor)
    (modelSemantics : Model → Input → Option Output)
    (representationSemantics : Rep → Input → Option Output)
    (source : Set Input)
    (mass : Set Input → ℕ) (bound : Model → ℕ)
    (hbounded : ∀ m, ∃ core,
      IsCharacteristicSet learner
        (fun model input => forget (rich model input))
        modelSemantics representationSemantics source m core ∧
      mass core ≤ bound m) :
    ∀ m, ∃ core,
      IsCharacteristicSet
        (liftLearnerAlongForget learner forget)
        rich modelSemantics representationSemantics source m core ∧
      mass core ≤ bound m := by
  intro m
  obtain ⟨core, hcore, hmass⟩ := hbounded m
  exact ⟨core,
    isCharacteristicSet_lift_along_forget
      learner rich forget modelSemantics representationSemantics
      source core m hcore,
    hmass⟩

end GenLimit.LearningAlgorithmsLimit
