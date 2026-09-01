import GenLimit.Paper11_LearningAlgorithmsInTheLimit.TimeBounds
import GenLimit.Paper11_LearningAlgorithmsInTheLimit.Transducers
import GenLimit.Paper11_LearningAlgorithmsInTheLimit.CharacteristicSets
import GenLimit.Paper11_LearningAlgorithmsInTheLimit.ObservationForgetting
import GenLimit.Paper11_LearningAlgorithmsInTheLimit.TaggedSimulation
import GenLimit.Paper11_LearningAlgorithmsInTheLimit.MSMMergeOrder

/-!
# P11 source-facing overview

Paper-facing declarations for Papazov--Flammarion,
*Learning Algorithms in the Limit* (COLT 2025 / PMLR 291).

Each declaration is a thin wrapper around the detailed module that owns the
proof. Names ending in `_core` deliberately expose only the formalized part
of the corresponding source result. In particular, this overview does not
postulate the paper's `q`-ECTT premise, claim the missing Halting-Problem
reduction, or turn the conditional MSM invariant into an unconditional
Theorem 21.
-/

namespace GenLimit.LearningAlgorithmsLimit.Results

/-! ## Characteristic sets -/

/-- Lemma 9 (Distinguishability), at the total-observation interface. -/
theorem lemma_9_distinguishability
    {learner : Set (Input × Obs) → Rep}
    {observe : Model → Input → Obs}
    {modelSemantics : Model → Input → Option Output}
    {representationSemantics : Rep → Input → Option Output}
    {source coreM coreN : Set Input} {m n : Model}
    (hM : IsCharacteristicSet
      learner observe modelSemantics representationSemantics source m coreM)
    (hN : IsCharacteristicSet
      learner observe modelSemantics representationSemantics source n coreN)
    (hdifferent : ¬AgreeOn modelSemantics source m n) :
    ∃ x ∈ coreM ∪ coreN, observe m x ≠ observe n x :=
  GenLimit.LearningAlgorithmsLimit.lemma_9_distinguishability
    hM hN hdifferent

/-! ## Input-output and time-bound learning -/

/-- Theorem 12's uniform bounded-enumeration core. -/
theorem theorem_12_timeRestrictedIOO_core
    [DecidableEq Output]
    (enumeration : BoundedEnumeration Input Output)
    (target : Input → Option Output)
    (stream : ℕ → Input) (source : Set Input)
    (hcover : Covers stream source)
    (hexists : ∃ candidate,
      CorrectOn enumeration.semantics target source candidate) :
    LearnsInLimit
      (labeledEnumerationLearner enumeration.semantics)
      (labeledStream target stream)
      enumeration.semantics target source :=
  GenLimit.LearningAlgorithmsLimit.theorem_12_timeRestrictedIOO_core
    enumeration target stream source hcover hexists

/-- Diagnostic for the unsupported minimum-representation-index sentence in
the printed proof of Theorem 12. -/
theorem theorem_12_minIndex_claim_not_justified :
    (∃ budget, minIndexDiagnosticRun budget 0 () = some false) ∧
      (∃ budget, minIndexDiagnosticRun budget 1 () = some false) ∧
      minIndexDiagnosticRun 2 0 () = none ∧
      minIndexDiagnosticRun 2 1 () = some false :=
  GenLimit.LearningAlgorithmsLimit.theorem_12_minIndex_claim_not_justified

/-- Corollary 13's abstract identity-encoding specialization. -/
theorem corollary_13_parametrizedTMClass_core
    [DecidableEq Output]
    (enumeration : BoundedEnumeration Input Output)
    (target : Input → Option Output)
    (stream : ℕ → Input) (source : Set Input)
    (hcover : Covers stream source)
    (hexists : ∃ candidate,
      CorrectOn enumeration.semantics target source candidate) :
    LearnsInLimit
      (labeledEnumerationLearner enumeration.semantics)
      (labeledStream target stream)
      enumeration.semantics target source :=
  GenLimit.LearningAlgorithmsLimit.corollary_13_parametrizedTMClass_core
    enumeration target stream source hcover hexists

/-- Theorem 14's conditional core after representative existence. -/
theorem theorem_14_universalTBO_core
    [DecidableEq Output]
    (simulate : ℕ → Input → ℕ → Option Output)
    (observation : Input → TimeBoundObservation Input Output)
    (stream : ℕ → Input) (source : Set Input)
    (hcover : Covers stream source)
    (hinput : ∀ input ∈ source, (observation input).input = input)
    (hexists : ∃ candidate,
      TimeObservedCorrectOn simulate observation source candidate) :
    LearnsByCriterion
      (timeObservedLearner simulate)
      (fun n => observation (stream n))
      (TimeObservedCorrectOn simulate observation source) :=
  GenLimit.LearningAlgorithmsLimit.theorem_14_universalTBO_core
    simulate observation stream source hcover hinput hexists

/-- Corollary 15 for the concrete finite-table single-tape evaluator. -/
theorem corollary_15_turingTBO
    [Fintype Symbol] [DecidableEq Symbol] [Encodable Symbol]
    [DecidableEq Output]
    (io : TuringIO Symbol Input Output) :
    SolvesTuringTBO io (turingTBOLearner io) :=
  GenLimit.LearningAlgorithmsLimit.corollary_15_turingTBO io

/-! ## Policy trajectories and rational functions -/

/-- The transition-diagram equation used by Theorem 16. -/
theorem theorem_16_recursiveToRational_behavior
    (M : PolicyMachine State Tape) (scanned : List Tape) :
    M.tapeBehavior scanned = (M.toFST.run scanned).2 :=
  GenLimit.LearningAlgorithmsLimit.theorem_16_recursiveToRational_behavior
    M scanned

/-- The rational learning-by-enumeration core of Theorem 16. -/
theorem theorem_16_rationalEnumeration_core
    [DecidableEq B]
    (machines : ℕ → Mealy State A B)
    (targetIndex : ℕ)
    (stream : ℕ → List A) (source : Set (List A))
    (hcover : Covers stream source) :
    LearnsInLimit
      (labeledEnumerationLearner
        (fun j => rationalSemantics (machines j)))
      (labeledStream
        (rationalSemantics (machines targetIndex)) stream)
      (fun j => rationalSemantics (machines j))
      (rationalSemantics (machines targetIndex))
      source :=
  GenLimit.LearningAlgorithmsLimit.theorem_16_rationalEnumeration_core
    machines targetIndex stream source hcover

/-! ## Characteristic-set lower bounds -/

/-- The late-splitting semantic obstruction behind Theorem 17. -/
theorem theorem_17_lateSplit_characteristic_obstruction
    (learner : Set (ℕ × Bool) → Bool)
    (splitAt : ℕ) (coreFalse coreTrue : Set ℕ)
    (hFalse : IsCharacteristicSet
      learner (lateSplitObservation splitAt)
      (lateSplitSemantics splitAt)
      (lateSplitSemantics splitAt)
      Set.univ false coreFalse)
    (hTrue : IsCharacteristicSet
      learner (lateSplitObservation splitAt)
      (lateSplitSemantics splitAt)
      (lateSplitSemantics splitAt)
      Set.univ true coreTrue) :
    ∃ n ∈ coreFalse ∪ coreTrue, splitAt ≤ n :=
  GenLimit.LearningAlgorithmsLimit.theorem_17_lateSplit_characteristic_obstruction
    learner splitAt coreFalse coreTrue hFalse hTrue

/-- The finite-mass lower-bound core of Theorem 17. -/
theorem theorem_17_mass_lower_bound_core
    (learner : Set (ℕ × Bool) → Bool)
    (splitAt : ℕ) (coreFalse coreTrue : Finset ℕ)
    (hFalse : IsCharacteristicSet
      learner (lateSplitObservation splitAt)
      (lateSplitSemantics splitAt)
      (lateSplitSemantics splitAt)
      Set.univ false (coreFalse : Set ℕ))
    (hTrue : IsCharacteristicSet
      learner (lateSplitObservation splitAt)
      (lateSplitSemantics splitAt)
      (lateSplitSemantics splitAt)
      Set.univ true (coreTrue : Set ℕ)) :
    splitAt + 1 ≤ inputMass coreFalse + inputMass coreTrue :=
  GenLimit.LearningAlgorithmsLimit.theorem_17_mass_lower_bound_core
    learner splitAt coreFalse coreTrue hFalse hTrue

/-! ## Observation-information order -/

/-- Corollary 18's pointwise information-forgetting implication. -/
theorem corollary_18_forgetting_preserves_indistinguishability
    (rich : Model → Input → Rich)
    (forget : Rich → Poor)
    {m n : Model} {inputs : Set Input}
    (h : ∀ x ∈ inputs, rich m x = rich n x) :
    ∀ x ∈ inputs, forget (rich m x) = forget (rich n x) :=
  GenLimit.LearningAlgorithmsLimit.corollary_18_forgetting_preserves_indistinguishability
    rich forget h

/-- Corollary 18's characteristic-bound lifting core. -/
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
      mass core ≤ bound m :=
  GenLimit.LearningAlgorithmsLimit.corollary_18_characteristic_bound_lifts_to_richer_observations
    learner rich forget modelSemantics representationSemantics
    source mass bound hbounded

/-! ## Tagged simulation and MSM -/

/-- The two-step tagged transition displayed in Theorem 21. -/
theorem theorem_21_tagged_two_step
    [DecidableEq State] [DecidableEq Tape]
    (M : PolicyMachine State Tape) (q : State) (a : Tape) :
    (taggedMachine M).toFST.runFrom (Sum.inl q)
        [Sum.inl a, Sum.inr (q, a)] =
      (Sum.inl (M.step q a).1,
        [markerAction (q, a), liftAction (M.step q a).2]) :=
  GenLimit.LearningAlgorithmsLimit.theorem_21_tagged_two_step M q a

/-- The full finite-run form of Theorem 21's tagged simulation. -/
theorem taggedMachine_runFrom
    [DecidableEq State] [DecidableEq Tape]
    (M : PolicyMachine State Tape) (q : State) (w : List Tape) :
    (taggedMachine M).toFST.runFrom (Sum.inl q)
        (taggedScannedFrom M q w) =
      (Sum.inl (M.toFST.runFrom q w).1,
        taggedActionsFrom M q w) :=
  GenLimit.LearningAlgorithmsLimit.taggedMachine_runFrom M q w

/-- The finite transition-cover and eventual-observation core of Theorem 21. -/
theorem theorem_21_transition_cover_core
    [DecidableEq Transition] [DecidableEq Sample]
    (used : Finset Transition)
    (exercises : Sample → Set Transition)
    (witness : Transition → Sample)
    (hwitness : ∀ e ∈ used, e ∈ exercises (witness e))
    (stream : ℕ → Sample) (source : Set Sample)
    (hcover : Covers stream source)
    (hwitnessSource : ∀ e ∈ used, witness e ∈ source) :
    (transitionCover used witness).card ≤ used.card ∧
      (∀ e ∈ used, ∃ sample ∈ transitionCover used witness,
        e ∈ exercises sample) ∧
      ∃ t, ∀ sample ∈ transitionCover used witness,
        ∃ n, n < t ∧ stream n = sample :=
  GenLimit.LearningAlgorithmsLimit.theorem_21_transition_cover_core
    used exercises witness hwitness stream source hcover hwitnessSource

/-- Conditional machine-independent merge-order core for Theorem 21. -/
theorem theorem_21_msm_merge_order_core
    [DecidableEq Candidate]
    (candidates : Config → Finset Candidate)
    (score : Config → Candidate → ℕ)
    (merge : Config → Candidate → Config)
    (remaining : Config → ℕ)
    (intended : Config → Candidate → Prop)
    (Sound Complete : Config → Prop)
    (initial : Config)
    (hinitial : Sound initial)
    (hgood :
      ∀ config, Sound config → ¬Complete config →
        ∃ good ∈ candidates config,
          intended config good ∧ 2 ≤ score config good)
    (hbad :
      ∀ config, Sound config → ¬Complete config →
        ∀ bad ∈ candidates config,
          ¬intended config bad → score config bad ≤ 1)
    (hpreserve :
      ∀ config choice, Sound config → intended config choice →
        Sound (merge config choice))
    (hcompleteTerminal :
      ∀ config, Sound config → Complete config →
        IsMSMTerminal candidates score config)
    (hdecrease :
      ∀ config choice,
        IsMSMChoice candidates score config choice →
          remaining (merge config choice) < remaining config) :
    ∃ final,
      Relation.ReflTransGen
          (MSMStep candidates score merge) initial final ∧
        Sound final ∧ Complete final ∧
        IsMSMTerminal candidates score final :=
  GenLimit.LearningAlgorithmsLimit.theorem_21_msm_merge_order_core
    candidates score merge remaining intended Sound Complete initial
    hinitial hgood hbad hpreserve hcompleteTerminal hdecrease

end GenLimit.LearningAlgorithmsLimit.Results
