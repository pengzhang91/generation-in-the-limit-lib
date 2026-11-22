import GenLimit.Paper11_LearningAlgorithmsInTheLimit.TeachingImpossibility
import GenLimit.Paper11_LearningAlgorithmsInTheLimit.RationalReduction
import GenLimit.Paper11_LearningAlgorithmsInTheLimit.PartialDomains
import GenLimit.Paper11_LearningAlgorithmsInTheLimit.QuantitativeSimulation
import GenLimit.Paper11_LearningAlgorithmsInTheLimit.TimeBounds
import GenLimit.Paper11_LearningAlgorithmsInTheLimit.Transducers
import GenLimit.Paper11_LearningAlgorithmsInTheLimit.CharacteristicSets
import GenLimit.Paper11_LearningAlgorithmsInTheLimit.ObservationForgetting
import GenLimit.Paper11_LearningAlgorithmsInTheLimit.TaggedSimulation
import GenLimit.Paper11_LearningAlgorithmsInTheLimit.TaggedTape
import GenLimit.Paper11_LearningAlgorithmsInTheLimit.MSMTheorem

/-!
# P11 source-facing overview

Paper-facing declarations for Papazov--Flammarion,
*Learning Algorithms in the Limit* (COLT 2025 / PMLR 291).

Each declaration is a thin wrapper around the detailed module that owns the
proof. Names ending in `_core` deliberately expose only the formalized part
of the corresponding source result. Theorems 12 and 14 take the paper's quantitative simulation thesis as a hypothesis. Theorem 16 uses completed tape trajectories. Theorem 17 uses a recursion-theorem diagonal on actual single-tape programs. Theorem 21 fixes the observable tie convention and proves stabilization of the resulting quotient.
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

open Quantitative

/-- Time-restricted IOO learning under the quantitative simulation thesis. -/
theorem theorem_12 [Encodable σ] [DecidableEq Y] (io : TuringIO σ X Y)
    (q Q : ℕ → ℕ → ℕ) (size : X → ℕ) (hq : ∀ a, Monotone (q a))
    (M : Set (Teacher X Y)) (thesis : QECTT io q M) :
    ∀ m ∈ M, TimeRestricted size Q m → ∀ (I : Set X), I ⊆ m.domain → ∀ s, Covers s I →
      LearnsByCriterion (labeledEnumerationLearner (ioRun io q Q size))
        (labeledStream (fun x ↦ some (m.value x)) s)
        (fun n ↦ TuringComputesOn io (prog n) m.value I) :=
  Quantitative.theorem_12 io q Q size hq M thesis

/-- Parameterized Turing-time classes are IOO learnable at identity overhead. -/
theorem corollary_13 [Encodable σ] [DecidableEq Y] (io : TuringIO σ X Y)
    (Q : ℕ → ℕ → ℕ) (size : X → ℕ) (P : TuringProgram σ)
    (domain : Set X) (value : X → Y)
    (timeBound : ∃ b c : ℕ, ∀ x ∈ domain, P.runWithin (b * Q c (size x)) io x = some (value x)) :
    ∀ (I : Set X), I ⊆ domain → ∀ s, Covers s I →
      LearnsByCriterion (labeledEnumerationLearner (ioRun io (fun _ t ↦ t) Q size))
        (labeledStream (fun x ↦ some (value x)) s)
        (fun n ↦ TuringComputesOn io (prog n) value I) :=
  Quantitative.corollary_13 io Q size P domain value timeBound

/-- Universal TBO learning under the quantitative simulation thesis. -/
theorem theorem_14 [Encodable σ] [DecidableEq Y] (io : TuringIO σ X Y) (q : ℕ → ℕ → ℕ)
    (hq : ∀ a, Monotone (q a)) (M : Set (Teacher X Y)) (thesis : QECTT io q M) :
    ∀ m ∈ M, ∀ (I : Set X), I ⊆ m.domain → ∀ (obs : X → TimeBoundObservation X Y),
      (∀ x ∈ I, (obs x).input = x ∧ (obs x).value = m.value x) →
      (∃ b : ℕ, ∀ x ∈ I, m.steps x ≤ b * (obs x).timeBound) → ∀ s, Covers s I →
        LearnsByCriterion (timeObservedLearner (tbRun io q)) (fun n ↦ obs (s n))
          (fun n ↦ TuringComputesOn io (prog n) m.value I) :=
  Quantitative.theorem_14 io q hq M thesis

/-- Theorem 16 on genuine halting tape trajectories, with the paper's rational
input and output alphabets and restricted sources. -/
theorem theorem_16 [Encodable σ] [Fintype σ] (R : Rational.IOAlgorithm σ (Policy.Action σ))
    (hr : Rational.Solves R) (io : TuringIO σ X Y) (P : TuringProgram σ) (target : X → Y)
    (I : Set X) (s : ℕ → Policy.Observation σ X Y) (hI : Set.range (fun n ↦ (s n).input) = I)
    (hs : ∀ n, (s n).value = target (s n).input ∧ ∃ out,
      Policy.Execution P io.blank 1 (io.initTape (s n).input) (s n).events out ∧
      io.readOutput out = some (s n).value) :
    LearnsByCriterion (Policy.reducedLearner R io.blank) s (fun Q ↦ TuringComputesOn io Q target I) :=
  Policy.theorem_16 R hr io P target I s hI hs

section NativeLowerBounds
open NativeTape
variable {Γ α : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ] [Primcodable Γ] [Primcodable α] [Finite α]

/-- Theorem 17. Even linear-time total word machines defeat each computable
mass budget. No effective selector supplies legal characteristic inputs on
the full machine class under the paper's policy-trajectory observations. -/
theorem theorem_17 (ι : α ↪ Γ) (noBlank : ∀ a, ι a ≠ default) (a : α)
    (A : Set (List α × WordObservation α Γ) → R) (rep : R → List α → Option (List α))
    (β : TuringProgram Γ → ℕ) (hβ : Computable (fun n ↦ β (decodeTuringProgram n)))
    (sideLength : Unit ⊕ ℕ ⊕ List (Policy.Event Γ) → ℕ) :
    let clock := fun (_ : TuringProgram Γ) (_ : List α) ↦ 0
    let obs := observed .policyTrajectory ι clock
    (¬ HasMass ι A rep obs (exampleLength .policyTrajectory ι clock sideLength) β) ∧
      ¬ HasSelector ι A rep obs :=
  ⟨no_mass_bound ι noBlank a A rep _ β hβ _ (fun _ _ _ ↦ output_le_exampleLength _ ι _ _),
    no_selector ι noBlank a A rep _⟩

/-- Corollary 18. In each of the IO, time-bound and policy-trajectory modes,
even an unrestricted learner fails the polynomial-mass requirement of IPTD.
Every polynomial in the state count has a majorant of the displayed form. -/
theorem corollary_18 (m : Mode) (ι : α ↪ Γ) (noBlank : ∀ a, ι a ≠ default) (a : α)
    (clock : TuringProgram Γ → List α → ℕ)
    (A : Set (List α × WordObservation α Γ) → R) (rep : R → List α → Option (List α))
    (sideLength : Unit ⊕ ℕ ⊕ List (Policy.Event Γ) → ℕ) :
    ¬ ∃ K d : ℕ, HasMass ι A rep (observed m ι clock) (exampleLength m ι clock sideLength)
      (fun P ↦ K*((Policy.states P).card+1)^d) :=
  no_polynomial_mass ι noBlank a A rep _ _ (fun _ _ _ ↦ output_le_exampleLength m ι clock sideLength)

end NativeLowerBounds

/-- Theorem 21. A finite tagged single-tape teacher admits genuine terminal
maximum-similarity quotients with a polynomial characteristic sample.
The tie convention is fixed by the observable transition labels. -/
theorem theorem_21 {σ : Type} [Fintype σ] [Encodable σ] [DecidableEq σ]
    (io : TuringIO σ X Y) (f : X → Y) (hf : ∃ P, TuringComputesOn io P f Set.univ) :
    ∃ (n : ℕ) (T : TuringProgram (TaggedTape.Symbol σ n)),
      TuringComputesOn (TaggedTape.liftIO n io) T f Set.univ ∧
      ∀ I : Set X, MSM.Learning.LearnsWithSamples TaggedTape.endpoints (TaggedTape.liftIO n io) T f I
        (2 * (Policy.states T).card * Fintype.card σ) :=
  TaggedTape.theorem_21 io f hf

end GenLimit.LearningAlgorithmsLimit.Results
