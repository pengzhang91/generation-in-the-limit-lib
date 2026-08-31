import GenLimit.Paper11_LearningAlgorithmsInTheLimit.TuringMachines

/-!
# Bounded simulation and time-bound observations

The abstract results in this file isolate the convergence arguments behind
Theorems 12 and 14.  Corollary 15 is then instantiated with the concrete
single-tape programs and executable bounded evaluator from
`TuringMachines.lean`.

The universal Theorem 14 still depends on the paper's physical `q`-ECTT
premise.  We record that dependency as a representative-existence hypothesis;
we do not encode the physical thesis as a Lean postulate.  Corollary 15 needs
no such cross-model premise because both target and hypotheses are concrete
Turing programs.
-/

namespace GenLimit.LearningAlgorithmsLimit

/-- A diagonal enumeration of representations together with finite
simulation budgets. -/
structure BoundedEnumeration (Input Output : Type*) where
  decode : ℕ → ℕ × ℕ
  runWithin : ℕ → ℕ → Input → Option Output

def BoundedEnumeration.semantics
    (enumeration : BoundedEnumeration Input Output) :
    ℕ → Input → Option Output :=
  fun candidate input =>
    enumeration.runWithin
      (enumeration.decode candidate).1
      (enumeration.decode candidate).2 input

/-- Theorem 12's semantic enumeration core with a genuinely uniform learner.
The existence proof is consumed only by the convergence theorem and is not an
argument to `labeledEnumerationLearner`. -/
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
  enumeration_learnsInLimit
    enumeration.semantics target stream source hcover hexists

/-- Corollary 13 remains the identity-encoding specialization of Theorem 12's
semantic core.  A concrete TM complexity-class instance is outside the scope
of the present P11 development. -/
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
  theorem_12_timeRestrictedIOO_core
    enumeration target stream source hcover hexists

/-- A time-bound observation records its input, output, and the observed rough
time bound. -/
structure TimeBoundObservation (Input Output : Type*) where
  input : Input
  value : Output
  timeBound : ℕ

def timeObservedFits
    (simulate : ℕ → Input → ℕ → Option Output)
    (candidate : ℕ) (observation : TimeBoundObservation Input Output) : Prop :=
  simulate candidate observation.input observation.timeBound =
    some observation.value

instance timeObservedFitsDecidableRel
    [DecidableEq Output]
    (simulate : ℕ → Input → ℕ → Option Output) :
    DecidableRel (timeObservedFits simulate) :=
  fun _ _ => by
    unfold timeObservedFits
    infer_instance

def timeObservedLearner
    [DecidableEq Output]
    (simulate : ℕ → Input → ℕ → Option Output) :
    GenLimit.Learner (TimeBoundObservation Input Output) ℕ :=
  enumerationLearner (timeObservedFits simulate)

def TimeObservedCorrectOn
    (simulate : ℕ → Input → ℕ → Option Output)
    (observation : Input → TimeBoundObservation Input Output)
    (source : Set Input) (candidate : ℕ) : Prop :=
  ∀ input ∈ source,
    simulate candidate input (observation input).timeBound =
      some (observation input).value

theorem streamConsistent_timeObserved_iff_correctOn
    (simulate : ℕ → Input → ℕ → Option Output)
    (observation : Input → TimeBoundObservation Input Output)
    (stream : ℕ → Input) (source : Set Input)
    (hcover : Covers stream source)
    (hinput : ∀ input ∈ source, (observation input).input = input)
    (candidate : ℕ) :
    StreamConsistent (timeObservedFits simulate)
        (fun n => observation (stream n)) candidate ↔
      TimeObservedCorrectOn simulate observation source candidate := by
  constructor
  · intro h input hsource
    obtain ⟨n, rfl⟩ := covers_exists_eq hcover hsource
    simpa [timeObservedFits,
      hinput (stream n) (covers_stream_mem hcover n)] using h n
  · intro h n
    simpa [timeObservedFits,
      hinput (stream n) (covers_stream_mem hcover n)] using
      h (stream n) (covers_stream_mem hcover n)

/-- Theorem 14's conditional core after the `q`-ECTT step has supplied a
bounded simulator representative.  The learner itself remains one fixed
history-based executable function. -/
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
      (TimeObservedCorrectOn simulate observation source) := by
  have hexistsStream :
      ∃ candidate, StreamConsistent (timeObservedFits simulate)
        (fun n => observation (stream n)) candidate := by
    simpa only [streamConsistent_timeObserved_iff_correctOn
      simulate observation stream source hcover hinput] using hexists
  obtain ⟨candidate, hconsistent, hstable⟩ :=
    enumeration_identifies_first_consistent
      (timeObservedFits simulate) (fun n => observation (stream n))
      hexistsStream
  exact ⟨candidate,
    (streamConsistent_timeObserved_iff_correctOn
      simulate observation stream source hcover hinput candidate).1 hconsistent,
    hstable⟩

/-! ## Concrete Turing-machine specialization -/

def turingTBOFits
    [Encodable Symbol]
    (io : TuringIO Symbol Input Output)
    (candidate : ℕ) (observation : TimeBoundObservation Input Output) : Prop :=
  (turingCandidateProgram candidate).runWithin
      (turingCandidateScale candidate * observation.timeBound)
      io observation.input = some observation.value

instance turingTBOFitsDecidableRel
    [Encodable Symbol] [DecidableEq Output]
    (io : TuringIO Symbol Input Output) :
    DecidableRel (turingTBOFits io) :=
  fun _ _ => by
    unfold turingTBOFits
    infer_instance

/-- The single learner used for every target program, source, observation
ordering, and admissible target-dependent scale. -/
def turingTBOLearner
    [Encodable Symbol] [DecidableEq Output]
    (io : TuringIO Symbol Input Output) :
    GenLimit.Learner (TimeBoundObservation Input Output) ℕ :=
  enumerationLearner (turingTBOFits io)

/-- The TBO data really comes from `targetProgram`: inputs are recorded
faithfully and one fixed target-dependent scale bounds every target run on the
restricted source. -/
def IsTuringTimeBoundObservation
    [Encodable Symbol]
    (io : TuringIO Symbol Input Output)
    (targetProgram : TuringProgram Symbol)
    (observation : Input → TimeBoundObservation Input Output)
    (source : Set Input) : Prop :=
  (∀ input ∈ source, (observation input).input = input) ∧
    ∃ scale, ∀ input ∈ source,
      targetProgram.runWithin
          (scale * (observation input).timeBound) io input =
        some (observation input).value

/-- A concrete statement of the `(T^Γ_Σ, α_TB)` learning problem.  The
learner quantified here is fixed before the target program, source, ordering,
and TBO scale are revealed. -/
def SolvesTuringTBO
    [Encodable Symbol]
    (io : TuringIO Symbol Input Output)
    (learner : GenLimit.Learner (TimeBoundObservation Input Output) ℕ) : Prop :=
  ∀ targetProgram source stream observation,
    Covers stream source →
    IsTuringTimeBoundObservation io targetProgram observation source →
    LearnsByCriterion learner
      (fun n => observation (stream n))
      (fun candidate =>
        TuringCandidateComputesOn io candidate
          (fun input => (observation input).value) source)

/-- Corollary 15, concrete Turing-machine specialization.  One executable
bounded-search learner solves the TBO learning problem for every finite-table
single-tape target program over the fixed finite tape alphabet. -/
theorem corollary_15_turingTBO
    [Fintype Symbol] [DecidableEq Symbol] [Encodable Symbol]
    [DecidableEq Output]
    (io : TuringIO Symbol Input Output) :
    SolvesTuringTBO io (turingTBOLearner io) := by
  intro targetProgram source stream observation hcover hadmissible
  obtain ⟨hinput, scale, htarget⟩ := hadmissible
  let targetCandidate :=
    Nat.pair scale (Encodable.encode targetProgram)
  have htargetConsistent :
      StreamConsistent (turingTBOFits io)
        (fun n => observation (stream n)) targetCandidate := by
    intro n
    have hsource : stream n ∈ source := covers_stream_mem hcover n
    change (turingCandidateProgram targetCandidate).runWithin
      (turingCandidateScale targetCandidate *
        (observation (stream n)).timeBound)
      io (observation (stream n)).input =
        some (observation (stream n)).value
    rw [show turingCandidateProgram targetCandidate = targetProgram by
      simp [targetCandidate]]
    rw [show turingCandidateScale targetCandidate = scale by
      simp [targetCandidate]]
    rw [hinput (stream n) hsource]
    exact htarget (stream n) hsource
  obtain ⟨candidate, hconsistent, hstable⟩ :=
    enumeration_identifies_first_consistent
      (turingTBOFits io) (fun n => observation (stream n))
      ⟨targetCandidate, htargetConsistent⟩
  refine ⟨candidate, ?_, hstable⟩
  intro input hsource
  obtain ⟨n, hn⟩ := covers_exists_eq hcover hsource
  refine ⟨turingCandidateScale candidate *
    (observation input).timeBound, ?_⟩
  have hfit := hconsistent n
  change (turingCandidateProgram candidate).runWithin
    (turingCandidateScale candidate *
      (observation (stream n)).timeBound)
    io (observation (stream n)).input =
      some (observation (stream n)).value at hfit
  rw [hn, hinput input hsource] at hfit
  exact hfit

section BudgetOrderDiagnostic

/-- A two-representation bounded evaluator witnessing the gap in the
Appendix B min-state claim.  Representation 0 needs scale 10; representation
1 needs only scale 2. -/
def minIndexDiagnosticRun
    (budget representation : ℕ) (_ : Unit) : Option Bool :=
  if representation = 0 then
    if 10 ≤ budget then some false else none
  else if representation = 1 then
    if 2 ≤ budget then some false else none
  else none

theorem minIndexDiagnostic_representation_zero_correct :
    minIndexDiagnosticRun 10 0 () = some false := by
  simp [minIndexDiagnosticRun]

theorem minIndexDiagnostic_budgetFirst_selects_one :
    minIndexDiagnosticRun 2 0 () = none ∧
      minIndexDiagnosticRun 2 1 () = some false := by
  decide

/-- The printed proof's assertion that its budget-first search converges to
the minimum representation index is not implied by its invariants.  This
does not refute Theorem 12: representation 1 is also target-correct.  The
correct stable object is the least admissible budget/index pair. -/
theorem theorem_12_minIndex_claim_not_justified :
    (∃ budget, minIndexDiagnosticRun budget 0 () = some false) ∧
      (∃ budget, minIndexDiagnosticRun budget 1 () = some false) ∧
      minIndexDiagnosticRun 2 0 () = none ∧
      minIndexDiagnosticRun 2 1 () = some false := by
  exact ⟨⟨10, minIndexDiagnostic_representation_zero_correct⟩,
    ⟨2, by simp [minIndexDiagnosticRun]⟩,
    minIndexDiagnostic_budgetFirst_selects_one⟩

end BudgetOrderDiagnostic

end GenLimit.LearningAlgorithmsLimit
