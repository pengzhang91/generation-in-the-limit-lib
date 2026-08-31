import GenLimit.Paper11_LearningAlgorithmsInTheLimit.Transducers
import Mathlib.Data.Finset.Image

/-!
# Tagged two-step simulation and transition covers

This file checks the construction in the proof of Theorem 21: every
transition receives a fresh tape symbol and is replaced by a stay-put write
to a dummy state followed by the original write-and-move transition.  It
also proves the paper's `at most m samples` transition-cover statement.

It does not claim the final MSM merge-order invariant.  The printed proof
does not supply that invariant (and contains an incomplete sentence in the
dummy-state case), so promoting it would overstate the source.
-/

namespace GenLimit.LearningAlgorithmsLimit

abbrev TaggedAlphabet (State Tape : Type*) :=
  Sum Tape (State × Tape)

abbrev TaggedState (State Tape : Type*) :=
  Sum State (State × Tape)

def liftAction
    (action : TapeAction Tape) :
    TapeAction (TaggedAlphabet State Tape) where
  write := Sum.inl action.write
  move := action.move

def markerAction
    (transition : State × Tape) :
    TapeAction (TaggedAlphabet State Tape) where
  write := Sum.inr transition
  move := HeadMove.stay

/-- The transition-doubling construction in Appendix D.  Off-construction
transitions are totalized by harmless stay-put self loops; none is used by
the simulation theorem. -/
def taggedMachine
    [DecidableEq State] [DecidableEq Tape]
    (M : PolicyMachine State Tape) :
    PolicyMachine (TaggedState State Tape)
      (TaggedAlphabet State Tape) where
  start := Sum.inl M.start
  step
    | Sum.inl q, Sum.inl a =>
        (Sum.inr (q, a), markerAction (q, a))
    | Sum.inr transition, Sum.inr tag =>
        if tag = transition then
          let original := M.step transition.1 transition.2
          (Sum.inl original.1, liftAction original.2)
        else
          (Sum.inr transition,
            { write := Sum.inr tag, move := HeadMove.stay })
    | Sum.inl q, Sum.inr tag =>
        (Sum.inl q, { write := Sum.inr tag, move := HeadMove.stay })
    | Sum.inr transition, Sum.inl a =>
        (Sum.inr transition,
          { write := Sum.inl a, move := HeadMove.stay })

@[simp] theorem taggedMachine_first_step
    [DecidableEq State] [DecidableEq Tape]
    (M : PolicyMachine State Tape) (q : State) (a : Tape) :
    (taggedMachine M).step (Sum.inl q) (Sum.inl a) =
      (Sum.inr (q, a), markerAction (q, a)) :=
  rfl

@[simp] theorem taggedMachine_second_step
    [DecidableEq State] [DecidableEq Tape]
    (M : PolicyMachine State Tape) (q : State) (a : Tape) :
    (taggedMachine M).step (Sum.inr (q, a)) (Sum.inr (q, a)) =
      (Sum.inl (M.step q a).1, liftAction (M.step q a).2) := by
  simp [taggedMachine]

@[simp] theorem taggedFST_first_step
    [DecidableEq State] [DecidableEq Tape]
    (M : PolicyMachine State Tape) (q : State) (a : Tape) :
    (taggedMachine M).toFST.step (Sum.inl q) (Sum.inl a) =
      (Sum.inr (q, a), markerAction (q, a)) :=
  taggedMachine_first_step M q a

@[simp] theorem taggedFST_second_step
    [DecidableEq State] [DecidableEq Tape]
    (M : PolicyMachine State Tape) (q : State) (a : Tape) :
    (taggedMachine M).toFST.step
        (Sum.inr (q, a)) (Sum.inr (q, a)) =
      (Sum.inl (M.step q a).1, liftAction (M.step q a).2) :=
  taggedMachine_second_step M q a

/-- One original transition is simulated by exactly the two transitions
displayed in the proof of Theorem 21. -/
theorem theorem_21_tagged_two_step
    [DecidableEq State] [DecidableEq Tape]
    (M : PolicyMachine State Tape) (q : State) (a : Tape) :
    (taggedMachine M).toFST.runFrom (Sum.inl q)
        [Sum.inl a, Sum.inr (q, a)] =
      (Sum.inl (M.step q a).1,
        [markerAction (q, a), liftAction (M.step q a).2]) := by
  simp [Mealy.runFrom, PolicyMachine.toFST, taggedMachine]

/-- Scanned-symbol sequence for the doubled run.  The fresh tag depends on
the current state and scanned symbol, exactly as in the source construction. -/
def taggedScannedFrom
    (M : PolicyMachine State Tape) :
    State → List Tape → List (TaggedAlphabet State Tape)
  | _, [] => []
  | q, a :: w =>
      Sum.inl a :: Sum.inr (q, a) ::
        taggedScannedFrom M (M.step q a).1 w

def taggedActionsFrom
    (M : PolicyMachine State Tape) :
    State → List Tape → List (TapeAction (TaggedAlphabet State Tape))
  | _, [] => []
  | q, a :: w =>
      markerAction (q, a) :: liftAction (M.step q a).2 ::
        taggedActionsFrom M (M.step q a).1 w

/-- Full finite-run simulation: the doubled machine ends in the lifted
original state and emits the marker/original-action pairs. -/
theorem taggedMachine_runFrom
    [DecidableEq State] [DecidableEq Tape]
    (M : PolicyMachine State Tape) (q : State) (w : List Tape) :
    (taggedMachine M).toFST.runFrom (Sum.inl q)
        (taggedScannedFrom M q w) =
      (Sum.inl (M.toFST.runFrom q w).1,
        taggedActionsFrom M q w) := by
  induction w generalizing q with
  | nil => rfl
  | cons a w ih =>
      simp only [taggedScannedFrom, taggedActionsFrom,
        Mealy.runFrom_cons, taggedFST_first_step,
        taggedFST_second_step]
      rw [ih]
      rfl

theorem taggedScannedFrom_length
    (M : PolicyMachine State Tape) (q : State) (w : List Tape) :
    (taggedScannedFrom M q w).length = 2 * w.length := by
  induction w generalizing q with
  | nil => rfl
  | cons a w ih =>
      simp [taggedScannedFrom, ih, Nat.mul_succ]

/-- Selecting one sample for every used transition produces a cover whose
cardinality is at most the number of used transitions. -/
def transitionCover
    [DecidableEq Sample]
    (used : Finset Transition)
    (witness : Transition → Sample) :
    Finset Sample :=
  used.image witness

theorem transitionCover_card_le
    [DecidableEq Transition] [DecidableEq Sample]
    (used : Finset Transition)
    (witness : Transition → Sample) :
    (transitionCover used witness).card ≤ used.card :=
  Finset.card_image_le

theorem transitionCover_exercises
    [DecidableEq Transition] [DecidableEq Sample]
    (used : Finset Transition)
    (exercises : Sample → Set Transition)
    (witness : Transition → Sample)
    (hwitness : ∀ e ∈ used, e ∈ exercises (witness e)) :
    ∀ e ∈ used, ∃ sample ∈ transitionCover used witness,
      e ∈ exercises sample := by
  intro e he
  exact ⟨witness e, by
      change witness e ∈ used.image witness
      exact Finset.mem_image.mpr ⟨e, he, rfl⟩,
    hwitness e he⟩

/-- Every finite collection of required samples appears by a finite time in
an exhaustive restricted presentation. -/
theorem finite_sample_cover_eventually_seen
    [DecidableEq Sample]
    (stream : ℕ → Sample) (source : Set Sample)
    (hcover : Covers stream source)
    (required : Finset Sample)
    (hrequired : (required : Set Sample) ⊆ source) :
    ∃ t, ∀ sample ∈ required, ∃ n, n < t ∧ stream n = sample := by
  induction required using Finset.induction_on with
  | empty =>
      exact ⟨0, by simp⟩
  | @insert sample required hnot ih =>
      have hsampleSource : sample ∈ source :=
        hrequired (by simp)
      obtain ⟨n, hn⟩ := covers_exists_eq hcover hsampleSource
      have hrequiredTail : (required : Set Sample) ⊆ source := by
        intro x hx
        exact hrequired (by simp [hx])
      obtain ⟨t, ht⟩ := ih hrequiredTail
      refine ⟨max (n + 1) t, ?_⟩
      intro x hx
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n)
          (Nat.le_max_left _ _), hn⟩
      · obtain ⟨k, hk, heq⟩ := ht x hx
        exact ⟨k, lt_of_lt_of_le hk (Nat.le_max_right _ _), heq⟩

/-- The polynomial-sample statement actually established by the finite
transition-cover argument in Theorem 21: at most `m` chosen samples suffice
to exercise all `m` used transitions, and every exhaustive ordering reaches
that cover after finite time. -/
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
        ∃ n, n < t ∧ stream n = sample := by
  refine ⟨transitionCover_card_le used witness,
    transitionCover_exercises used exercises witness hwitness, ?_⟩
  apply finite_sample_cover_eventually_seen
    stream source hcover (transitionCover used witness)
  intro sample hsample
  change sample ∈ used.image witness at hsample
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hsample
  exact hwitnessSource e he

end GenLimit.LearningAlgorithmsLimit
