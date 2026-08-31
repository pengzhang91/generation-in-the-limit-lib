import GenLimit.Paper11_LearningAlgorithmsInTheLimit.Enumeration

/-!
# Policy trajectories and finite-state transducers

This file formalizes the transition-diagram identity behind Theorem 16.  A
Turing-machine policy step reads one tape symbol and emits the written symbol
and head movement; forgetting the tape geometry gives a Mealy transducer with
the same state transition diagram.
-/

namespace GenLimit.LearningAlgorithmsLimit

inductive HeadMove
  | left
  | right
  | stay
  deriving DecidableEq, Repr

structure TapeAction (Tape : Type*) where
  write : Tape
  move : HeadMove
  deriving DecidableEq

/-- A total deterministic finite-state transducer (Definition 1's semantic
core).  Finiteness is carried by a `Fintype State` instance at uses that
need it. -/
structure Mealy (State Input Output : Type*) where
  start : State
  step : State → Input → State × Output

namespace Mealy

def runFrom
    (M : Mealy State Input Output) :
    State → List Input → State × List Output
  | q, [] => (q, [])
  | q, a :: w =>
      let transition := M.step q a
      let tail := runFrom M transition.1 w
      (tail.1, transition.2 :: tail.2)

def run
    (M : Mealy State Input Output) (w : List Input) :
    State × List Output :=
  M.runFrom M.start w

@[simp] theorem runFrom_nil
    (M : Mealy State Input Output) (q : State) :
    M.runFrom q [] = (q, []) := rfl

@[simp] theorem runFrom_cons
    (M : Mealy State Input Output) (q : State)
    (a : Input) (w : List Input) :
    M.runFrom q (a :: w) =
      let transition := M.step q a
      let tail := M.runFrom transition.1 w
      (tail.1, transition.2 :: tail.2) := rfl

theorem runFrom_output_length
    (M : Mealy State Input Output) (q : State)
    (w : List Input) :
    (M.runFrom q w).2.length = w.length := by
  induction w generalizing q with
  | nil => rfl
  | cons a w ih =>
      simp only [runFrom_cons, List.length_cons]
      exact congrArg Nat.succ (ih (M.step q a).1)

theorem run_output_length
    (M : Mealy State Input Output) (w : List Input) :
    (M.run w).2.length = w.length :=
  M.runFrom_output_length M.start w

end Mealy

/-- The observable policy fragment of the paper's TM model.  Tape contents
and head position determine the scanned-symbol word; each local transition
is represented exactly here. -/
structure PolicyMachine (State Tape : Type*) where
  start : State
  step : State → Tape → State × TapeAction Tape

def PolicyMachine.toFST
    (M : PolicyMachine State Tape) :
    Mealy State Tape (TapeAction Tape) where
  start := M.start
  step := M.step

/-- The paper's `T[x]`: the action sequence generated from the scanned
symbol sequence `T{x}`. -/
def PolicyMachine.tapeBehavior
    (M : PolicyMachine State Tape) (scanned : List Tape) :
    List (TapeAction Tape) :=
  (M.toFST.run scanned).2

/-- The exact transition-diagram equation in Theorem 16:
`T[x] = ψ(T)(T{x})`. -/
theorem theorem_16_recursiveToRational_behavior
    (M : PolicyMachine State Tape) (scanned : List Tape) :
    M.tapeBehavior scanned = (M.toFST.run scanned).2 :=
  rfl

theorem theorem_16_behavior_length
    (M : PolicyMachine State Tape) (scanned : List Tape) :
    (M.tapeBehavior scanned).length = scanned.length :=
  M.toFST.run_output_length scanned

/-- The rational function computed by a Mealy transducer. -/
def rationalSemantics
    (M : Mealy State A B) (input : List A) :
    Option (List B) :=
  some (M.run input).2

/-- The learning-by-enumeration half of Theorem 16 for a supplied countable
enumeration of FSTs.  Unlike the printed Appendix D line
`w : ℕ ↠ A*`, `Covers` explicitly requires every presented word to lie in
the restricted source. -/
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
      source := by
  exact enumeration_learnsInLimit
    (fun j => rationalSemantics (machines j))
    (rationalSemantics (machines targetIndex))
    stream source hcover
    ⟨targetIndex, by intro _ _; rfl⟩

end GenLimit.LearningAlgorithmsLimit
