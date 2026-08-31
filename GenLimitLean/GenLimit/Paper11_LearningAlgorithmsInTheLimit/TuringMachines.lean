import GenLimit.Paper11_LearningAlgorithmsInTheLimit.Enumeration
import Mathlib.Logic.Equiv.List
import Mathlib.Tactic.DeriveEncodable

/-!
# A concrete Turing-machine evaluator for Corollary 15

The paper separates an abstract machine from its input-setting and
output-reading convention.  This file follows that separation while making
the machine dynamics concrete: a deterministic single-tape program has a
finite transition table, natural-number states, start state `1`, halt state
`0`, and a bidirectionally infinite tape represented by two finite lists plus
the scanned cell.  Missing table entries transition to the halt state.

Programs form an effectively enumerable datatype.  `runWithin` is a total,
executable bounded evaluator, which is the operation needed by the TBO
learner.  No unbounded halting oracle is introduced.
-/

namespace GenLimit.LearningAlgorithmsLimit

inductive TuringHeadMove
  | left
  | right
  | stay
  deriving DecidableEq, Repr, Encodable

/-- The finite tape content around the scanned cell.  `left` is stored with
the nearest cell first, and likewise for `right`; omitted cells are blank. -/
structure TuringTape (Symbol : Type*) where
  left : List Symbol
  scanned : Symbol
  right : List Symbol

namespace TuringTape

/-- Write the scanned cell and perform one concrete head movement. -/
def writeAndMove
    (blank write : Symbol) (move : TuringHeadMove)
    (tape : TuringTape Symbol) : TuringTape Symbol :=
  match move with
  | .stay => ⟨tape.left, write, tape.right⟩
  | .left =>
      match tape.left with
      | [] => ⟨[], blank, write :: tape.right⟩
      | next :: rest => ⟨rest, next, write :: tape.right⟩
  | .right =>
      match tape.right with
      | [] => ⟨write :: tape.left, blank, []⟩
      | next :: rest => ⟨write :: tape.left, next, rest⟩

end TuringTape

/-- A transition writes one symbol, moves the head, and selects the next
state. -/
abbrev TuringInstruction (Symbol : Type*) :=
  ℕ × Symbol × TuringHeadMove

/-- A finite transition table.  Entry `pair state (encode symbol)` contains
the instruction for that state and scanned symbol. -/
abbrev TuringProgram (Symbol : Type*) :=
  List (TuringInstruction Symbol)

/-- Input-setting and output-reading conventions for a fixed tape alphabet. -/
structure TuringIO (Symbol Input Output : Type*) where
  blank : Symbol
  initTape : Input → TuringTape Symbol
  readOutput : TuringTape Symbol → Option Output

structure TuringConfiguration (Symbol : Type*) where
  state : ℕ
  tape : TuringTape Symbol

namespace TuringProgram

/-- Decode the instruction table at a state/symbol pair.  A missing entry
halts without changing the scanned symbol. -/
def instruction
    [Encodable Symbol]
    (program : TuringProgram Symbol) (state : ℕ) (scanned : Symbol) :
    TuringInstruction Symbol :=
  (program[Nat.pair state (Encodable.encode scanned)]?).getD
    (0, scanned, .stay)

/-- One deterministic transition; `none` means the designated halt state has
already been reached. -/
def step
    [Encodable Symbol]
    (blank : Symbol) (program : TuringProgram Symbol)
    (configuration : TuringConfiguration Symbol) :
    Option (TuringConfiguration Symbol) :=
  if configuration.state = 0 then none
  else
    let action := program.instruction configuration.state
      configuration.tape.scanned
    some
      { state := action.1
        tape := configuration.tape.writeAndMove blank action.2.1 action.2.2 }

/-- Execute at most the given number of machine transitions.  A halted
configuration remains halted for the unused part of the budget. -/
def runConfiguration
    [Encodable Symbol]
    (blank : Symbol) (program : TuringProgram Symbol) :
    ℕ → TuringConfiguration Symbol → TuringConfiguration Symbol
  | 0, configuration => configuration
  | budget + 1, configuration =>
      match program.step blank configuration with
      | none => configuration
      | some next => runConfiguration blank program budget next

/-- Concrete bounded evaluation from the start state.  It returns an output
exactly when the machine reaches halt state `0` within the budget and the
output convention accepts the final tape. -/
def runWithin
    [Encodable Symbol]
    (budget : ℕ) (io : TuringIO Symbol Input Output)
    (program : TuringProgram Symbol) (input : Input) : Option Output :=
  let final := program.runConfiguration io.blank budget
    { state := 1, tape := io.initTape input }
  if final.state = 0 then io.readOutput final.tape else none

end TuringProgram

/-- Decode a program from its effective natural-number representation.
Numbers outside the image of `Encodable.encode` denote the empty program. -/
def decodeTuringProgram
    [Encodable Symbol] (code : ℕ) : TuringProgram Symbol :=
  (Encodable.decode code).getD []

@[simp] theorem decodeTuringProgram_encode
    [Encodable Symbol] (program : TuringProgram Symbol) :
    decodeTuringProgram (Encodable.encode program) = program := by
  simp [decodeTuringProgram]

/-- A TBO candidate fixes both a scale and a concrete program code.  Pairing
them prevents later budget increases from reintroducing an earlier rejected
candidate. -/
def turingCandidateScale (candidate : ℕ) : ℕ :=
  candidate.unpair.1

def turingCandidateProgramCode (candidate : ℕ) : ℕ :=
  candidate.unpair.2

def turingCandidateProgram
    [Encodable Symbol] (candidate : ℕ) : TuringProgram Symbol :=
  decodeTuringProgram (turingCandidateProgramCode candidate)

@[simp] theorem turingCandidateScale_pair
    (scale : ℕ) [Encodable Symbol]
    (program : TuringProgram Symbol) :
    turingCandidateScale
        (Nat.pair scale (Encodable.encode program)) = scale := by
  simp [turingCandidateScale]

@[simp] theorem turingCandidateProgram_pair
    (scale : ℕ) [Encodable Symbol]
    (program : TuringProgram Symbol) :
    turingCandidateProgram
        (Nat.pair scale (Encodable.encode program)) = program := by
  simp [turingCandidateProgram, turingCandidateProgramCode]

/-- Relational, halting semantics on a restricted source.  This avoids
pretending that unbounded Turing evaluation is an `Option`-valued algorithm. -/
def TuringComputesOn
    [Encodable Symbol]
    (io : TuringIO Symbol Input Output)
    (program : TuringProgram Symbol)
    (target : Input → Output) (source : Set Input) : Prop :=
  ∀ input ∈ source, ∃ budget,
    program.runWithin budget io input = some (target input)

def TuringCandidateComputesOn
    [Encodable Symbol]
    (io : TuringIO Symbol Input Output)
    (candidate : ℕ)
    (target : Input → Output) (source : Set Input) : Prop :=
  TuringComputesOn io (turingCandidateProgram candidate) target source

end GenLimit.LearningAlgorithmsLimit
