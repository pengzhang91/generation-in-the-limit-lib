import GenLimit.Paper26_IdentificationWithComputationalTrace.FiniteControl
import Mathlib.Tactic.DeriveFintype

/-! # Binary deterministic pushdown machines

An instruction consumes the next input symbol or leaves it unread, and pops,
keeps, or pushes one stack symbol. The current lookahead may be the end of the
input. A computation accepts exactly when both input and stack are empty.
-/
namespace GenLimit.ComputationalTrace.PDA
open Control

inductive Op where | pop | keep | push (bit : Bool)
  deriving DecidableEq, Fintype
abbrev Action := Bool × Op
abbrev Observation := Option Bool × Option Bool

structure Memory where
  input : List Bool
  stack : List Bool
  deriving DecidableEq

def Op.apply (o : Op) (stack : List Bool) :=
  match o with
  | .pop => stack.tail
  | .keep => stack
  | .push b => b :: stack

def device : Device Memory Observation Action where
  load w := ⟨w,[false]⟩
  read m := (m.input.head?,m.stack.head?)
  act m a := ⟨if a.1 then m.input.tail else m.input, a.2.apply m.stack⟩
  terminal m := m.input.isEmpty && m.stack.isEmpty

structure Program (σ : Type) where
  initial : σ
  rule : σ → Bool → Option Bool → Option (σ × Action)

def Program.machine {σ : Type} (P : Program σ) : Machine σ Observation Action where
  initial := P.initial
  final _ := true
  table q obs := do
    let top ← obs.2
    let (r,act) ← P.rule q top obs.1
    if act.1 && obs.1.isNone then none else some (r,act)

@[simp] theorem final_program {σ : Type} (P : Program σ) (c : Frame σ Memory) :
    isFinal device P.machine c = (c.2.input.isEmpty && c.2.stack.isEmpty) := by
  simp [isFinal,Program.machine,device]

end GenLimit.ComputationalTrace.PDA
