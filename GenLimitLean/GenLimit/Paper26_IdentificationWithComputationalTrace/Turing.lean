import GenLimit.Paper26_IdentificationWithComputationalTrace.FiniteError
import GenLimit.Paper26_IdentificationWithComputationalTrace.ControlPath
import Mathlib.Tactic.DeriveFintype

/-! # Two-tape machine of Appendix B.3

The input tape is read-only and has distinct end blanks. The initially blank
work tape stores bits. Each transition moves both heads independently and may
write a bit at the old work-head position. Keeping the current bit is also an
instruction. Full configurations record both head positions and tape contents.
-/
namespace GenLimit.ComputationalTrace.TM
open Control

inductive Motion where | left | stay | right
  deriving Fintype, DecidableEq

def Motion.offset : Motion → ℤ
  | .left => -1
  | .stay => 0
  | .right => 1

structure Memory where
  input : List Bool
  inputHead : ℤ
  workHead : ℤ
  tape : ℤ → Bool

abbrev Observation := Option Bool × Bool
abbrev Action := Motion × Motion × Option Bool

def readInput (w : List Bool) (i : ℤ) : Option Bool :=
  if 0 ≤ i then w[i.toNat]? else none

def device : Device Memory Observation Action where
  load w := ⟨w,0,0, fun _ => false⟩
  read m := (readInput m.input m.inputHead,m.tape m.workHead)
  act m a := ⟨m.input,m.inputHead + a.1.offset,m.workHead + a.2.1.offset,
    a.2.2.elim m.tape (fun bit => Function.update m.tape m.workHead bit)⟩

@[simp] theorem isFinal_device {σ : Type} (M : Machine σ Observation Action) (c : Frame σ Memory) :
    isFinal device M c = M.final c.1 := rfl

theorem identifies_finite (C cutoff : ℕ) (M : Machine ℕ Observation Action)
    (s : ℕ → Sample Memory) (hs : Presentation device M (FiniteBound C cutoff) s) :
    ∃ H : Guess Observation Action, H.language device = language device M ∧
      ∃ T, ∀ t ≥ T, learner device C cutoff (textPrefix s t) = H :=
  identifies_finite_error device C cutoff M s hs

end GenLimit.ComputationalTrace.TM
