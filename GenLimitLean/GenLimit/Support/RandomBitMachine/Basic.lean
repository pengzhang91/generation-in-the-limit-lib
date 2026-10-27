import GenLimit.Support.BinaryWords
import GenLimit.Support.ComputableLists
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.Compactness.Compact

/-!
# Computable binary-branching operational machines

Configurations and outputs have natural-number encodings. An action either
halts, makes a deterministic transition, or reads a fair Boolean and chooses
between two successors. One tape coordinate is allocated per small step;
deterministic steps ignore their coordinate. This padding makes finite-prefix
causality explicit. `readTrace` records only the coordinates actually used by
coin actions. Internal transitions are computable total functions; unbounded
execution is not assumed computable or terminating.
-/

namespace GenLimit.Support.RandomBitMachine

/-- Halt with an output, deterministic successor, or two coin successors. -/
abbrev Action := ℕ ⊕ (ℕ ⊕ (ℕ × ℕ))
/-- A running configuration or a completed output. -/
abbrev Configuration := ℕ ⊕ ℕ

structure Machine where
  initial : ℕ → ℕ
  action : ℕ → Action
  initial_computable : Computable initial
  action_computable : Computable action

namespace Machine

def advance (M : Machine) (bit : Bool) : Configuration → Configuration
  | .inr output => .inr output
  | .inl state =>
    match M.action state with
    | .inl output => .inr output
    | .inr (.inl next) => .inl next
    | .inr (.inr next) => .inl (if bit then next.2 else next.1)

def evaluate (M : Machine) (c : Configuration) (bits : List Bool) : Configuration :=
  bits.foldl (fun current bit => M.advance bit current) c

def tapePrefix (tape : ℕ → Bool) (n : ℕ) : List Bool := (List.range n).map tape

def run (M : Machine) (input : ℕ) (tape : ℕ → Bool) (n : ℕ) : Configuration :=
  M.evaluate (.inl (M.initial input)) (tapePrefix tape n)

def AlwaysHalts (M : Machine) : Prop :=
  ∀ input tape, ∃ n output, M.run input tape n = .inr output

def CanOutput (M : Machine) (input output : ℕ) : Prop :=
  ∃ bits : List Bool, M.evaluate (.inl (M.initial input)) bits = .inr output

@[simp] theorem evaluate_nil (M : Machine) (c : Configuration) : M.evaluate c [] = c := rfl

@[simp] theorem evaluate_cons (M : Machine) (c : Configuration) (b : Bool) (bs : List Bool) :
    M.evaluate c (b :: bs) = M.evaluate (M.advance b c) bs := rfl

@[simp] theorem evaluate_halted (M : Machine) (output : ℕ) (bits : List Bool) :
    M.evaluate (.inr output) bits = .inr output := by
  induction bits with
  | nil => rfl
  | cons b bs ih => exact ih

theorem evaluate_append (M : Machine) (c : Configuration) (xs ys : List Bool) :
    M.evaluate c (xs ++ ys) = M.evaluate (M.evaluate c xs) ys := List.foldl_append

theorem run_succ (M : Machine) (input : ℕ) (tape : ℕ → Bool) (n : ℕ) :
    M.run input tape (n + 1) = M.advance (tape n) (M.run input tape n) := by
  simp [run, tapePrefix, List.range_succ, List.map_append, evaluate]

theorem run_halted_mono (M : Machine) (input : ℕ) (tape : ℕ → Bool)
    {n m output : ℕ} (hnm : n ≤ m) (h : M.run input tape n = .inr output) :
    M.run input tape m = .inr output := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  clear hnm
  induction k with
  | zero => exact h
  | succ k ih => rw [Nat.add_succ, run_succ, ih]; rfl

theorem run_prefix (M : Machine) (input : ℕ) (tape other : ℕ → Bool) (n : ℕ)
    (h : ∀ k < n, tape k = other k) : M.run input tape n = M.run input other n := by
  unfold run tapePrefix
  congr 1
  exact List.map_congr_left (fun k hk => h k (List.mem_range.mp hk))

/-- Actual random-bit reads along a finite padded execution. -/
def readTrace (M : Machine) : Configuration → List Bool → List Bool
  | _, [] => []
  | .inr _, _ :: _ => []
  | .inl s, b :: bs =>
    match M.action s with
    | .inl _ => []
    | .inr (.inl next) => M.readTrace (.inl next) bs
    | .inr (.inr next) => b :: M.readTrace (.inl (if b then next.2 else next.1)) bs

theorem readTrace_length_le (M : Machine) (c : Configuration) (bits : List Bool) :
    (M.readTrace c bits).length ≤ bits.length := by
  induction bits generalizing c with
  | nil => simp [readTrace]
  | cons b bs ih =>
    cases c with
    | inr output => simp [readTrace]
    | inl s =>
      cases h : M.action s with
      | inl output => simp [readTrace, h]
      | inr next =>
        cases next with
        | inl next => simpa [readTrace, h] using (ih (.inl next)).trans (Nat.le_succ _)
        | inr next => simpa [readTrace, h] using Nat.succ_le_succ (ih (.inl (if b then next.2 else next.1)))

end Machine
end GenLimit.Support.RandomBitMachine
