import GenLimit.Core.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Set.Finite.Basic

/-!
# Priority-queue generation rounds

Paper-independent state and one-round semantics for generators which retain a
finite priority queue, record every value used by either player, and otherwise
draw from an infinite current language.  Paper-specific developments remain
responsible for constructing the finite priority additions.
-/

namespace GenLimit.Support.PriorityRound

/-- State immediately before one adversary/generator round. -/
structure State where
  used : Finset ℕ
  queue : Finset ℕ
  previousOutput : Option ℕ

def State.initial : State := ⟨∅, ∅, none⟩

/-- A fresh value available either from the queue or the current language. -/
def OutputCandidate
    (preferred : Finset ℕ) (current : Language)
    (used : Finset ℕ) (x : ℕ) : Prop :=
  x ∉ used ∧ (x ∈ preferred ∨ x ∈ current)

theorem outputCandidate_exists
    (preferred : Finset ℕ) (current : Language)
    (used : Finset ℕ) (hCurrent : current.Infinite) :
    ∃ x, OutputCandidate preferred current used x := by
  obtain ⟨x, hxCurrent, hxFresh⟩ :=
    hCurrent.exists_notMem_finset used
  exact ⟨x, hxFresh, Or.inr hxCurrent⟩

/-- The least fresh value in the queue union the current language. -/
noncomputable def leastOutput
    (preferred : Finset ℕ) (current : Language)
    (used : Finset ℕ) (hCurrent : current.Infinite) : ℕ := by
  classical
  exact Nat.find (outputCandidate_exists preferred current used hCurrent)

theorem leastOutput_spec
    (preferred : Finset ℕ) (current : Language)
    (used : Finset ℕ) (hCurrent : current.Infinite) :
    OutputCandidate preferred current used
      (leastOutput preferred current used hCurrent) := by
  classical
  exact Nat.find_spec (outputCandidate_exists preferred current used hCurrent)

theorem leastOutput_min
    (preferred : Finset ℕ) (current : Language)
    (used : Finset ℕ) (hCurrent : current.Infinite)
    {x : ℕ} (hx : OutputCandidate preferred current used x) :
    leastOutput preferred current used hCurrent ≤ x := by
  classical
  exact Nat.find_min'
    (outputCandidate_exists preferred current used hCurrent) hx

/-- Output selected in a round after the adversary input has been marked
used. -/
noncomputable def emittedAtStep
    (state : State) (input : ℕ)
    (current : Language) (hCurrent : current.Infinite)
    (preferred : Finset ℕ) : ℕ :=
  leastOutput preferred current (insert input state.used) hCurrent

/-- Update the used set, remove the emitted value from the priority queue,
and remember it as the previous output. -/
noncomputable def step
    (state : State) (input : ℕ)
    (current : Language) (hCurrent : current.Infinite)
    (preferred : Finset ℕ) : State := by
  classical
  let output := emittedAtStep state input current hCurrent preferred
  exact
    ⟨insert output (insert input state.used),
      preferred.erase output, some output⟩

@[simp] theorem step_previousOutput
    (state : State) (input : ℕ)
    (current : Language) (hCurrent : current.Infinite)
    (preferred : Finset ℕ) :
    (step state input current hCurrent preferred).previousOutput =
      some (emittedAtStep state input current hCurrent preferred) := by
  rfl

theorem emittedAtStep_fresh
    (state : State) (input : ℕ)
    (current : Language) (hCurrent : current.Infinite)
    (preferred : Finset ℕ) :
    emittedAtStep state input current hCurrent preferred ∉
      insert input state.used :=
  (leastOutput_spec preferred current
    (insert input state.used) hCurrent).1

theorem emittedAtStep_mem_priority_or_current
    (state : State) (input : ℕ)
    (current : Language) (hCurrent : current.Infinite)
    (preferred : Finset ℕ) :
    emittedAtStep state input current hCurrent preferred ∈ preferred ∨
      emittedAtStep state input current hCurrent preferred ∈ current :=
  (leastOutput_spec preferred current
    (insert input state.used) hCurrent).2

theorem emittedAtStep_le_candidate
    (state : State) (input : ℕ)
    (current : Language) (hCurrent : current.Infinite)
    (preferred : Finset ℕ) {x : ℕ}
    (hxFresh : x ∉ insert input state.used)
    (hxAvailable : x ∈ preferred ∨ x ∈ current) :
    emittedAtStep state input current hCurrent preferred ≤ x :=
  leastOutput_min preferred current (insert input state.used) hCurrent
    ⟨hxFresh, hxAvailable⟩

theorem emittedAtStep_le_of_mem_step_queue
    (state : State) (input : ℕ)
    (current : Language) (hCurrent : current.Infinite)
    (preferred : Finset ℕ)
    (hpreferred : ∀ {x}, x ∈ preferred → x ∉ insert input state.used)
    {x : ℕ} (hx : x ∈ (step state input current hCurrent preferred).queue) :
    emittedAtStep state input current hCurrent preferred ≤ x := by
  have hxPreferred : x ∈ preferred := by
    change x ∈ preferred.erase
      (emittedAtStep state input current hCurrent preferred) at hx
    exact (Finset.mem_erase.mp hx).2
  exact emittedAtStep_le_candidate state input current hCurrent preferred
    (hpreferred hxPreferred) (Or.inl hxPreferred)

/-- A fresh preferred set yields a queue disjoint from the updated used set. -/
theorem step_queue_fresh
    (state : State) (input : ℕ)
    (current : Language) (hCurrent : current.Infinite)
    (preferred : Finset ℕ)
    (hpreferred : ∀ {x}, x ∈ preferred → x ∉ insert input state.used) :
    Disjoint (step state input current hCurrent preferred).queue
      (step state input current hCurrent preferred).used := by
  classical
  rw [Finset.disjoint_left]
  intro x hxQueue hxUsed
  change x ∈ preferred.erase
    (emittedAtStep state input current hCurrent preferred) at hxQueue
  change x ∈ insert
    (emittedAtStep state input current hCurrent preferred)
    (insert input state.used) at hxUsed
  rcases Finset.mem_erase.mp hxQueue with ⟨hxNe, hxPreferred⟩
  rcases Finset.mem_insert.mp hxUsed with hxOutput | hxUsedNow
  · exact hxNe hxOutput
  · exact (hpreferred hxPreferred) hxUsedNow

end GenLimit.Support.PriorityRound
