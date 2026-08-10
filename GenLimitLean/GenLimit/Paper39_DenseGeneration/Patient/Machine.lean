import GenLimit.Paper39_DenseGeneration.Critical
import GenLimit.Core.OracleFamily
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Finite.Basic

/-!
# A semantic patient-scope machine

This file gives a precise state machine for the patient-scope algorithm from
Section 3.2 of the patient-scope manuscript.  It is deliberately semantic:
criticality uses exact inclusion between languages, and the definitions below
use classical choice.  In particular, this is not the finite-membership-query
machine from `GenLimit.Paper01_LanguageGeneration.FiniteQuery.Machine`.

Time is zero-based.  A state at time `t` records the situation after the first
`t` adversary announcements and generator outputs.  A scope `s` is an
exclusive upper bound, so it contains the indices in `Finset.range s`.

The `age` field counts completed rounds with the current focus.  Consequently,
scope expansion is tested by `2 ^ tau ≤ age` before the next output.  This is
the literal meaning of waiting until the focus has been unchanged throughout
the previous `2 ^ tau` rounds.
-/

namespace GenLimit
namespace PatientMachine

/-- The reason for the most recent focus update. -/
inductive MoveKind where
  | initial
  | stay
  | expand
  | backtrack
deriving DecidableEq, Repr

/-- State after a finite number of complete adversary/generator rounds. -/
structure State where
  /-- Exclusive upper bound on language indices in scope. -/
  scope : ℕ
  /-- Number of focus changes, initialized to one as in the paper. -/
  tau : ℕ
  /-- Number of completed consecutive rounds with the current focus. -/
  age : ℕ
  /-- Index of the current focus language. -/
  focus : ℕ
  /-- All values previously output by the generator. -/
  used : Finset ℕ
  /-- Output of the most recently completed round. -/
  lastOutput : Option ℕ
  /-- Branch taken in the most recently completed round. -/
  move : MoveKind

/-- The initial state, before either party has announced a value. -/
def initialState : State where
  scope := 1
  tau := 1
  age := 0
  focus := 0
  used := ∅
  lastOutput := none
  move := .initial

/-- Indices that are consistent after `t` observations and lie in scope. -/
noncomputable def consistentIndices
    (C : LanguageFamily) (stream : ℕ → ℕ) (t scope : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range scope).filter (Consistent C stream t)

/-- Critical indices after `t` observations and inside the given scope. -/
noncomputable def criticalIndices
    (C : LanguageFamily) (stream : ℕ → ℕ) (t scope : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range scope).filter (RecursiveCritical C stream t)

/-- Old critical indices that remain critical after the current observation. -/
noncomputable def survivingCriticalIndices
    (C : LanguageFamily) (stream : ℕ → ℕ) (t scope : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range scope).filter fun i =>
    RecursiveCritical C stream t i ∧ RecursiveCritical C stream (t + 1) i

@[simp] theorem mem_consistentIndices
    {C : LanguageFamily} {stream : ℕ → ℕ} {t scope i : ℕ} :
    i ∈ consistentIndices C stream t scope ↔
      i < scope ∧ Consistent C stream t i := by
  classical
  simp [consistentIndices]

@[simp] theorem mem_criticalIndices
    {C : LanguageFamily} {stream : ℕ → ℕ} {t scope i : ℕ} :
    i ∈ criticalIndices C stream t scope ↔
      i < scope ∧ RecursiveCritical C stream t i := by
  classical
  simp [criticalIndices]

@[simp] theorem mem_survivingCriticalIndices
    {C : LanguageFamily} {stream : ℕ → ℕ} {t scope i : ℕ} :
    i ∈ survivingCriticalIndices C stream t scope ↔
      i < scope ∧ RecursiveCritical C stream t i ∧
        RecursiveCritical C stream (t + 1) i := by
  classical
  simp [survivingCriticalIndices]

/-- Highest critical index in scope, with an explicit fallback for histories
outside the paper's model. -/
noncomputable def highestCritical
    (C : LanguageFamily) (stream : ℕ → ℕ) (t scope fallback : ℕ) : ℕ := by
  classical
  let candidates := criticalIndices C stream t scope
  exact if h : candidates.Nonempty then candidates.max' h else fallback

/-- Highest old critical index that is still critical, again totalized by an
explicit fallback. -/
noncomputable def highestSurvivor
    (C : LanguageFamily) (stream : ℕ → ℕ) (t scope fallback : ℕ) : ℕ := by
  classical
  let candidates := survivingCriticalIndices C stream t scope
  exact if h : candidates.Nonempty then candidates.max' h else fallback

/-- Lowest consistent index in a nonempty finite scope. -/
noncomputable def lowestConsistentInScope
    (C : LanguageFamily) (stream : ℕ → ℕ) (t scope fallback : ℕ) : ℕ := by
  classical
  let candidates := consistentIndices C stream t scope
  exact if h : candidates.Nonempty then candidates.min' h else fallback

/-- Lowest globally consistent language.  The fallback makes the definition
total on streams that have no consistent language in the family. -/
noncomputable def lowestConsistent
    (C : LanguageFamily) (stream : ℕ → ℕ) (t fallback : ℕ) : ℕ := by
  classical
  exact if h : ∃ i, Consistent C stream t i then Nat.find h else fallback

theorem highestCritical_isFocus
    {C : LanguageFamily} {stream : ℕ → ℕ} {t scope fallback : ℕ}
    (hne : (criticalIndices C stream t scope).Nonempty) :
    IsFocus C stream t scope
      (highestCritical C stream t scope fallback) := by
  classical
  let candidates := criticalIndices C stream t scope
  have hne' : candidates.Nonempty := hne
  have hmem : candidates.max' hne' ∈ candidates := candidates.max'_mem hne'
  have hparts : candidates.max' hne' < scope ∧
      RecursiveCritical C stream t (candidates.max' hne') := by
    simpa [candidates] using hmem
  have hmax : ∀ j, j < scope → RecursiveCritical C stream t j →
      j ≤ candidates.max' hne' := by
    intro j hjs hj
    exact Finset.le_max' candidates j (by simp [candidates, hjs, hj])
  simpa [highestCritical, candidates, hne'] using
    (show IsFocus C stream t scope (candidates.max' hne') from
      ⟨hparts.1, hparts.2, hmax⟩)

theorem highestSurvivor_spec
    {C : LanguageFamily} {stream : ℕ → ℕ} {t scope fallback : ℕ}
    (hne : (survivingCriticalIndices C stream t scope).Nonempty) :
    let i := highestSurvivor C stream t scope fallback
    i < scope ∧ RecursiveCritical C stream t i ∧
      RecursiveCritical C stream (t + 1) i ∧
      ∀ j, j < scope → RecursiveCritical C stream t j →
        RecursiveCritical C stream (t + 1) j → j ≤ i := by
  classical
  let candidates := survivingCriticalIndices C stream t scope
  have hne' : candidates.Nonempty := hne
  have hmem : candidates.max' hne' ∈ candidates := candidates.max'_mem hne'
  have hparts : candidates.max' hne' < scope ∧
      RecursiveCritical C stream t (candidates.max' hne') ∧
      RecursiveCritical C stream (t + 1) (candidates.max' hne') := by
    simpa [candidates] using hmem
  have hmax : ∀ j, j < scope → RecursiveCritical C stream t j →
      RecursiveCritical C stream (t + 1) j → j ≤ candidates.max' hne' := by
    intro j hjs hjold hjnew
    exact Finset.le_max' candidates j
      (by simp [candidates, hjs, hjold, hjnew])
  have heq : highestSurvivor C stream t scope fallback =
      candidates.max' hne' := by
    simp only [highestSurvivor]
    rw [dif_pos hne']
  rw [heq]
  exact ⟨hparts.1, hparts.2.1, hparts.2.2, hmax⟩

theorem lowestConsistentInScope_spec
    {C : LanguageFamily} {stream : ℕ → ℕ} {t scope fallback : ℕ}
    (hne : (consistentIndices C stream t scope).Nonempty) :
    let i := lowestConsistentInScope C stream t scope fallback
    i < scope ∧ Consistent C stream t i ∧
      ∀ j, j < i → ¬ Consistent C stream t j := by
  classical
  let candidates := consistentIndices C stream t scope
  have hne' : candidates.Nonempty := hne
  have hmem : candidates.min' hne' ∈ candidates := candidates.min'_mem hne'
  have hparts : candidates.min' hne' < scope ∧
      Consistent C stream t (candidates.min' hne') := by
    simpa [candidates] using hmem
  have hmin : ∀ j, j < candidates.min' hne' →
      ¬ Consistent C stream t j := by
    intro j hj hcon
    have hjs : j < scope := lt_trans hj hparts.1
    have hjmem : j ∈ candidates := by simp [candidates, hjs, hcon]
    exact (Nat.not_lt_of_ge (Finset.min'_le candidates j hjmem)) hj
  have heq : lowestConsistentInScope C stream t scope fallback =
      candidates.min' hne' := by
    simp only [lowestConsistentInScope]
    rw [dif_pos hne']
  rw [heq]
  exact ⟨hparts.1, hparts.2, hmin⟩

theorem lowestConsistent_spec
    {C : LanguageFamily} {stream : ℕ → ℕ} {t fallback : ℕ}
    (hne : ∃ i, Consistent C stream t i) :
    Consistent C stream t (lowestConsistent C stream t fallback) ∧
      ∀ j, j < lowestConsistent C stream t fallback →
        ¬ Consistent C stream t j := by
  classical
  have hspec := Nat.find_spec hne
  have hmin : ∀ j, j < Nat.find hne → ¬ Consistent C stream t j :=
    fun j hj => Nat.find_min hne hj
  have heq : lowestConsistent C stream t fallback = Nat.find hne := by
    simp only [lowestConsistent]
    rw [dif_pos hne]
  rw [heq]
  exact ⟨hspec, hmin⟩

/-- A consistent index with no earlier consistent predecessor is
recursively critical. -/
theorem recursiveCritical_of_consistent_of_minimal
    {C : LanguageFamily} {stream : ℕ → ℕ} {t i : ℕ}
    (hcon : Consistent C stream t i)
    (hmin : ∀ j, j < i → ¬ Consistent C stream t j) :
    RecursiveCritical C stream t i := by
  cases i with
  | zero => simpa only [RecursiveCritical] using hcon
  | succ n =>
      rw [RecursiveCritical]
      refine ⟨hcon, ?_⟩
      intro j hj hjcrit
      exact False.elim
        (hmin j (Nat.lt_succ_of_le hj) (recursiveCritical_consistent hjcrit))

/-- The focus/scope part of a transition, before producing the output. -/
structure Decision where
  scope : ℕ
  tau : ℕ
  focus : ℕ
  move : MoveKind

/-- Backtracking after round `t`'s adversary announcement falsifies the old
focus.  Criticality before the announcement is evaluated at `t`; criticality
after it is evaluated at `t + 1`.

If the old scope still contains a consistent language, the machine keeps the
highest old critical language that remains critical.  When none survives, it
uses the lowest consistent language in that scope.  If the old scope has no
consistent language, it expands to the globally lowest consistent index. -/
noncomputable def backtrackDecision
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State) : Decision := by
  classical
  let consistent := consistentIndices C stream (t + 1) old.scope
  if hcon : consistent.Nonempty then
    let survivors := survivingCriticalIndices C stream t old.scope
    let i := if survivors.Nonempty then
      highestSurvivor C stream t old.scope old.focus
    else
      lowestConsistentInScope C stream (t + 1) old.scope old.focus
    exact ⟨i + 1, old.tau + 1, i, .backtrack⟩
  else
    let i := lowestConsistent C stream (t + 1) old.focus
    if hall : ∃ j, Consistent C stream (t + 1) j then
      exact ⟨i + 1, old.tau + 1, i, .backtrack⟩
    else
      -- Off-model case: preserve a positive scope and the old focus.
      exact ⟨max old.scope 1, old.tau + 1, old.focus, .backtrack⟩

/-- Stable-focus update.  Once `2 ^ tau` complete rounds have elapsed under
the current focus, the exclusive scope grows by one. -/
noncomputable def stableDecision
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State) : Decision := by
  classical
  if hwait : 2 ^ old.tau ≤ old.age then
    let newScope := old.scope + 1
    let newFocus := highestCritical C stream (t + 1) newScope old.focus
    let newTau := if newFocus = old.focus then old.tau else old.tau + 1
    exact ⟨newScope, newTau, newFocus, .expand⟩
  else
    exact ⟨old.scope, old.tau, old.focus, .stay⟩

/-- Focus update after receiving the adversary value in round `t`. -/
noncomputable def decide
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) (old : State) : Decision := by
  classical
  exact if Consistent C stream (t + 1) old.focus then
    stableDecision C stream t old
  else
    backtrackDecision C stream t old

/-- A value is available for output when it is in the focus and has been
announced by neither party. -/
def Available
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ)
    (used : Finset ℕ) (focus x : ℕ) : Prop :=
  x ∈ C focus ∧ x ∉ sample stream t ∧ x ∉ used

theorem available_exists
    (C : LanguageFamily) (hInfinite : ∀ i, (C i).Infinite)
    (stream : ℕ → ℕ) (t : ℕ) (used : Finset ℕ) (focus : ℕ) :
    ∃ x, Available C stream t used focus x := by
  classical
  obtain ⟨x, hx, hfresh⟩ :=
    (hInfinite focus).exists_notMem_finset (sample stream t ∪ used)
  simp only [Finset.mem_union, not_or] at hfresh
  exact ⟨x, hx, hfresh.1, hfresh.2⟩

/-- Smallest value in the focus not previously announced by either party. -/
noncomputable def leastAvailable
    (C : LanguageFamily) (hInfinite : ∀ i, (C i).Infinite)
    (stream : ℕ → ℕ) (t : ℕ) (used : Finset ℕ) (focus : ℕ) : ℕ := by
  classical
  exact Nat.find (available_exists C hInfinite stream t used focus)

theorem leastAvailable_spec
    (C : LanguageFamily) (hInfinite : ∀ i, (C i).Infinite)
    (stream : ℕ → ℕ) (t : ℕ) (used : Finset ℕ) (focus : ℕ) :
    Available C stream t used focus
      (leastAvailable C hInfinite stream t used focus) := by
  classical
  exact Nat.find_spec (available_exists C hInfinite stream t used focus)

theorem leastAvailable_minimal
    (C : LanguageFamily) (hInfinite : ∀ i, (C i).Infinite)
    (stream : ℕ → ℕ) (t : ℕ) (used : Finset ℕ) (focus x : ℕ)
    (hx : Available C stream t used focus x) :
    leastAvailable C hInfinite stream t used focus ≤ x := by
  classical
  exact Nat.find_min' (available_exists C hInfinite stream t used focus) hx

/-- Execute round `t`: receive `stream t`, update the focus, and announce the
smallest fresh value in the resulting focus. -/
noncomputable def processRound
    (O : OracleFamily)
    (stream : ℕ → ℕ) (t : ℕ) (old : State) : State := by
  classical
  let d := decide O.language stream t old
  let x := leastAvailable O.language O.infinite' stream (t + 1) old.used d.focus
  exact
    { scope := d.scope
      tau := d.tau
      age := if d.focus = old.focus then old.age + 1 else 1
      focus := d.focus
      used := insert x old.used
      lastOutput := some x
      move := d.move }

/-- State after the first `t` complete rounds. -/
noncomputable def run
    (O : OracleFamily)
    (stream : ℕ → ℕ) : ℕ → State
  | 0 => initialState
  | t + 1 => processRound O stream t (run O stream t)

/-- The generator's round-`t` announcement. -/
noncomputable def output
    (O : OracleFamily)
    (stream : ℕ → ℕ) (t : ℕ) : ℕ :=
  (run O stream (t + 1)).lastOutput.getD 0

@[simp] theorem run_zero
    (O : OracleFamily)
    (stream : ℕ → ℕ) :
    run O stream 0 = initialState := rfl

@[simp] theorem run_succ
    (O : OracleFamily)
    (stream : ℕ → ℕ) (t : ℕ) :
    run O stream (t + 1) =
      processRound O stream t (run O stream t) := rfl

@[simp] theorem processRound_lastOutput
    (O : OracleFamily)
    (stream : ℕ → ℕ) (t : ℕ) (old : State) :
    (processRound O stream t old).lastOutput =
      some (leastAvailable O.language O.infinite' stream (t + 1) old.used
        (decide O.language stream t old).focus) := by
  simp [processRound]

@[simp] theorem output_eq_leastAvailable
    (O : OracleFamily)
    (stream : ℕ → ℕ) (t : ℕ) :
    output O stream t =
      leastAvailable O.language O.infinite' stream (t + 1)
        (run O stream t).used
        (decide O.language stream t (run O stream t)).focus := by
  simp [output]

/-- Every output belongs to the focus selected in its round, is absent from
the adversary sample through that round, and was not output earlier. -/
theorem output_available
    (O : OracleFamily)
    (stream : ℕ → ℕ) (t : ℕ) :
    Available O.language stream (t + 1) (run O stream t).used
      (decide O.language stream t (run O stream t)).focus
      (output O stream t) := by
  rw [output_eq_leastAvailable]
  exact leastAvailable_spec O.language O.infinite' stream (t + 1)
    (run O stream t).used
    (decide O.language stream t (run O stream t)).focus

end PatientMachine
end GenLimit
