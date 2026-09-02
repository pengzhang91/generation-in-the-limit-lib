import GenLimit.Paper13_ParetoOptimalNonuniformGeneration.Order
import Mathlib.Data.Set.Finite.Basic

/-!
# The admissible-sequence core of Proposition 3.3

For the co-singleton family `ℤ \ {eᵢ}`, the paper proves that a positive
time vector is achievable exactly when every upper level set is infinite.
The final Pareto-impossibility argument is purely order theoretic: lowering
one coordinate to one preserves that condition.  This file formalizes that
entire frontier argument, leaving the separate algorithm/admissibility
equivalence visibly outside the theorem.
-/

namespace GenLimit.ParetoGeneration

/-- The admissibility condition in the proof of Proposition 3.3. -/
def TailAdmissible (time : TimeVector) : Prop :=
  ∀ k, ({i | k ≤ time i} : Set ℕ).Infinite

/-- Positive admissible sequences, the exact order-theoretic feasible region
identified in the proof for the co-singleton family. -/
def PositiveAdmissibleVectors : Set TimeVector :=
  {time | (∀ i, 1 ≤ time i) ∧ TailAdmissible time}

/-- Replace one coordinate by the earliest permitted generation time. -/
def lowerCoordinate (time : TimeVector) (i : ℕ) : TimeVector :=
  fun j => if j = i then 1 else time j

@[simp] theorem lowerCoordinate_same (time : TimeVector) (i : ℕ) :
    lowerCoordinate time i i = 1 := by
  simp [lowerCoordinate]

@[simp] theorem lowerCoordinate_other
    (time : TimeVector) {i j : ℕ} (hji : j ≠ i) :
    lowerCoordinate time i j = time j := by
  simp [lowerCoordinate, hji]

/-- An admissible vector cannot be constantly one: its level-two set must
already be infinite. -/
theorem TailAdmissible.exists_gt_one
    {time : TimeVector} (h : TailAdmissible time) :
    ∃ i, 1 < time i := by
  obtain ⟨i, hi⟩ := (h 2).nonempty
  exact ⟨i, hi⟩

/-- Removing at most one index from every infinite level set preserves
admissibility. -/
theorem TailAdmissible.lowerCoordinate
    {time : TimeVector} (h : TailAdmissible time) (i : ℕ) :
    TailAdmissible (lowerCoordinate time i) := by
  intro k
  have hinfinite :
      (({j | k ≤ time j} : Set ℕ) \ {i}).Infinite :=
    (h k).diff (Set.finite_singleton i)
  apply hinfinite.mono
  intro j hj
  have hji : j ≠ i := by
    simpa only [Set.mem_singleton_iff] using hj.2
  simpa [lowerCoordinate, hji] using hj.1

theorem positive_lowerCoordinate
    {time : TimeVector} (h : ∀ j, 1 ≤ time j) (i : ℕ) :
    ∀ j, 1 ≤ lowerCoordinate time i j := by
  intro j
  by_cases hji : j = i
  · simp [lowerCoordinate, hji]
  · simpa [lowerCoordinate, hji] using h j

/-- Lowering a coordinate that was larger than one is a strict Pareto
improvement and never worsens any coordinate. -/
theorem lowerCoordinate_strictlyDominates
    {time : TimeVector} {i : ℕ} (hPositive : ∀ j, 1 ≤ time j)
    (hi : 1 < time i) :
    ImprovesSomewhere (lowerCoordinate time i) time ∧
      ¬ WorseSomewhere (lowerCoordinate time i) time := by
  constructor
  · exact ⟨i, by simpa using hi⟩
  · rintro ⟨j, hj⟩
    by_cases hji : j = i
    · subst j
      rw [lowerCoordinate_same] at hj
      exact (Nat.not_lt_of_ge (hPositive i)) hj
    · rw [lowerCoordinate_other time hji] at hj
      exact (Nat.lt_irrefl _) hj

/-- No positive admissible sequence is a Pareto-minimal point of the
admissible region.  This is the final contradiction in Proposition 3.3. -/
theorem no_paretoOptimal_positiveAdmissible
    (time : TimeVector) (htime : time ∈ PositiveAdmissibleVectors) :
    ¬ ParetoOptimal PositiveAdmissibleVectors time := by
  intro hPareto
  obtain ⟨i, hi⟩ := htime.2.exists_gt_one
  have hLower :
      lowerCoordinate time i ∈ PositiveAdmissibleVectors :=
    ⟨positive_lowerCoordinate htime.1 i,
      htime.2.lowerCoordinate i⟩
  have hDominates :=
    lowerCoordinate_strictlyDominates htime.1 hi
  exact hDominates.2 (hPareto (lowerCoordinate time i) hLower hDominates.1)

end GenLimit.ParetoGeneration
