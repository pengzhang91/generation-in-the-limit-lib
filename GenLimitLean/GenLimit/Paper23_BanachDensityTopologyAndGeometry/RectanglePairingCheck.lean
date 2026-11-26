import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! A finite check on inequality (28) in the proof of Theorem 5.5.
All four points lie on one horizontal lattice line, so their distances
in the infinity norm are their horizontal distances. Each adversarial
input has a unique closest available point of the opposite color. Both
partners are outside a rectangle with exactly balanced colors. -/
namespace GenLimit.KleinbergWei.Banach.FilteredPairing

def pos : Fin 4 → ℤ := ![1,2,5,6]
def color : Fin 4 → ℤ := ![-1,1,-1,1]

private def traceLine (l u : ℤ) : Finset (Fin 4) := Finset.univ.filter fun i => l ≤ pos i ∧ pos i ≤ u

/-- Every rectangular trace of this coloring has discrepancy at most one.
A horizontal line intersects an axis-parallel rectangle in an interval. -/
theorem coloring_balanced (l u : ℤ) : |∑ i ∈ traceLine l u, color i| ≤ 1 := by
  have check : ∀ S : Finset (Fin 4),
      (∀ i ∈ S, ∀ j ∈ S, ∀ k : Fin 4, i ≤ k → k ≤ j → k ∈ S) →
      |∑ i ∈ S, color i| ≤ 1 := by decide
  have ordered : ∀ a b : Fin 4, a ≤ b → pos a ≤ pos b := by decide
  apply check
  intro i hi j hj k ik kj
  simp only [traceLine,Finset.mem_filter,Finset.mem_univ,true_and] at *
  exact ⟨hi.1.trans (ordered _ _ ik),(ordered _ _ kj).trans hj.2⟩

def UniqueClosest (available : Finset (Fin 4)) (input output : Fin 4) :=
  output ∈ available ∧ color output = -color input ∧
    ∀ v ∈ available, color v = -color input → v ≠ output →
      |pos input-pos output| < |pos input-pos v|

/-- The inputs at 2 and 5 force outputs at 1 and 6. On the second
round the first input and its output are already occupied. Inside
[2,5] the input excess is two while the coloring discrepancy is zero. -/
theorem nearest_opposite_exits :
    UniqueClosest (Finset.univ.erase 1) 1 0 ∧
    UniqueClosest (Finset.univ \ {0,1,2}) 2 3 ∧
    let B := traceLine 2 5
    let inputs : Finset (Fin 4) := {1,2}
    let outputs : Finset (Fin 4) := {0,3}
    (B ∩ inputs).card = 2 ∧ (B ∩ outputs).card = 0 ∧ |∑ v ∈ B, color v| = 0 := by
  unfold UniqueClosest
  decide

end GenLimit.KleinbergWei.Banach.FilteredPairing
