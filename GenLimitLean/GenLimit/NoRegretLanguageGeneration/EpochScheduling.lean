import Std

namespace PredictionToGeneration

/-- Sum of the budgets of epochs strictly before `j`. -/
def epochBudget (C : Nat → Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => epochBudget C j + C j

theorem epochBudget_mono (C : Nat → Nat) {i j : Nat} (hij : i ≤ j) :
    epochBudget C i ≤ epochBudget C j := by
  induction j with
  | zero =>
    have he : i = 0 := by omega
    rw [he]
    exact Nat.le_refl _
  | succ j ih =>
    by_cases he : i = j + 1
    · subst i; exact Nat.le_refl _
    · have := ih (by omega)
      simp only [epochBudget]
      omega


end PredictionToGeneration

namespace PredictionToGeneration

theorem epochBudget_constant (d j : Nat) : epochBudget (fun _ => d) j = d * j := by
  induction j with
  | zero => simp [epochBudget]
  | succ j ih => simp [epochBudget, ih, Nat.mul_succ]

end PredictionToGeneration
