import GenLimit.NoRegretLanguageGeneration.Forcing
import GenLimit.NoRegretLanguageGeneration.Littlestone

namespace PredictionToGeneration

/- Semantic regression checks for the protocol and regret signs. -/

example : Legal ([(0, 2), (0, 1)] : Trajectory Nat) := by simp [Legal, Fresh, demonstrations]
example : Legal ([(0, 0)] : Trajectory Nat) := by simp [Legal, Fresh, demonstrations]
example : ¬ Legal ([(1, 2), (0, 1)] : Trajectory Nat) := by simp [Legal, Fresh, demonstrations]
example : ¬ Legal ([(0, 1), (0, 1)] : Trajectory Nat) := by simp [Legal, Fresh, demonstrations]

example : regret (fun n : Nat => n == 0) [(0, 1)] = -1 := by decide
example : regret (fun n : Nat => n == 0) [(1, 0)] = 1 := by decide
example : regret (fun n : Nat => n == 0) [(0, 0)] = 0 := by decide

example : sauer 4 0 = 1 := by decide
example : sauer 4 1 = 5 := by decide
example : sauer 4 2 = 11 := by decide
example : sauer 4 4 = 16 := by decide

/-- One comparator must explain the entire demonstration history. -/
example : ¬ ∃ h : Hypothesis Bool,
    (h = (fun b => b) ∨ h = (fun b => !b)) ∧ Realizes h [(true, true), (false, false)] := by
  rintro ⟨h, he, hr⟩
  rcases he with rfl | rfl <;> simp [Realizes] at hr

end PredictionToGeneration

