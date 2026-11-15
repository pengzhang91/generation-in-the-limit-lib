import GenLimit.NoRegretLanguageGeneration.Littlestone
import Mathlib.Data.Nat.Choose.Sum

namespace PredictionToGeneration

open Finset

/-- The recurrence already checked in Littlestone.lean is the binomial sum. -/
theorem sauer_eq_sum_choose (n d : Nat) : sauer n d = ∑ i ∈ range (d + 1), n.choose i := by
  induction n generalizing d with
  | zero => simp [sauer, sum_range_succ']
  | succ n ih =>
    cases d with
    | zero => simp [sauer]
    | succ d =>
      rw [sauer, ih, ih]
      conv_rhs => rw [sum_range_succ']
      simp only [Nat.choose_succ_succ', Nat.choose_zero_right, sum_add_distrib]
      rw [sum_range_succ' (fun i => n.choose i) (d + 1)]
      simp only [Nat.choose_zero_right]; omega

/-- The manuscript truncates at min(d,n); terms beyond n vanish. -/
theorem sauer_eq_truncated_choose (n d : Nat) :
    sauer n d = ∑ i ∈ range (min d n + 1), n.choose i := by
  rw [sauer_eq_sum_choose]
  apply (sum_subset (by intro i hi; simp only [mem_range] at hi ⊢; omega) ?_).symm
  intro i hi hnot
  simp only [mem_range] at hi hnot
  exact Nat.choose_eq_zero_of_lt (by omega)

theorem sequential_sauer_binomial (H : HypothesisClass X) (d : Nat) (hd : LdimLE H d)
    {n : Nat} (tree : QueryTree X n) :
    leafCount H tree ≤ ∑ i ∈ range (min d n + 1), n.choose i := by
  rw [← sauer_eq_truncated_choose]
  exact sequential_sauer H d hd tree

end PredictionToGeneration


