import GenLimit.Paper29_MistakeBoundedLanguageGeneration.Potential

/-!
# The positive-target-weight component of Theorem 4.1

Kleinberg--Peale--Reingold, *Mistake-Bounded Language Generation*,
arXiv:2605.10809v1, Theorem 4.1 and its Appendix A proof.

The printed theorem allows `w₀(i) = 0` but then displays the finite quantity
`⌊log₂ (W / w₀(i))⌋`.  This module records the deterministic numerical
argument with its necessary guard `0 < w₀(i)`.

The construction of Algorithm 1's maximizing output on an arbitrary
countable universe is deliberately not asserted here.  Instead, the theorem
starts from the already checked `HalvingPotential` interface.  Its
`activation` rounds account for the paper's `f⁻¹(i)` prefix, and
`DyadicUpperBudget W w₀ B` is the division-free statement
`W / w₀ < 2^(B+1)`.  Thus `B = ⌊log₂ (W / w₀)⌋` is the intended
instantiation when that real logarithm is defined.
-/

namespace GenLimit.MistakeBounded

/-- The mistake trace beginning at round `activation`. -/
def traceAfter (trace : MistakeTrace) (activation : ℕ) : MistakeTrace :=
  fun t => trace (activation + t)

/-- Mistakes split exactly into the prefix before `activation` and the
shifted suffix. -/
theorem mistakeCount_add_traceAfter
    (trace : MistakeTrace) (activation t : ℕ) :
    mistakeCount trace (activation + t) =
      mistakeCount trace activation +
        mistakeCount (traceAfter trace activation) t := by
  induction t with
  | zero =>
      simp
  | succ t ih =>
      rw [Nat.add_succ, mistakeCount_succ, mistakeCount_succ, ih]
      simp only [traceAfter]
      omega

/-- A trace has at most one mistake per round. -/
theorem mistakeCount_le_round (trace : MistakeTrace) (t : ℕ) :
    mistakeCount trace t ≤ t := by
  exact
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (Finset.card_range t)

/-- Division-free upper dyadic budget.  With `0 < targetWeight`, this says
`totalBound / targetWeight < 2^(budget+1)`. -/
def DyadicUpperBudget
    (totalBound targetWeight : ℝ) (budget : ℕ) : Prop :=
  totalBound < (2 : ℝ) ^ (budget + 1) * targetWeight

/-- The checked halving argument gives the logarithmic part of Theorem 4.1
once the target has entered the active prefix.  Positivity of the initial
target weight is carried by `TargetWeightSurvives`; in particular this
theorem has no zero-weight specialization. -/
theorem theorem_4_1_positive_weight_after_activation
    {trace : MistakeTrace} (P : HalvingPotential trace)
    {targetWeight totalBound : ℝ} {budget : ℕ}
    (hsurvives : TargetWeightSurvives P targetWeight)
    (htotal : P.potential 0 ≤ totalBound)
    (hbudget : DyadicUpperBudget totalBound targetWeight budget) :
    TotalMistakesAtMost trace budget := by
  intro t
  have hcountBound :
      (2 : ℝ) ^ mistakeCount trace t * targetWeight ≤ totalBound :=
    (halvingPotential_bound P hsurvives t).trans htotal
  by_contra hnot
  have hsucc : budget + 1 ≤ mistakeCount trace t := by
    omega
  have hpowNat :
      2 ^ (budget + 1) ≤ 2 ^ mistakeCount trace t :=
    Nat.pow_le_pow_right (by omega) hsucc
  have hpowReal :
      (2 : ℝ) ^ (budget + 1) ≤
        (2 : ℝ) ^ mistakeCount trace t := by
    exact_mod_cast hpowNat
  have hthreshold :
      (2 : ℝ) ^ (budget + 1) * targetWeight ≤ totalBound :=
    (mul_le_mul_of_nonneg_right hpowReal
      (le_of_lt hsurvives.1)).trans hcountBound
  exact (not_le_of_gt hbudget) hthreshold

/-- Corrected source-facing numerical wrapper for Theorem 4.1.

There can be at most `activation` mistakes before the target enters the
active prefix, and the positive-weight halving argument permits at most
`budget` further mistakes.  Taking `activation = f⁻¹(i)` and
`budget = ⌊log₂ (W / w₀(i))⌋` recovers the theorem's displayed sum whenever
`0 < w₀(i)`. -/
theorem theorem_4_1_positive_weight_bound
    {trace : MistakeTrace} {activation budget : ℕ}
    (P : HalvingPotential (traceAfter trace activation))
    {targetWeight totalBound : ℝ}
    (hsurvives : TargetWeightSurvives P targetWeight)
    (htotal : P.potential 0 ≤ totalBound)
    (hbudget : DyadicUpperBudget totalBound targetWeight budget) :
    TotalMistakesAtMost trace (activation + budget) := by
  have hafter :
      TotalMistakesAtMost
        (traceAfter trace activation) budget :=
    theorem_4_1_positive_weight_after_activation
      P hsurvives htotal hbudget
  intro t
  by_cases ht : activation ≤ t
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
    rw [mistakeCount_add_traceAfter]
    exact Nat.add_le_add
      (mistakeCount_le_round trace activation) (hafter d)
  · have htt : t ≤ activation := Nat.le_of_not_ge ht
    exact (mistakeCount_le_round trace t).trans
      (htt.trans (Nat.le_add_right activation budget))

/-- The omitted source guard is substantive: a nonnegative total bound can
never have a finite dyadic budget against zero target weight. -/
theorem no_dyadicUpperBudget_of_zero_targetWeight
    {totalBound : ℝ} (htotal : 0 ≤ totalBound) (budget : ℕ) :
    ¬DyadicUpperBudget totalBound 0 budget := by
  simp [DyadicUpperBudget, not_lt.mpr htotal]

end GenLimit.MistakeBounded
