import GenLimit.NoRegretLanguageGeneration.AsymptoticBridge

namespace PredictionToGeneration

theorem contamination_transfer_real (h : Hypothesis X) (τ : Trajectory X) (r : ℝ)
    (hr : (regret h τ : ℝ) ≤ r) :
    (mistakes h τ : ℝ) ≤ r + (demonstrationLoss h τ : ℝ) := by
  simp only [regret, Int.cast_sub, Int.cast_natCast] at hr
  linarith

/-- A sublinear comparator regret and sublinear contamination imply sublinear
output mistakes on the same sequence, with the same target. -/
theorem contamination_transfer_littleO (h : Hypothesis X) (τ : Nat → Trajectory X)
    (r : Nat → ℝ)
    (hr : ∀ᶠ t in Filter.atTop, (regret h (τ t) : ℝ) ≤ r t)
    (hrate : r =o[Filter.atTop] (fun t : Nat => (t : ℝ)))
    (hnoise : (fun t => (demonstrationLoss h (τ t) : ℝ))
      =o[Filter.atTop] (fun t : Nat => (t : ℝ))) :
    (fun t => (mistakes h (τ t) : ℝ)) =o[Filter.atTop] (fun t : Nat => (t : ℝ)) := by
  have hdom : (fun t => (mistakes h (τ t) : ℝ)) =O[Filter.atTop]
      (fun t => r t + (demonstrationLoss h (τ t) : ℝ)) := by
    apply Asymptotics.IsBigO.of_bound'
    filter_upwards [hr] with t ht
    have hb := contamination_transfer_real h (τ t) (r t) ht
    rw [Real.norm_natCast, Real.norm_eq_abs]
    exact hb.trans (le_abs_self _)
  exact hdom.trans_isLittleO (hrate.add hnoise)

end PredictionToGeneration
