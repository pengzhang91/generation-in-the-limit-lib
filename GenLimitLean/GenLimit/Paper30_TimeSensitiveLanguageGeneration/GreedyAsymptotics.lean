import GenLimit.Paper30_TimeSensitiveLanguageGeneration.GreedyUpperDensity

/-!
# Greedy half-density asymptotics

Source: Ganju--McVoy--Dughmi--Teng, arXiv:2605.11302v2,
Section 4 and Appendix E, Algorithm 2 and Theorem 12.

`GreedyUpperDensity` proves the finite ownership estimate printed in
Appendix E.  This file closes its elementary asymptotic endgame: for every
fixed burn-in time `T`, the ratio

`⌊(i - 2T) / 2⌋ / i`

converges to one half.  Consequently every stage threshold
`αₘ = 1/2 - 2⁻ᵐ` is eventually crossed whenever the finite ownership bound
continues to hold.

This is a deterministic statement about a sequence of credited-cardinality
bounds.  `TotalizedGCGProgress` connects it to the repaired stateful machine;
the separate optimality direction is in `TurnTakingUpperBound`.
-/

namespace GenLimit.TimeSensitive

open Filter

/-- The normalized finite lower bound from Appendix E after burn-in `T`. -/
noncomputable def greedyBurnInRatio (T i : ℕ) : ℝ :=
  ((((i - 2 * T) / 2 : ℕ) : ℝ) / i)

theorem greedyBurnInRatio_nonneg (T i : ℕ) :
    0 ≤ greedyBurnInRatio T i := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The finite greedy lower-bound ratio never exceeds one half. -/
theorem greedyBurnInRatio_le_half (T i : ℕ) :
    greedyBurnInRatio T i ≤ (1 / 2 : ℝ) := by
  by_cases hi : i = 0
  · simp [greedyBurnInRatio, hi]
  · have hiReal : (0 : ℝ) < i := by
      exact_mod_cast Nat.pos_of_ne_zero hi
    rw [greedyBurnInRatio, div_le_iff₀ hiReal]
    have hNat : 2 * ((i - 2 * T) / 2) ≤ i := by
      omega
    have hReal :
        (2 : ℝ) * (((i - 2 * T) / 2 : ℕ) : ℝ) ≤ i := by
      exact_mod_cast hNat
    linarith

/-- The gap from one half is at most the fixed burn-in error `(T+1)/i`. -/
theorem half_sub_greedyBurnInRatio_le
    (T : ℕ) {i : ℕ} (hi : 0 < i) :
    (1 / 2 : ℝ) - greedyBurnInRatio T i ≤
      ((T + 1 : ℕ) : ℝ) / i := by
  have hiReal : (0 : ℝ) < i := by
    exact_mod_cast hi
  rw [greedyBurnInRatio, sub_le_iff_le_add, ← add_div,
    le_div_iff₀ hiReal]
  have hNat :
      i ≤ 2 * ((i - 2 * T) / 2) + 2 * (T + 1) := by
    omega
  have hReal :
      (i : ℝ) ≤
        2 * (((i - 2 * T) / 2 : ℕ) : ℝ) +
          2 * ((T + 1 : ℕ) : ℝ) := by
    exact_mod_cast hNat
  linarith

/-- For fixed burn-in, Appendix E's exact finite greedy ratio converges to
one half. -/
theorem tendsto_greedyBurnInRatio (T : ℕ) :
    Tendsto (greedyBurnInRatio T) atTop (nhds (1 / 2 : ℝ)) := by
  have herror :
      Tendsto
        (fun i : ℕ => (1 / 2 : ℝ) - greedyBurnInRatio T i)
        atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun i =>
        sub_nonneg.mpr (greedyBurnInRatio_le_half T i)
    · filter_upwards [eventually_gt_atTop 0] with i hi
      exact half_sub_greedyBurnInRatio_le T hi
    · simpa using
        tendsto_const_div_atTop_nhds_zero_nat
          (((T + 1 : ℕ) : ℝ))
  have hreconstruct :
      Tendsto
        (fun i : ℕ =>
          (1 / 2 : ℝ) -
            ((1 / 2 : ℝ) - greedyBurnInRatio T i))
        atTop (nhds (1 / 2 : ℝ)) := by
    simpa using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (1 / 2 : ℝ))
          atTop (nhds (1 / 2 : ℝ))).sub herror
  exact hreconstruct.congr'
    (Filter.Eventually.of_forall fun i => by ring)

/-- Every Algorithm-2 threshold is eventually below the finite greedy
lower-bound ratio. -/
theorem eventually_gcgThreshold_le_greedyBurnInRatio
    (m T : ℕ) :
    ∀ᶠ i in atTop, gcgThreshold m ≤ greedyBurnInRatio T i := by
  filter_upwards [
    (tendsto_greedyBurnInRatio T).eventually
      (lt_mem_nhds (gcgThreshold_lt_half m))] with i hi
  exact hi.le

/-- Deterministic stage-termination endgame from Appendix E.

If a continuing stage satisfies the printed greedy cardinality bound
eventually, then its credited ratio eventually reaches the stage threshold.
The connection to the concrete repaired state machine is proved in
`TotalizedGCGProgress`; no runtime-complexity claim is made here. -/
theorem stage_eventually_crosses_threshold
    (m T : ℕ) (credited : ℕ → ℕ)
    (hgreedy :
      ∀ᶠ i in atTop, (i - 2 * T) / 2 ≤ credited i) :
    ∀ᶠ i in atTop,
      gcgThreshold m ≤ (credited i : ℝ) / i := by
  filter_upwards [
    hgreedy,
    eventually_gcgThreshold_le_greedyBurnInRatio m T] with i hbound hratio
  exact stage_crosses_threshold_of_greedy_bound hbound hratio

end GenLimit.TimeSensitive
