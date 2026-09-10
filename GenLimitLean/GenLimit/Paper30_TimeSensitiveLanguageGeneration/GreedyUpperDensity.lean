import GenLimit.Paper30_TimeSensitiveLanguageGeneration.DensityReduction
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.NormNum

/-!
# Greedy upper-density core

Source: Ganju--McVoy--Dughmi--Teng, arXiv:2605.11302v2,
Section 4 and Appendix E, Algorithm 2 and Theorem 12.

The source's `GCG` proof repeatedly uses one deterministic fact: after a
finite burn-in, if the adversary can consume at most one still-available
string between generator moves, the greedy generator receives at least half
of the remaining finite prefix.  We formalize that ownership argument and
the exact threshold schedule `α_m = 1/2 - 2^{-m}`.

This is the finite combinatorial core used by the repaired stateful machine in
`TotalizedGCGProgress`.  The external optimality direction is separated in
`TurnTakingUpperBound`.
-/

namespace GenLimit.TimeSensitive

/-- Algorithm 2's stage threshold `α_m = 1/2 - 2^{-m}`. -/
noncomputable def gcgThreshold (m : ℕ) : ℝ :=
  (1 / 2 : ℝ) - (1 / 2 : ℝ) ^ m

theorem gcgThreshold_eq (m : ℕ) :
    gcgThreshold m = (1 / 2 : ℝ) - 1 / (2 : ℝ) ^ m := by
  simp [gcgThreshold, one_div, inv_pow]

theorem gcgThreshold_lt_half (m : ℕ) :
    gcgThreshold m < (1 / 2 : ℝ) := by
  unfold gcgThreshold
  have hpos : 0 < (1 / 2 : ℝ) ^ m := pow_pos (by norm_num) _
  linarith

theorem gcgThreshold_monotone : Monotone gcgThreshold := by
  intro m n hmn
  have hpow : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ m :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn
  unfold gcgThreshold
  linarith

theorem tendsto_gcgThreshold :
    Filter.Tendsto gcgThreshold Filter.atTop (nhds (1 / 2 : ℝ)) := by
  have hpow :
      Filter.Tendsto (fun m : ℕ => (1 / 2 : ℝ) ^ m)
        Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  change Filter.Tendsto
    (fun m : ℕ => (1 / 2 : ℝ) - (1 / 2 : ℝ) ^ m)
    Filter.atTop (nhds (1 / 2 : ℝ))
  simpa only [sub_zero] using tendsto_const_nhds.sub hpow

/-- The alternating-ownership inequality used in all three cases of the
Appendix-E proof.  `available` is partitioned between the generator and
adversary, and the adversary is never more than one move ahead. -/
theorem greedy_alternation_half
    [DecidableEq α]
    {available generated adversary : Finset α}
    (hdisjoint : Disjoint generated adversary)
    (hcover : generated ∪ adversary = available)
    (hahead : adversary.card ≤ generated.card + 1) :
    available.card / 2 ≤ generated.card := by
  have hcard :
      available.card = generated.card + adversary.card := by
    rw [← hcover, Finset.card_union_of_disjoint hdisjoint]
  omega

/-- Burn-in version of the same bound.

At most `2T` strings in the first `i` target positions can already be
unavailable at entry time `T` (late strings plus adversary-claimed strings).
The greedy alternation therefore credits at least
`⌊(i - 2T)/2⌋` strings, exactly the finite estimate printed in Appendix E. -/
theorem greedy_after_burnIn_bound
    [DecidableEq α]
    {prefixSet unavailable available generated adversary : Finset α}
    {i T : ℕ}
    (hprefix : prefixSet.card = i)
    (hpartition₁ : Disjoint unavailable available)
    (hcover₁ : unavailable ∪ available = prefixSet)
    (hunavailable : unavailable.card ≤ 2 * T)
    (hpartition₂ : Disjoint generated adversary)
    (hcover₂ : generated ∪ adversary = available)
    (hahead : adversary.card ≤ generated.card + 1) :
    (i - 2 * T) / 2 ≤ generated.card := by
  have havailable :
      i ≤ unavailable.card + available.card := by
    rw [← hprefix, ← hcover₁,
      Finset.card_union_of_disjoint hpartition₁]
  have hhalf :
      available.card / 2 ≤ generated.card :=
    greedy_alternation_half hpartition₂ hcover₂ hahead
  omega

/-- If the same stage continues indefinitely, any threshold below one half
is crossed once the printed finite greedy bound crosses it.  This packages
the last implication in the stage-termination argument without introducing
the unformalized `GCG` state machine. -/
theorem stage_crosses_threshold_of_greedy_bound
    {m i T credited : ℕ}
    (hgreedy : (i - 2 * T) / 2 ≤ credited)
    (hlarge :
      gcgThreshold m ≤
        (((i - 2 * T) / 2 : ℕ) : ℝ) / i) :
    gcgThreshold m ≤ (credited : ℝ) / i := by
  have hiReal : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  exact hlarge.trans
    (div_le_div_of_nonneg_right (by exact_mod_cast hgreedy) hiReal)

end GenLimit.TimeSensitive
