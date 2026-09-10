import GenLimit.Paper30_TimeSensitiveLanguageGeneration.GreedyAsymptotics

/-!
# Theorem 4: checkpoint-to-upper-density endgame

Source: Ganju--McVoy--Dughmi--Teng, arXiv:2605.11302v2,
Section 4 and Appendix E, Theorems 4 and 12.

The paper's GCG argument produces arbitrarily late checkpoints whose timely
density reaches the stage threshold `αₘ = 1/2 - 2⁻ᵐ`.  The theorem below
closes the remaining `limsup` argument: cofinal checkpoints for every stage
imply timely upper density at least one half.

This is the reusable analytic endpoint.  `TotalizedGCGMain` now discharges
the checkpoint premise for the documented repaired queue; the source-faithful
strict-rise skeleton retains a separately recorded consistency gap.
-/

namespace GenLimit.TimeSensitive

open Filter

/-- A cofinal family of GCG threshold checkpoints gives timely upper density
at least one half under the identity deadline.

This packages the final analytic implication in Theorems 4/12 without hiding
the state-machine invariant in an existential wrapper. -/
theorem theorem_4_density_endgame
    (S R : ℕ → α)
    (hcheckpoints : ∀ m : ℕ,
      ∃ᶠ i : ℕ in atTop,
        gcgThreshold m ≤ timelyDensity S R id i) :
    (1 / 2 : ℝ) ≤ upperTimelyDensity S R id := by
  have hbounded :
      IsBoundedUnder LE.le atTop (timelyDensity S R id) :=
    isBoundedUnder_of
      ⟨1, fun i => timelyDensity_le_one S R id i⟩
  have hstage : ∀ m : ℕ,
      gcgThreshold m ≤ upperTimelyDensity S R id := by
    intro m
    unfold upperTimelyDensity
    exact le_limsup_of_frequently_le (hcheckpoints m) hbounded
  apply le_of_tendsto tendsto_gcgThreshold
  exact Eventually.of_forall hstage

/-- Equivalent explicit-cofinality interface for the same endgame.  This is
often the most convenient form for a concrete GCG run: after any requested
time `N`, provide a later checkpoint for stage `m`. -/
theorem theorem_4_density_endgame_of_cofinal_checkpoints
    (S R : ℕ → α)
    (hcheckpoints : ∀ m N : ℕ, ∃ i : ℕ,
      N ≤ i ∧ gcgThreshold m ≤ timelyDensity S R id i) :
    (1 / 2 : ℝ) ≤ upperTimelyDensity S R id := by
  apply theorem_4_density_endgame S R
  intro m
  rw [frequently_atTop]
  intro N
  exact hcheckpoints m N

end GenLimit.TimeSensitive
