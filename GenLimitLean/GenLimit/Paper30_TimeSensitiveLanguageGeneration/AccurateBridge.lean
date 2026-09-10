import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.InfinitelyOften

/-!
# Appendix E: reuse of the P07 accurate selector

Appendix E's GCG construction assumes an `Accurate` subroutine whose guessed
language is eventually contained in the target and equals the target at
arbitrarily late rounds.  P07 already proves exactly that semantic guarantee
for its strict-critical selector.  This file records the dependency as a thin
bridge instead of duplicating the selector or its proof.

The bridge does not establish Theorem 4 by itself.  The documented
queue-totalized consumer and its checkpoint proof are in
`TotalizedGCGMachine`, `TotalizedGCGProgress`, and `TotalizedGCGMain`.
-/

namespace GenLimit.TimeSensitive

open GenLimit.KleinbergWei
open GenLimit.KleinbergWei.DensityMeasures

/-- The P07 strict-critical selector supplies the `Accurate` oracle contract
used by P30 Appendix E: eventual target containment and cofinally many exact
target guesses. -/
theorem appendix_E_accurate_oracle_from_paper07
    {C : LanguageFamily} {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (C z))
    (hfirst : FirstOccurrence C z) :
    IndexValidInLimit C stream z ∧
      ∀ t, ∃ r, t ≤ r ∧ AccurateAt C stream z r :=
  GenLimit.KleinbergWei.DensityMeasures.theorem_2_1 hP hfirst

end GenLimit.TimeSensitive
