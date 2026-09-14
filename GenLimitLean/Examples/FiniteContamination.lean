import GenLimit.Core.FiniteContamination

/-!
# Example: use the shared finite-contamination counts

For a nonempty finite sample, accepted and rejected observations form
complementary fractions.  The proof consumes the shared Core identity instead
of unfolding either count.
-/

namespace GenLimit.Examples

open Generic

theorem accepted_and_rejected_fractions_sum_to_one
    (Acceptable : α → Prop) {sample : Finset α}
    (hsample : sample.Nonempty) :
    acceptedFraction Acceptable sample +
        rejectedFraction Acceptable sample = 1 := by
  have hcard : sample.card ≠ 0 := Finset.card_ne_zero.mpr hsample
  rw [acceptedFraction_eq_one_sub_rejectedFraction Acceptable hcard]
  linarith

end GenLimit.Examples
