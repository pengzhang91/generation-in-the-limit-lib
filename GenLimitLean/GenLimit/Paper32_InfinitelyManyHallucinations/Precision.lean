import GenLimit.Paper32_InfinitelyManyHallucinations.Definitions

/-!
# Membership precision and vanishing hallucination frequency

The new phenomenon in Paper 32 is that an exhaustion may contain infinitely
many invalid strings while their cumulative fraction tends to zero.  This
module isolates the exact analytic obligation used by Theorems 4.3, 4.8, and
4.9: vanishing finite-prefix error fraction implies lower membership
precision one.
-/

namespace GenLimit.InfinitelyManyHallucinations

open Filter

noncomputable local instance (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- Number of generated strings outside the target. -/
noncomputable def invalidCount (L : Language) (S : Finset ℕ) : ℕ := by
  exact GenLimit.Generic.rejectedCount (fun x => x ∈ L) S

theorem invalidCount_eq_filter_card (L : Language) (S : Finset ℕ) :
    invalidCount L S = (S.filter fun x => x ∉ L).card := by
  classical
  rfl

theorem countIn_add_invalidCount (L : Language) (S : Finset ℕ) :
    countIn L S + invalidCount L S = S.card :=
  GenLimit.Generic.acceptedCount_add_rejectedCount
    (fun x => x ∈ L) S

/-- Cumulative hallucination fraction, assigning zero to an empty guess. -/
noncomputable def invalidFraction (L : Language) (S : Finset ℕ) : ℝ :=
  GenLimit.Generic.rejectedFraction (fun x => x ∈ L) S

theorem invalidFraction_eq (L : Language) (S : Finset ℕ) :
    invalidFraction L S =
      if S.card = 0 then 0 else (invalidCount L S : ℝ) / S.card := by
  rfl

theorem invalidFraction_nonneg (L : Language) (S : Finset ℕ) :
    0 ≤ invalidFraction L S :=
  GenLimit.Generic.rejectedFraction_nonneg (fun x => x ∈ L) S

theorem invalidCount_le (L : Language) (S : Finset ℕ) :
    invalidCount L S ≤ S.card :=
  GenLimit.Generic.rejectedCount_le (fun x => x ∈ L) S

theorem invalidFraction_le_one (L : Language) (S : Finset ℕ) :
    invalidFraction L S ≤ 1 :=
  GenLimit.Generic.rejectedFraction_le_one (fun x => x ∈ L) S

theorem membershipFraction_eq_one_sub_invalidFraction
    (L : Language) {S : Finset ℕ} (hS : S.card ≠ 0) :
    membershipFraction L S = 1 - invalidFraction L S :=
  GenLimit.Generic.acceptedFraction_eq_one_sub_rejectedFraction
    (fun x => x ∈ L) hS

/-- A vanishing cumulative hallucination fraction gives precision one.  The
eventual nonemptiness premise merely removes the harmless zero-denominator
convention at the initial stages. -/
theorem lowerMembershipPrecision_eq_one_of_invalidFraction_tendsto_zero
    {L : Language} {guess : Exhaustion}
    (hpositive : ∀ᶠ n : ℕ in atTop, (guess.stage n).card ≠ 0)
    (herrors :
      Tendsto (fun n => invalidFraction L (guess.stage n))
        atTop (nhds 0)) :
    lowerMembershipPrecision L guess = 1 := by
  have heq :
      (fun n => membershipFraction L (guess.stage n)) =ᶠ[atTop]
        (fun n => 1 - invalidFraction L (guess.stage n)) := by
    filter_upwards [hpositive] with n hn
    exact membershipFraction_eq_one_sub_invalidFraction L hn
  have htendstoSub :
      Tendsto (fun n => 1 - invalidFraction L (guess.stage n))
        atTop (nhds (1 - 0)) :=
    tendsto_const_nhds.sub herrors
  have htendsto :
      Tendsto (fun n => membershipFraction L (guess.stage n))
        atTop (nhds 1) := by
    simpa using htendstoSub.congr' heq.symm
  exact htendsto.liminf_eq

/-- Pointwise control of invalid counts yields the corresponding error-rate
control whenever the guess stage is nonempty. -/
theorem invalidFraction_le_of_count_le
    (L : Language) {S : Finset ℕ} {b : ℕ}
    (hcount : invalidCount L S ≤ b) :
    invalidFraction L S ≤
      if S.card = 0 then 0 else (b : ℝ) / S.card := by
  by_cases hS : S.card = 0
  · simp [invalidFraction_eq, hS]
  · simp only [invalidFraction_eq, hS, if_false]
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast hcount) (Nat.cast_nonneg _)

/-- A convenient theorem-facing certificate: an explicit real error envelope
that tends to zero suffices for precision one. -/
theorem lowerMembershipPrecision_eq_one_of_error_envelope
    {L : Language} {guess : Exhaustion} {error : ℕ → ℝ}
    (hpositive : ∀ᶠ n : ℕ in atTop, (guess.stage n).card ≠ 0)
    (hbound : ∀ᶠ n : ℕ in atTop,
      invalidFraction L (guess.stage n) ≤ error n)
    (herror : Tendsto error atTop (nhds 0)) :
    lowerMembershipPrecision L guess = 1 := by
  apply lowerMembershipPrecision_eq_one_of_invalidFraction_tendsto_zero
    hpositive
  exact squeeze_zero'
    (Eventually.of_forall fun n => invalidFraction_nonneg L (guess.stage n))
    hbound herror

end GenLimit.InfinitelyManyHallucinations
