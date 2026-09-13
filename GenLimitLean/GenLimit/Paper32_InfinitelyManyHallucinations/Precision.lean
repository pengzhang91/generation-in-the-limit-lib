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

/-- Number of generated strings outside the target. -/
noncomputable def invalidCount (L : Language) (S : Finset ℕ) : ℕ := by
  classical
  exact (S.filter fun x => x ∉ L).card

theorem countIn_add_invalidCount (L : Language) (S : Finset ℕ) :
    countIn L S + invalidCount L S = S.card := by
  classical
  unfold countIn invalidCount
  exact Finset.filter_card_add_filter_neg_card_eq_card
    (s := S) (p := fun x => x ∈ L)

/-- Cumulative hallucination fraction, assigning zero to an empty guess. -/
noncomputable def invalidFraction (L : Language) (S : Finset ℕ) : ℝ :=
  if S.card = 0 then 0 else (invalidCount L S : ℝ) / S.card

theorem invalidFraction_nonneg (L : Language) (S : Finset ℕ) :
    0 ≤ invalidFraction L S := by
  by_cases hS : S.card = 0
  · simp [invalidFraction, hS]
  · simp only [invalidFraction, hS, if_false]
    positivity

theorem invalidCount_le (L : Language) (S : Finset ℕ) :
    invalidCount L S ≤ S.card := by
  classical
  exact Finset.card_filter_le _ _

theorem invalidFraction_le_one (L : Language) (S : Finset ℕ) :
    invalidFraction L S ≤ 1 := by
  by_cases hS : S.card = 0
  · simp [invalidFraction, hS]
  · simp only [invalidFraction, hS, if_false]
    have hpos : (0 : ℝ) < S.card := by
      exact_mod_cast Nat.pos_of_ne_zero hS
    rw [div_le_one hpos]
    exact_mod_cast invalidCount_le L S

theorem membershipFraction_eq_one_sub_invalidFraction
    (L : Language) {S : Finset ℕ} (hS : S.card ≠ 0) :
    membershipFraction L S = 1 - invalidFraction L S := by
  simp only [membershipFraction, invalidFraction, hS, if_false]
  have hsumNat := countIn_add_invalidCount L S
  have hsumReal :
      (countIn L S : ℝ) + (invalidCount L S : ℝ) = (S.card : ℝ) := by
    exact_mod_cast hsumNat
  have hcardReal : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS
  field_simp
  linarith

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
  · simp [invalidFraction, hS]
  · simp only [invalidFraction, hS, if_false]
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
