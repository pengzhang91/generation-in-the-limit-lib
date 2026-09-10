import GenLimit.Paper30_TimeSensitiveLanguageGeneration.AccurateBridge

/-!
# Prefix causality of the P07 accurate selector

P30's adversary speaks before the generator in each round.  To run the
repaired GCG against an adaptive presentation, the semantic P07 selector must
therefore be evaluable from the finite observation history available at that
round.  This module proves that `guessIndex C stream t` depends only on the
first `t` values of `stream`.

The result is extensional: no computability claim about the selector or the
language family is introduced.
-/

namespace GenLimit.TimeSensitive

open GenLimit.KleinbergWei.DensityMeasures

theorem consistent_iff_of_eqOn_prefix
    {C : LanguageFamily} {stream₁ stream₂ : ℕ → ℕ} {t i : ℕ}
    (hstream : ∀ n, n < t → stream₁ n = stream₂ n) :
    Consistent C stream₁ t i ↔ Consistent C stream₂ t i := by
  have hsample : sample stream₁ t = sample stream₂ t := by
    ext x
    simp only [mem_sample_iff]
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨n, hn, (hstream n hn).symm⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨n, hn, hstream n hn⟩
  simp only [Consistent, hsample]

theorem strictCritical_iff_of_eqOn_prefix
    {C : LanguageFamily} {stream₁ stream₂ : ℕ → ℕ} {t i : ℕ}
    (hstream : ∀ n, n < t → stream₁ n = stream₂ n) :
    StrictCritical C stream₁ t i ↔ StrictCritical C stream₂ t i := by
  unfold StrictCritical
  constructor
  · rintro ⟨hi, hminimal⟩
    refine ⟨(consistent_iff_of_eqOn_prefix hstream).mp hi, ?_⟩
    intro j hji hj
    exact hminimal j hji
      ((consistent_iff_of_eqOn_prefix hstream).mpr hj)
  · rintro ⟨hi, hminimal⟩
    refine ⟨(consistent_iff_of_eqOn_prefix hstream).mpr hi, ?_⟩
    intro j hji hj
    exact hminimal j hji
      ((consistent_iff_of_eqOn_prefix hstream).mp hj)

theorem scopedStrictCriticalIndices_eq_of_eqOn_prefix
    {C : LanguageFamily} {stream₁ stream₂ : ℕ → ℕ} {t : ℕ}
    (hstream : ∀ n, n < t → stream₁ n = stream₂ n) :
    scopedStrictCriticalIndices C stream₁ t =
      scopedStrictCriticalIndices C stream₂ t := by
  classical
  ext i
  simp only [mem_scopedStrictCriticalIndices]
  exact and_congr_right fun _ => strictCritical_iff_of_eqOn_prefix hstream

theorem scopedFocus_eq_of_eqOn_prefix
    {C : LanguageFamily} {stream₁ stream₂ : ℕ → ℕ} {t : ℕ}
    (hstream : ∀ n, n < t → stream₁ n = stream₂ n) :
    scopedFocus C stream₁ t = scopedFocus C stream₂ t := by
  classical
  simp only [scopedFocus]
  rw [scopedStrictCriticalIndices_eq_of_eqOn_prefix hstream]

theorem badStrictCritical_iff_of_eqOn_prefix
    {C : LanguageFamily} {stream₁ stream₂ : ℕ → ℕ} {t w i : ℕ}
    (hstream : ∀ n, n < t → stream₁ n = stream₂ n) :
    BadStrictCritical C stream₁ t w i ↔
      BadStrictCritical C stream₂ t w i := by
  unfold BadStrictCritical
  constructor
  · rintro ⟨hi, hw⟩
    exact ⟨(strictCritical_iff_of_eqOn_prefix hstream).mp hi, hw⟩
  · rintro ⟨hi, hw⟩
    exact ⟨(strictCritical_iff_of_eqOn_prefix hstream).mpr hi, hw⟩

theorem firstBadStrictCritical_eq_of_eqOn_prefix
    {C : LanguageFamily} {stream₁ stream₂ : ℕ → ℕ} {t w : ℕ}
    (hstream : ∀ n, n < t → stream₁ n = stream₂ n) :
    firstBadStrictCritical C stream₁ t w =
      firstBadStrictCritical C stream₂ t w := by
  classical
  by_cases hbad₁ : ∃ i, BadStrictCritical C stream₁ t w i
  · have hbad₂ : ∃ i, BadStrictCritical C stream₂ t w i := by
      obtain ⟨i, hi⟩ := hbad₁
      exact ⟨i, (badStrictCritical_iff_of_eqOn_prefix hstream).mp hi⟩
    simp only [firstBadStrictCritical, dif_pos hbad₁, dif_pos hbad₂]
    exact Nat.find_congr'
      (fun {_} => badStrictCritical_iff_of_eqOn_prefix hstream)
  · have hbad₂ : ¬∃ i, BadStrictCritical C stream₂ t w i := by
      intro h
      obtain ⟨i, hi⟩ := h
      exact hbad₁ ⟨i, (badStrictCritical_iff_of_eqOn_prefix hstream).mpr hi⟩
    simp [firstBadStrictCritical, hbad₁, hbad₂]

theorem boundaryCandidates_eq_of_eqOn_prefix
    {C : LanguageFamily} {stream₁ stream₂ : ℕ → ℕ} {t w : ℕ}
    (hstream : ∀ n, n < t → stream₁ n = stream₂ n) :
    boundaryCandidates C stream₁ t w =
      boundaryCandidates C stream₂ t w := by
  classical
  ext i
  simp only [mem_boundaryCandidates]
  rw [firstBadStrictCritical_eq_of_eqOn_prefix hstream]
  constructor
  · rintro ⟨hi, hcritical, hw⟩
    exact ⟨hi, (strictCritical_iff_of_eqOn_prefix hstream).mp hcritical, hw⟩
  · rintro ⟨hi, hcritical, hw⟩
    exact ⟨hi, (strictCritical_iff_of_eqOn_prefix hstream).mpr hcritical, hw⟩

theorem selectIndex_eq_of_eqOn_prefix
    {C : LanguageFamily} {stream₁ stream₂ : ℕ → ℕ} {t w : ℕ}
    (hstream : ∀ n, n < t → stream₁ n = stream₂ n) :
    selectIndex C stream₁ t w = selectIndex C stream₂ t w := by
  classical
  have hcritical : ∀ i,
      StrictCritical C stream₁ t i ↔ StrictCritical C stream₂ t i :=
    fun _ => strictCritical_iff_of_eqOn_prefix hstream
  have hall :
      (∀ i, StrictCritical C stream₁ t i → w ∈ C i) ↔
        ∀ i, StrictCritical C stream₂ t i → w ∈ C i := by
    constructor
    · intro h i hi
      exact h i ((hcritical i).mpr hi)
    · intro h i hi
      exact h i ((hcritical i).mp hi)
  by_cases h₁ : ∀ i, StrictCritical C stream₁ t i → w ∈ C i
  · have h₂ : ∀ i, StrictCritical C stream₂ t i → w ∈ C i := hall.mp h₁
    simp only [selectIndex, dif_pos h₁, dif_pos h₂]
    exact scopedFocus_eq_of_eqOn_prefix hstream
  · have h₂ : ¬∀ i, StrictCritical C stream₂ t i → w ∈ C i :=
      fun h => h₁ (hall.mpr h)
    simp only [selectIndex, dif_neg h₁, dif_neg h₂]
    rw [boundaryCandidates_eq_of_eqOn_prefix hstream]
    by_cases hS : (boundaryCandidates C stream₂ t w).Nonempty
    · simp [hS]
    · simp [hS, scopedFocus_eq_of_eqOn_prefix hstream]

/-- The P07 selector is causal at its paper-facing time index. -/
theorem guessIndex_eq_of_eqOn_prefix
    {C : LanguageFamily} {stream₁ stream₂ : ℕ → ℕ} {t : ℕ}
    (hstream : ∀ n, n < t → stream₁ n = stream₂ n) :
    guessIndex C stream₁ t = guessIndex C stream₂ t := by
  cases t with
  | zero => rfl
  | succ t =>
      simp only [guessIndex]
      have hcurrent : stream₁ t = stream₂ t :=
        hstream t (Nat.lt_succ_self t)
      rw [← hcurrent]
      apply selectIndex_eq_of_eqOn_prefix
      intro n hn
      exact hstream n (hn.trans (Nat.lt_succ_self t))

end GenLimit.TimeSensitive
