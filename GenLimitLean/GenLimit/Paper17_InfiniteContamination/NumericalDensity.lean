import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.FiniteHistory
import GenLimit.Paper17_InfiniteContamination.ElementDensity

/-! # Numerical element-density guarantees (Theorem 6.19 and Corollary 6.20) -/

namespace GenLimit.InfiniteContamination

open GenLimit.Generic GenLimit.KleinbergWei
open GenLimit.KleinbergWei.DensityMeasures.OrderedFocus

/-- Run the P07 finite-history rule on the observations available at this round. -/
private noncomputable def densityGenerator (O : OracleFamily) : Generator ℕ :=
  fun _ xs => historyRule (canonicalFamilyOrders O) (List.ofFn xs)

private theorem densityGenerator_succ (O : OracleFamily) (s : Stream ℕ) (t : ℕ) :
    Generic.output (densityGenerator O) s (t + 1) =
      play (historyRule (canonicalFamilyOrders O)) s t := by
  simp only [Generic.output, densityGenerator, play, textPrefix_eq_ofFn]

/-- Theorem 6.19. A single finite-history rule attains both noiseless constants. -/
theorem noiseless_numerical_density (O : OracleFamily) :
    ∃ gen : Generator ℕ, ∀ j s, Generic.Presents s (O.language j) →
      GeneratesElementInLimitOn gen (O.language j) s ∧
      ElementDensityGuaranteeOn gen (canonicalFamilyOrders O j) s (1/8) (1/2) := by
  refine ⟨densityGenerator O, ?_⟩
  intro j s hs
  let orders := canonicalFamilyOrders O
  let g := play (historyRule orders) s
  have compat : Compatible orders := by
    intro i j a b c d hac hbd hab
    exact (canonicalFamilyOrders_strictMono O j).lt_iff_lt.mp
      (hac ▸ hbd ▸ (canonicalFamilyOrders_strictMono O i hab))
  obtain ⟨⟨T, hT⟩, hlow⟩ := historyRule_density orders compat (z := j) (s := s) hs
  have hup := (historyRule_upper orders compat (z := j) (s := s) hs).2
  have shift (t) : Generic.output (densityGenerator O) s (t+1) = g t :=
    densityGenerator_succ O s t
  have hzero : ∃ N, ∀ t ≥ N, Generic.output (densityGenerator O) s 0 ≠ g t := by
    by_cases h : ∃ i, g i = Generic.output (densityGenerator O) s 0
    · obtain ⟨i, hi⟩ := h
      refine ⟨max T (i+1), fun t ht he ↦ ?_⟩
      exact (hT t (le_trans (le_max_left ..) ht)).2.2 i (by omega) (hi.trans he)
    · exact ⟨0, fun t _ he ↦ h ⟨t, he.symm⟩⟩
  obtain ⟨N, hN⟩ := hzero
  constructor
  · refine ⟨max T N + 1, ?_⟩
    rintro (_ | t) ht
    · omega
    obtain ⟨hmem, hseen, hused⟩ := hT t (by omega)
    refine ⟨(shift t).symm ▸ hmem, ?_, ?_⟩
    · rintro h
      obtain ⟨k, hk, he⟩ := Generic.mem_sample_iff.mp h
      exact hseen k (by omega) (he.trans (shift t))
    · rintro h
      obtain ⟨k, hk, he⟩ := mem_generatedBefore_iff.mp h
      cases k with
      | zero => exact hN t (by omega) (he.trans (shift t))
      | succ k => exact hused k (by omega) ((shift k).symm.trans (he.trans (shift t)))
  · have hsub : generatedIn (historyRule orders) s (orders j).carrier ⊆
        elementOutputLanguage (densityGenerator O) s := by
      rintro x ⟨⟨t, rfl⟩, _⟩
      exact ⟨t+1, shift t⟩
    exact ⟨(by norm_num : (1/8 : ℝ) ≤ 1/2).trans
      (hlow.trans ((orders j).lowerDensity_mono hsub)),
      hup.trans ((orders j).upperDensity_mono hsub)⟩

/-- Corollary 6.20. The same two numerical bounds survive finitely many noisy
observations and finitely many omitted target words. -/
theorem finite_contamination_numerical_density (O : OracleFamily) :
    ∃ gen : Generator ℕ, ∀ j s, FiniteNoiseFiniteOmissionEnumeration s (O.language j) →
      GeneratesElementInLimitOn gen (O.language j) s ∧
      ElementDensityGuaranteeOn gen (canonicalFamilyOrders O j) s (1/8) (1/2) := by
  obtain ⟨gen, hgen⟩ := noiseless_numerical_density (finiteExpansionOracleFamily O)
  exact ⟨gen, theorem_6_18_finiteContamination_transfer O gen _ _ hgen⟩

end GenLimit.InfiniteContamination
