import GenLimit.Paper03_HallucinationAndModeCollapse.LabeledEnumeration

/-!
# Exponential identification from labeled finite witnesses

Finite IID coverage gives the upper bound in Theorem 3.13 directly. The
learner is fixed before the distribution is chosen. Positive constants may
depend on that distribution, and the prefactor covers every small sample
size. This proof does not require the source's batching estimator.
-/

namespace GenLimit.HallucinationModeCollapse

open GenLimit.Generic GenLimit.DiscreteIID

theorem finiteLabeledWitness_error_bound (C : Generic.LanguageFamily ℕ) (A : List LabeledDatum → ℕ)
    (i : ℕ) (T : Finset LabeledDatum) (N : ℕ)
    (hA : ∀ xs : List LabeledDatum, N ≤ xs.length → GenLimit.Gold.Informant.InformantCompatible xs (C i) →
      (∀ x ∈ T, x ∈ xs) → C (A xs) = C i)
    (p : PMF LabeledDatum) (hp : ValidLabeledDistribution C i p) (n : ℕ) (hn : N ≤ n) :
    labeledIdentificationError C (deterministicLabeledIdentifier A) p i n ≤
      probability (samples p n) {xs | ¬∀ x ∈ T, x ∈ xs} := by
  rw [labeledIdentificationError_deterministic, ← probability_inter_support]
  apply probability_mono
  rintro xs ⟨hwrong, hs⟩ hT
  obtain ⟨hl, hm⟩ := (samples_support p n xs).mp hs
  apply hwrong
  apply hA xs (hl.symm ▸ hn) _ hT
  intro x hx
  have hc : CorrectLabel C i x := by
    change x ∈ {z | CorrectLabel C i z}
    rw [← hp]
    exact hm x hx
  exact hc

/-- All-sample exponential identification from a labeled finite witness. -/
theorem finiteLabeledWitness_exponential (C : Generic.LanguageFamily ℕ) (A : List LabeledDatum → ℕ)
    (hA : FiniteLabeledWitnessIdentifies C A) :
    ExponentialLabeledIdentifies C (deterministicLabeledIdentifier A) := by
  intro i p hp
  obtain ⟨T, hT, N, hcorrect⟩ := hA i
  obtain ⟨c, hc, hmiss⟩ := finite_missing_exponential p T (by
    intro x hx
    change x ∈ p.support
    rw [hp]
    exact hT x hx)
  let D : ℝ := (T.card + 1) * Real.exp (c * N)
  have hcard : (T.card : ℝ) + 1 ≥ 1 := by linarith [Nat.cast_nonneg (α := ℝ) T.card]
  have hD : 0 < D := mul_pos (by positivity) (Real.exp_pos _)
  have hlarge : (T.card : ℝ) ≤ D := by
    have he : 1 ≤ Real.exp (c * N) := Real.one_le_exp (by positivity)
    dsimp [D]
    nlinarith
  refine ⟨c, hc, D, hD, fun n => ?_⟩
  by_cases hn : N ≤ n
  · exact (finiteLabeledWitness_error_bound C A i T N hcorrect p hp n hn).trans
      ((hmiss n).trans (mul_le_mul_of_nonneg_right hlarge (Real.exp_nonneg _)))
  · have hdiff : 0 ≤ c * (N : ℝ) - c * (n : ℝ) := by
      have hcast : (n : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hn))
      nlinarith
    have he : 1 ≤ Real.exp (c * (N : ℝ) - c * (n : ℝ)) := Real.one_le_exp hdiff
    apply (probability_le_one _ _).trans
    dsimp [D]
    rw [mul_assoc, ← Real.exp_add]
    have harg : c * (N : ℝ) + -c * (n : ℝ) = c * (N : ℝ) - c * (n : ℝ) := by ring
    rw [harg]
    nlinarith

end GenLimit.HallucinationModeCollapse

namespace GenLimit.HallucinationModeCollapse

/-- The exponential upper bound of Theorem 3.13, for the explicit
membership-only bounded enumeration learner. -/
theorem theorem_3_13_upper (C : GenLimit.Generic.LanguageFamily ℕ)
    (O : GenLimit.MembershipOracle C) :
    ExponentialLabeledIdentifies C (deterministicLabeledIdentifier (labeledEnumerationLearner O)) ∧
      (Computable₂ O.query → Computable (labeledEnumerationLearner O)) :=
  ⟨finiteLabeledWitness_exponential C _ (labeledEnumeration_finiteWitness C O),
    labeledEnumerationLearner_computable O⟩

end GenLimit.HallucinationModeCollapse
