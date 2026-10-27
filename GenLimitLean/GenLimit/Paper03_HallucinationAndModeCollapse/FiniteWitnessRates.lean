import GenLimit.Paper03_HallucinationAndModeCollapse.StatisticalModel

/-!
# Finite witnesses imply exponential statistical identification

This is the mathematical probability implication in Lemma 8.1 of
arXiv:2411.09642v3. It applies to any deterministic learner with the stated
finite-witness property; no computability assumption is needed for the bound.
-/

namespace GenLimit.HallucinationModeCollapse

open GenLimit.Generic GenLimit.DiscreteIID

theorem finiteWitness_error_bound (C : Generic.LanguageFamily ℕ) (A : GenLimit.Learner ℕ ℕ)
    (i : ℕ) (T : Finset ℕ) (N : ℕ)
    (hA : ∀ xs : List ℕ, N ≤ xs.length → (∀ x ∈ xs, x ∈ C i) →
      (∀ x ∈ T, x ∈ xs) → C (A xs) = C i)
    (p : PMF ℕ) (hp : ValidDistribution C i p) (n : ℕ) (hn : N ≤ n) :
    identificationError C (deterministicIdentifier A) p i n ≤
      probability (samples p n) {xs | ¬∀ x ∈ T, x ∈ xs} := by
  rw [identificationError_deterministic, ← probability_inter_support]
  apply probability_mono
  rintro xs ⟨hwrong, hs⟩ hT
  obtain ⟨hl, hm⟩ := (samples_support p n xs).mp hs
  apply hwrong
  apply hA xs (hl.symm ▸ hn) _ hT
  intro x hx
  rw [← hp]
  exact hm x hx

/-- Lemma 8.1, including all small sample sizes by increasing the prefactor. -/
theorem lemma_8_1 (C : Generic.LanguageFamily ℕ) (A : GenLimit.Learner ℕ ℕ)
    (hA : FiniteWitnessIdentifies C A) :
    ExponentialIdentifies C (deterministicIdentifier A) := by
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
  · exact (finiteWitness_error_bound C A i T N hcorrect p hp n hn).trans
      ((hmiss n).trans (mul_le_mul_of_nonneg_right hlarge (Real.exp_nonneg _)))
  · have hdiff : 0 ≤ c * (N : ℝ) - c * (n : ℝ) := by
      have hcast : (n : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hn))
      nlinarith
    have he : 1 ≤ Real.exp (c * (N : ℝ) - c * (n : ℝ)) := Real.one_le_exp hdiff
    apply (identificationError_le_one C _ p i n).trans
    dsimp [D]
    rw [mul_assoc, ← Real.exp_add]
    have harg : c * (N : ℝ) + -c * (n : ℝ) = c * (N : ℝ) - c * (n : ℝ) := by ring
    rw [harg]
    nlinarith

end GenLimit.HallucinationModeCollapse
