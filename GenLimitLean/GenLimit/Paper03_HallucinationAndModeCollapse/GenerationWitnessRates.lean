import GenLimit.Paper03_HallucinationAndModeCollapse.GenerationModel

/-!
# Lemma 5.11: finite witnesses imply exponential fresh-generation rates

The coverage estimate is shared with the identification development. Witnesses
and cutoffs depend on the target, while the generator is fixed before the
valid distribution is chosen. Small sample sizes are included in the bound.
-/

namespace GenLimit.HallucinationModeCollapse

open GenLimit.Generic GenLimit.DiscreteIID

theorem generation_finiteWitness_error_bound (C : Generic.LanguageFamily ℕ)
    (G : GenLimit.Learner ℕ ℕ) (i : ℕ) (T : Finset ℕ) (N : ℕ)
    (hG : ∀ xs : List ℕ, N ≤ xs.length → (∀ x ∈ xs, x ∈ C i) →
      (∀ x ∈ T, x ∈ xs) → G xs ∈ C i ∧ G xs ∉ xs)
    (p : PMF ℕ) (hp : ValidDistribution C i p) (n : ℕ) (hn : N ≤ n) :
    generationError C (deterministicIdentifier G) p i n ≤
      probability (samples p n) {xs | ¬∀ x ∈ T, x ∈ xs} := by
  rw [generationError_deterministic, ← probability_inter_support]
  apply probability_mono
  rintro xs ⟨hwrong, hs⟩ hT
  obtain ⟨hl, hm⟩ := (samples_support p n xs).mp hs
  have hc := hG xs (hl.symm ▸ hn) (fun x hx => hp ▸ hm x hx) hT
  exact hwrong.elim (fun h => h hc.1) hc.2

/-- Source Lemma 5.11, including a positive prefactor for all sample sizes. -/
theorem lemma_5_11 (C : Generic.LanguageFamily ℕ) (G : GenLimit.Learner ℕ ℕ)
    (hG : FiniteWitnessGenerates C G) :
    ExponentialGenerates C (deterministicIdentifier G) := by
  intro i p hp
  obtain ⟨T, hT, N, hcorrect⟩ := hG i
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
  · exact (generation_finiteWitness_error_bound C G i T N hcorrect p hp n hn).trans
      ((hmiss n).trans (mul_le_mul_of_nonneg_right hlarge (Real.exp_nonneg _)))
  · have hdiff : 0 ≤ c * (N : ℝ) - c * (n : ℝ) := by
      have hcast : (n : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hn))
      nlinarith
    have he : 1 ≤ Real.exp (c * (N : ℝ) - c * (n : ℝ)) := Real.one_le_exp hdiff
    apply (generationError_le_one C _ p i n).trans
    dsimp [D]
    rw [mul_assoc, ← Real.exp_add]
    have harg : c * (N : ℝ) + -c * (n : ℝ) = c * (N : ℝ) - c * (n : ℝ) := by ring
    rw [harg]
    nlinarith

end GenLimit.HallucinationModeCollapse
