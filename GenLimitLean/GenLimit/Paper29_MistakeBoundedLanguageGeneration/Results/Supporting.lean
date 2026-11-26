import GenLimit.Core.ClassGeneration
import GenLimit.Paper29_MistakeBoundedLanguageGeneration.FiniteLowerBound
import GenLimit.Paper29_MistakeBoundedLanguageGeneration.FiniteWeightedAlgorithm
import GenLimit.Paper29_MistakeBoundedLanguageGeneration.ModifiedGreedy
import GenLimit.Paper29_MistakeBoundedLanguageGeneration.NoisyInfinite
import GenLimit.Paper29_MistakeBoundedLanguageGeneration.PolynomialPrior
import GenLimit.Paper29_MistakeBoundedLanguageGeneration.TradeoffDiagnostic

/-! # Paper 29: supporting bounds and proof diagnostics -/

namespace GenLimit.MistakeBounded.Results

/-- Kernel-checked obstruction to the unshifted closure-dimension clause in
the printed Theorem 5.1 under generator-first order. -/
theorem theorem_5_1_order_diagnostic
    {L₀ L₁ : Generic.Language α}
    (hL₀ : L₀.Infinite) (hL₁ : L₁.Infinite)
    (hdisjoint : Disjoint L₀ L₁) (x : α) :
    GenLimit.MistakeBounded.FiniteClassClosureDimensionAtMost
        (GenLimit.MistakeBounded.disjointPairLanguage L₀ L₁) 0 ∧
      (x ∉ GenLimit.MistakeBounded.disjointPairLanguage L₀ L₁ 0 ∨
        x ∉ GenLimit.MistakeBounded.disjointPairLanguage L₀ L₁ 1) :=
  GenLimit.MistakeBounded.theorem_5_1_reversed_order_diagnostic
    hL₀ hL₁ hdisjoint x

/-- Lemma 5.3, finite-class tightness. An exact injective presentation forces
the first floor(log₂ N) predictions to miss a language in a class of size N. -/
theorem lemma_5_3 (N : ℕ) (positive : 0 < N) :
    ∃ H : Generic.LanguageClass (List Bool), H.Finite ∧ H.ncard = N ∧ Generic.UUS H ∧
      ∀ G : Generic.Generator (List Bool), (∀ t h (i : Fin t), G t h ≠ h i) →
        ∃ K ∈ H, ∃ s, Generic.Presents s K ∧ Function.Injective s ∧
          ∀ t < Nat.log2 N, Generic.output G s t ∉ K :=
  finite_log_mistake_lower N positive

/-- Theorem 6.1. With a polynomial prior and a doubling activation schedule,
the mistake count at every horizon is at most `3 log₂ i + log₂ (π² / 6)`,
where the paper’s one-based language index is `i = target + 1`. -/
theorem theorem_6_1_displayed_bound
    [Infinite α]
    (language : Generic.LanguageFamily α) (observed : Generic.Stream α)
    (hInjective : Function.Injective observed)
    (target : ℕ)
    (hObserved : ∀ t, observed t ∈ language target) :
    ∀ t,
      (GenLimit.MistakeBounded.mistakeCount
          (GenLimit.MistakeBounded.countableTargetTrace language
            (GenLimit.MistakeBounded.countableSemanticGenerated
              GenLimit.MistakeBounded.paperDoublingActiveCount
              GenLimit.MistakeBounded.polynomialPrior language observed)
            target)
          t : ℝ) ≤
        3 * Real.logb 2 (target + 1) +
          Real.logb 2 (Real.pi ^ 2 / 6) :=
  GenLimit.MistakeBounded.theorem_6_1_displayed_real_bound_concrete_semantic_algorithm
    language observed hInjective target hObserved

/-- Lemma 6.2: the concrete Modified-Greedy mistake bound and last-mistake
guarantee, packaged together. -/
theorem lemma_6_2
    [Infinite α]
    (language : Generic.LanguageFamily α) (observed : Generic.Stream α)
    (hInjective : Function.Injective observed)
    (target m : ℕ)
    (hTarget : ∀ s, observed s ∈ language target)
    (hComplexity : GenLimit.MistakeBounded.NonuniformComplexityAtMost
      language target m) :
    GenLimit.MistakeBounded.TotalMistakesAtMost
      (GenLimit.MistakeBounded.countableTargetTrace language
        (GenLimit.MistakeBounded.modifiedGreedyGenerated language observed)
        target)
      (min (2 * target) (max target (m + 1))) :=
  GenLimit.MistakeBounded.lemma_6_2_modifiedGreedy_complete
    language observed hInjective target m hTarget hComplexity

/-- Lemma 6.3: the concrete Modified-Greedy last-mistake guarantee. -/
theorem lemma_6_3
    [Infinite α]
    (language : Generic.LanguageFamily α) (observed : Generic.Stream α)
    (hInjective : Function.Injective observed)
    (target m : ℕ)
    (hTarget : ∀ s, observed s ∈ language target)
    (hComplexity : GenLimit.MistakeBounded.NonuniformComplexityAtMost
      language target m) :
    GenLimit.MistakeBounded.LastMistakeBefore
      (GenLimit.MistakeBounded.countableTargetTrace language
        (GenLimit.MistakeBounded.modifiedGreedyGenerated language observed)
        target)
      (max target (m + 1)) :=
  GenLimit.MistakeBounded.lemma_6_3_modifiedGreedy_last_mistake
    language observed hInjective target m hTarget hComplexity

/-- Exact arithmetic identity exposing the fixed-base quantifier problem in
the printed proof of Theorem 6.4.  This is a diagnostic, not the theorem. -/
theorem theorem_6_4_proof_diagnostic
    (base i : ℕ) (hi : 0 < i) :
    GenLimit.MistakeBounded.geometricPrefix base i + base ^ i + 1 =
      GenLimit.MistakeBounded.geometricPrefix base (i + 1) + 1 :=
  GenLimit.MistakeBounded.theorem_6_4_fixed_base_diagnostic base i hi

/-- Lemma 7.1. The same generator compares its errors with every language
in a finite family, at every horizon of an injective noisy stream. -/
theorem lemma_7_1 [Infinite α] {N : ℕ} (L : Fin N → Generic.Language α)
    (g : ℝ) (hg : 0 < g) (hu : g ≤ 3/4) :
    ∃ G : Generic.Generator α, (∀ t h (i : Fin t), G t h ≠ h i) ∧
      ∀ s, Function.Injective s → ∀ i T,
        (membershipErrors (L i) (Generic.output G s) T : ℝ) ≤
          (1+2*g)*membershipErrors (L i) s T + Real.logb 2 N / g :=
  noisy_finite_generation L g hg hu

/-- Lemma 7.2. The published bound has no additive normalizing constant.
The first language has zero additive budget, and each later comparator is
charged for demonstrations from its source cutoff, inclusive. -/
theorem lemma_7_2 [Infinite α] (L : Generic.LanguageFamily α) (inf : ∀ i, (L i).Infinite)
    (g : ℝ) (hg : 0 < g) (hu : g ≤ 3/4) :
    ∃ G : Generic.Generator α, (∀ t h (i : Fin t), G t h ≠ h i) ∧
      ∀ s, Function.Injective s → ∀ i T,
        (membershipErrors (L i) (Generic.output G s) T : ℝ) ≤
          (1+2*g)*noisyErrorsFrom (L i) s (noisyStart i) T +
          (1+2/g)*Real.logb 2 ((i:ℝ)+1) :=
  noisy_infinite_generation L inf g hg hu

end GenLimit.MistakeBounded.Results
