import GenLimit.Paper29_MistakeBoundedLanguageGeneration.ClosureBridge
import GenLimit.Paper29_MistakeBoundedLanguageGeneration.CountableWeightedRun
import GenLimit.Paper29_MistakeBoundedLanguageGeneration.FiniteWeightedRun
import GenLimit.Paper29_MistakeBoundedLanguageGeneration.ModifiedGreedy
import GenLimit.Paper29_MistakeBoundedLanguageGeneration.PolynomialPrior
import GenLimit.Paper29_MistakeBoundedLanguageGeneration.PositiveTargetWeight
import GenLimit.Paper29_MistakeBoundedLanguageGeneration.TradeoffDiagnostic

/-!
# Paper 29: main-results overview

This module is the public results facade for Kleinberg--Peale--Reingold,
*Mistake-Bounded Language Generation* (arXiv:2605.10809v1).  The declarations
below are thin aliases for canonical proofs; no proof is duplicated here.

## Coverage boundary

The paper's three constructive headline results are kernel-checked at the
semantic/classical level.  Theorem 4.1 is stated with the necessary positive
target-prior guard omitted by the printed statement.  Theorem 5.1 has the
necessary `d+1` correction forced by the paper's generator-first order.
Theorem 6.1 is available both as an exact natural-valued logarithmic budget
and in the source's displayed real-valued form, with an invalid floor-removal
equality replaced by an inequality.

The printed proof of Theorem 6.4 fixes one geometric base before invoking a
big-O contradiction.  Its alleged late round is only the next geometric
prefix and therefore remains within a base-dependent constant factor.  The
arithmetic diagnostic is checked below, but the disputed theorem is not
claimed.

Lemmas 6.2 and 6.3 are fully checked for the concrete Modified-Greedy
algorithm.  The finite-class lower bound (Lemma 5.3), the LfD reduction and
reward-regret results in Appendix B, and noisy Lemmas 7.1--7.2 are not yet
formalized.  The recalled Theorem 5.2 remains in its canonical earlier-paper
development.  No machine-level implementation or runtime theorem is claimed.
-/

namespace GenLimit.MistakeBounded.Results

/-- Corrected, concrete semantic Algorithm 1 form of Theorem 4.1. -/
theorem theorem_4_1
    [Infinite α]
    (activeCount : ℕ → ℕ) (initialWeight : ℕ → ℝ)
    (language : ℕ → Set α) (observed : ℕ → α)
    (hmono : Monotone activeCount)
    (hInitial : ∀ i, 0 ≤ initialWeight i)
    (hInjective : Function.Injective observed)
    {totalBound : ℝ}
    (hPrior : ∀ n,
      GenLimit.MistakeBounded.initialPrefixWeight initialWeight n ≤
        totalBound)
    (target activation budget : ℕ)
    (hFirst : GenLimit.MistakeBounded.FirstActivated
      activeCount target activation)
    (hObserved : ∀ t, observed t ∈ language target)
    (hTargetPositive : 0 < initialWeight target)
    (hBudget : GenLimit.MistakeBounded.DyadicUpperBudget
      totalBound (initialWeight target) budget) :
    GenLimit.MistakeBounded.TotalMistakesAtMost
      (GenLimit.MistakeBounded.countableTargetTrace language
        (GenLimit.MistakeBounded.countableSemanticGenerated
          activeCount initialWeight language observed)
        target)
      (activation + budget) :=
  GenLimit.MistakeBounded.theorem_4_1_corrected_concrete_semantic_algorithm
    activeCount initialWeight language observed hmono hInitial hInjective
    hPrior target activation budget hFirst hObserved hTargetPositive hBudget

/-- Corrected, concrete semantic finite-class form of Theorem 5.1. -/
theorem theorem_5_1
    [Infinite α] {N : ℕ} (language : Fin N → Set α)
    (observed : ℕ → α) (target : Fin N)
    (hObserved : ∀ t, observed t ∈ language target)
    (hInjective : Function.Injective observed)
    {d : ℕ}
    (hdim : GenLimit.MistakeBounded.FiniteClassClosureDimensionAtMost
      language d) :
    GenLimit.MistakeBounded.TotalMistakesAtMost
        (GenLimit.MistakeBounded.finiteTargetTrace language
          (GenLimit.MistakeBounded.finiteSemanticGenerated language observed)
          target)
        (min (Nat.log 2 N) (d + 1)) ∧
      GenLimit.MistakeBounded.LastMistakeBefore
        (GenLimit.MistakeBounded.finiteTargetTrace language
          (GenLimit.MistakeBounded.finiteSemanticGenerated language observed)
          target)
        (d + 1) :=
  GenLimit.MistakeBounded.theorem_5_1_corrected_concrete_semantic_algorithm
    language observed target hObserved hInjective hdim

/-- Kernel-checked obstruction to the unshifted closure-dimension clause in
the printed Theorem 5.1 under generator-first order. -/
theorem theorem_5_1_order_diagnostic
    {L₀ L₁ : Set α}
    (hL₀ : L₀.Infinite) (hL₁ : L₁.Infinite)
    (hdisjoint : Disjoint L₀ L₁) (x : α) :
    GenLimit.MistakeBounded.FiniteClassClosureDimensionAtMost
        (GenLimit.MistakeBounded.disjointPairLanguage L₀ L₁) 0 ∧
      (x ∉ GenLimit.MistakeBounded.disjointPairLanguage L₀ L₁ 0 ∨
        x ∉ GenLimit.MistakeBounded.disjointPairLanguage L₀ L₁ 1) :=
  GenLimit.MistakeBounded.theorem_5_1_reversed_order_diagnostic
    hL₀ hL₁ hdisjoint x

/-- Section 6.1's exact source-aligned integer logarithmic bound. -/
theorem theorem_6_1
    [Infinite α]
    (language : ℕ → Set α) (observed : ℕ → α)
    (hInjective : Function.Injective observed)
    (target : ℕ)
    (hObserved : ∀ t, observed t ∈ language target) :
    GenLimit.MistakeBounded.TotalMistakesAtMost
      (GenLimit.MistakeBounded.countableTargetTrace language
        (GenLimit.MistakeBounded.countableSemanticGenerated
          GenLimit.MistakeBounded.paperDoublingActiveCount
          GenLimit.MistakeBounded.polynomialPrior language observed)
        target)
      ((Nat.clog 2 (target + 1)).pred +
        GenLimit.MistakeBounded.polynomialPriorLogBudget target) :=
  GenLimit.MistakeBounded.theorem_6_1_logFloor_concrete_semantic_algorithm
    language observed hInjective target hObserved

/-- Section 6.1's displayed real-valued bound, with the invalid arithmetic
equality in the source proof repaired to the valid inequality. -/
theorem theorem_6_1_displayed_bound
    [Infinite α]
    (language : ℕ → Set α) (observed : ℕ → α)
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
    (language : ℕ → Set α) (observed : ℕ → α)
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
    (language : ℕ → Set α) (observed : ℕ → α)
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

end GenLimit.MistakeBounded.Results
