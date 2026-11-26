import GenLimit.Paper29_MistakeBoundedLanguageGeneration.ClosureBridge
import GenLimit.Paper29_MistakeBoundedLanguageGeneration.FiniteWeightedRun
import GenLimit.Paper29_MistakeBoundedLanguageGeneration.PositiveTargetWeight
import GenLimit.Paper29_MistakeBoundedLanguageGeneration.Results.Supporting
import GenLimit.Paper29_MistakeBoundedLanguageGeneration.TargetPriority

/-!
# Paper 29: main theorems

The original main-text theorems of Kleinberg, Peale, and Reingold,
*Mistake-Bounded Language Generation* (arXiv:2605.10809v1), in paper order.
-/

namespace GenLimit.MistakeBounded.Results

/-- Theorem 4.1. With positive target weight, Algorithm 1 makes at most
the activation time plus the dyadic budget in mistakes. -/
theorem theorem_4_1
    [Infinite α]
    (activeCount : ℕ → ℕ) (initialWeight : ℕ → ℝ)
    (language : Generic.LanguageFamily α) (observed : Generic.Stream α)
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

/-- Theorem 5.1. On a finite class, Algorithm 1 makes at most
`min (Nat.log 2 N) (d + 1)` mistakes. Generator-first timing gives the cutoff `d + 1`. -/
theorem theorem_5_1
    [Infinite α] {N : ℕ} (language : Fin N → Generic.Language α)
    (observed : Generic.Stream α) (target : Fin N)
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

/-- Theorem 6.1, in its sharper integer form. Write `i = target + 1` for the paper's
one-based language index. The doubling schedule takes `max(0, ⌈log₂ i⌉ − 1)` rounds
to activate language `i`. From activation onward, its prior weight `1/i²` gives a
budget of `⌊log₂(π² i² / 6)⌋` further mistakes.

The sum bounds the total mistakes at every horizon. Bounding the first term by
`log₂ i` and the second by `log₂(π² i² / 6)` gives the paper's displayed bound
`3 log₂ i + log₂(π² / 6)`, formalized in `theorem_6_1_displayed_bound`. -/
theorem theorem_6_1
    [Infinite α]
    (language : Generic.LanguageFamily α) (observed : Generic.Stream α)
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

/-- Refutation of the displayed pointwise Theorem 6.4. Indices are zero-based,
so the claimed lower bound at the second language is one. -/
theorem theorem_6_4_printed_false (α : Type*) [Infinite α] :
    ¬∃ L : Generic.LanguageFamily α, (∀ i, (L i).Infinite) ∧
      ∀ G : Generic.Generator α, (∀ t xs, G t xs ∉ Generic.sequenceSample xs) →
        (∃ C : ℕ, ∀ i (s : PositiveRun (L i)),
          LastMistakeBefore (countableTargetTrace L (Generic.output G s.val) i)
            (C * paperTimeScale L i)) →
        ∀ i : ℕ, 1 ≤ i → (i : WithTop ℕ) ≤ worstCaseMistakes
          (fun s : PositiveRun (L i) => countableTargetTrace L (Generic.output G s.val) i) := by
  rintro ⟨L, hL, claim⟩
  obtain ⟨G, hfresh, htime, hzero⟩ := priority_zero_mistakes L 1 (hL 1)
  have h := claim G hfresh htime 1 le_rfl
  rw [hzero] at h
  exact (by norm_num : ¬((1 : ℕ) : WithTop ℕ) ≤ 0) h

end GenLimit.MistakeBounded.Results
