import GenLimit.Paper29_MistakeBoundedLanguageGeneration.FiniteWeightedAlgorithm
import GenLimit.Paper29_MistakeBoundedLanguageGeneration.WeightedMaximizer

/-!
# A concrete semantic run of finite-class Algorithm 1

The finite-class development previously accepted the paper's weighted-argmax
rule as a hypothesis on an arbitrary generated stream.  The finite-pattern
maximizer now lets us construct such a stream on every infinite point
universe.

We recurse first on the current vector of weights.  The output at round `t`
is the fresh semantic maximizer for that vector, and the successor vector is
the paper's displayed update using this output.  This avoids any circularity
between the stream and its induced weights.  A short induction then proves
that the constructed vector is exactly `finiteAlgorithmWeight` for the
constructed stream.

The construction is noncomputable and carries no runtime claim.
-/

namespace GenLimit.MistakeBounded

open scoped BigOperators

/-- The recursively maintained weight vector for the concrete semantic run. -/
noncomputable def finiteSemanticWeight
    [Infinite α] {N : ℕ} (language : Fin N → Set α)
    (observed : ℕ → α) :
    ℕ → Fin N → ℝ
  | 0 => fun _ => 1
  | t + 1 =>
      updateWeight
        (finiteSemanticWeight language observed t)
        language (observed t)
        (infiniteFreshWeightedMaximizer Finset.univ
          (finiteSemanticWeight language observed t)
          language (GenLimit.Generic.sample observed t))

/-- Algorithm 1's output stream, selecting a fresh weighted maximizer at
each round for the recursively maintained vector. -/
noncomputable def finiteSemanticGenerated
    [Infinite α] {N : ℕ} (language : Fin N → Set α)
    (observed : ℕ → α) (t : ℕ) : α :=
  infiniteFreshWeightedMaximizer Finset.univ
    (finiteSemanticWeight language observed t)
    language (GenLimit.Generic.sample observed t)

@[simp] theorem finiteSemanticWeight_zero
    [Infinite α] {N : ℕ} (language : Fin N → Set α)
    (observed : ℕ → α) (i : Fin N) :
    finiteSemanticWeight language observed 0 i = 1 := by
  rfl

@[simp] theorem finiteSemanticWeight_succ
    [Infinite α] {N : ℕ} (language : Fin N → Set α)
    (observed : ℕ → α) (t : ℕ) (i : Fin N) :
    finiteSemanticWeight language observed (t + 1) i =
      updateWeight
        (finiteSemanticWeight language observed t)
        language (observed t)
        (finiteSemanticGenerated language observed t) i := by
  rfl

/-- The auxiliary recursive vector agrees pointwise with the existing
Algorithm 1 recurrence driven by the constructed output stream. -/
theorem finiteAlgorithmWeight_eq_finiteSemanticWeight
    [Infinite α] {N : ℕ} (language : Fin N → Set α)
    (observed : ℕ → α) :
    ∀ t i,
      finiteAlgorithmWeight language observed
          (finiteSemanticGenerated language observed) t i =
        finiteSemanticWeight language observed t i := by
  intro t
  induction t with
  | zero =>
      intro i
      rfl
  | succ t ih =>
      intro i
      rw [finiteAlgorithmWeight_succ, finiteSemanticWeight_succ]
      have hweights :
          finiteAlgorithmWeight language observed
              (finiteSemanticGenerated language observed) t =
            finiteSemanticWeight language observed t :=
        funext ih
      rw [hweights]

/-- The constructed stream satisfies the full unseen weighted-argmax rule
that the earlier finite-class theorems used as a hypothesis. -/
theorem finiteSemanticGenerated_isFiniteWeightedArgmax
    [Infinite α] {N : ℕ} (language : Fin N → Set α)
    (observed : ℕ → α) :
    IsFiniteWeightedArgmax language observed
      (finiteSemanticGenerated language observed) := by
  intro t
  constructor
  · exact infiniteFreshWeightedMaximizer_not_mem Finset.univ
      (finiteSemanticWeight language observed t) language
      (GenLimit.Generic.sample observed t)
  · intro x hx
    have hmax :=
      infiniteFreshWeightedMaximizer_spec Finset.univ
        (finiteSemanticWeight language observed t) language
        (GenLimit.Generic.sample observed t) x hx
    have hweights :
        finiteAlgorithmWeight language observed
            (finiteSemanticGenerated language observed) t =
          finiteSemanticWeight language observed t :=
      funext
        (finiteAlgorithmWeight_eq_finiteSemanticWeight
          language observed t)
    rw [hweights]
    simpa only [finiteSemanticGenerated] using hmax

/-- On an injective observed enumeration, the constructed argmax also
satisfies the comparison used by Appendix Lemma A.1. -/
theorem finiteSemanticGenerated_beatsObserved
    [Infinite α] {N : ℕ} (language : Fin N → Set α)
    (observed : ℕ → α)
    (hInjective : Function.Injective observed) :
    ∀ t,
      BeatsObserved Finset.univ
        (finiteAlgorithmWeight language observed
          (finiteSemanticGenerated language observed) t)
        language (finiteSemanticGenerated language observed t)
        (observed t) :=
  finiteArgmax_implies_beatsObserved
    language observed (finiteSemanticGenerated language observed)
    hInjective
    (finiteSemanticGenerated_isFiniteWeightedArgmax language observed)

/-- Concrete, assumption-free-in-the-generator form of the logarithmic
finite-cardinality mistake bound. -/
theorem finiteSemanticGenerated_totalMistakesAtMost_log_card
    [Infinite α] {N : ℕ} (language : Fin N → Set α)
    (observed : ℕ → α) (target : Fin N)
    (hObserved : ∀ t, observed t ∈ language target)
    (hInjective : Function.Injective observed) :
    TotalMistakesAtMost
      (finiteTargetTrace language
        (finiteSemanticGenerated language observed) target)
      (Nat.log 2 N) :=
  finiteAlgorithm_totalMistakesAtMost_log_card
    language observed (finiteSemanticGenerated language observed)
    target hObserved
    (finiteSemanticGenerated_beatsObserved
      language observed hInjective)

/-- Fully instantiated corrected Theorem 5.1 components for the concrete
semantic Algorithm 1 stream.  The `d+1` term is the necessary reversed-order
correction documented by the source diagnostic. -/
theorem theorem_5_1_corrected_concrete_semantic_algorithm
    [Infinite α] {N : ℕ} (language : Fin N → Set α)
    (observed : ℕ → α) (target : Fin N)
    (hObserved : ∀ t, observed t ∈ language target)
    (hInjective : Function.Injective observed)
    {d : ℕ}
    (hdim : FiniteClassClosureDimensionAtMost language d) :
    TotalMistakesAtMost
        (finiteTargetTrace language
          (finiteSemanticGenerated language observed) target)
        (min (Nat.log 2 N) (d + 1)) ∧
      LastMistakeBefore
        (finiteTargetTrace language
          (finiteSemanticGenerated language observed) target)
        (d + 1) :=
  theorem_5_1_corrected_components
    language observed (finiteSemanticGenerated language observed)
    target hObserved hInjective
    (finiteSemanticGenerated_isFiniteWeightedArgmax language observed)
    hdim

end GenLimit.MistakeBounded
