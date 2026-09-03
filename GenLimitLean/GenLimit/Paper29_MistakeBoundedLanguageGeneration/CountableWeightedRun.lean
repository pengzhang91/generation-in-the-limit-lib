import GenLimit.Paper29_MistakeBoundedLanguageGeneration.PositiveTargetWeight
import GenLimit.Paper29_MistakeBoundedLanguageGeneration.WeightedMaximizer
import GenLimit.Core.GenericGeneration
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A semantic countable-class run of Algorithm 1

This module implements the growing active-prefix version of Algorithm 1 from
Kleinberg--Peale--Reingold, *Mistake-Bounded Language Generation*,
arXiv:2605.10809v1.

At round `t`, indices below `activeCount t` are active.  Old weights follow
the paper's eliminate/keep/double recurrence.  An index that first enters at
round `t + 1` receives its prior weight exactly when every observation
through round `t` belongs to its language.  The output is the noncomputable
fresh weighted maximizer already constructed from finite membership
patterns.

The main accounting theorem says that total active mass never exceeds the
corresponding prefix of the prior mass.  For a target with positive prior
weight, the later theorems identify its weight exactly with its prior weight
times `2^(number of mistakes since activation)` and derive the corrected
Theorem 4.1 bound.

This is a semantic construction on an arbitrary infinite point universe.  It
does not claim an effective search procedure or a runtime bound.
-/

namespace GenLimit.MistakeBounded

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- The target-relative mistake trace for a countable language family. -/
noncomputable def countableTargetTrace
    (language : ℕ → Set α) (generated : ℕ → α)
    (target : ℕ) : MistakeTrace := by
  classical
  exact fun t => decide (generated t ∉ language target)

/-- The recursively maintained weights of the growing-prefix semantic run.

Indices already active at round `t` use `updateWeight`.  Newly activated
indices are initialized from `initialWeight` exactly when the observed
prefix through the current round is consistent with them.  Inactive indices
have weight zero. -/
noncomputable def countableSemanticWeight
    [Infinite α]
    (activeCount : ℕ → ℕ) (initialWeight : ℕ → ℝ)
    (language : ℕ → Set α) (observed : ℕ → α) :
    ℕ → ℕ → ℝ := by
  classical
  exact fun round =>
    Nat.rec
      (fun i =>
        if i < activeCount 0 then initialWeight i else 0)
      (fun t weight i =>
        if i < activeCount t then
          updateWeight weight language (observed t)
            (infiniteFreshWeightedMaximizer
              (Finset.range (activeCount t)) weight
              language (GenLimit.Generic.sample observed t))
            i
        else if i < activeCount (t + 1) ∧
            ∀ s, s ≤ t → observed s ∈ language i then
          initialWeight i
        else 0)
      round

/-- Algorithm 1's semantic fresh maximizer at round `t`. -/
noncomputable def countableSemanticGenerated
    [Infinite α]
    (activeCount : ℕ → ℕ) (initialWeight : ℕ → ℝ)
    (language : ℕ → Set α) (observed : ℕ → α)
    (t : ℕ) : α :=
  infiniteFreshWeightedMaximizer
    (Finset.range (activeCount t))
    (countableSemanticWeight activeCount initialWeight
      language observed t)
    language (GenLimit.Generic.sample observed t)

@[simp] theorem countableSemanticWeight_zero
    [Infinite α]
    (activeCount : ℕ → ℕ) (initialWeight : ℕ → ℝ)
    (language : ℕ → Set α) (observed : ℕ → α)
    (i : ℕ) :
    countableSemanticWeight activeCount initialWeight
        language observed 0 i =
      if i < activeCount 0 then initialWeight i else 0 := by
  rfl

@[simp] theorem countableSemanticWeight_succ
    [Infinite α]
    (activeCount : ℕ → ℕ) (initialWeight : ℕ → ℝ)
    (language : ℕ → Set α) (observed : ℕ → α)
    (t i : ℕ) :
    countableSemanticWeight activeCount initialWeight
        language observed (t + 1) i =
      if i < activeCount t then
        updateWeight
          (countableSemanticWeight activeCount initialWeight
            language observed t)
          language (observed t)
          (countableSemanticGenerated activeCount initialWeight
            language observed t) i
      else if i < activeCount (t + 1) ∧
          ∀ s, s ≤ t → observed s ∈ language i then
        initialWeight i
      else 0 := by
  rfl

theorem countableSemanticWeight_succ_old
    [Infinite α]
    (activeCount : ℕ → ℕ) (initialWeight : ℕ → ℝ)
    (language : ℕ → Set α) (observed : ℕ → α)
    (t i : ℕ) (hi : i < activeCount t) :
    countableSemanticWeight activeCount initialWeight
        language observed (t + 1) i =
      updateWeight
        (countableSemanticWeight activeCount initialWeight
          language observed t)
        language (observed t)
        (countableSemanticGenerated activeCount initialWeight
          language observed t) i := by
  rw [countableSemanticWeight_succ, if_pos hi]

theorem countableSemanticWeight_succ_new
    [Infinite α]
    (activeCount : ℕ → ℕ) (initialWeight : ℕ → ℝ)
    (language : ℕ → Set α) (observed : ℕ → α)
    (t i : ℕ)
    (hold : activeCount t ≤ i)
    (hnew : i < activeCount (t + 1))
    (hconsistent : ∀ s, s ≤ t → observed s ∈ language i) :
    countableSemanticWeight activeCount initialWeight
        language observed (t + 1) i =
      initialWeight i := by
  rw [countableSemanticWeight_succ,
    if_neg (Nat.not_lt.mpr hold),
    if_pos ⟨hnew, hconsistent⟩]

theorem countableSemanticWeight_succ_new_inconsistent
    [Infinite α]
    (activeCount : ℕ → ℕ) (initialWeight : ℕ → ℝ)
    (language : ℕ → Set α) (observed : ℕ → α)
    (t i : ℕ)
    (hold : activeCount t ≤ i)
    (hbad : ¬(i < activeCount (t + 1) ∧
      ∀ s, s ≤ t → observed s ∈ language i)) :
    countableSemanticWeight activeCount initialWeight
      language observed (t + 1) i = 0 := by
  rw [countableSemanticWeight_succ,
    if_neg (Nat.not_lt.mpr hold), if_neg hbad]

/-- Every generated point is fresh from the observed prefix. -/
theorem countableSemanticGenerated_not_mem
    [Infinite α]
    (activeCount : ℕ → ℕ) (initialWeight : ℕ → ℝ)
    (language : ℕ → Set α) (observed : ℕ → α)
    (t : ℕ) :
    countableSemanticGenerated activeCount initialWeight
        language observed t ∉
      GenLimit.Generic.sample observed t := by
  exact infiniteFreshWeightedMaximizer_not_mem
    (Finset.range (activeCount t))
    (countableSemanticWeight activeCount initialWeight
      language observed t)
    language (GenLimit.Generic.sample observed t)

/-- The generated point maximizes active weighted score among all points
fresh from the observed prefix. -/
theorem countableSemanticGenerated_spec
    [Infinite α]
    (activeCount : ℕ → ℕ) (initialWeight : ℕ → ℝ)
    (language : ℕ → Set α) (observed : ℕ → α)
    (t : ℕ) :
    ∀ x, x ∉ GenLimit.Generic.sample observed t →
      weightedScore (Finset.range (activeCount t))
          (countableSemanticWeight activeCount initialWeight
            language observed t)
          language x ≤
        weightedScore (Finset.range (activeCount t))
          (countableSemanticWeight activeCount initialWeight
            language observed t)
          language
          (countableSemanticGenerated activeCount initialWeight
            language observed t) := by
  exact infiniteFreshWeightedMaximizer_spec
    (Finset.range (activeCount t))
    (countableSemanticWeight activeCount initialWeight
      language observed t)
    language (GenLimit.Generic.sample observed t)

/-- On an injective presentation, the semantic argmax beats the current
observation in the comparison used by Appendix Lemma A.1. -/
theorem countableSemanticGenerated_beatsObserved
    [Infinite α]
    (activeCount : ℕ → ℕ) (initialWeight : ℕ → ℝ)
    (language : ℕ → Set α) (observed : ℕ → α)
    (hInjective : Function.Injective observed) :
    ∀ t,
      BeatsObserved (Finset.range (activeCount t))
        (countableSemanticWeight activeCount initialWeight
          language observed t)
        language
        (countableSemanticGenerated activeCount initialWeight
          language observed t)
        (observed t) := by
  intro t
  apply countableSemanticGenerated_spec
  intro hmem
  obtain ⟨s, hs, hst⟩ :=
    GenLimit.Generic.mem_sample_iff.mp hmem
  have : s = t := hInjective hst
  omega

/-- All maintained weights are nonnegative when the prior weights are. -/
theorem countableSemanticWeight_nonnegative
    [Infinite α]
    (activeCount : ℕ → ℕ) (initialWeight : ℕ → ℝ)
    (language : ℕ → Set α) (observed : ℕ → α)
    (hInitial : ∀ i, 0 ≤ initialWeight i) :
    ∀ t i,
      0 ≤ countableSemanticWeight activeCount initialWeight
        language observed t i := by
  intro t
  induction t with
  | zero =>
      intro i
      rw [countableSemanticWeight_zero]
      split
      · exact hInitial i
      · exact le_rfl
  | succ t ih =>
      intro i
      rw [countableSemanticWeight_succ]
      split
      next hold =>
        by_cases hObserved : observed t ∈ language i
        · by_cases hGenerated :
              countableSemanticGenerated activeCount initialWeight
                language observed t ∈ language i
          · simp [updateWeight, hObserved, hGenerated, ih i]
          · simp [updateWeight, hObserved, hGenerated, ih i]
        · simp [updateWeight, hObserved]
      next hnotOld =>
        split
        next hnew => exact hInitial i
        next hnotNew => exact le_rfl

/-- Under a monotone schedule, every index outside the current active prefix
has weight zero. -/
theorem countableSemanticWeight_eq_zero_of_inactive
    [Infinite α]
    (activeCount : ℕ → ℕ) (initialWeight : ℕ → ℝ)
    (language : ℕ → Set α) (observed : ℕ → α)
    (hmono : Monotone activeCount) :
    ∀ t i, activeCount t ≤ i →
      countableSemanticWeight activeCount initialWeight
        language observed t i = 0 := by
  intro t
  cases t with
  | zero =>
      intro i hi
      rw [countableSemanticWeight_zero,
        if_neg (Nat.not_lt.mpr hi)]
  | succ t =>
      intro i hi
      have hold : activeCount t ≤ i :=
        (hmono (Nat.le_succ t)).trans hi
      apply countableSemanticWeight_succ_new_inconsistent
        activeCount initialWeight language observed t i hold
      exact fun h => (Nat.not_lt.mpr hi) h.1

/-- The indices entering the active prefix between rounds `t` and `t+1`. -/
def newlyActivated
    (activeCount : ℕ → ℕ) (t : ℕ) : Finset ℕ :=
  (Finset.range (activeCount (t + 1))).filter
    fun i => activeCount t ≤ i

theorem activePrefix_union_newlyActivated
    (activeCount : ℕ → ℕ) (hmono : Monotone activeCount)
    (t : ℕ) :
    Finset.range (activeCount (t + 1)) =
      Finset.range (activeCount t) ∪ newlyActivated activeCount t := by
  ext i
  have hstep : activeCount t ≤ activeCount (t + 1) :=
    hmono (Nat.le_succ t)
  simp only [newlyActivated, Finset.mem_range, Finset.mem_union,
    Finset.mem_filter]
  omega

theorem activePrefix_disjoint_newlyActivated
    (activeCount : ℕ → ℕ) (t : ℕ) :
    Disjoint (Finset.range (activeCount t))
      (newlyActivated activeCount t) := by
  apply Finset.disjoint_left.mpr
  intro i hiOld hiNew
  have hiOld' : i < activeCount t := by simpa using hiOld
  have hiNew' : activeCount t ≤ i := by
    exact (Finset.mem_filter.mp hiNew).2
  omega

/-- Total mass carried by the active prefix at a given round. -/
noncomputable def countableActiveWeight
    [Infinite α]
    (activeCount : ℕ → ℕ) (initialWeight : ℕ → ℝ)
    (language : ℕ → Set α) (observed : ℕ → α)
    (t : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (activeCount t),
    countableSemanticWeight activeCount initialWeight
      language observed t i

/-- Prior mass assigned to a finite index prefix. -/
noncomputable def initialPrefixWeight
    (initialWeight : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, initialWeight i

/-- One growing-prefix step can add at most the prior mass of the indices
activated in that step.  The old active mass itself cannot increase. -/
theorem countableActiveWeight_succ_le
    [Infinite α]
    (activeCount : ℕ → ℕ) (initialWeight : ℕ → ℝ)
    (language : ℕ → Set α) (observed : ℕ → α)
    (hmono : Monotone activeCount)
    (hInitial : ∀ i, 0 ≤ initialWeight i)
    (hInjective : Function.Injective observed)
    (t : ℕ) :
    countableActiveWeight activeCount initialWeight
        language observed (t + 1) ≤
      countableActiveWeight activeCount initialWeight
          language observed t +
        ∑ i ∈ newlyActivated activeCount t, initialWeight i := by
  classical
  let old := Finset.range (activeCount t)
  let new := newlyActivated activeCount t
  let weight :=
    countableSemanticWeight activeCount initialWeight
      language observed t
  let generated :=
    countableSemanticGenerated activeCount initialWeight
      language observed t

  have hOldUpdate :
      (∑ i ∈ old,
          countableSemanticWeight activeCount initialWeight
            language observed (t + 1) i) =
        ∑ i ∈ old,
          updateWeight weight language (observed t) generated i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < activeCount t := by
      simpa [old] using hi
    exact countableSemanticWeight_succ_old
      activeCount initialWeight language observed t i hi'

  have hOldLe :
      (∑ i ∈ old,
          countableSemanticWeight activeCount initialWeight
            language observed (t + 1) i) ≤
        ∑ i ∈ old, weight i := by
    rw [hOldUpdate]
    apply updated_active_weight_le
    · intro i hi
      exact countableSemanticWeight_nonnegative
        activeCount initialWeight language observed hInitial t i
    · exact countableSemanticGenerated_beatsObserved
        activeCount initialWeight language observed hInjective t

  have hNewLe :
      (∑ i ∈ new,
          countableSemanticWeight activeCount initialWeight
            language observed (t + 1) i) ≤
        ∑ i ∈ new, initialWeight i := by
    apply Finset.sum_le_sum
    intro i hi
    have hiData :
        i ∈ Finset.range (activeCount (t + 1)) ∧
          activeCount t ≤ i := by
      simpa [new, newlyActivated] using hi
    have hnotOld : ¬i < activeCount t := by
      omega
    rw [countableSemanticWeight_succ, if_neg hnotOld]
    split
    · exact le_rfl
    · exact hInitial i

  have hPartition :=
    activePrefix_union_newlyActivated activeCount hmono t
  have hDisjoint :=
    activePrefix_disjoint_newlyActivated activeCount t
  rw [countableActiveWeight, hPartition,
    Finset.sum_union hDisjoint]
  exact add_le_add hOldLe hNewLe

/-- The active mass never exceeds the prior mass of the currently activated
prefix.  This is the growing-class form of Appendix Lemma A.1. -/
theorem countableActiveWeight_le_initialPrefix
    [Infinite α]
    (activeCount : ℕ → ℕ) (initialWeight : ℕ → ℝ)
    (language : ℕ → Set α) (observed : ℕ → α)
    (hmono : Monotone activeCount)
    (hInitial : ∀ i, 0 ≤ initialWeight i)
    (hInjective : Function.Injective observed) :
    ∀ t,
      countableActiveWeight activeCount initialWeight
          language observed t ≤
        initialPrefixWeight initialWeight (activeCount t) := by
  intro t
  induction t with
  | zero =>
      apply le_of_eq
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i < activeCount 0 := by simpa using hi
      rw [countableSemanticWeight_zero, if_pos hi']
  | succ t ih =>
      have hstep :=
        countableActiveWeight_succ_le
          activeCount initialWeight language observed
          hmono hInitial hInjective t
      have hprior :
          initialPrefixWeight initialWeight (activeCount (t + 1)) =
            initialPrefixWeight initialWeight (activeCount t) +
              ∑ i ∈ newlyActivated activeCount t,
                initialWeight i := by
        rw [initialPrefixWeight, initialPrefixWeight,
          activePrefix_union_newlyActivated activeCount hmono t,
          Finset.sum_union
            (activePrefix_disjoint_newlyActivated activeCount t)]
      rw [hprior]
      exact hstep.trans (add_le_add_right ih _)

/-- A uniform bound on all prior prefix sums bounds every active potential. -/
theorem countableActiveWeight_le_totalBound
    [Infinite α]
    (activeCount : ℕ → ℕ) (initialWeight : ℕ → ℝ)
    (language : ℕ → Set α) (observed : ℕ → α)
    (hmono : Monotone activeCount)
    (hInitial : ∀ i, 0 ≤ initialWeight i)
    (hInjective : Function.Injective observed)
    {totalBound : ℝ}
    (hPrior : ∀ n, initialPrefixWeight initialWeight n ≤ totalBound) :
    ∀ t,
      countableActiveWeight activeCount initialWeight
        language observed t ≤ totalBound := by
  intro t
  exact
    (countableActiveWeight_le_initialPrefix
      activeCount initialWeight language observed
      hmono hInitial hInjective t).trans
      (hPrior (activeCount t))

/-- `activation` is the first round at which `target` belongs to the active
index prefix. -/
def FirstActivated
    (activeCount : ℕ → ℕ) (target activation : ℕ) : Prop :=
  target < activeCount activation ∧
    ∀ t, t < activation → activeCount t ≤ target

/-- A realizable target receives exactly its prior weight on its first
activation round. -/
theorem countableSemanticWeight_at_firstActivation
    [Infinite α]
    (activeCount : ℕ → ℕ) (initialWeight : ℕ → ℝ)
    (language : ℕ → Set α) (observed : ℕ → α)
    (target activation : ℕ)
    (hFirst : FirstActivated activeCount target activation)
    (hObserved : ∀ t, observed t ∈ language target) :
    countableSemanticWeight activeCount initialWeight
        language observed activation target =
      initialWeight target := by
  cases activation with
  | zero =>
      rw [countableSemanticWeight_zero, if_pos hFirst.1]
  | succ t =>
      apply countableSemanticWeight_succ_new
      · exact hFirst.2 t (Nat.lt_succ_self t)
      · exact hFirst.1
      · intro s _hs
        exact hObserved s

/-- A first-activated target remains active forever under a monotone
schedule. -/
theorem target_active_after_firstActivation
    (activeCount : ℕ → ℕ)
    (hmono : Monotone activeCount)
    {target activation : ℕ}
    (hFirst : FirstActivated activeCount target activation) :
    ∀ d, target < activeCount (activation + d) := by
  intro d
  exact lt_of_lt_of_le hFirst.1
    (hmono (Nat.le_add_right activation d))

/-- After activation, a realizable target's weight is exactly its prior
weight multiplied by `2` once for every target mistake. -/
theorem countableSemantic_targetWeight_eq_pow_mistakes
    [Infinite α]
    (activeCount : ℕ → ℕ) (initialWeight : ℕ → ℝ)
    (language : ℕ → Set α) (observed : ℕ → α)
    (hmono : Monotone activeCount)
    (target activation : ℕ)
    (hFirst : FirstActivated activeCount target activation)
    (hObserved : ∀ t, observed t ∈ language target) :
    ∀ d,
      countableSemanticWeight activeCount initialWeight
          language observed (activation + d) target =
        (2 : ℝ) ^ mistakeCount
            (traceAfter
              (countableTargetTrace language
                (countableSemanticGenerated activeCount initialWeight
                  language observed)
                target)
              activation)
            d *
          initialWeight target := by
  intro d
  induction d with
  | zero =>
      simpa using
        countableSemanticWeight_at_firstActivation
          activeCount initialWeight language observed
          target activation hFirst hObserved
  | succ d ih =>
      let generated :=
        countableSemanticGenerated activeCount initialWeight
          language observed
      let trace :=
        countableTargetTrace language generated target
      have hactive :
          target < activeCount (activation + d) :=
        target_active_after_firstActivation
          activeCount hmono hFirst d
      rw [Nat.add_succ,
        countableSemanticWeight_succ_old
          activeCount initialWeight language observed
          (activation + d) target hactive,
        mistakeCount_succ]
      change
        updateWeight
            (countableSemanticWeight activeCount initialWeight
              language observed (activation + d))
            language (observed (activation + d))
            (generated (activation + d)) target =
          (2 : ℝ) ^
              (mistakeCount (traceAfter trace activation) d +
                if traceAfter trace activation d = true then 1 else 0) *
            initialWeight target
      simp only [updateWeight]
      have ih' :
          countableSemanticWeight activeCount initialWeight
              language observed (activation + d) target =
            (2 : ℝ) ^
                mistakeCount (traceAfter trace activation) d *
              initialWeight target := by
        simpa [trace, generated] using ih
      rw [ih']
      by_cases hGenerated :
          generated (activation + d) ∈ language target
      · have hTrace :
            traceAfter trace activation d = false := by
          simp [traceAfter, trace, countableTargetTrace,
            hGenerated]
        simp [hObserved (activation + d),
          hGenerated, hTrace]
      · have hTrace :
            traceAfter trace activation d = true := by
          simp [traceAfter, trace, countableTargetTrace,
            hGenerated]
        simp [hObserved (activation + d),
          hGenerated, hTrace, pow_succ]
        ring

/-- The weight of any active index is bounded by total active mass. -/
theorem countableSemanticWeight_le_activeWeight
    [Infinite α]
    (activeCount : ℕ → ℕ) (initialWeight : ℕ → ℝ)
    (language : ℕ → Set α) (observed : ℕ → α)
    (hInitial : ∀ i, 0 ≤ initialWeight i)
    {t target : ℕ} (hactive : target < activeCount t) :
    countableSemanticWeight activeCount initialWeight
        language observed t target ≤
      countableActiveWeight activeCount initialWeight
        language observed t := by
  apply Finset.single_le_sum
  · intro i hi
    exact countableSemanticWeight_nonnegative
      activeCount initialWeight language observed hInitial t i
  · simpa using hactive

/-- Concrete countable-class mistake inequality after target activation. -/
theorem countableSemantic_two_pow_mistakes_mul_weight_le
    [Infinite α]
    (activeCount : ℕ → ℕ) (initialWeight : ℕ → ℝ)
    (language : ℕ → Set α) (observed : ℕ → α)
    (hmono : Monotone activeCount)
    (hInitial : ∀ i, 0 ≤ initialWeight i)
    (hInjective : Function.Injective observed)
    {totalBound : ℝ}
    (hPrior : ∀ n, initialPrefixWeight initialWeight n ≤ totalBound)
    (target activation : ℕ)
    (hFirst : FirstActivated activeCount target activation)
    (hObserved : ∀ t, observed t ∈ language target) :
    ∀ d,
      (2 : ℝ) ^ mistakeCount
            (traceAfter
              (countableTargetTrace language
                (countableSemanticGenerated activeCount initialWeight
                  language observed)
                target)
              activation)
            d *
          initialWeight target ≤
        totalBound := by
  intro d
  rw [← countableSemantic_targetWeight_eq_pow_mistakes
    activeCount initialWeight language observed
    hmono target activation hFirst hObserved d]
  exact
    (countableSemanticWeight_le_activeWeight
      activeCount initialWeight language observed hInitial
      (target_active_after_firstActivation
        activeCount hmono hFirst d)).trans
      (countableActiveWeight_le_totalBound
        activeCount initialWeight language observed
        hmono hInitial hInjective hPrior (activation + d))

/-- Corrected concrete semantic form of Theorem 4.1.

The target must have positive prior weight.  `activation` is its first active
round, and `budget` is any division-free dyadic budget satisfying
`totalBound < 2^(budget+1) * initialWeight target`.  The result includes the
trivial possible mistakes before activation and the logarithmic bound after
activation. -/
theorem theorem_4_1_corrected_concrete_semantic_algorithm
    [Infinite α]
    (activeCount : ℕ → ℕ) (initialWeight : ℕ → ℝ)
    (language : ℕ → Set α) (observed : ℕ → α)
    (hmono : Monotone activeCount)
    (hInitial : ∀ i, 0 ≤ initialWeight i)
    (hInjective : Function.Injective observed)
    {totalBound : ℝ}
    (hPrior : ∀ n, initialPrefixWeight initialWeight n ≤ totalBound)
    (target activation budget : ℕ)
    (hFirst : FirstActivated activeCount target activation)
    (hObserved : ∀ t, observed t ∈ language target)
    (hTargetPositive : 0 < initialWeight target)
    (hBudget :
      DyadicUpperBudget totalBound (initialWeight target) budget) :
    TotalMistakesAtMost
      (countableTargetTrace language
        (countableSemanticGenerated activeCount initialWeight
          language observed)
        target)
      (activation + budget) := by
  let trace :=
    countableTargetTrace language
      (countableSemanticGenerated activeCount initialWeight
        language observed)
      target
  have hpower :
      ∀ d,
        (2 : ℝ) ^
              mistakeCount (traceAfter trace activation) d *
            initialWeight target ≤
          totalBound := by
    exact countableSemantic_two_pow_mistakes_mul_weight_le
      activeCount initialWeight language observed
      hmono hInitial hInjective hPrior
      target activation hFirst hObserved
  have hafter :
      TotalMistakesAtMost
        (traceAfter trace activation) budget := by
    intro d
    by_contra hnot
    have hsucc :
        budget + 1 ≤
          mistakeCount (traceAfter trace activation) d := by
      omega
    have hpowNat :
        2 ^ (budget + 1) ≤
          2 ^ mistakeCount (traceAfter trace activation) d :=
      Nat.pow_le_pow_right (by omega) hsucc
    have hpowReal :
        (2 : ℝ) ^ (budget + 1) ≤
          (2 : ℝ) ^
            mistakeCount (traceAfter trace activation) d := by
      exact_mod_cast hpowNat
    have hthreshold :
        (2 : ℝ) ^ (budget + 1) * initialWeight target ≤
          totalBound :=
      (mul_le_mul_of_nonneg_right hpowReal
        (le_of_lt hTargetPositive)).trans (hpower d)
    exact (not_le_of_gt hBudget) hthreshold
  intro t
  by_cases ht : activation ≤ t
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
    rw [mistakeCount_add_traceAfter]
    exact Nat.add_le_add
      (mistakeCount_le_round trace activation) (hafter d)
  · have htt : t ≤ activation := Nat.le_of_not_ge ht
    exact (mistakeCount_le_round trace t).trans
      (htt.trans (Nat.le_add_right activation budget))

end GenLimit.MistakeBounded
