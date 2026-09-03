import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Algorithm 1's one-step weight recurrence

This is the concrete algebra in Appendix Lemma A.1 of Kleinberg--Peale--
Reingold, *Mistake-Bounded Language Generation*, arXiv:2605.10809v1.
For a finite active prefix of languages, the algorithm outputs a point whose
consistent-language weight is maximal.  After observing the adversary's
point, inconsistent languages are eliminated and mistaken surviving
languages have their weight doubled.  The total active weight cannot grow.

The proof partitions active weight into the four membership cells determined
by the generated and observed points.  Unlike the earlier abstract potential
module, this theorem checks the paper's actual update rule.
-/

namespace GenLimit.MistakeBounded

open scoped BigOperators

/-- Total active weight of languages containing `x`. -/
noncomputable def weightedScore
    (active : Finset ι) (weight : ι → ℝ)
    (language : ι → Set α) (x : α) : ℝ := by
  classical
  exact ∑ i ∈ active, if x ∈ language i then weight i else 0

/-- Algorithm 1's update on an already active language. -/
noncomputable def updateWeight
    (weight : ι → ℝ) (language : ι → Set α)
    (observed generated : α) (i : ι) : ℝ := by
  classical
  exact
    if observed ∉ language i then 0
    else if generated ∈ language i then weight i
    else 2 * weight i

/-- The generated point is a maximizer against the observed point.  This is
the only property of `argmax` used by Appendix Lemma A.1. -/
def BeatsObserved
    (active : Finset ι) (weight : ι → ℝ)
    (language : ι → Set α) (generated observed : α) : Prop :=
  weightedScore active weight language observed ≤
    weightedScore active weight language generated

/-- Appendix Lemma A.1, active-prefix step: the update cannot increase total
weight when all old weights are nonnegative and the generated point beats
the subsequently observed point in weighted score. -/
theorem updated_active_weight_le
    [DecidableEq ι]
    (active : Finset ι) (weight : ι → ℝ)
    (language : ι → Set α) (observed generated : α)
    (hweight : ∀ i ∈ active, 0 ≤ weight i)
    (hmax : BeatsObserved active weight language generated observed) :
    (∑ i ∈ active,
        updateWeight weight language observed generated i) ≤
      ∑ i ∈ active, weight i := by
  classical
  let both : ℝ :=
    ∑ i ∈ active,
      if observed ∈ language i ∧ generated ∈ language i
      then weight i else 0
  let observedOnly : ℝ :=
    ∑ i ∈ active,
      if observed ∈ language i ∧ generated ∉ language i
      then weight i else 0
  let generatedOnly : ℝ :=
    ∑ i ∈ active,
      if observed ∉ language i ∧ generated ∈ language i
      then weight i else 0
  let neither : ℝ :=
    ∑ i ∈ active,
      if observed ∉ language i ∧ generated ∉ language i
      then weight i else 0

  have hObserved :
      weightedScore active weight language observed =
        both + observedOnly := by
    change (∑ i ∈ active,
        if observed ∈ language i then weight i else 0) =
      both + observedOnly
    rw [show both + observedOnly =
      ∑ i ∈ active,
        ((if observed ∈ language i ∧ generated ∈ language i
          then weight i else 0) +
        (if observed ∈ language i ∧ generated ∉ language i
          then weight i else 0)) by
      simp only [both, observedOnly, Finset.sum_add_distrib]]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hObserved : observed ∈ language i <;>
      by_cases hGenerated : generated ∈ language i <;>
      simp [hObserved, hGenerated]

  have hGenerated :
      weightedScore active weight language generated =
        both + generatedOnly := by
    change (∑ i ∈ active,
        if generated ∈ language i then weight i else 0) =
      both + generatedOnly
    rw [show both + generatedOnly =
      ∑ i ∈ active,
        ((if observed ∈ language i ∧ generated ∈ language i
          then weight i else 0) +
        (if observed ∉ language i ∧ generated ∈ language i
          then weight i else 0)) by
      simp only [both, generatedOnly, Finset.sum_add_distrib]]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hObserved : observed ∈ language i <;>
      by_cases hGenerated : generated ∈ language i <;>
      simp [hObserved, hGenerated]

  have hUpdated :
      (∑ i ∈ active,
          updateWeight weight language observed generated i) =
        both + 2 * observedOnly := by
    have hmul :
        2 * observedOnly =
          ∑ i ∈ active,
            2 * (if observed ∈ language i ∧ generated ∉ language i
              then weight i else 0) := by
      simp only [observedOnly]
      exact map_sum (AddMonoidHom.mulLeft (2 : ℝ)) _ active
    change (∑ i ∈ active,
        if observed ∉ language i then 0
        else if generated ∈ language i then weight i
        else 2 * weight i) =
      both + 2 * observedOnly
    rw [show both + 2 * observedOnly =
      ∑ i ∈ active,
        ((if observed ∈ language i ∧ generated ∈ language i
          then weight i else 0) +
        2 * (if observed ∈ language i ∧ generated ∉ language i
          then weight i else 0)) by
      rw [hmul]
      simp only [both, Finset.sum_add_distrib]]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hObserved : observed ∈ language i <;>
      by_cases hGenerated : generated ∈ language i <;>
      simp [hObserved, hGenerated]

  have hOld :
      (∑ i ∈ active, weight i) =
        both + observedOnly + generatedOnly + neither := by
    change (∑ i ∈ active, weight i) =
      (∑ i ∈ active,
          if observed ∈ language i ∧ generated ∈ language i
          then weight i else 0) +
        (∑ i ∈ active,
          if observed ∈ language i ∧ generated ∉ language i
          then weight i else 0) +
        (∑ i ∈ active,
          if observed ∉ language i ∧ generated ∈ language i
          then weight i else 0) +
        (∑ i ∈ active,
          if observed ∉ language i ∧ generated ∉ language i
          then weight i else 0)
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hObserved : observed ∈ language i <;>
      by_cases hGenerated : generated ∈ language i <;>
      simp [hObserved, hGenerated]

  have hObservedOnlyNonnegative : 0 ≤ observedOnly := by
    apply Finset.sum_nonneg
    intro i hi
    split
    · exact hweight i hi
    · exact le_rfl
  have hGeneratedOnlyNonnegative : 0 ≤ generatedOnly := by
    apply Finset.sum_nonneg
    intro i hi
    split
    · exact hweight i hi
    · exact le_rfl
  have hNeitherNonnegative : 0 ≤ neither := by
    apply Finset.sum_nonneg
    intro i hi
    split
    · exact hweight i hi
    · exact le_rfl
  have hObservedOnlyLe : observedOnly ≤ generatedOnly := by
    rw [BeatsObserved, hObserved, hGenerated] at hmax
    linarith
  rw [hUpdated, hOld]
  linarith

end GenLimit.MistakeBounded
