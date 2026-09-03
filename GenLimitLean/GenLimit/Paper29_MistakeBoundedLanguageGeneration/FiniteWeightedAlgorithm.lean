import GenLimit.Paper29_MistakeBoundedLanguageGeneration.Definitions
import GenLimit.Paper29_MistakeBoundedLanguageGeneration.WeightedStep
import GenLimit.Core.GenericGeneration
import Mathlib.Data.Nat.Log
import Mathlib.Data.Set.Card
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite-class weighted generator

This module instantiates Algorithm 1 with a fixed finite class and unit
initial weights, as in the proof of Theorem 5.1.  The generated point is
assumed to satisfy the algorithm's displayed weighted-argmax rule; the
observed point belongs to the target.  From these literal hypotheses Lean
checks both recurrences used in the proof:

1. total active weight never exceeds the initial class size; and
2. target weight is exactly `2^(number of target mistakes)`.

Their combination yields the paper's logarithmic finite-class mistake
inequality `2^M ≤ |𝓛|`.  The closure-dimension argument is also formalized,
with the one-round correction forced by the paper's generator-first order.
-/

namespace GenLimit.MistakeBounded

open scoped BigOperators

/-- Unit-initialized weights produced by Algorithm 1 on a fixed finite
language class. -/
noncomputable def finiteAlgorithmWeight
    {N : ℕ} (language : Fin N → Set α)
    (observed generated : ℕ → α) :
    ℕ → Fin N → ℝ
  | 0 => fun _ => 1
  | t + 1 =>
      updateWeight
        (finiteAlgorithmWeight language observed generated t)
        language (observed t) (generated t)

/-- Mistakes against a selected target language. -/
noncomputable def finiteTargetTrace
    {N : ℕ} (language : Fin N → Set α)
    (generated : ℕ → α) (target : Fin N) : MistakeTrace :=
  by
    classical
    exact fun t => decide (generated t ∉ language target)

/-- The indices not yet eliminated by the adversarial examples strictly
before round `t`.  This is the set `C` in Algorithms 1 and 2. -/
noncomputable def finiteVersionIndices
    {N : ℕ} (language : Fin N → Set α)
    (observed : ℕ → α) (t : ℕ) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter
    (fun i => ∀ s, s < t → observed s ∈ language i)

/-- Intersection of an indexed finite subcollection, matching Definition 4
of the mistake-bounded paper. -/
def finiteClassIntersection
    {N : ℕ} (language : Fin N → Set α)
    (active : Finset (Fin N)) : Set α :=
  {x | ∀ i, i ∈ active → x ∈ language i}

/-- The upper-bound half of Definition 4: every finite intersection of a
subcollection has at most `d` elements.  This avoids assigning a maximum
when the collection has no finite intersection. -/
def FiniteClassClosureDimensionAtMost
    {N : ℕ} (language : Fin N → Set α) (d : ℕ) : Prop :=
  ∀ active : Finset (Fin N),
    (finiteClassIntersection language active).Finite →
      (finiteClassIntersection language active).ncard ≤ d

/-- Algorithm 1's displayed argmax rule over unseen points. -/
def IsFiniteWeightedArgmax
    {N : ℕ} (language : Fin N → Set α)
    (observed generated : ℕ → α) : Prop :=
  ∀ t,
    generated t ∉ GenLimit.Generic.sample observed t ∧
      ∀ x, x ∉ GenLimit.Generic.sample observed t →
        weightedScore Finset.univ
            (finiteAlgorithmWeight language observed generated t)
            language x ≤
          weightedScore Finset.univ
            (finiteAlgorithmWeight language observed generated t)
            language (generated t)

@[simp] theorem finiteAlgorithmWeight_zero
    {N : ℕ} (language : Fin N → Set α)
    (observed generated : ℕ → α) (i : Fin N) :
    finiteAlgorithmWeight language observed generated 0 i = 1 := by
  rfl

@[simp] theorem finiteAlgorithmWeight_succ
    {N : ℕ} (language : Fin N → Set α)
    (observed generated : ℕ → α) (t : ℕ) (i : Fin N) :
    finiteAlgorithmWeight language observed generated (t + 1) i =
      updateWeight
        (finiteAlgorithmWeight language observed generated t)
        language (observed t) (generated t) i := by
  rfl

@[simp] theorem finiteVersionIndices_zero
    {N : ℕ} (language : Fin N → Set α)
    (observed : ℕ → α) :
    finiteVersionIndices language observed 0 = Finset.univ := by
  classical
  ext i
  simp [finiteVersionIndices]

theorem mem_finiteVersionIndices_iff
    {N : ℕ} (language : Fin N → Set α)
    (observed : ℕ → α) (t : ℕ) (i : Fin N) :
    i ∈ finiteVersionIndices language observed t ↔
      ∀ s, s < t → observed s ∈ language i := by
  classical
  simp [finiteVersionIndices]

theorem mem_finiteVersionIndices_succ_iff
    {N : ℕ} (language : Fin N → Set α)
    (observed : ℕ → α) (t : ℕ) (i : Fin N) :
    i ∈ finiteVersionIndices language observed (t + 1) ↔
      i ∈ finiteVersionIndices language observed t ∧
        observed t ∈ language i := by
  rw [mem_finiteVersionIndices_iff,
    mem_finiteVersionIndices_iff]
  constructor
  · intro hall
    exact ⟨fun s hs => hall s (by omega), hall t (by omega)⟩
  · rintro ⟨hprev, hnow⟩ s hs
    by_cases hst : s = t
    · simpa [hst] using hnow
    · exact hprev s (by omega)

theorem target_mem_finiteVersionIndices
    {N : ℕ} (language : Fin N → Set α)
    (observed : ℕ → α) (target : Fin N)
    (hObserved : ∀ t, observed t ∈ language target) :
    ∀ t, target ∈ finiteVersionIndices language observed t := by
  intro t
  rw [mem_finiteVersionIndices_iff]
  intro s _hs
  exact hObserved s

/-- All weights maintained by the update rule are nonnegative. -/
theorem finiteAlgorithmWeight_nonnegative
    {N : ℕ} (language : Fin N → Set α)
    (observed generated : ℕ → α) :
    ∀ t i, 0 ≤ finiteAlgorithmWeight language observed generated t i := by
  intro t
  induction t with
  | zero =>
      intro i
      norm_num
  | succ t ih =>
      intro i
      rw [finiteAlgorithmWeight_succ]
      by_cases hObserved : observed t ∈ language i
      · by_cases hGenerated : generated t ∈ language i
        · simp [updateWeight, hObserved, hGenerated, ih i]
        · simp [updateWeight, hObserved, hGenerated, ih i]
      · simp [updateWeight, hObserved]

/-- Algorithm 1 assigns positive weight exactly to the languages still
consistent with the observed prefix. -/
theorem finiteAlgorithmWeight_pos_iff_mem_version
    {N : ℕ} (language : Fin N → Set α)
    (observed generated : ℕ → α) :
    ∀ t i,
      0 < finiteAlgorithmWeight language observed generated t i ↔
        i ∈ finiteVersionIndices language observed t := by
  intro t
  induction t with
  | zero =>
      intro i
      simp [finiteAlgorithmWeight]
  | succ t ih =>
      intro i
      rw [finiteAlgorithmWeight_succ,
        mem_finiteVersionIndices_succ_iff, ← ih i]
      by_cases hObserved : observed t ∈ language i
      · by_cases hGenerated : generated t ∈ language i
        · simp [updateWeight, hObserved, hGenerated]
        · simp [updateWeight, hObserved, hGenerated]
      · simp [updateWeight, hObserved]

theorem finiteAlgorithmWeight_eq_zero_of_not_mem_version
    {N : ℕ} (language : Fin N → Set α)
    (observed generated : ℕ → α)
    {t : ℕ} {i : Fin N}
    (hi : i ∉ finiteVersionIndices language observed t) :
    finiteAlgorithmWeight language observed generated t i = 0 := by
  have hnonneg :=
    finiteAlgorithmWeight_nonnegative
      language observed generated t i
  have hnotPos :
      ¬0 < finiteAlgorithmWeight language observed generated t i := by
    intro hpos
    exact hi
      ((finiteAlgorithmWeight_pos_iff_mem_version
        language observed generated t i).mp hpos)
  linarith

/-- A point in the intersection of all consistent languages receives the
entire surviving weight. -/
theorem weightedScore_eq_total_of_mem_finiteIntersection
    {N : ℕ} (language : Fin N → Set α)
    (observed generated : ℕ → α)
    {t : ℕ} {x : α}
    (hx :
      x ∈ finiteClassIntersection language
        (finiteVersionIndices language observed t)) :
    weightedScore Finset.univ
        (finiteAlgorithmWeight language observed generated t)
        language x =
      ∑ i ∈ (Finset.univ : Finset (Fin N)),
        finiteAlgorithmWeight language observed generated t i := by
  classical
  change
    (∑ i ∈ (Finset.univ : Finset (Fin N)),
        if x ∈ language i then
          finiteAlgorithmWeight language observed generated t i
        else 0) =
      ∑ i ∈ (Finset.univ : Finset (Fin N)),
        finiteAlgorithmWeight language observed generated t i
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hi :
      i ∈ finiteVersionIndices language observed t
  · have hxi : x ∈ language i := hx i hi
    simp [hxi]
  · have hzero :=
      finiteAlgorithmWeight_eq_zero_of_not_mem_version
        language observed generated hi
    simp [hzero]

/-- If a generated point omits one positive-weight consistent language,
its score plus that language's weight is still at most the total weight. -/
theorem weightedScore_add_missing_weight_le_total
    {N : ℕ} (language : Fin N → Set α)
    (observed generated : ℕ → α)
    {t : ℕ} {i : Fin N}
    (hmiss : generated t ∉ language i) :
    weightedScore Finset.univ
        (finiteAlgorithmWeight language observed generated t)
        language (generated t) +
        finiteAlgorithmWeight language observed generated t i ≤
      ∑ j ∈ (Finset.univ : Finset (Fin N)),
        finiteAlgorithmWeight language observed generated t j := by
  classical
  let weight : Fin N → ℝ :=
    finiteAlgorithmWeight language observed generated t
  have hsingle :
      weight i =
        ∑ j ∈ (Finset.univ : Finset (Fin N)),
          if j = i then weight i else 0 := by
    simp
  change
    (∑ j ∈ (Finset.univ : Finset (Fin N)),
        if generated t ∈ language j then weight j else 0) +
        weight i ≤
      ∑ j ∈ (Finset.univ : Finset (Fin N)), weight j
  rw [hsingle, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _hj
  by_cases hji : j = i
  · subst j
    simp [hmiss]
  · by_cases hmem : generated t ∈ language j
    · simp [hji, hmem]
    · simp only [hji, hmem, if_false, zero_add]
      exact finiteAlgorithmWeight_nonnegative
        language observed generated t j

/-- The critical-choice step in the proof of Theorem 5.1.  Whenever the
current consistent intersection contains an unseen point, Algorithm 1's
weighted argmax is itself an unseen point in that entire intersection. -/
theorem finiteAlgorithm_critical_choice
    {N : ℕ} (language : Fin N → Set α)
    (observed generated : ℕ → α)
    (hArgmax :
      IsFiniteWeightedArgmax language observed generated)
    {t : ℕ}
    (hfresh :
      (finiteClassIntersection language
          (finiteVersionIndices language observed t) \
        (↑(GenLimit.Generic.sample observed t) : Set α)).Nonempty) :
    generated t ∈
      finiteClassIntersection language
          (finiteVersionIndices language observed t) \
        (↑(GenLimit.Generic.sample observed t) : Set α) := by
  classical
  obtain ⟨x, hxCore, hxFresh⟩ := hfresh
  refine ⟨?_, (hArgmax t).1⟩
  intro i hi
  by_contra hmiss
  have hpositive :
      0 <
        finiteAlgorithmWeight
          language observed generated t i :=
    (finiteAlgorithmWeight_pos_iff_mem_version
      language observed generated t i).mpr hi
  have hScoreX :=
    weightedScore_eq_total_of_mem_finiteIntersection
      language observed generated hxCore
  have hMax := (hArgmax t).2 x hxFresh
  have hMissing :=
    weightedScore_add_missing_weight_le_total
      language observed generated hmiss
  rw [hScoreX] at hMax
  linarith

/-- Every observed prefix lies in the intersection of the languages that
remain consistent with it. -/
theorem sample_subset_finiteClassIntersection
    {N : ℕ} (language : Fin N → Set α)
    (observed : ℕ → α) (t : ℕ) :
    (↑(GenLimit.Generic.sample observed t) : Set α) ⊆
      finiteClassIntersection language
        (finiteVersionIndices language observed t) := by
  intro x hx i hi
  obtain ⟨s, hs, hsx⟩ :=
    GenLimit.Generic.mem_sample_iff.mp hx
  have his :=
    (mem_finiteVersionIndices_iff
      language observed t i).mp hi s hs
  simpa [hsx] using his

/-- Once more than `d` distinct examples have been observed, the current
consistent intersection must be infinite under Definition 4's bound. -/
theorem finiteClassIntersection_infinite_after_dimension
    {N : ℕ} (language : Fin N → Set α)
    (observed : ℕ → α)
    (hinjective : Function.Injective observed)
    {d t : ℕ}
    (hdim : FiniteClassClosureDimensionAtMost language d)
    (hdt : d < t) :
    (finiteClassIntersection language
      (finiteVersionIndices language observed t)).Infinite := by
  by_contra hnot
  have hfinite :
      (finiteClassIntersection language
        (finiteVersionIndices language observed t)).Finite :=
    Set.not_infinite.mp hnot
  have hsubset :=
    sample_subset_finiteClassIntersection language observed t
  have hsampleLe :
      (GenLimit.Generic.sample observed t).card ≤
        (finiteClassIntersection language
          (finiteVersionIndices language observed t)).ncard := by
    simpa using Set.ncard_le_ncard hsubset hfinite
  have hcoreLe :
      (finiteClassIntersection language
        (finiteVersionIndices language observed t)).ncard ≤ d :=
    hdim (finiteVersionIndices language observed t) hfinite
  rw [GenLimit.Generic.sample_card_of_injective observed hinjective t]
    at hsampleLe
  omega

/-- The consistent intersection has an unseen point after the corrected
closure threshold. -/
theorem finiteClassIntersection_has_fresh_after_dimension
    {N : ℕ} (language : Fin N → Set α)
    (observed : ℕ → α)
    (hinjective : Function.Injective observed)
    {d t : ℕ}
    (hdim : FiniteClassClosureDimensionAtMost language d)
    (hdt : d < t) :
    (finiteClassIntersection language
        (finiteVersionIndices language observed t) \
      (↑(GenLimit.Generic.sample observed t) : Set α)).Nonempty := by
  exact
    ((finiteClassIntersection_infinite_after_dimension
      language observed hinjective hdim hdt).diff
        (GenLimit.Generic.sample observed t).finite_toSet).nonempty

/-- The closure-dimension component of Theorem 5.1 in zero-based Lean time:
after strictly more than `d` distinct prior examples, every output is valid.
-/
theorem finiteAlgorithm_correct_after_closure_dimension
    {N : ℕ} (language : Fin N → Set α)
    (observed generated : ℕ → α) (target : Fin N)
    (hObserved : ∀ t, observed t ∈ language target)
    (hInjective : Function.Injective observed)
    (hArgmax : IsFiniteWeightedArgmax language observed generated)
    {d : ℕ}
    (hdim : FiniteClassClosureDimensionAtMost language d) :
    ∀ t, d < t → generated t ∈ language target := by
  intro t hdt
  have hfresh :=
    finiteClassIntersection_has_fresh_after_dimension
      language observed hInjective hdim hdt
  have hchoice :=
    finiteAlgorithm_critical_choice
      language observed generated hArgmax hfresh
  exact hchoice.1 target
    (target_mem_finiteVersionIndices
      language observed target hObserved t)

/-- Corrected last-mistake form of Theorem 5.1 for the paper's reversed
move order.  With zero-based rounds, mistakes can occur through round `d`;
none occur at or after `d+1`. -/
theorem finiteAlgorithm_lastMistakeBefore_succ_dimension
    {N : ℕ} (language : Fin N → Set α)
    (observed generated : ℕ → α) (target : Fin N)
    (hObserved : ∀ t, observed t ∈ language target)
    (hInjective : Function.Injective observed)
    (hArgmax : IsFiniteWeightedArgmax language observed generated)
    {d : ℕ}
    (hdim : FiniteClassClosureDimensionAtMost language d) :
    LastMistakeBefore
      (finiteTargetTrace language generated target) (d + 1) := by
  intro t hdt
  have hvalid :=
    finiteAlgorithm_correct_after_closure_dimension
      language observed generated target hObserved hInjective
        hArgmax hdim t (by omega)
  simp [finiteTargetTrace, hvalid]

/-- The full argmax rule implies the one comparison needed by the weighted
potential recurrence, provided the adversarial stream is injective. -/
theorem finiteArgmax_implies_beatsObserved
    {N : ℕ} (language : Fin N → Set α)
    (observed generated : ℕ → α)
    (hInjective : Function.Injective observed)
    (hArgmax : IsFiniteWeightedArgmax language observed generated) :
    ∀ t,
      BeatsObserved Finset.univ
        (finiteAlgorithmWeight language observed generated t)
        language (generated t) (observed t) := by
  intro t
  apply (hArgmax t).2
  intro hmem
  obtain ⟨s, hs, hst⟩ :=
    GenLimit.Generic.mem_sample_iff.mp hmem
  have : s = t := hInjective hst
  omega

/-- If every generated point satisfies the weighted-argmax comparison, total
weight is nonincreasing. -/
theorem finiteAlgorithm_totalWeight_mono
    {N : ℕ} (language : Fin N → Set α)
    (observed generated : ℕ → α)
    (hmax : ∀ t,
      BeatsObserved Finset.univ
        (finiteAlgorithmWeight language observed generated t)
        language (generated t) (observed t)) :
    ∀ t,
      (∑ i : Fin N,
        finiteAlgorithmWeight language observed generated (t + 1) i) ≤
      ∑ i : Fin N,
        finiteAlgorithmWeight language observed generated t i := by
  intro t
  simpa only [finiteAlgorithmWeight_succ] using
    updated_active_weight_le Finset.univ
      (finiteAlgorithmWeight language observed generated t)
      language (observed t) (generated t)
      (by
        intro i hi
        exact finiteAlgorithmWeight_nonnegative
          language observed generated t i)
      (hmax t)

/-- The total active mass stays below its initial value `N`. -/
theorem finiteAlgorithm_totalWeight_le_card
    {N : ℕ} (language : Fin N → Set α)
    (observed generated : ℕ → α)
    (hmax : ∀ t,
      BeatsObserved Finset.univ
        (finiteAlgorithmWeight language observed generated t)
        language (generated t) (observed t)) :
    ∀ t,
      (∑ i : Fin N,
        finiteAlgorithmWeight language observed generated t i) ≤ N := by
  intro t
  induction t with
  | zero =>
      simp [finiteAlgorithmWeight]
  | succ t ih =>
      exact (finiteAlgorithm_totalWeight_mono
        language observed generated hmax t).trans ih

/-- On a realizable stream, the target is never eliminated; its weight
doubles exactly on the rounds when the generated point misses it. -/
theorem finiteAlgorithm_targetWeight_eq_pow_mistakes
    {N : ℕ} (language : Fin N → Set α)
    (observed generated : ℕ → α) (target : Fin N)
    (hObserved : ∀ t, observed t ∈ language target) :
    ∀ t,
      finiteAlgorithmWeight language observed generated t target =
        (2 : ℝ) ^ mistakeCount
          (finiteTargetTrace language generated target) t := by
  intro t
  induction t with
  | zero =>
      simp [finiteAlgorithmWeight]
  | succ t ih =>
      rw [finiteAlgorithmWeight_succ, mistakeCount_succ]
      by_cases hGenerated : generated t ∈ language target
      · have hTrace :
          finiteTargetTrace language generated target t = false := by
          simp [finiteTargetTrace, hGenerated]
        simp [updateWeight, hObserved t, hGenerated, hTrace, ih]
      · have hTrace :
          finiteTargetTrace language generated target t = true := by
          simp [finiteTargetTrace, hGenerated]
        simp [updateWeight, hObserved t, hGenerated, hTrace, ih, pow_succ]
        ring

/-- The finite-class mistake inequality in Theorem 5.1:
`2^(mistakes before t) ≤ |𝓛|` for every finite prefix. -/
theorem finiteAlgorithm_two_pow_mistakes_le_card
    {N : ℕ} (language : Fin N → Set α)
    (observed generated : ℕ → α) (target : Fin N)
    (hObserved : ∀ t, observed t ∈ language target)
    (hmax : ∀ t,
      BeatsObserved Finset.univ
        (finiteAlgorithmWeight language observed generated t)
        language (generated t) (observed t)) :
    ∀ t,
      (2 : ℝ) ^ mistakeCount
          (finiteTargetTrace language generated target) t ≤ N := by
  intro t
  rw [← finiteAlgorithm_targetWeight_eq_pow_mistakes
    language observed generated target hObserved t]
  have hTargetLe :
      finiteAlgorithmWeight language observed generated t target ≤
        ∑ i : Fin N,
          finiteAlgorithmWeight language observed generated t i := by
    apply Finset.single_le_sum
    · intro i hi
      exact finiteAlgorithmWeight_nonnegative
        language observed generated t i
    · exact Finset.mem_univ target
  exact hTargetLe.trans
    (finiteAlgorithm_totalWeight_le_card
      language observed generated hmax t)

/-- Natural-logarithm form of the finite-cardinality component of Theorem
5.1.  `Nat.log 2 N` is exactly `⌊log₂ N⌋` for positive `N`. -/
theorem finiteAlgorithm_totalMistakesAtMost_log_card
    {N : ℕ} (language : Fin N → Set α)
    (observed generated : ℕ → α) (target : Fin N)
    (hObserved : ∀ t, observed t ∈ language target)
    (hmax : ∀ t,
      BeatsObserved Finset.univ
        (finiteAlgorithmWeight language observed generated t)
        language (generated t) (observed t)) :
    TotalMistakesAtMost
      (finiteTargetTrace language generated target) (Nat.log 2 N) := by
  intro t
  have hreal :=
    finiteAlgorithm_two_pow_mistakes_le_card
      language observed generated target hObserved hmax t
  have hnat :
      2 ^ mistakeCount
          (finiteTargetTrace language generated target) t ≤ N := by
    exact_mod_cast hreal
  exact Nat.le_log_of_pow_le (by omega) hnat

/-- The closure component gives the corrected `d+1` total-mistake bound. -/
theorem finiteAlgorithm_totalMistakesAtMost_succ_dimension
    {N : ℕ} (language : Fin N → Set α)
    (observed generated : ℕ → α) (target : Fin N)
    (hObserved : ∀ t, observed t ∈ language target)
    (hInjective : Function.Injective observed)
    (hArgmax : IsFiniteWeightedArgmax language observed generated)
    {d : ℕ}
    (hdim : FiniteClassClosureDimensionAtMost language d) :
    TotalMistakesAtMost
      (finiteTargetTrace language generated target) (d + 1) :=
  lastMistakeBefore_implies_totalMistakesAtMost
    (finiteAlgorithm_lastMistakeBefore_succ_dimension
      language observed generated target hObserved hInjective
        hArgmax hdim)

/-- Corrected dual component of Theorem 5.1: the concrete Algorithm 1
specification simultaneously satisfies the checked logarithmic inequality
and the `d+1` last-mistake threshold forced by the paper's reversed order.
-/
theorem theorem_5_1_corrected_components
    {N : ℕ} (language : Fin N → Set α)
    (observed generated : ℕ → α) (target : Fin N)
    (hObserved : ∀ t, observed t ∈ language target)
    (hInjective : Function.Injective observed)
    (hArgmax : IsFiniteWeightedArgmax language observed generated)
    {d : ℕ}
    (hdim : FiniteClassClosureDimensionAtMost language d) :
    TotalMistakesAtMost
        (finiteTargetTrace language generated target)
        (min (Nat.log 2 N) (d + 1)) ∧
      LastMistakeBefore
        (finiteTargetTrace language generated target) (d + 1) := by
  refine ⟨?_, ?_⟩
  · intro t
    apply Nat.le_min.mpr
    constructor
    · exact finiteAlgorithm_totalMistakesAtMost_log_card
        language observed generated target hObserved
          (finiteArgmax_implies_beatsObserved
            language observed generated hInjective hArgmax) t
    · exact finiteAlgorithm_totalMistakesAtMost_succ_dimension
        language observed generated target hObserved hInjective
          hArgmax hdim t
  · exact finiteAlgorithm_lastMistakeBefore_succ_dimension
      language observed generated target hObserved hInjective
        hArgmax hdim

/-! ## Reversed-order indexing diagnostic -/

/-- A two-language class used to expose the one-round shift in the printed
closure-dimension guarantee. -/
def disjointPairLanguage (L₀ L₁ : Set α) : Fin 2 → Set α :=
  fun i => if i = 0 then L₀ else L₁

@[simp] theorem disjointPairLanguage_zero (L₀ L₁ : Set α) :
    disjointPairLanguage L₀ L₁ 0 = L₀ := by
  simp [disjointPairLanguage]

@[simp] theorem disjointPairLanguage_one (L₀ L₁ : Set α) :
    disjointPairLanguage L₀ L₁ 1 = L₁ := by
  simp [disjointPairLanguage]

/-- Two disjoint infinite languages have closure dimension at most zero
under the paper's Definition 4: every finite subcollection intersection is
empty. -/
theorem disjointPair_closureDimensionAtMost_zero
    {L₀ L₁ : Set α}
    (hL₀ : L₀.Infinite) (hL₁ : L₁.Infinite)
    (hdisjoint : Disjoint L₀ L₁) :
    FiniteClassClosureDimensionAtMost
      (disjointPairLanguage L₀ L₁) 0 := by
  classical
  intro active hfinite
  have hzero : (0 : Fin 2) ∈ active := by
    by_contra hnot
    have hsubset :
        L₁ ⊆ finiteClassIntersection
          (disjointPairLanguage L₀ L₁) active := by
      intro x hx i hi
      fin_cases i
      · exact (hnot hi).elim
      · simpa using hx
    exact (hL₁.mono hsubset) hfinite
  have hone : (1 : Fin 2) ∈ active := by
    by_contra hnot
    have hsubset :
        L₀ ⊆ finiteClassIntersection
          (disjointPairLanguage L₀ L₁) active := by
      intro x hx i hi
      fin_cases i
      · simpa using hx
      · exact (hnot hi).elim
    exact (hL₀.mono hsubset) hfinite
  have hempty :
      finiteClassIntersection
          (disjointPairLanguage L₀ L₁) active = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact Set.disjoint_left.mp hdisjoint
      (hx 0 hzero) (hx 1 hone)
  rw [hempty]
  simp

/-- At the first generator-first round, one fixed output must be a mistake
for at least one of two disjoint targets.  Together with
`disjointPair_closureDimensionAtMost_zero`, this kernel-checks the off-by-one
obstruction to the printed `last mistake ≤ Cdim` claim under the paper's
reversed order. -/
theorem disjointPair_first_round_obstruction
    {L₀ L₁ : Set α} (hdisjoint : Disjoint L₀ L₁) (x : α) :
    x ∉ disjointPairLanguage L₀ L₁ 0 ∨
      x ∉ disjointPairLanguage L₀ L₁ 1 := by
  simp only [disjointPairLanguage_zero, disjointPairLanguage_one]
  by_cases hx : x ∈ L₀
  · exact Or.inr (fun hx₁ =>
      Set.disjoint_left.mp hdisjoint hx hx₁)
  · exact Or.inl hx

/-- A single kernel-checked diagnostic for the printed closure-dimension
bound: the class has dimension at most zero, yet every generator-first
initial output is wrong for at least one target. -/
theorem theorem_5_1_reversed_order_diagnostic
    {L₀ L₁ : Set α}
    (hL₀ : L₀.Infinite) (hL₁ : L₁.Infinite)
    (hdisjoint : Disjoint L₀ L₁) (x : α) :
    FiniteClassClosureDimensionAtMost
        (disjointPairLanguage L₀ L₁) 0 ∧
      (x ∉ disjointPairLanguage L₀ L₁ 0 ∨
        x ∉ disjointPairLanguage L₀ L₁ 1) := by
  exact ⟨disjointPair_closureDimensionAtMost_zero
      hL₀ hL₁ hdisjoint,
    disjointPair_first_round_obstruction hdisjoint x⟩

end GenLimit.MistakeBounded
