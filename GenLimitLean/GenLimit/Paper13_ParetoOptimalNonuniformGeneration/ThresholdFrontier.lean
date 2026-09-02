import GenLimit.Paper13_ParetoOptimalNonuniformGeneration.CoSingletonFrontier
import GenLimit.Support.Fresh
import Mathlib.Data.Int.Interval
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.NormNum

/-!
# The uniformly generatable family with no Pareto frontier

This module formalizes Proposition 3.4 and Appendix A of
Charikar--Pabbaraju, *Pareto-optimal Non-uniform Language Generation*,
arXiv:2510.02795v1, pp. 11 and 17--18, in the repository's
distinct-history semantic model.

For an enumeration `threshold : ℕ → ℤ`, the languages are

`{1, ..., 100} ∪ ℤ≥threshold(i)`.

The source's admissibility condition collapses to one upper-bound condition
at level 100.  We prove that this condition exactly characterizes
realizable positive time vectors, construct a uniform generator with time
101, and prove that no realizable vector is Pareto optimal whenever the
enumerated thresholds are unbounded above.

There is a localized error in the printed necessity proof.  At a level
`t < 100`, novelty from the prefix `{1, ..., t}` does not imply that the
output is outside the fixed 100-point core.  Thus `threshold(i) > z` alone
does not imply `z ∉ L_i`.  The statement remains correct: the repaired
proof presents the whole 100-point core, at which point novelty does put the
output outside the core.  Both the elementary counterexample to the printed
step and the corrected diagonal are checked below.
-/

namespace GenLimit.ParetoGeneration

/-- The fixed core `{1, ..., 100}` from Proposition 3.4. -/
def hundredCore : Finset Int :=
  Finset.Icc 1 100

theorem hundredCore_card :
    hundredCore.card = 100 := by
  rw [hundredCore, Int.card_Icc]
  exact Int.toNat_natCast 100

/-- The family `L_e = {1, ..., 100} ∪ ℤ≥e`. -/
def thresholdLanguage (e : Int) : Set Int :=
  (↑hundredCore : Set Int) ∪ Set.Ici e

/-- An arbitrary no-repetition enumeration of the source family is
represented by its threshold at each natural-number index. -/
def thresholdFamily (threshold : Nat -> Int) (i : Nat) : Set Int :=
  thresholdLanguage (threshold i)

theorem hundredCore_subset_thresholdLanguage (e : Int) :
    (↑hundredCore : Set Int) ⊆ thresholdLanguage e :=
  Set.subset_union_left

theorem Ici_subset_thresholdLanguage (e : Int) :
    Set.Ici e ⊆ thresholdLanguage e :=
  Set.subset_union_right

/-- A concrete counterexample to the implication used at lines 1143--1147
of the pinned source: `2` is fresh after the one-point input `{1}` and is
less than threshold `3`, but it remains in the fixed hundred-point core. -/
theorem printed_proposition_3_4_diagonal_step_false :
    (2 : Int) ∉ ({1} : Set Int) ∧
      (2 : Int) < 3 ∧
      (2 : Int) ∈ thresholdLanguage 3 := by
  norm_num [thresholdLanguage, hundredCore]

/-- The repaired diagonal step: once the input contains the entire fixed
core, freshness plus `z < e` really does imply `z ∉ L_e`. -/
theorem corrected_proposition_3_4_diagonal_step
    {sample : Set Int} {z e : Int}
    (hcore : (↑hundredCore : Set Int) ⊆ sample)
    (hfresh : z ∉ sample) (hbelow : z < e) :
    z ∉ thresholdLanguage e := by
  intro hz
  rcases hz with hzCore | hzTail
  · exact hfresh (hcore hzCore)
  · exact (Int.not_le_of_gt hbelow) hzTail

/-- The source's levels `1, ..., 100` are equivalent to this single
level-100 condition because the active collections are nested. -/
def SourceThresholdAdmissible
    (threshold : Nat -> Int) (time : TimeVector) : Prop :=
  ∀ t, 1 ≤ t -> t ≤ 100 ->
    ∃ bound : Int, ∀ i, time i ≤ t -> threshold i ≤ bound

def ThresholdAdmissible
    (threshold : Nat -> Int) (time : TimeVector) : Prop :=
  ∃ bound : Int, ∀ i, time i ≤ 100 -> threshold i ≤ bound

theorem sourceThresholdAdmissible_iff
    (threshold : Nat -> Int) (time : TimeVector) :
    SourceThresholdAdmissible threshold time ↔
      ThresholdAdmissible threshold time := by
  constructor
  · intro h
    exact h 100 (by omega) (by omega)
  · rintro ⟨bound, hbound⟩ t _ ht
    exact ⟨bound, fun i hi => hbound i (hi.trans ht)⟩

def PositiveThresholdAdmissibleVectors
    (threshold : Nat -> Int) : Set TimeVector :=
  {time | (∀ i, 1 ≤ time i) ∧
    ThresholdAdmissible threshold time}

/-- The fresh point chosen above a prescribed integer bound. -/
noncomputable def freshAbove
    (bound : Int) {t : Nat} (xs : Fin t -> Int) : Int :=
  GenLimit.Support.freshFromInfinite
    (Set.Ici bound) (Set.Ici_infinite bound)
    (GenLimit.Generic.sequenceSample xs)

theorem freshAbove_spec
    (bound : Int) {t : Nat} (xs : Fin t -> Int) :
    bound ≤ freshAbove bound xs ∧
      ∀ k, freshAbove bound xs ≠ xs k := by
  have hmem :=
    GenLimit.Support.freshFromInfinite_mem
      (Set.Ici bound) (Set.Ici_infinite bound)
      (GenLimit.Generic.sequenceSample xs)
  have hfresh :=
    GenLimit.Support.freshFromInfinite_not_mem
      (Set.Ici bound) (Set.Ici_infinite bound)
      (GenLimit.Generic.sequenceSample xs)
  constructor
  · exact hmem
  · intro k hk
    exact hfresh
      (GenLimit.Generic.mem_sequenceSample_iff.mpr
        ⟨k, hk.symm⟩)

/-- More than 100 distinct inputs cannot all lie in the hundred-point
core. -/
theorem exists_history_outside_hundredCore
    {t : Nat} (xs : Fin t -> Int)
    (hinjective : Function.Injective xs) (ht : 100 < t) :
    ∃ x, x ∈ Set.range xs ∧ x ∉ hundredCore := by
  by_contra hnone
  push_neg at hnone
  let intoCore : Fin t -> (hundredCore : Set Int) :=
    fun k => ⟨xs k, hnone (xs k) (Set.mem_range_self k)⟩
  have hIntoInjective : Function.Injective intoCore := by
    intro i j hij
    apply hinjective
    exact congrArg Subtype.val hij
  have hcard :
      Fintype.card (Fin t) ≤
        Fintype.card (hundredCore : Set Int) :=
    Fintype.card_le_of_injective intoCore hIntoInjective
  have hcoreFintype :
      Fintype.card (hundredCore : Set Int) =
        hundredCore.card :=
    Fintype.card_coe hundredCore
  rw [Fintype.card_fin, hcoreFintype, hundredCore_card] at hcard
  omega

/-- The generator used for the sufficiency direction.

For histories of size at most 100 it uses the admissibility bound.  For
larger histories, if a sample point outside the fixed core exists, it uses
that point as a lower bound.  The final fallback only makes the definition
total on non-injective histories and is never used in correctness proofs. -/
noncomputable def thresholdAdmissibleGenerator
    (threshold : Nat -> Int) (time : TimeVector)
    (hadmissible : ThresholdAdmissible threshold time) :
    HistoryGenerator Int := by
  classical
  exact fun t xs =>
    if ht : t ≤ 100 then
      freshAbove (Classical.choose hadmissible) xs
    else if hpivot :
        ∃ x, x ∈ Set.range xs ∧ x ∉ hundredCore then
      freshAbove (Classical.choose hpivot) xs
    else
      freshAbove 0 xs

theorem thresholdAdmissibleGenerator_correct_small
    (threshold : Nat -> Int) {time : TimeVector}
    (hadmissible : ThresholdAdmissible threshold time)
    {i t : Nat} (xs : Fin t -> Int)
    (ht : t ≤ 100) (htime : time i ≤ t) :
    thresholdAdmissibleGenerator threshold time hadmissible t xs ∈
        thresholdFamily threshold i ∧
      ∀ k,
        thresholdAdmissibleGenerator threshold time hadmissible t xs ≠
          xs k := by
  classical
  have hbound :
      threshold i ≤ Classical.choose hadmissible :=
    (Classical.choose_spec hadmissible) i (htime.trans ht)
  have hfresh :=
    freshAbove_spec (Classical.choose hadmissible) xs
  rw [thresholdAdmissibleGenerator, dif_pos ht]
  constructor
  · exact Ici_subset_thresholdLanguage (threshold i)
      (hbound.trans hfresh.1)
  · exact hfresh.2

theorem thresholdAdmissibleGenerator_correct_large
    (threshold : Nat -> Int) {time : TimeVector}
    (hadmissible : ThresholdAdmissible threshold time)
    {i t : Nat} (xs : Fin t -> Int)
    (ht : 100 < t) (hinjective : Function.Injective xs)
    (htarget : ∀ k, xs k ∈ thresholdFamily threshold i) :
    thresholdAdmissibleGenerator threshold time hadmissible t xs ∈
        thresholdFamily threshold i ∧
      ∀ k,
        thresholdAdmissibleGenerator threshold time hadmissible t xs ≠
          xs k := by
  classical
  have hpivot :
      ∃ x, x ∈ Set.range xs ∧ x ∉ hundredCore :=
    exists_history_outside_hundredCore xs hinjective ht
  let pivot : Int := Classical.choose hpivot
  have hpivotSpec := Classical.choose_spec hpivot
  obtain ⟨q, hq⟩ := hpivotSpec.1
  have hpivotTarget :
      pivot ∈ thresholdFamily threshold i := by
    simpa [pivot, ← hq] using htarget q
  have hthresholdPivot :
      threshold i ≤ pivot := by
    rcases hpivotTarget with hcore | htail
    · exact (hpivotSpec.2 hcore).elim
    · exact htail
  have hfresh := freshAbove_spec pivot xs
  rw [thresholdAdmissibleGenerator, dif_neg (Nat.not_le_of_gt ht),
    dif_pos hpivot]
  constructor
  · exact Ici_subset_thresholdLanguage (threshold i)
      (hthresholdPivot.trans hfresh.1)
  · exact hfresh.2

theorem thresholdAdmissibleGenerator_achieves
    (threshold : Nat -> Int) {time : TimeVector}
    (hadmissible : ThresholdAdmissible threshold time) :
    AchievesTimeVector
      (thresholdAdmissibleGenerator threshold time hadmissible)
      (thresholdFamily threshold) time := by
  intro i t xs htime hinjective htarget
  by_cases ht : t ≤ 100
  · exact thresholdAdmissibleGenerator_correct_small
      threshold hadmissible xs ht htime
  · exact thresholdAdmissibleGenerator_correct_large
      threshold hadmissible xs (Nat.lt_of_not_ge ht)
      hinjective htarget

theorem positiveThresholdAdmissible_realizable
    (threshold : Nat -> Int) {time : TimeVector}
    (htime : time ∈
      PositiveThresholdAdmissibleVectors threshold) :
    time ∈ RealizableTimeVectors (thresholdFamily threshold) :=
  ⟨thresholdAdmissibleGenerator threshold time htime.2,
    thresholdAdmissibleGenerator_achieves threshold htime.2,
    htime.1⟩

/-- A history listing all one hundred core points. -/
noncomputable def hundredCoreHistory : Fin 100 -> Int :=
  finiteSetHistory (↑hundredCore : Set Int)
    hundredCore.finite_toSet 100
    (by simpa using hundredCore_card)

theorem hundredCoreHistory_injective :
    Function.Injective hundredCoreHistory :=
  finiteSetHistory_injective (↑hundredCore : Set Int)
    hundredCore.finite_toSet 100
    (by simpa using hundredCore_card)

theorem hundredCoreHistory_range :
    Set.range hundredCoreHistory =
      (↑hundredCore : Set Int) :=
  finiteSetHistory_range (↑hundredCore : Set Int)
    hundredCore.finite_toSet 100
    (by simpa using hundredCore_card)

/-- Necessity of the repaired admissibility condition. -/
theorem threshold_realizable_admissible
    (threshold : Nat -> Int) {time : TimeVector}
    (htime : time ∈
      RealizableTimeVectors (thresholdFamily threshold)) :
    ThresholdAdmissible threshold time := by
  obtain ⟨G, hAchieves, -⟩ := htime
  by_contra hnot
  simp only [ThresholdAdmissible, not_exists, not_forall,
    not_le] at hnot
  let z := G 100 hundredCoreHistory
  obtain ⟨i, hiTime, hiThreshold⟩ := hnot z
  have htargetHistory :
      ∀ q, hundredCoreHistory q ∈ thresholdFamily threshold i := by
    intro q
    apply hundredCore_subset_thresholdLanguage (threshold i)
    rw [← hundredCoreHistory_range]
    exact Set.mem_range_self q
  have hout :=
    hAchieves i 100 hundredCoreHistory hiTime
      hundredCoreHistory_injective htargetHistory
  have hzFresh :
      z ∉ (↑hundredCore : Set Int) := by
    intro hz
    rw [← hundredCoreHistory_range] at hz
    obtain ⟨q, hq⟩ := hz
    exact hout.2 q hq.symm
  exact (corrected_proposition_3_4_diagonal_step
    Set.Subset.rfl hzFresh hiThreshold) hout.1

/-- Exact realizable-frontier characterization from Appendix A. -/
theorem threshold_realizable_iff_positiveAdmissible
    (threshold : Nat -> Int) (time : TimeVector) :
    time ∈ RealizableTimeVectors (thresholdFamily threshold) ↔
      time ∈ PositiveThresholdAdmissibleVectors threshold := by
  constructor
  · intro htime
    exact ⟨htime.choose_spec.2,
      threshold_realizable_admissible threshold htime⟩
  · exact positiveThresholdAdmissible_realizable threshold

theorem threshold_realizableTimeVectors_eq
    (threshold : Nat -> Int) :
    RealizableTimeVectors (thresholdFamily threshold) =
      PositiveThresholdAdmissibleVectors threshold := by
  ext time
  exact threshold_realizable_iff_positiveAdmissible threshold time

/-- Lowering one coordinate preserves threshold admissibility, after
enlarging the finite upper bound by that coordinate's threshold. -/
theorem ThresholdAdmissible.lowerCoordinate
    {threshold : Nat -> Int} {time : TimeVector}
    (h : ThresholdAdmissible threshold time) (i : Nat) :
    ThresholdAdmissible threshold (lowerCoordinate time i) := by
  obtain ⟨bound, hbound⟩ := h
  refine ⟨max bound (threshold i), ?_⟩
  intro j hj
  by_cases hji : j = i
  · subst j
    exact le_max_right _ _
  · exact (hbound j (by simpa [lowerCoordinate, hji] using hj)).trans
      (le_max_left _ _)

/-- Unbounded thresholds force every admissible time vector to have some
coordinate strictly larger than one. -/
theorem ThresholdAdmissible.exists_gt_one
    {threshold : Nat -> Int} {time : TimeVector}
    (h : ThresholdAdmissible threshold time)
    (hunbounded : ∀ bound : Int, ∃ i, bound < threshold i) :
    ∃ i, 1 < time i := by
  obtain ⟨bound, hbound⟩ := h
  obtain ⟨i, hi⟩ := hunbounded bound
  refine ⟨i, ?_⟩
  by_contra hnot
  have htime : time i ≤ 100 := by omega
  exact (Int.not_lt_of_ge (hbound i htime)) hi

/-- No positive threshold-admissible vector is Pareto minimal. -/
theorem no_paretoOptimal_positiveThresholdAdmissible
    (threshold : Nat -> Int)
    (hunbounded : ∀ bound : Int, ∃ i, bound < threshold i)
    (time : TimeVector)
    (htime : time ∈
      PositiveThresholdAdmissibleVectors threshold) :
    ¬ParetoOptimal
      (PositiveThresholdAdmissibleVectors threshold) time := by
  intro hPareto
  obtain ⟨i, hi⟩ := htime.2.exists_gt_one hunbounded
  have hLower :
      lowerCoordinate time i ∈
        PositiveThresholdAdmissibleVectors threshold :=
    ⟨positive_lowerCoordinate htime.1 i,
      htime.2.lowerCoordinate i⟩
  have hDominates :=
    lowerCoordinate_strictlyDominates htime.1 hi
  exact hDominates.2
    (hPareto (lowerCoordinate time i) hLower hDominates.1)

/-- Proposition 3.4's Pareto-impossibility statement, for any enumeration
whose thresholds are unbounded above (in particular, for any enumeration of
all integer thresholds). -/
theorem proposition_3_4_no_pareto_frontier
    (threshold : Nat -> Int)
    (hunbounded : ∀ bound : Int, ∃ i, bound < threshold i) :
    ¬∃ time,
      time ∈ RealizableTimeVectors (thresholdFamily threshold) ∧
      ParetoOptimal
        (RealizableTimeVectors (thresholdFamily threshold)) time := by
  rintro ⟨time, htime, hPareto⟩
  have hAdmissible :
      time ∈ PositiveThresholdAdmissibleVectors threshold :=
    (threshold_realizable_iff_positiveAdmissible
      threshold time).mp htime
  apply no_paretoOptimal_positiveThresholdAdmissible
    threshold hunbounded time hAdmissible
  simpa only [threshold_realizableTimeVectors_eq threshold] using
    hPareto

/-- The family is uniformly generatable: the constant time 101 is
admissible regardless of the threshold enumeration. -/
theorem threshold_constant_101_admissible
    (threshold : Nat -> Int) :
    ThresholdAdmissible threshold (fun _ => 101) := by
  refine ⟨0, ?_⟩
  intro i hi
  norm_num at hi

theorem proposition_3_4_uniform_generation
    (threshold : Nat -> Int) :
    ∃ G : HistoryGenerator Int,
      AchievesTimeVector G (thresholdFamily threshold)
        (fun _ => 101) := by
  refine ⟨thresholdAdmissibleGenerator threshold
    (fun _ => 101)
    (threshold_constant_101_admissible threshold), ?_⟩
  exact thresholdAdmissibleGenerator_achieves threshold
    (threshold_constant_101_admissible threshold)

end GenLimit.ParetoGeneration
