import GenLimit.Paper13_ParetoOptimalNonuniformGeneration.GlobalInvariant
import GenLimit.Support.Fresh
import Mathlib.Data.Nat.Find

/-!
# The arbitrary scheduler in Theorem 4

This module formalizes Theorem 4 of Charikar--Pabbaraju,
*Pareto-optimal Non-uniform Language Generation*,
arXiv:2510.02795v1, p. 9.

The paper fixes an arbitrary nondecreasing unbounded scheduler `f`.  At a
history of size `t`, the algorithm constructs the Procedure-1 ordering of
the first `f t` languages and greedily retains every sample-consistent
language whose addition preserves an infinite common core.  The inverse
time `g(i)` is the first `t` for which the zero-based language index `i`
belongs to that finite scope.

The existing `GlobalInvariant` module proves the hard max-score invariant
for every finite Procedure-1 stage and the target-selection argument for an
arbitrary scan order.  The new work here proves that canonical
complexities are stable after insertion, constructs the scheduler-driven
generator, and derives the exact displayed bound

`max (g i) (mStar i + 1)`.

As elsewhere in this development, `AchievesTimeVector` is the semantic
distinct-history version of non-uniform generation.  No effective
membership-oracle or runtime claim is made.
-/

namespace GenLimit.ParetoGeneration

/-- The source assumptions on the scheduler in zero-based form.

`i < f t` means that language index `i` is among the first `f t`
languages. -/
def IsUnboundedScheduler (f : Nat -> Nat) : Prop :=
  Monotone f ∧ ∀ i, ∃ t, i < f t

/-- The paper's generalized inverse `g(i)`: the first history size at which
language `i` is included in the scheduler scope. -/
noncomputable def schedulerEntryTime
    (f : Nat -> Nat) (hf : IsUnboundedScheduler f) (i : Nat) : Nat :=
  Nat.find (hf.2 i)

theorem schedulerEntryTime_spec
    (f : Nat -> Nat) (hf : IsUnboundedScheduler f) (i : Nat) :
    i < f (schedulerEntryTime f hf i) :=
  Nat.find_spec (hf.2 i)

/-- Minimality of the generalized inverse. -/
theorem schedulerEntryTime_min
    (f : Nat -> Nat) (hf : IsUnboundedScheduler f)
    {i t : Nat} (ht : t < schedulerEntryTime f hf i) :
    f t ≤ i := by
  exact Nat.le_of_not_gt (Nat.find_min (hf.2 i) ht)

theorem schedulerEntryTime_le_of_in_scope
    (f : Nat -> Nat) (hf : IsUnboundedScheduler f)
    {i t : Nat} (hit : i < f t) :
    schedulerEntryTime f hf i ≤ t :=
  Nat.find_min' (hf.2 i) hit

/-- For a monotone scheduler, being past the inverse time is exactly being
in the current finite scope. -/
theorem schedulerEntryTime_le_iff
    (f : Nat -> Nat) (hf : IsUnboundedScheduler f)
    {i t : Nat} :
    schedulerEntryTime f hf i ≤ t ↔ i < f t := by
  constructor
  · intro htime
    exact (schedulerEntryTime_spec f hf i).trans_le
      (hf.1 htime)
  · exact schedulerEntryTime_le_of_in_scope f hf

/-- One further Procedure-1 insertion leaves every old complexity
coordinate unchanged. -/
theorem extendProcedureStage_complexity_old
    (F : Nat -> Set α) {stage i : Nat}
    (current : ProcedureStage F stage) (hi : i < stage) :
    (extendProcedureStage F current).complexity i =
      current.complexity i := by
  classical
  simp [extendProcedureStage, setComplexity, Nat.ne_of_lt hi]

/-- The permanent Procedure-1 complexity assigned when language `i` is
first inserted. -/
noncomputable def canonicalComplexity
    (F : Nat -> Set α) (i : Nat) : Nat :=
  (canonicalProcedureStage F (i + 1)).complexity i

/-- Once a language has been inserted, every later finite Procedure-1 stage
retains its canonical complexity. -/
theorem canonicalProcedureStage_complexity_stable
    (F : Nat -> Set α) {stage i : Nat} (hi : i < stage) :
    (canonicalProcedureStage F stage).complexity i =
      canonicalComplexity F i := by
  induction stage with
  | zero => omega
  | succ stage ih =>
      by_cases hieq : i = stage
      · subst i
        rfl
      · have hiOld : i < stage := by omega
        calc
          (canonicalProcedureStage F (Nat.succ stage)).complexity i =
              (canonicalProcedureStage F stage).complexity i := by
                rw [canonicalProcedureStage]
                exact extendProcedureStage_complexity_old
                  F (canonicalProcedureStage F stage) hiOld
          _ = canonicalComplexity F i := ih hiOld

/-- The exact time vector displayed in Theorem 4. -/
noncomputable def schedulerTimeVector
    (F : Nat -> Set α) (f : Nat -> Nat)
    (hf : IsUnboundedScheduler f) : TimeVector :=
  fun i => max (schedulerEntryTime f hf i)
    (canonicalComplexity F i + 1)

theorem schedulerTimeVector_positive
    (F : Nat -> Set α) (f : Nat -> Nat)
    (hf : IsUnboundedScheduler f) :
    PositiveTimeVector (schedulerTimeVector F f hf) := by
  intro i
  exact le_trans (by omega)
    (Nat.le_max_right _ _)

/-- The Procedure-1 scan order used by the literal Theorem-4 algorithm at
history size `t`. -/
noncomputable def schedulerScanOrder
    (F : Nat -> Set α) (f : Nat -> Nat) (t : Nat) : List Nat :=
  (canonicalProcedureStage F (f t)).order

/-- The literal scheduler-driven greedy algorithm from Section 3.2. -/
noncomputable def schedulerGenerator
    [Infinite α] (F : Nat -> Set α) (f : Nat -> Nat) :
    HistoryGenerator α := by
  classical
  exact fun _ xs =>
    let sample := GenLimit.Generic.sequenceSample xs
    let selected :=
      greedyListScan F sample ∅
        (schedulerScanOrder F f sample.card)
    GenLimit.Support.freshFromInfinite
      (indexedIntersection F selected)
      (greedyListScan_core_infinite F sample ∅
        (schedulerScanOrder F f sample.card)
        (by simpa using
          (Set.infinite_univ : (Set.univ : Set α).Infinite)))
      sample

theorem schedulerGenerator_spec
    [Infinite α] (F : Nat -> Set α) (f : Nat -> Nat)
    {t : Nat} (xs : Fin t -> α) :
    schedulerGenerator F f t xs ∈
        indexedIntersection F
          (greedyListScan F
            (GenLimit.Generic.sequenceSample xs) ∅
            (schedulerScanOrder F f
              (GenLimit.Generic.sequenceSample xs).card)) ∧
      schedulerGenerator F f t xs ∉
        GenLimit.Generic.sequenceSample xs := by
  classical
  simp only [schedulerGenerator]
  exact ⟨GenLimit.Support.freshFromInfinite_mem _ _ _,
    GenLimit.Support.freshFromInfinite_not_mem _ _ _⟩

/-- The full target-selection argument for the arbitrary scheduler. -/
theorem schedulerGenerator_correct
    [Infinite α] (F : Nat -> Set α)
    (f : Nat -> Nat) (hf : IsUnboundedScheduler f)
    {i t : Nat} (xs : Fin t -> α)
    (hthreshold : schedulerTimeVector F f hf i ≤ t)
    (hInjective : Function.Injective xs)
    (hTarget : ∀ k, xs k ∈ F i) :
    schedulerGenerator F f t xs ∈ F i ∧
      ∀ k, schedulerGenerator F f t xs ≠ xs k := by
  classical
  let sample := GenLimit.Generic.sequenceSample xs
  have hsampleCard : sample.card = t :=
    GenLimit.Generic.sequenceSample_card_of_injective xs hInjective
  have hentry :
      schedulerEntryTime f hf i ≤ t := by
    exact (Nat.le_max_left _ _).trans hthreshold
  have hiScope : i < f t :=
    (schedulerEntryTime_le_iff f hf).mp hentry
  let current := canonicalProcedureStage F (f t)
  have hiOrder : i ∈ current.order := by
    apply current.order_perm.mem_iff.mpr
    exact List.mem_range.mpr hiScope
  obtain ⟨before, after, hOrder⟩ :=
    List.mem_iff_append.mp hiOrder
  have hScanOrder :
      schedulerScanOrder F f sample.card =
        before ++ i :: after := by
    rw [hsampleCard]
    simpa [schedulerScanOrder, current] using hOrder
  have hSampleTarget :
      (↑sample : Set α) ⊆ F i :=
    GenLimit.Generic.sequenceSample_subset_of_pointwise hTarget
  have hcomplexity :
      current.complexity i = canonicalComplexity F i :=
    canonicalProcedureStage_complexity_stable F hiScope
  have hcard : canonicalComplexity F i < sample.card := by
    have hbound :
        canonicalComplexity F i + 1 ≤ t := by
      exact (Nat.le_max_right _ _).trans hthreshold
    omega
  have hiSelected :
      i ∈ greedyListScan F sample ∅
        (schedulerScanOrder F f sample.card) := by
    exact target_selected_in_greedyListScan F sample
      hScanOrder
      (by simpa [hcomplexity] using
        current.max_bounds before i after hOrder)
      hSampleTarget hcard
  have hspec := schedulerGenerator_spec F f xs
  constructor
  · exact hspec.1 i hiSelected
  · intro k hk
    exact hspec.2
      (GenLimit.Generic.mem_sequenceSample_iff.mpr
        ⟨k, hk.symm⟩)

/-- Theorem 4: the scheduler-driven algorithm achieves exactly the displayed
non-uniform threshold vector
`max (g i) (mStar i + 1)`. -/
theorem theorem_4_arbitrary_scheduler
    [Infinite α] (F : Nat -> Set α)
    (f : Nat -> Nat) (hf : IsUnboundedScheduler f) :
    AchievesTimeVector (schedulerGenerator F f) F
      (schedulerTimeVector F f hf) ∧
    PositiveTimeVector (schedulerTimeVector F f hf) := by
  constructor
  · intro i t xs htime hInjective hTarget
    exact schedulerGenerator_correct F f hf xs htime
      hInjective hTarget
  · exact schedulerTimeVector_positive F f hf

/-- In particular, the exact displayed Theorem-4 vector belongs to the
semantic realizable frontier. -/
theorem theorem_4_timeVector_realizable
    [Infinite α] (F : Nat -> Set α)
    (f : Nat -> Nat) (hf : IsUnboundedScheduler f) :
    schedulerTimeVector F f hf ∈ RealizableTimeVectors F :=
  ⟨schedulerGenerator F f,
    (theorem_4_arbitrary_scheduler F f hf).1,
    (theorem_4_arbitrary_scheduler F f hf).2⟩

end GenLimit.ParetoGeneration
