import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.InfiniteRank.ConsumptionBridge
import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.InfiniteRank.RunThinning

/-!
# Capacity-two long-bad charging

This module packages the unconditional conclusion of a token-source-backed
first-consumption schedule.  Retained long-bad positions charge earlier
output positions, with injectivity separately in the input-first and
output-first classes.  Every output consequently has capacity at most two.
Combining that estimate with one-half run thinning gives

`Long(n) ≤ 4 * Output(n) + error`

and hence the corrected `1/10` density conclusion.
-/

open Filter

namespace GenLimit.KleinbergWei.DensityMeasures.InfiniteRank

/-- A backward output charge with two disjoint injectivity classes.

This is the capacity-two analogue of `LongBadCharge`. -/
structure LongBadCapacityTwoCharge
    (K : OrderedLanguage) (Output Long : Language) where
  retained : Set ℕ
  charge : ℕ → ℕ
  inputFirst : ℕ → Prop
  longError : ℕ
  retained_long :
    ∀ ⦃i : ℕ⦄, i ∈ retained → K.enumeration i ∈ Long
  half_mass :
    ∀ᶠ n : ℕ in atTop,
      K.prefixCount Long n ≤
        2 * positionPrefixCount retained n + longError
  charge_earlier :
    ∀ ⦃i : ℕ⦄, i ∈ retained → charge i < i
  charge_output :
    ∀ ⦃i : ℕ⦄, i ∈ retained →
      K.enumeration (charge i) ∈ Output
  charge_injectiveOn_input :
    Set.InjOn charge (retained ∩ {i | inputFirst i})
  charge_injectiveOn_output :
    Set.InjOn charge (retained ∩ {i | ¬ inputFirst i})

namespace LongBadCapacityTwoCharge

/-- Every retained prefix fits into two copies of the preceding output
prefix, one for each first-consumer class. -/
theorem retainedPrefix_le_two_outputPrefix
    {K : OrderedLanguage} {Output Long : Language}
    (C : LongBadCapacityTwoCharge K Output Long) (n : ℕ) :
    positionPrefixCount C.retained n ≤
      2 * K.prefixCount Output n := by
  classical
  let source : Finset ℕ :=
    (Finset.range n).filter fun i => i ∈ C.retained
  let target : Finset ℕ :=
    (Finset.range n).filter fun i => K.enumeration i ∈ Output
  let inputSource : Finset ℕ :=
    source.filter C.inputFirst
  let outputSource : Finset ℕ :=
    source.filter fun i => ¬ C.inputFirst i
  have hSourceMaps : Set.MapsTo C.charge source target := by
    intro i hi
    have hi' : i < n ∧ i ∈ C.retained := by
      simpa [source] using hi
    have hChargeLt : C.charge i < n :=
      lt_trans (C.charge_earlier hi'.2) hi'.1
    have hChargeOutput :
        K.enumeration (C.charge i) ∈ Output :=
      C.charge_output hi'.2
    simpa [target, hChargeLt] using hChargeOutput
  have hInputMaps : Set.MapsTo C.charge inputSource target := by
    intro i hi
    exact hSourceMaps (Finset.mem_filter.mp hi).1
  have hOutputMaps : Set.MapsTo C.charge outputSource target := by
    intro i hi
    exact hSourceMaps (Finset.mem_filter.mp hi).1
  have hInputInj : Set.InjOn C.charge inputSource := by
    intro i hi j hj hEq
    apply C.charge_injectiveOn_input
    · have hi' : (i < n ∧ i ∈ C.retained) ∧ C.inputFirst i := by
        simpa [inputSource, source] using hi
      exact ⟨hi'.1.2, hi'.2⟩
    · have hj' : (j < n ∧ j ∈ C.retained) ∧ C.inputFirst j := by
        simpa [inputSource, source] using hj
      exact ⟨hj'.1.2, hj'.2⟩
    · exact hEq
  have hOutputInj : Set.InjOn C.charge outputSource := by
    intro i hi j hj hEq
    apply C.charge_injectiveOn_output
    · have hi' :
          (i < n ∧ i ∈ C.retained) ∧ ¬ C.inputFirst i := by
        simpa [outputSource, source] using hi
      exact ⟨hi'.1.2, hi'.2⟩
    · have hj' :
          (j < n ∧ j ∈ C.retained) ∧ ¬ C.inputFirst j := by
        simpa [outputSource, source] using hj
      exact ⟨hj'.1.2, hj'.2⟩
    · exact hEq
  have hInputCard : inputSource.card ≤ target.card :=
    card_le_of_injective_charge
      inputSource target C.charge hInputMaps hInputInj
  have hOutputCard : outputSource.card ≤ target.card :=
    card_le_of_injective_charge
      outputSource target C.charge hOutputMaps hOutputInj
  have hPartition : source = inputSource ∪ outputSource := by
    ext i
    by_cases hi : C.inputFirst i <;>
      simp [inputSource, outputSource, hi]
  have hDisjoint : Disjoint inputSource outputSource := by
    rw [Finset.disjoint_left]
    intro i hiInput hiOutput
    exact (Finset.mem_filter.mp hiOutput).2
      (Finset.mem_filter.mp hiInput).2
  have hCapacity : source.card ≤ 2 * target.card := by
    rw [hPartition, Finset.card_union_of_disjoint hDisjoint]
    omega
  simpa [source, target, positionPrefixCount,
    OrderedLanguage.prefixCount] using hCapacity

/-- One-half thinning followed by a capacity-two backward charge gives the
corrected coefficient four. -/
theorem eventually_long_le
    {K : OrderedLanguage} {Output Long : Language}
    (C : LongBadCapacityTwoCharge K Output Long) :
    ∀ᶠ n : ℕ in atTop,
      K.prefixCount Long n ≤
        4 * K.prefixCount Output n + C.longError := by
  filter_upwards [C.half_mass] with n hn
  have hCapacity := C.retainedPrefix_le_two_outputPrefix n
  omega

/-- Arbitrary one-point-per-run thinning plus a two-class backward charge
constructs the capacity-two long-bad package. -/
noncomputable def ofRunThinning
    (K : OrderedLanguage) (Output Long : Language)
    (retained : Set ℕ)
    (C :
      RunThinning.Certificate
        (RunThinning.orderedPositions K Long) retained)
    (exceptions : Finset ℕ)
    (charge : ℕ → ℕ)
    (inputFirst : ℕ → Prop)
    (charge_earlier :
      ∀ ⦃i : ℕ⦄,
        i ∈ retained \ (exceptions : Set ℕ) → charge i < i)
    (charge_output :
      ∀ ⦃i : ℕ⦄,
        i ∈ retained \ (exceptions : Set ℕ) →
          K.enumeration (charge i) ∈ Output)
    (charge_injectiveOn_input :
      Set.InjOn charge
        ((retained \ (exceptions : Set ℕ)) ∩
          {i | inputFirst i}))
    (charge_injectiveOn_output :
      Set.InjOn charge
        ((retained \ (exceptions : Set ℕ)) ∩
          {i | ¬ inputFirst i})) :
    LongBadCapacityTwoCharge K Output Long where
  retained := retained \ (exceptions : Set ℕ)
  charge := charge
  inputFirst := inputFirst
  longError := 2 * exceptions.card + 1
  retained_long := by
    intro i hi
    exact C.retained_subset hi.1
  half_mass := Filter.Eventually.of_forall fun n => by
    rw [RunThinning.prefixCount_eq_positionPrefixCount_orderedPositions]
    exact
      RunThinning.positionPrefixCount_le_two_diff_finset_add_error
        C exceptions n
  charge_earlier := charge_earlier
  charge_output := charge_output
  charge_injectiveOn_input := charge_injectiveOn_input
  charge_injectiveOn_output := charge_injectiveOn_output

/-! ## Constructor from a first-consumption schedule -/

open FirstConsumptionBridge

/-- Totalize the subtype charge away from the retained set. -/
noncomputable def scheduleTotalCharge
    {input output : ℕ → ℕ} {retained : Set ℕ}
    (schedule :
      FirstConsumptionBridge.Schedule
        {i // i ∈ retained} input output)
    (i : ℕ) : ℕ := by
  classical
  exact if hi : i ∈ retained then
    schedule.charge ⟨i, hi⟩
  else
    0

/-- Totalize the input-first predicate away from the retained set. -/
noncomputable def scheduleTotalInputFirst
    {input output : ℕ → ℕ} {retained : Set ℕ}
    (schedule :
      FirstConsumptionBridge.Schedule
        {i // i ∈ retained} input output)
    (i : ℕ) : Prop := by
  classical
  exact if hi : i ∈ retained then
    schedule.InputFirst ⟨i, hi⟩
  else
    False

/-- A schedule over retained positions supplies the capacity-two charge
without an independent token-injectivity premise. -/
noncomputable def ofSchedule
    (K : OrderedLanguage) (Output Long : Language)
    (retained : Set ℕ)
    {input output : ℕ → ℕ}
    (schedule :
      FirstConsumptionBridge.Schedule
        {i // i ∈ retained} input output)
    (longError : ℕ)
    (retained_long :
      ∀ ⦃i : ℕ⦄, i ∈ retained → K.enumeration i ∈ Long)
    (half_mass :
      ∀ᶠ n : ℕ in atTop,
        K.prefixCount Long n ≤
          2 * positionPrefixCount retained n + longError)
    (key_eq :
      ∀ d, schedule.keyPosition d = d.1)
    (charged_output :
      ∀ d, K.enumeration (schedule.charge d) ∈ Output) :
    LongBadCapacityTwoCharge K Output Long where
  retained := retained
  charge := scheduleTotalCharge schedule
  inputFirst := scheduleTotalInputFirst schedule
  longError := longError
  retained_long := retained_long
  half_mass := half_mass
  charge_earlier := by
    intro i hi
    have hLt :=
      schedule.charge_lt_key
        (⟨i, hi⟩ : {j // j ∈ retained})
    rw [key_eq] at hLt
    simpa [scheduleTotalCharge, hi] using hLt
  charge_output := by
    intro i hi
    simpa [scheduleTotalCharge, hi] using
      charged_output (⟨i, hi⟩ : {j // j ∈ retained})
  charge_injectiveOn_input := by
    intro i hi j hj hCharge
    have hiRetained : i ∈ retained := hi.1
    have hjRetained : j ∈ retained := hj.1
    have hiInput :
        schedule.InputFirst
          (⟨i, hiRetained⟩ : {k // k ∈ retained}) := by
      simpa [scheduleTotalInputFirst, hiRetained] using hi.2
    have hjInput :
        schedule.InputFirst
          (⟨j, hjRetained⟩ : {k // k ∈ retained}) := by
      simpa [scheduleTotalInputFirst, hjRetained] using hj.2
    have hCharge' :
        schedule.charge
            (⟨i, hiRetained⟩ : {k // k ∈ retained}) =
          schedule.charge
            (⟨j, hjRetained⟩ : {k // k ∈ retained}) := by
      simpa [scheduleTotalCharge, hiRetained, hjRetained] using hCharge
    have hSubtype :=
      schedule.charge_injectiveOn_inputFirst
        hiInput hjInput hCharge'
    exact congrArg Subtype.val hSubtype
  charge_injectiveOn_output := by
    intro i hi j hj hCharge
    have hiRetained : i ∈ retained := hi.1
    have hjRetained : j ∈ retained := hj.1
    have hiOutput :
        ¬ schedule.InputFirst
          (⟨i, hiRetained⟩ : {k // k ∈ retained}) := by
      intro hiInput
      apply hi.2
      simpa [scheduleTotalInputFirst, hiRetained] using hiInput
    have hjOutput :
        ¬ schedule.InputFirst
          (⟨j, hjRetained⟩ : {k // k ∈ retained}) := by
      intro hjInput
      apply hj.2
      simpa [scheduleTotalInputFirst, hjRetained] using hjInput
    have hCharge' :
        schedule.charge
            (⟨i, hiRetained⟩ : {k // k ∈ retained}) =
          schedule.charge
            (⟨j, hjRetained⟩ : {k // k ∈ retained}) := by
      simpa [scheduleTotalCharge, hiRetained, hjRetained] using hCharge
    have hSubtype :=
      schedule.charge_injectiveOn_outputFirst
        hiOutput hjOutput hCharge'
    exact congrArg Subtype.val hSubtype

/-- Combine arbitrary-run thinning, finite exceptions, and a
first-consumption schedule on the surviving positions. -/
noncomputable def ofRunThinningOfSchedule
    (K : OrderedLanguage) (Output Long : Language)
    (retained : Set ℕ)
    (C :
      RunThinning.Certificate
        (RunThinning.orderedPositions K Long) retained)
    (exceptions : Finset ℕ)
    {input output : ℕ → ℕ}
    (schedule :
      FirstConsumptionBridge.Schedule
        {i // i ∈ retained \ (exceptions : Set ℕ)}
        input output)
    (key_eq :
      ∀ d, schedule.keyPosition d = d.1)
    (charged_output :
      ∀ d, K.enumeration (schedule.charge d) ∈ Output) :
    LongBadCapacityTwoCharge K Output Long :=
  ofSchedule
    K Output Long (retained \ (exceptions : Set ℕ))
    schedule (2 * exceptions.card + 1)
    (fun _ hi => C.retained_subset hi.1)
    (Filter.Eventually.of_forall fun n => by
      rw [RunThinning.prefixCount_eq_positionPrefixCount_orderedPositions]
      exact
        RunThinning.positionPrefixCount_le_two_diff_finset_add_error
          C exceptions n)
    key_eq charged_output

end LongBadCapacityTwoCharge

/-- Feed a capacity-two long-bad charge directly into the corrected
one-tenth endgame. -/
theorem orderedLowerDensity_one_tenth_of_longBadCapacityTwoCharge
    (K : OrderedLanguage)
    (Output Good Singleton Long : Language)
    (eSingleton eGood : ℕ)
    (hpartition : ∀ n,
      K.prefixCount Output n +
          K.prefixCount Good n +
          K.prefixCount Singleton n +
          K.prefixCount Long n = n)
    (hsingleton : ∀ᶠ n : ℕ in atTop,
      2 * K.prefixCount Singleton n ≤
        K.prefixCount Output n +
          K.prefixCount Good n +
          K.prefixCount Singleton n +
          eSingleton)
    (hgood : ∀ᶠ n : ℕ in atTop,
      K.prefixCount Good n ≤
        2 * K.prefixCount Output n + eGood)
    (C : LongBadCapacityTwoCharge K Output Long) :
    (1 / 10 : ℝ) ≤ K.lowerDensity Output :=
  orderedLowerDensity_one_tenth_of_eventual_charges
    K Output Good Singleton Long
    eSingleton eGood C.longError
    hpartition hsingleton hgood C.eventually_long_le

end GenLimit.KleinbergWei.DensityMeasures.InfiniteRank
