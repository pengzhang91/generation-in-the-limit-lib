import GenLimit.Paper17_InfiniteContamination.SetDensityObstruction
import GenLimit.Support.PrefixCompletion

/-!
# Finite contamination: lower-density necessity

Source: Mehrotra--Velegkas--Yu--Zhou,
*Language Generation with Infinite Contamination*,
arXiv:2511.07417v1, Lemma 6.7 and the necessity direction of Theorem 6.5.

For targets `L₁` and `L₂` with finite asymmetric difference `L₁ \ L₂`,
the paper alternately completes a growing repetition-free prefix to an
enumeration of `L₂` and to an enumeration of `L₁`.  Correctness on the
`L₁` completions forces a cofinal sequence of output sets contained in
`L₁`.  The limit of the nested prefixes is nevertheless a valid
finite-noise, finite-omission presentation of `L₂`.

The source finally bounds a liminf by writing a limit along the selected
subsequence.  Convergence of that subsequence is not established.  Here the
same step is expressed by
`setBasedLowerDensity_le_of_frequently_subset`, which needs only the
cofinal/frequent containment actually proved by the construction.
-/

namespace GenLimit.InfiniteContamination

open Filter
open GenLimit.KleinbergWei

/-- A set generator eventually generates correctly on every repetition-free
finite-noise, finite-omission presentation of one target. -/
def GeneratesSetUnderFiniteContaminationOn
    (gen : SetGenerator α)
    (L : GenLimit.Generic.Language α) : Prop :=
  ∀ stream,
    FiniteNoiseFiniteOmissionEnumeration stream L →
      GeneratesSetInLimitOn gen L stream

/-- Source-faithful finite-contamination generation: every output on every
finite history is infinite, and the legacy correctness predicate holds
eventually on every valid contaminated presentation. -/
def GeneratesInfiniteSetUnderFiniteContaminationOn
    (gen : SetGenerator α)
    (L : GenLimit.Generic.Language α) : Prop :=
  IsInfiniteSetGenerator gen ∧
    GeneratesSetUnderFiniteContaminationOn gen L

/-- The source-faithful finite-contamination predicate implies the existing
weak predicate. -/
theorem GeneratesInfiniteSetUnderFiniteContaminationOn.generatesSet
    {gen : SetGenerator α}
    {L : GenLimit.Generic.Language α}
    (h : GeneratesInfiniteSetUnderFiniteContaminationOn gen L) :
    GeneratesSetUnderFiniteContaminationOn gen L :=
  h.2

/-- The lower-density part of Definition 10, restricted to one ordered
target and the finite-noise, finite-omission regime of Theorem 6.5. -/
def GuaranteesSetBasedLowerDensityUnderFiniteContaminationOn
    (gen : SetGenerator ℕ)
    (K : OrderedLanguage) (c : ℝ) : Prop :=
  ∀ stream,
    FiniteNoiseFiniteOmissionEnumeration stream K.carrier →
      c ≤ setBasedLowerDensity gen K stream

/-- Every ordered language is infinite: its enumeration embeds `ℕ` into its
carrier and has exactly that carrier as its range. -/
theorem orderedLanguage_carrier_infinite
    (K : OrderedLanguage) :
    K.carrier.Infinite := by
  rw [← K.range_enumeration]
  exact Set.infinite_range_of_injective K.enumeration_injective

namespace FiniteContaminationNecessity

private def listInput (history : List ℕ) :
    Fin history.length → ℕ :=
  fun i => history.get i

private theorem sequenceSample_listInput
    (history : List ℕ) :
    GenLimit.Generic.sequenceSample (listInput history) =
      history.toFinset := by
  classical
  ext x
  rw [GenLimit.Generic.mem_sequenceSample_iff, List.mem_toFinset]
  exact List.mem_iff_get.symm

/-- Retain a finite ordered history, then enumerate every target value not
already in that history. -/
private noncomputable def prefixCompletion
    (history : List ℕ) (L : Set ℕ) (hL : L.Infinite) :
    GenLimit.Generic.Stream ℕ :=
  GenLimit.Support.prefixThenTarget
    (listInput history) L
    (hL.diff
      (GenLimit.Generic.sequenceSample
        (listInput history)).finite_toSet)

private theorem prefixCompletion_prefix
    (history : List ℕ) (L : Set ℕ) (hL : L.Infinite)
    (i : Fin history.length) :
    prefixCompletion history L hL i = history.get i := by
  exact
    GenLimit.Support.prefixThenTarget_prefix
      (listInput history) L
      (hL.diff
        (GenLimit.Generic.sequenceSample
          (listInput history)).finite_toSet) i

private theorem prefixCompletion_injective
    (history : List ℕ) (L : Set ℕ) (hL : L.Infinite)
    (hnodup : history.Nodup) :
    Function.Injective (prefixCompletion history L hL) := by
  apply GenLimit.Support.prefixThenTarget_injective
  exact List.nodup_iff_injective_get.mp hnodup

private theorem range_prefixCompletion
    (history : List ℕ) (L : Set ℕ) (hL : L.Infinite) :
    Set.range (prefixCompletion history L hL) =
      (history.toFinset : Set ℕ) ∪ L := by
  have h :=
    GenLimit.Support.range_prefixThenTarget_eq_prefix_union
      (listInput history) L
      (hL.diff
        (GenLimit.Generic.sequenceSample
          (listInput history)).finite_toSet)
  simpa [prefixCompletion, sequenceSample_listInput] using h

/-- Completing any duplicate-free finite history to an infinite target is a
valid finite-contamination presentation of that target.  All noise lies in
the retained finite history and there are no omissions. -/
private theorem prefixCompletion_valid
    (history : List ℕ) (L : Set ℕ) (hL : L.Infinite)
    (hnodup : history.Nodup) :
    FiniteNoiseFiniteOmissionEnumeration
      (prefixCompletion history L hL) L := by
  let stream := prefixCompletion history L hL
  have hinjective : Function.Injective stream :=
    prefixCompletion_injective history L hL hnodup
  have hrange :
      Set.range stream = (history.toFinset : Set ℕ) ∪ L := by
    simpa [stream] using range_prefixCompletion history L hL
  refine ⟨hinjective, ?_, ?_⟩
  · change {t | stream t ∉ L}.Finite
    have hbad :
        {t | stream t ∉ L} ⊆
          stream ⁻¹' (history.toFinset : Set ℕ) := by
      intro t ht
      change stream t ∈ (history.toFinset : Set ℕ)
      have htRange : stream t ∈ Set.range stream := ⟨t, rfl⟩
      rw [hrange] at htRange
      exact htRange.resolve_right ht
    exact
      ((history.toFinset.finite_toSet.preimage
        hinjective.injOn).subset hbad)
  · rw [FiniteOmissions, hrange]
    have hempty :
        L \ ((history.toFinset : Set ℕ) ∪ L) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hx.2 (Set.mem_union_right _ hx.1)
    rw [hempty]
    exact Set.finite_empty

/-- The nested prefix maintained after `n` complete `L₂`/`L₁` cycles. -/
private structure AlternatingPrefixState
    (L₁ : Set ℕ) (K₂ : OrderedLanguage) (n : ℕ) where
  history : List ℕ
  history_nodup : history.Nodup
  history_mem_union :
    ∀ x, x ∈ history → x ∈ L₁ ∪ K₂.carrier
  covers_target_prefix :
    ∀ j, j < n → K₂.enumeration j ∈ history

private def initialState
    (L₁ : Set ℕ) (K₂ : OrderedLanguage) :
    AlternatingPrefixState L₁ K₂ 0 where
  history := []
  history_nodup := by simp
  history_mem_union := by simp
  covers_target_prefix := by omega

/-- One full source phase: first complete the current prefix toward `L₂`,
then complete the resulting prefix toward `L₁`.  Both completion times are
chosen after the corresponding generator threshold. -/
private structure AlternatingPrefixStep
    (gen : SetGenerator ℕ) (L₁ : Set ℕ)
    (K₂ : OrderedLanguage) (n : ℕ)
    (state : AlternatingPrefixState L₁ K₂ n) where
  next : AlternatingPrefixState L₁ K₂ (n + 1)
  extends_history : state.history <+: next.history
  strict_growth : state.history.length < next.history.length
  oddTime : ℕ
  old_length_le_oddTime : state.history.length ≤ oddTime
  oddTime_lt_next : oddTime < next.history.length
  odd_output_subset :
    setOutput gen
      (GenLimit.Generic.historyThenFallback next.history 0)
      oddTime ⊆ K₂.carrier
  forcedTime : ℕ
  oddTime_lt_forcedTime : oddTime < forcedTime
  forcedTime_lt_next : forcedTime < next.history.length
  forced_output_subset :
    setOutput gen
      (GenLimit.Generic.historyThenFallback next.history 0)
      forcedTime ⊆ L₁

private theorem exists_alternatingPrefixStep
    (gen : SetGenerator ℕ) (L₁ : Set ℕ)
    (K₂ : OrderedLanguage) (hL₁ : L₁.Infinite)
    (hgenerate₁ :
      GeneratesSetUnderFiniteContaminationOn gen L₁)
    (hgenerate₂ :
      GeneratesSetUnderFiniteContaminationOn gen K₂.carrier)
    (n : ℕ) (state : AlternatingPrefixState L₁ K₂ n) :
    Nonempty (AlternatingPrefixStep gen L₁ K₂ n state) := by
  classical
  have hL₂ : K₂.carrier.Infinite :=
    orderedLanguage_carrier_infinite K₂

  let oddFull :=
    prefixCompletion state.history K₂.carrier hL₂
  have hOddInjective : Function.Injective oddFull := by
    exact
      prefixCompletion_injective state.history K₂.carrier hL₂
        state.history_nodup
  have hOddValid :
      FiniteNoiseFiniteOmissionEnumeration oddFull K₂.carrier := by
    exact
      prefixCompletion_valid state.history K₂.carrier hL₂
        state.history_nodup
  obtain ⟨T₂, hT₂⟩ := hgenerate₂ oddFull hOddValid
  have hnextTargetRange :
      K₂.enumeration n ∈ Set.range oddFull := by
    rw [range_prefixCompletion state.history K₂.carrier hL₂]
    exact
      Set.mem_union_right _
        (by
          rw [← K₂.range_enumeration]
          exact ⟨n, rfl⟩)
  obtain ⟨q, hq⟩ := hnextTargetRange
  let oddTime := max (max T₂ state.history.length) q
  have hT₂odd : T₂ ≤ oddTime :=
    (Nat.le_max_left T₂ state.history.length).trans
      (Nat.le_max_left _ q)
  have hhistoryOdd : state.history.length ≤ oddTime :=
    (Nat.le_max_right T₂ state.history.length).trans
      (Nat.le_max_left _ q)
  have hqOdd : q ≤ oddTime := Nat.le_max_right _ _
  have hOddCorrect :
      SetCorrectAt gen K₂.carrier oddFull oddTime :=
    hT₂ oddTime hT₂odd
  let oddHistory : List ℕ :=
    List.ofFn (fun i : Fin (oddTime + 1) => oddFull i)
  have hOddHistoryLength :
      oddHistory.length = oddTime + 1 := by
    simp [oddHistory]
  have hOddHistoryNodup : oddHistory.Nodup := by
    rw [List.nodup_iff_injective_getElem]
    intro a b hab
    apply Fin.ext
    apply hOddInjective
    simpa only [oddHistory, List.getElem_ofFn] using hab
  have hhistoryPrefixOdd :
      state.history <+: oddHistory := by
    apply List.prefix_iff_getElem.mpr
    refine ⟨by rw [hOddHistoryLength]; omega, ?_⟩
    intro k hk
    simp only [oddHistory, List.getElem_ofFn]
    exact
      (prefixCompletion_prefix state.history K₂.carrier hL₂
        ⟨k, hk⟩).symm
  have hnextTargetOdd :
      K₂.enumeration n ∈ oddHistory := by
    dsimp only [oddHistory]
    rw [List.mem_ofFn]
    exact ⟨⟨q, by omega⟩, hq⟩
  have hOddHistoryMemUnion :
      ∀ x, x ∈ oddHistory → x ∈ L₁ ∪ K₂.carrier := by
    intro x hx
    dsimp only [oddHistory] at hx
    rw [List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    have hiRange : oddFull i ∈ Set.range oddFull := ⟨i, rfl⟩
    rw [range_prefixCompletion state.history K₂.carrier hL₂]
      at hiRange
    rcases hiRange with hiOld | hiTarget
    · exact
        state.history_mem_union _ (List.mem_toFinset.mp hiOld)
    · exact Set.mem_union_right _ hiTarget

  let evenFull := prefixCompletion oddHistory L₁ hL₁
  have hEvenInjective : Function.Injective evenFull := by
    exact
      prefixCompletion_injective oddHistory L₁ hL₁
        hOddHistoryNodup
  have hEvenValid :
      FiniteNoiseFiniteOmissionEnumeration evenFull L₁ := by
    exact
      prefixCompletion_valid oddHistory L₁ hL₁
        hOddHistoryNodup
  obtain ⟨T₁, hT₁⟩ := hgenerate₁ evenFull hEvenValid
  let forcedTime := max T₁ oddHistory.length
  have hT₁forced : T₁ ≤ forcedTime := Nat.le_max_left _ _
  have hOddLengthForced :
      oddHistory.length ≤ forcedTime := Nat.le_max_right _ _
  have hEvenCorrect :
      SetCorrectAt gen L₁ evenFull forcedTime :=
    hT₁ forcedTime hT₁forced
  let nextHistory : List ℕ :=
    List.ofFn (fun i : Fin (forcedTime + 1) => evenFull i)
  have hNextHistoryLength :
      nextHistory.length = forcedTime + 1 := by
    simp [nextHistory]
  have hNextHistoryNodup : nextHistory.Nodup := by
    rw [List.nodup_iff_injective_getElem]
    intro a b hab
    apply Fin.ext
    apply hEvenInjective
    simpa only [nextHistory, List.getElem_ofFn] using hab
  have hOddPrefixNext :
      oddHistory <+: nextHistory := by
    apply List.prefix_iff_getElem.mpr
    refine ⟨by rw [hNextHistoryLength]; omega, ?_⟩
    intro k hk
    simp only [nextHistory, List.getElem_ofFn]
    exact
      (prefixCompletion_prefix oddHistory L₁ hL₁
        ⟨k, hk⟩).symm
  have hNextHistoryMemUnion :
      ∀ x, x ∈ nextHistory → x ∈ L₁ ∪ K₂.carrier := by
    intro x hx
    dsimp only [nextHistory] at hx
    rw [List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    have hiRange : evenFull i ∈ Set.range evenFull := ⟨i, rfl⟩
    rw [range_prefixCompletion oddHistory L₁ hL₁] at hiRange
    rcases hiRange with hiOdd | hiTarget
    · exact hOddHistoryMemUnion _ (List.mem_toFinset.mp hiOdd)
    · exact Set.mem_union_left _ hiTarget
  have hNextCovers :
      ∀ j, j < n + 1 → K₂.enumeration j ∈ nextHistory := by
    intro j hj
    apply hOddPrefixNext.subset
    by_cases hjn : j < n
    · exact
        hhistoryPrefixOdd.subset
          (state.covers_target_prefix j hjn)
    · have hjEq : j = n := by omega
      simpa [hjEq] using hnextTargetOdd
  let next : AlternatingPrefixState L₁ K₂ (n + 1) :=
    { history := nextHistory
      history_nodup := hNextHistoryNodup
      history_mem_union := hNextHistoryMemUnion
      covers_target_prefix := hNextCovers }

  have hOddOutputOnNext :
      setOutput gen
        (GenLimit.Generic.historyThenFallback next.history 0)
        oddTime ⊆ K₂.carrier := by
    have houtputEq :
        setOutput gen
            (GenLimit.Generic.historyThenFallback next.history 0)
            oddTime =
          setOutput gen oddFull oddTime := by
      unfold setOutput
      congr 1
      funext i
      have hiOddHistory : i.val < oddHistory.length := by
        rw [hOddHistoryLength]
        omega
      have hiNext : i.val < next.history.length := by
        dsimp only [next]
        rw [hNextHistoryLength]
        omega
      simp only [GenLimit.Generic.historyThenFallback, dif_pos hiNext]
      change nextHistory.get ⟨i, hiNext⟩ = oddFull i
      rw [List.get_eq_getElem]
      have hprefixValue :=
        (List.prefix_iff_getElem.mp hOddPrefixNext).2
          i.val hiOddHistory
      change nextHistory[i.val] = oddFull i
      rw [← hprefixValue]
      simp only [oddHistory, List.getElem_ofFn]
    rw [houtputEq]
    exact hOddCorrect.1
  have hForcedOutputOnNext :
      setOutput gen
        (GenLimit.Generic.historyThenFallback next.history 0)
        forcedTime ⊆ L₁ := by
    have houtputEq :
        setOutput gen
            (GenLimit.Generic.historyThenFallback next.history 0)
            forcedTime =
          setOutput gen evenFull forcedTime := by
      unfold setOutput
      congr 1
      funext i
      have hiNext : i.val < next.history.length := by
        dsimp only [next]
        rw [hNextHistoryLength]
        omega
      simp only [GenLimit.Generic.historyThenFallback, dif_pos hiNext]
      change nextHistory.get ⟨i, hiNext⟩ = evenFull i
      rw [List.get_eq_getElem]
      change nextHistory[i.val] = evenFull i
      simp only [nextHistory, List.getElem_ofFn]
    rw [houtputEq]
    exact hEvenCorrect.1
  refine ⟨{
    next := next
    extends_history := hhistoryPrefixOdd.trans hOddPrefixNext
    strict_growth := by
      dsimp only [next]
      rw [hNextHistoryLength]
      omega
    oddTime := oddTime
    old_length_le_oddTime := hhistoryOdd
    oddTime_lt_next := by
      dsimp only [next]
      rw [hNextHistoryLength]
      omega
    odd_output_subset := hOddOutputOnNext
    forcedTime := forcedTime
    oddTime_lt_forcedTime := by
      have : oddTime + 1 = oddHistory.length :=
        hOddHistoryLength.symm
      omega
    forcedTime_lt_next := by
      dsimp only [next]
      rw [hNextHistoryLength]
      omega
    forced_output_subset := hForcedOutputOnNext }⟩

private noncomputable def chosenStep
    (gen : SetGenerator ℕ) (L₁ : Set ℕ)
    (K₂ : OrderedLanguage) (hL₁ : L₁.Infinite)
    (hgenerate₁ :
      GeneratesSetUnderFiniteContaminationOn gen L₁)
    (hgenerate₂ :
      GeneratesSetUnderFiniteContaminationOn gen K₂.carrier)
    (n : ℕ) (state : AlternatingPrefixState L₁ K₂ n) :
    AlternatingPrefixStep gen L₁ K₂ n state :=
  Classical.choice
    (exists_alternatingPrefixStep
      gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂ n state)

/-- The state after `n` complete alternating cycles. -/
private noncomputable def alternatingStates
    (gen : SetGenerator ℕ) (L₁ : Set ℕ)
    (K₂ : OrderedLanguage) (hL₁ : L₁.Infinite)
    (hgenerate₁ :
      GeneratesSetUnderFiniteContaminationOn gen L₁)
    (hgenerate₂ :
      GeneratesSetUnderFiniteContaminationOn gen K₂.carrier) :
    (n : ℕ) → AlternatingPrefixState L₁ K₂ n
  | 0 => initialState L₁ K₂
  | n + 1 =>
      (chosenStep gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂ n
        (alternatingStates gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂ n)).next

private theorem state_history_prefix_succ
    (gen : SetGenerator ℕ) (L₁ : Set ℕ)
    (K₂ : OrderedLanguage) (hL₁ : L₁.Infinite)
    (hgenerate₁ :
      GeneratesSetUnderFiniteContaminationOn gen L₁)
    (hgenerate₂ :
      GeneratesSetUnderFiniteContaminationOn gen K₂.carrier)
    (n : ℕ) :
    (alternatingStates gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂ n).history
      <+:
    (alternatingStates gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂
      (n + 1)).history := by
  rw [alternatingStates]
  exact
    (chosenStep gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂ n
      (alternatingStates gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂ n)).extends_history

private theorem state_history_prefix
    (gen : SetGenerator ℕ) (L₁ : Set ℕ)
    (K₂ : OrderedLanguage) (hL₁ : L₁.Infinite)
    (hgenerate₁ :
      GeneratesSetUnderFiniteContaminationOn gen L₁)
    (hgenerate₂ :
      GeneratesSetUnderFiniteContaminationOn gen K₂.carrier)
    {n m : ℕ} (hnm : n ≤ m) :
    (alternatingStates gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂ n).history
      <+:
    (alternatingStates gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂ m).history := by
  induction m, hnm using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ m hnm ih =>
      exact ih.trans
        (state_history_prefix_succ
          gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂ m)

private theorem state_index_le_length
    (gen : SetGenerator ℕ) (L₁ : Set ℕ)
    (K₂ : OrderedLanguage) (hL₁ : L₁.Infinite)
    (hgenerate₁ :
      GeneratesSetUnderFiniteContaminationOn gen L₁)
    (hgenerate₂ :
      GeneratesSetUnderFiniteContaminationOn gen K₂.carrier)
    (n : ℕ) :
    n ≤
      (alternatingStates gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂
        n).history.length := by
  induction n with
  | zero => omega
  | succ n ih =>
      rw [alternatingStates]
      have hstrict :=
        (chosenStep gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂ n
          (alternatingStates gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂ n)).strict_growth
      omega

/-- The pointwise limit of the compatible nested histories. -/
private noncomputable def alternatingLimitStream
    (gen : SetGenerator ℕ) (L₁ : Set ℕ)
    (K₂ : OrderedLanguage) (hL₁ : L₁.Infinite)
    (hgenerate₁ :
      GeneratesSetUnderFiniteContaminationOn gen L₁)
    (hgenerate₂ :
      GeneratesSetUnderFiniteContaminationOn gen K₂.carrier) :
    GenLimit.Generic.Stream ℕ :=
  fun k =>
    (alternatingStates gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂
      (k + 1)).history[k]'(by
        have hlen :=
          state_index_le_length
            gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂ (k + 1)
        omega)

private theorem limitStream_eq_state_getElem
    (gen : SetGenerator ℕ) (L₁ : Set ℕ)
    (K₂ : OrderedLanguage) (hL₁ : L₁.Infinite)
    (hgenerate₁ :
      GeneratesSetUnderFiniteContaminationOn gen L₁)
    (hgenerate₂ :
      GeneratesSetUnderFiniteContaminationOn gen K₂.carrier)
    (n k : ℕ)
    (hk :
      k <
        (alternatingStates gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂
          n).history.length) :
    alternatingLimitStream gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂ k =
      (alternatingStates gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂
        n).history[k] := by
  unfold alternatingLimitStream
  by_cases hnk : n ≤ k + 1
  · have hp :=
      state_history_prefix
        gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂ hnk
    exact (hp.getElem hk).symm
  · have hkn : k + 1 ≤ n :=
      Nat.le_of_lt (Nat.lt_of_not_ge hnk)
    have hp :=
      state_history_prefix
        gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂ hkn
    have hkShort :
        k <
          (alternatingStates gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂
            (k + 1)).history.length := by
      have hlen :=
        state_index_le_length
          gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂ (k + 1)
      omega
    exact hp.getElem hkShort

private theorem alternatingLimitStream_injective
    (gen : SetGenerator ℕ) (L₁ : Set ℕ)
    (K₂ : OrderedLanguage) (hL₁ : L₁.Infinite)
    (hgenerate₁ :
      GeneratesSetUnderFiniteContaminationOn gen L₁)
    (hgenerate₂ :
      GeneratesSetUnderFiniteContaminationOn gen K₂.carrier) :
    Function.Injective
      (alternatingLimitStream
        gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂) := by
  intro a b hab
  let n := max a b + 1
  have hnLen :=
    state_index_le_length
      gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂ n
  have ha :
      a <
        (alternatingStates gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂
          n).history.length := by
    dsimp [n] at hnLen ⊢
    omega
  have hb :
      b <
        (alternatingStates gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂
          n).history.length := by
    dsimp [n] at hnLen ⊢
    omega
  have hget :
      (alternatingStates gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂
          n).history[a] =
        (alternatingStates gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂
          n).history[b] := by
    rw [← limitStream_eq_state_getElem
      gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂ n a ha]
    rw [← limitStream_eq_state_getElem
      gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂ n b hb]
    exact hab
  have hfin :
      (⟨a, ha⟩ :
          Fin
            (alternatingStates gen L₁ K₂ hL₁
              hgenerate₁ hgenerate₂ n).history.length) =
        ⟨b, hb⟩ := by
    apply
      (List.nodup_iff_injective_getElem.mp
        (alternatingStates gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂
          n).history_nodup)
    simpa using hget
  exact congrArg Fin.val hfin

private theorem range_limitStream_subset_union
    (gen : SetGenerator ℕ) (L₁ : Set ℕ)
    (K₂ : OrderedLanguage) (hL₁ : L₁.Infinite)
    (hgenerate₁ :
      GeneratesSetUnderFiniteContaminationOn gen L₁)
    (hgenerate₂ :
      GeneratesSetUnderFiniteContaminationOn gen K₂.carrier) :
    Set.range
        (alternatingLimitStream
          gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂) ⊆
      L₁ ∪ K₂.carrier := by
  rintro x ⟨k, rfl⟩
  let n := k + 1
  have hk :
      k <
        (alternatingStates gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂
          n).history.length := by
    have hlen :=
      state_index_le_length
        gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂ n
    dsimp [n] at hlen ⊢
    omega
  rw [limitStream_eq_state_getElem
    gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂ n k hk]
  apply
    (alternatingStates gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂
      n).history_mem_union
  exact List.get_mem _ _

private theorem limitStream_noOmissions
    (gen : SetGenerator ℕ) (L₁ : Set ℕ)
    (K₂ : OrderedLanguage) (hL₁ : L₁.Infinite)
    (hgenerate₁ :
      GeneratesSetUnderFiniteContaminationOn gen L₁)
    (hgenerate₂ :
      GeneratesSetUnderFiniteContaminationOn gen K₂.carrier) :
    NoOmissions
      (alternatingLimitStream
        gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂)
      K₂.carrier := by
  intro x hx
  rw [← K₂.range_enumeration] at hx
  obtain ⟨j, rfl⟩ := hx
  have hmem :
      K₂.enumeration j ∈
        (alternatingStates gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂
          (j + 1)).history :=
    (alternatingStates gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂
      (j + 1)).covers_target_prefix j (by omega)
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hmem
  refine ⟨i, ?_⟩
  rw [limitStream_eq_state_getElem
    gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂ (j + 1) i i.isLt]
  exact hi

private theorem limitStream_finiteNoise
    (gen : SetGenerator ℕ) (L₁ : Set ℕ)
    (K₂ : OrderedLanguage) (hL₁ : L₁.Infinite)
    (hgenerate₁ :
      GeneratesSetUnderFiniteContaminationOn gen L₁)
    (hgenerate₂ :
      GeneratesSetUnderFiniteContaminationOn gen K₂.carrier)
    (hfinite : (L₁ \ K₂.carrier).Finite) :
    FiniteNoise
      (alternatingLimitStream
        gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂)
      K₂.carrier := by
  let stream :=
    alternatingLimitStream
      gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂
  have hinjective : Function.Injective stream := by
    exact
      alternatingLimitStream_injective
        gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂
  have hrange :
      Set.range stream ⊆ L₁ ∪ K₂.carrier := by
    exact
      range_limitStream_subset_union
        gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂
  change {t | stream t ∉ K₂.carrier}.Finite
  have hbad :
      {t | stream t ∉ K₂.carrier} ⊆
        stream ⁻¹' (L₁ \ K₂.carrier) := by
    intro t ht
    refine ⟨?_, ht⟩
    have htRange : stream t ∈ Set.range stream := ⟨t, rfl⟩
    rcases hrange htRange with htL₁ | htL₂
    · exact htL₁
    · exact False.elim (ht htL₂)
  exact (hfinite.preimage hinjective.injOn).subset hbad

private theorem alternatingLimitStream_valid
    (gen : SetGenerator ℕ) (L₁ : Set ℕ)
    (K₂ : OrderedLanguage) (hL₁ : L₁.Infinite)
    (hgenerate₁ :
      GeneratesSetUnderFiniteContaminationOn gen L₁)
    (hgenerate₂ :
      GeneratesSetUnderFiniteContaminationOn gen K₂.carrier)
    (hfinite : (L₁ \ K₂.carrier).Finite) :
    FiniteNoiseFiniteOmissionEnumeration
      (alternatingLimitStream
        gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂)
      K₂.carrier := by
  refine
    ⟨alternatingLimitStream_injective
        gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂,
      limitStream_finiteNoise
        gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂ hfinite,
      ?_⟩
  rw [FiniteOmissions]
  have hno :=
    limitStream_noOmissions
      gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂
  have hempty :
      K₂.carrier \
          Set.range
            (alternatingLimitStream
              gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂) =
        ∅ :=
    Set.diff_eq_empty.mpr hno
  rw [hempty]
  exact Set.finite_empty

private theorem output_limitStream_at_forcedTime
    (gen : SetGenerator ℕ) (L₁ : Set ℕ)
    (K₂ : OrderedLanguage) (hL₁ : L₁.Infinite)
    (hgenerate₁ :
      GeneratesSetUnderFiniteContaminationOn gen L₁)
    (hgenerate₂ :
      GeneratesSetUnderFiniteContaminationOn gen K₂.carrier)
    (n : ℕ) :
    let state :=
      alternatingStates gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂ n
    let step :=
      chosenStep gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂ n state
    setOutput gen
        (alternatingLimitStream
          gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂)
        step.forcedTime ⊆
      L₁ := by
  dsimp only
  let state :=
    alternatingStates gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂ n
  let step :=
    chosenStep gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂ n state
  have houtputEq :
      setOutput gen
          (alternatingLimitStream
            gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂)
          step.forcedTime =
        setOutput gen
          (GenLimit.Generic.historyThenFallback step.next.history 0)
          step.forcedTime := by
    unfold setOutput
    congr 1
    funext i
    have hiNext : i.val < step.next.history.length :=
      lt_trans i.isLt step.forcedTime_lt_next
    rw [limitStream_eq_state_getElem
      gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂
      (n + 1) i.val (by
        simpa [alternatingStates, state, step] using hiNext)]
    simp [GenLimit.Generic.historyThenFallback, hiNext,
      alternatingStates, state, step]
  rw [houtputEq]
  exact step.forced_output_subset

private theorem frequently_limitOutput_subset
    (gen : SetGenerator ℕ) (L₁ : Set ℕ)
    (K₂ : OrderedLanguage) (hL₁ : L₁.Infinite)
    (hgenerate₁ :
      GeneratesSetUnderFiniteContaminationOn gen L₁)
    (hgenerate₂ :
      GeneratesSetUnderFiniteContaminationOn gen K₂.carrier) :
    ∃ᶠ t : ℕ in atTop,
      setOutput gen
        (alternatingLimitStream
          gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂) t ⊆ L₁ := by
  rw [Filter.frequently_atTop]
  intro cutoff
  let state :=
    alternatingStates
      gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂ cutoff
  let step :=
    chosenStep
      gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂ cutoff state
  refine ⟨step.forcedTime, ?_, ?_⟩
  · have hlen :=
      state_index_le_length
        gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂ cutoff
    exact hlen.trans
      (step.old_length_le_oddTime.trans
        (Nat.le_of_lt step.oddTime_lt_forcedTime))
  · exact
      output_limitStream_at_forcedTime
        gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂ cutoff

end FiniteContaminationNecessity

/-- Lemma 6.7's adaptive alternating-prefix adversary.  Under the finite
asymmetric-difference hypothesis, its limiting stream is a repetition-free
finite-noise, finite-omission presentation of `L₂`, while a cofinal set of
generator outputs is contained in `L₁`.

The construction also waits for correctness on each intervening `L₂`
completion, matching the source's alternating phases even though only the
`L₁` containment is needed by the final liminf argument. -/
theorem exists_finiteContamination_alternating_adversary
    (gen : SetGenerator ℕ)
    (L₁ : Set ℕ) (K₂ : OrderedLanguage)
    (hL₁ : L₁.Infinite)
    (hfinite : (L₁ \ K₂.carrier).Finite)
    (hgenerate₁ :
      GeneratesSetUnderFiniteContaminationOn gen L₁)
    (hgenerate₂ :
      GeneratesSetUnderFiniteContaminationOn gen K₂.carrier) :
    ∃ stream,
      FiniteNoiseFiniteOmissionEnumeration stream K₂.carrier ∧
      ∃ᶠ t : ℕ in atTop, setOutput gen stream t ⊆ L₁ := by
  let stream :=
    FiniteContaminationNecessity.alternatingLimitStream
      gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂
  refine ⟨stream, ?_, ?_⟩
  · exact
      FiniteContaminationNecessity.alternatingLimitStream_valid
        gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂ hfinite
  · exact
      FiniteContaminationNecessity.frequently_limitOutput_subset
        gen L₁ K₂ hL₁ hgenerate₁ hgenerate₂

/-- Necessity direction of Theorem 6.5, at the exact pair of targets used by
the source proof.  Any lower-density guarantee on `L₂` is bounded by the
ordered lower density of `L₁` inside `L₂` whenever `L₁ \ L₂` is finite.

This is only the necessity implication; no sufficiency claim is made. -/
theorem theorem_6_5_lowerDensity_necessity
    (gen : SetGenerator ℕ)
    (L₁ : Set ℕ) (K₂ : OrderedLanguage)
    (hL₁ : L₁.Infinite)
    (hfinite : (L₁ \ K₂.carrier).Finite)
    (hgenerate₁ :
      GeneratesSetUnderFiniteContaminationOn gen L₁)
    (hgenerate₂ :
      GeneratesSetUnderFiniteContaminationOn gen K₂.carrier)
    (c : ℝ)
    (hdensity₂ :
      GuaranteesSetBasedLowerDensityUnderFiniteContaminationOn
        gen K₂ c) :
    c ≤ K₂.lowerDensity L₁ := by
  obtain ⟨stream, hvalid, hfrequent⟩ :=
    exists_finiteContamination_alternating_adversary
      gen L₁ K₂ hL₁ hfinite hgenerate₁ hgenerate₂
  exact
    (hdensity₂ stream hvalid).trans
      (setBasedLowerDensity_le_of_frequently_subset
        gen K₂ stream L₁ hfrequent)

/-- Complete collection-level necessity direction of Theorem 6.5.  If one
generator succeeds under finite contamination and guarantees lower density
`c` on every ordered language in `𝓒`, then every ordered pair `L, L' ∈ 𝓒`
whose asymmetric difference `L.carrier \ L'.carrier` is finite satisfies the
paper's required lower-density bound.

This theorem is only the necessity direction; it makes no sufficiency
claim. -/
theorem theorem_6_5_lowerDensity_complete_necessity
    (gen : SetGenerator ℕ)
    (𝓒 : Set OrderedLanguage)
    (c : ℝ)
    (hgenerate :
      ∀ K ∈ 𝓒,
        GeneratesSetUnderFiniteContaminationOn gen K.carrier)
    (hdensity :
      ∀ K ∈ 𝓒,
        GuaranteesSetBasedLowerDensityUnderFiniteContaminationOn
          gen K c) :
    ∀ ⦃L L' : OrderedLanguage⦄,
      L ∈ 𝓒 →
      L' ∈ 𝓒 →
      (L.carrier \ L'.carrier).Finite →
      c ≤ L'.lowerDensity L.carrier := by
  intro L L' hL hL' hfinite
  exact
    theorem_6_5_lowerDensity_necessity
      gen L.carrier L'
      (orderedLanguage_carrier_infinite L)
      hfinite
      (hgenerate L hL)
      (hgenerate L' hL')
      c
      (hdensity L' hL')

end GenLimit.InfiniteContamination
