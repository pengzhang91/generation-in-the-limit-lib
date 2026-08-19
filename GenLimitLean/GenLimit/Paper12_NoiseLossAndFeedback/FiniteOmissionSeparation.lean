import GenLimit.Paper12_NoiseLossAndFeedback.NoSampleCharacterization
import GenLimit.Paper11_UnionClosednessOfLanguageGeneration.SweepGenerators

/-!
# Noise, Loss, and Feedback: the finite-omission hierarchy

Source: Bai--Panigrahi--Zhang, *Language Generation in the Limit:
Noise, Loss, and Feedback*, arXiv:2507.15319v2, Definitions 4.13--4.14,
Lemmas 4.16--4.17, and Theorem 4.15.

For each `i`, the source uses `i+1` marker integers, an eventually-positive
class containing all markers, and an always-negative class containing none
of them.  With at most `i` omissions, some marker from a first-class target
must eventually be observed, so a generator can switch from a negative sweep
to a positive sweep.  With `i+1` omissions, all markers can be hidden.  The
phase construction below then builds the source's limiting adversarial
enumeration.

The result is the full semantic separation.  No effectiveness or runtime
claim is made.
-/

namespace GenLimit.NoiseLossFeedback

open GenLimit.Generic

/-! ## Definitions 4.13--4.14 -/

/-- Definition 4.13: an injective no-noise stream whose range omits at most
`i` target values. -/
def EnumerationWithOmissionsAtMost
    (stream : Stream α) (L : GenLimit.Generic.Language α)
    (i : ℕ) : Prop :=
  Function.Injective stream ∧
    Set.range stream ⊆ L ∧
    GenLimit.Support.MissingAtMost
      L (Set.range stream) i

/-- Definition 4.14 at a fixed generator, in paper time: at time `t`,
`x₀,...,xₜ` have already been observed. -/
def IsLimitGeneratorWithOmissions
    (gen : Generator α) (C : LanguageClass α) (i : ℕ) : Prop :=
  ∀ L, L ∈ C → ∀ stream,
    EnumerationWithOmissionsAtMost stream L i →
      ∃ T, ∀ t, T ≤ t → CorrectAt gen L stream t

/-- Generatability in the limit with at most `i` omissions. -/
def GeneratableInLimitWithOmissions
    (C : LanguageClass α) (i : ℕ) : Prop :=
  ∃ gen : Generator α, IsLimitGeneratorWithOmissions gen C i

theorem enumerationWithOmissions_mono
    {stream : Stream α} {L : GenLimit.Generic.Language α}
    {i j : ℕ} (hij : i ≤ j)
    (h : EnumerationWithOmissionsAtMost stream L i) :
    EnumerationWithOmissionsAtMost stream L j :=
  ⟨h.1, h.2.1,
    GenLimit.Support.missingAtMost_mono hij h.2.2⟩

/-! ## The literal source witness `Cⁱ` -/

/-- The source's marker set `{0,...,i}`. -/
def omissionMarkerFinset (i : ℕ) : Finset ℤ :=
  (Finset.range (i + 1)).image Int.ofNat

theorem mem_omissionMarkerFinset_iff
    {i : ℕ} {z : ℤ} :
    z ∈ omissionMarkerFinset i ↔
      ∃ k < i + 1, Int.ofNat k = z := by
  simp [omissionMarkerFinset]

theorem omissionMarkerFinset_card (i : ℕ) :
    (omissionMarkerFinset i).card = i + 1 := by
  rw [omissionMarkerFinset, Finset.card_image_of_injective]
  · simp
  · intro a b hab
    exact Int.ofNat_inj.mp hab

theorem omissionMarker_nonnegative
    {i : ℕ} {z : ℤ}
    (hz : z ∈ omissionMarkerFinset i) :
    0 ≤ z := by
  obtain ⟨k, _hk, rfl⟩ :=
    mem_omissionMarkerFinset_iff.mp hz
  exact Int.ofNat_zero_le k

theorem negativeCode_not_marker
    (i k : ℕ) :
    GenLimit.UnionClosedness.negativeCode k ∉
      omissionMarkerFinset i := by
  intro hmem
  have hnonneg := omissionMarker_nonnegative hmem
  have hneg :=
    GenLimit.UnionClosedness.negativeCode_mem k
  exact (Int.not_lt_of_ge hnonneg) hneg

/-- The source's first class `C₁ⁱ`: all markers are present and the language
contains some positive integer tail `Pⱼ`.  Allowing the arbitrary set `A`
in the printed definition is extensionally equivalent to this condition. -/
def finiteOmissionFirstClass (i : ℕ) :
    LanguageClass ℤ :=
  {L |
    (↑(omissionMarkerFinset i) : Set ℤ) ⊆ L ∧
      ∃ j, GenLimit.UnionClosedness.positiveTail j ⊆ L}

/-- The source's second class `C₂ⁱ`: every negative integer is present and
none of the markers is present. -/
def finiteOmissionSecondClass (i : ℕ) :
    LanguageClass ℤ :=
  {L |
    GenLimit.UnionClosedness.negativeIntegers ⊆ L ∧
      Disjoint L (↑(omissionMarkerFinset i) : Set ℤ)}

/-- The source witness `Cⁱ = C₁ⁱ ∪ C₂ⁱ`. -/
def finiteOmissionClass (i : ℕ) :
    LanguageClass ℤ :=
  finiteOmissionFirstClass i ∪ finiteOmissionSecondClass i

theorem finiteOmissionClass_uus (i : ℕ) :
    GenLimit.Generic.UUS (finiteOmissionClass i) := by
  intro L hL
  rcases hL with hfirst | hsecond
  · obtain ⟨_hmarkers, j, htail⟩ := hfirst
    exact
      (GenLimit.UnionClosedness.positiveTail_infinite j).mono htail
  · exact
      GenLimit.UnionClosedness.negativeIntegers_infinite.mono
        hsecond.1

/-! ## Lemma 4.16: the upper bound with `i` omissions -/

/-- Some marker must appear in any at-most-`i`-omission stream for a target
containing all `i+1` markers. -/
theorem marker_mem_range_of_omissionsAtMost
    {i : ℕ} {stream : Stream ℤ}
    {L : GenLimit.Generic.Language ℤ}
    (henum : EnumerationWithOmissionsAtMost stream L i)
    (hmarkers : (↑(omissionMarkerFinset i) : Set ℤ) ⊆ L) :
    ∃ z, z ∈ omissionMarkerFinset i ∧
      z ∈ Set.range stream := by
  obtain ⟨F, hF, hcard⟩ := henum.2.2
  by_contra hnone
  push_neg at hnone
  have hsubset : omissionMarkerFinset i ⊆ F := by
    intro z hz
    have hzL := hmarkers hz
    have hznotRange := hnone z hz
    have hzDiff : z ∈ L \ Set.range stream :=
      ⟨hzL, hznotRange⟩
    change z ∈ (F : Set ℤ)
    rw [hF]
    exact hzDiff
  have hmarkersCard :
      i + 1 ≤ F.card := by
    rw [← omissionMarkerFinset_card i]
    exact Finset.card_le_card hsubset
  omega

theorem marker_eventually_observed
    {i : ℕ} {stream : Stream ℤ}
    {L : GenLimit.Generic.Language ℤ}
    (henum : EnumerationWithOmissionsAtMost stream L i)
    (hmarkers : (↑(omissionMarkerFinset i) : Set ℤ) ⊆ L) :
    ∃ T, ∀ t, T ≤ t →
      ((observedThrough stream t) ∩
        omissionMarkerFinset i).Nonempty := by
  obtain ⟨z, hzMarker, n, hn⟩ :=
    marker_mem_range_of_omissionsAtMost henum hmarkers
  refine ⟨n, ?_⟩
  intro t hnt
  refine ⟨z, ?_⟩
  rw [Finset.mem_inter]
  constructor
  · apply GenLimit.Generic.mem_sample_iff.mpr
    exact ⟨n, by omega, hn⟩
  · exact hzMarker

/-- The source's two-sided sweep, simplified extensionally: before a marker
appears use fresh negative integers; afterwards use fresh positive integers. -/
noncomputable def finiteOmissionSweepGenerator
    (i : ℕ) : Generator ℤ :=
  fun n xs =>
    if ((sequenceSample xs) ∩ omissionMarkerFinset i).Nonempty then
      GenLimit.UnionClosedness.ascendingPositiveGenerator n xs
    else
      GenLimit.UnionClosedness.descendingNegativeGenerator n xs

theorem finiteOmissionSweepGenerator_first_correct
    {i : ℕ} {L : GenLimit.Generic.Language ℤ}
    (hL : L ∈ finiteOmissionFirstClass i)
    {stream : Stream ℤ}
    (henum : EnumerationWithOmissionsAtMost stream L i) :
    ∃ T, ∀ t, T ≤ t →
      CorrectAt (finiteOmissionSweepGenerator i) L stream t := by
  obtain ⟨hmarkers, j, htail⟩ := hL
  obtain ⟨Td, hTd⟩ :=
    marker_eventually_observed henum hmarkers
  refine ⟨max Td j, ?_⟩
  intro t ht
  have hdetect :
      ((observedThrough stream t) ∩
        omissionMarkerFinset i).Nonempty :=
    hTd t (le_trans (Nat.le_max_left _ _) ht)
  have hsample :
      sequenceSample (fun k : Fin (t + 1) => stream k) =
        observedThrough stream t :=
    sequenceSample_prefix stream (t + 1)
  obtain ⟨n, hnTime, hout, hfresh⟩ :=
    GenLimit.UnionClosedness.ascendingPositiveGenerator_spec
      (fun k : Fin (t + 1) => stream k)
  have hnTail : j ≤ n := by
    have hjt : j ≤ t := le_trans (Nat.le_max_right _ _) ht
    omega
  have hpositiveTail :
      GenLimit.UnionClosedness.positiveCode n ∈
        GenLimit.UnionClosedness.positiveTail j := by
    refine ⟨n - j, ?_⟩
    apply Int.ofNat_inj.mpr
    omega
  have hbranch :
      finiteOmissionSweepGenerator i (t + 1)
          (fun k : Fin (t + 1) => stream k) =
        GenLimit.UnionClosedness.ascendingPositiveGenerator
          (t + 1) (fun k : Fin (t + 1) => stream k) := by
    simp [finiteOmissionSweepGenerator, hsample, hdetect]
  constructor
  · rw [outputAt, GenLimit.Generic.output, hbranch, hout]
    exact htail hpositiveTail
  · rw [outputAt, GenLimit.Generic.output, hbranch, hout]
    rw [← hsample]
    simpa only [hout] using hfresh

theorem finiteOmissionSweepGenerator_second_correct
    {i : ℕ} {L : GenLimit.Generic.Language ℤ}
    (hL : L ∈ finiteOmissionSecondClass i)
    {stream : Stream ℤ}
    (henum : EnumerationWithOmissionsAtMost stream L i) :
    ∃ T, ∀ t, T ≤ t →
      CorrectAt (finiteOmissionSweepGenerator i) L stream t := by
  refine ⟨0, ?_⟩
  intro t _ht
  have hnoMarker :
      ¬((observedThrough stream t) ∩
        omissionMarkerFinset i).Nonempty := by
    rintro ⟨z, hz⟩
    have hzObs := (Finset.mem_inter.mp hz).1
    have hzMarker := (Finset.mem_inter.mp hz).2
    obtain ⟨k, _hkt, hkz⟩ :=
      GenLimit.Generic.mem_sample_iff.mp hzObs
    have hzL : z ∈ L := henum.2.1 ⟨k, hkz⟩
    exact Set.disjoint_left.mp hL.2 hzL hzMarker
  have hsample :
      sequenceSample (fun k : Fin (t + 1) => stream k) =
        observedThrough stream t :=
    sequenceSample_prefix stream (t + 1)
  obtain ⟨n, _hnTime, hout, hfresh⟩ :=
    GenLimit.UnionClosedness.descendingNegativeGenerator_spec
      (fun k : Fin (t + 1) => stream k)
  have hbranch :
      finiteOmissionSweepGenerator i (t + 1)
          (fun k : Fin (t + 1) => stream k) =
        GenLimit.UnionClosedness.descendingNegativeGenerator
          (t + 1) (fun k : Fin (t + 1) => stream k) := by
    simp [finiteOmissionSweepGenerator, hsample, hnoMarker]
  constructor
  · rw [outputAt, GenLimit.Generic.output, hbranch, hout]
    exact hL.1 (GenLimit.UnionClosedness.negativeCode_mem n)
  · rw [outputAt, GenLimit.Generic.output, hbranch, hout]
    rw [← hsample]
    simpa only [hout] using hfresh

/-- Lemma 4.16: the source witness is generatable with `i` omissions. -/
theorem lemma_4_16 (i : ℕ) :
    GeneratableInLimitWithOmissions
      (finiteOmissionClass i) i := by
  refine ⟨finiteOmissionSweepGenerator i, ?_⟩
  intro L hL stream henum
  rcases hL with hfirst | hsecond
  · exact finiteOmissionSweepGenerator_first_correct hfirst henum
  · exact finiteOmissionSweepGenerator_second_correct hsecond henum

/-! ## Lemma 4.17: the nested adversarial phases -/

private def omissionListInput (l : List α) : Fin l.length → α :=
  fun k => l.get k

private theorem sequenceSample_omissionListInput
    [DecidableEq α] (l : List α) :
    sequenceSample (omissionListInput l) = l.toFinset := by
  classical
  ext x
  rw [GenLimit.Generic.mem_sequenceSample_iff, List.mem_toFinset]
  exact List.mem_iff_get.symm

private theorem exists_positiveTail_disjoint_finset
    (S : Finset ℤ) :
    ∃ d, Disjoint
      (GenLimit.UnionClosedness.positiveTail d)
      (S : Set ℤ) := by
  let badIndices : Set ℕ :=
    GenLimit.UnionClosedness.positiveCode ⁻¹' (S : Set ℤ)
  have hbadFinite : badIndices.Finite := by
    apply S.finite_toSet.preimage
    exact Set.injOn_of_injective
      GenLimit.UnionClosedness.positiveCode_injective
  obtain ⟨d, hd⟩ :=
    Finset.exists_nat_subset_range hbadFinite.toFinset
  refine ⟨d, ?_⟩
  rw [Set.disjoint_left]
  intro z hzTail hzS
  obtain ⟨k, rfl⟩ := hzTail
  have hmem :
      d + k ∈ hbadFinite.toFinset := by
    rw [Set.Finite.mem_toFinset]
    exact hzS
  have hlt : d + k < d := by
    simpa using hd hmem
  omega

/-- The finite state retained after `n` completed adversarial phases. -/
structure FiniteOmissionPhaseState (i n : ℕ) where
  history : List ℤ
  forbidden : Finset ℤ
  history_nodup : history.Nodup
  history_marker_disjoint :
    Disjoint history.toFinset (omissionMarkerFinset i)
  history_forbidden_disjoint :
    Disjoint history.toFinset forbidden
  forbidden_nonnegative :
    ∀ z, z ∈ forbidden → 0 ≤ z
  negative_mem_history_iff :
    ∀ k,
      GenLimit.UnionClosedness.negativeCode k ∈ history ↔
        k < n

/-- The empty state before phase zero. -/
def initialFiniteOmissionPhaseState (i : ℕ) :
    FiniteOmissionPhaseState i 0 where
  history := []
  forbidden := ∅
  history_nodup := by simp
  history_marker_disjoint := by simp
  history_forbidden_disjoint := by simp
  forbidden_nonnegative := by simp
  negative_mem_history_iff := by simp

/-- One successful source phase.  Its endpoint extends the old history,
adds the next negative integer, and permanently records one generator output
that is absent from the new history. -/
structure SuccessfulFiniteOmissionPhase
    (G : Generator ℤ) (i n : ℕ)
    (state : FiniteOmissionPhaseState i n) where
  next : FiniteOmissionPhaseState i (n + 1)
  extends_history : state.history <+: next.history
  strict_growth : state.history.length < next.history.length
  forbidden_subset : state.forbidden ⊆ next.forbidden
  failureTime : ℕ
  old_length_le_failureTime :
    state.history.length ≤ failureTime
  failureTime_lt_next : failureTime < next.history.length
  badOutput : ℤ
  bad_mem_forbidden : badOutput ∈ next.forbidden
  output_on_next :
    G (failureTime + 1)
        (fun k =>
          next.history.get
            ⟨k, lt_of_lt_of_le k.isLt
              (Nat.succ_le_iff.mpr failureTime_lt_next)⟩) =
      badOutput

private theorem positiveTail_disjoint_negativeIntegers
    (d : ℕ) :
    Disjoint
      (GenLimit.UnionClosedness.positiveTail d)
      GenLimit.UnionClosedness.negativeIntegers := by
  rw [Set.disjoint_left]
  intro z hzTail hzNeg
  obtain ⟨k, rfl⟩ := hzTail
  have hpos :=
    GenLimit.UnionClosedness.positiveCode_mem (d + k)
  exact (Int.not_lt_of_ge (Int.le_of_lt hpos)) hzNeg

private theorem list_prefix_membership
    {l l' : List α} (hprefix : l <+: l')
    {x : α} (hx : x ∈ l) :
    x ∈ l' :=
  hprefix.subset hx

private theorem exists_successfulFiniteOmissionPhase
    (G : Generator ℤ) (i n : ℕ)
    (hG :
      IsLimitGeneratorWithOmissions G
        (finiteOmissionClass i) (i + 1))
    (state : FiniteOmissionPhaseState i n) :
    Nonempty (SuccessfulFiniteOmissionPhase G i n state) := by
  classical
  let blocked :=
    state.history.toFinset ∪ state.forbidden ∪
      omissionMarkerFinset i
  obtain ⟨d, htailBlocked⟩ :=
    exists_positiveTail_disjoint_finset blocked
  let tail := GenLimit.UnionClosedness.positiveTail d
  have htailHistory :
      Disjoint tail (state.history.toFinset : Set ℤ) := by
    rw [Set.disjoint_left] at htailBlocked ⊢
    intro z hzTail hz
    apply htailBlocked hzTail
    change z ∈ blocked
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hz)
  have htailForbidden :
      Disjoint tail (state.forbidden : Set ℤ) := by
    rw [Set.disjoint_left] at htailBlocked ⊢
    intro z hzTail hz
    apply htailBlocked hzTail
    change z ∈ blocked
    exact Finset.mem_union_left _
      (Finset.mem_union_right _ hz)
  have htailMarkers :
      Disjoint tail (omissionMarkerFinset i : Set ℤ) := by
    rw [Set.disjoint_left] at htailBlocked ⊢
    intro z hzTail hz
    apply htailBlocked hzTail
    change z ∈ blocked
    exact Finset.mem_union_right _ hz
  have hhistorySample :
      sequenceSample (omissionListInput state.history) =
        state.history.toFinset :=
    sequenceSample_omissionListInput state.history
  let hrest :
      (tail \
        (sequenceSample (omissionListInput state.history) : Set ℤ)).Infinite :=
    (GenLimit.UnionClosedness.positiveTail_infinite d).diff
      (sequenceSample
        (omissionListInput state.history)).finite_toSet
  let full : Stream ℤ :=
    prefixThenTarget (omissionListInput state.history) tail hrest
  have hhistoryGetInjective :
      Function.Injective (omissionListInput state.history) := by
    exact List.nodup_iff_injective_get.mp state.history_nodup
  have hfullInjective :
      Function.Injective full :=
    prefixThenTarget_injective hhistoryGetInjective tail hrest
  have hrange :
      Set.range full =
        (state.history.toFinset : Set ℤ) ∪ tail := by
    have h :=
      range_prefixThenTarget_eq_prefix_union
        (omissionListInput state.history) tail hrest
    simpa [full, hhistorySample] using h
  let target : Set ℤ :=
    (omissionMarkerFinset i : Set ℤ) ∪
      (state.history.toFinset : Set ℤ) ∪ tail
  have htargetFirst :
      target ∈ finiteOmissionFirstClass i := by
    refine ⟨?_, d, ?_⟩
    · intro z hz
      exact Set.mem_union_left tail
        (Set.mem_union_left _ hz)
    · intro z hz
      exact Set.mem_union_right _ hz
  have hmarkerRangeDisjoint :
      Disjoint (omissionMarkerFinset i : Set ℤ)
        (Set.range full) := by
    rw [Set.disjoint_left]
    intro z hzMarker hzRange
    rw [hrange] at hzRange
    rcases hzRange with hzHistory | hzTail
    · exact Finset.disjoint_left.mp
        state.history_marker_disjoint hzHistory hzMarker
    · exact Set.disjoint_left.mp htailMarkers
        hzTail hzMarker
  have htargetDiff :
      target \ Set.range full =
        (omissionMarkerFinset i : Set ℤ) := by
    apply Set.Subset.antisymm
    · rintro z ⟨hzTarget, hznotRange⟩
      rcases hzTarget with hzInitial | hzTail
      · rcases hzInitial with hzMarker | hzHistory
        · exact hzMarker
        · exact False.elim
            (hznotRange (hrange.symm ▸ Set.mem_union_left _ hzHistory))
      · exact False.elim
          (hznotRange (hrange.symm ▸ Set.mem_union_right _ hzTail))
    · intro z hzMarker
      refine
        ⟨Set.mem_union_left tail
          (Set.mem_union_left _ hzMarker), ?_⟩
      exact Set.disjoint_left.mp hmarkerRangeDisjoint hzMarker
  have hfullEnum :
      EnumerationWithOmissionsAtMost full target (i + 1) := by
    refine ⟨hfullInjective, ?_, ?_⟩
    · rw [hrange]
      intro z hz
      rcases hz with hzHistory | hzTail
      · exact Set.mem_union_left tail
          (Set.mem_union_right _ hzHistory)
      · exact Set.mem_union_right _ hzTail
    · refine ⟨omissionMarkerFinset i, ?_, ?_⟩
      · exact htargetDiff.symm
      · rw [omissionMarkerFinset_card]
  obtain ⟨T, hT⟩ :=
    hG target (Set.mem_union_left _ htargetFirst) full hfullEnum
  let t := max T state.history.length
  have hTt : T ≤ t := Nat.le_max_left _ _
  have hhistoryLenT : state.history.length ≤ t :=
    Nat.le_max_right _ _
  have hcorrect : CorrectAt G target full t :=
    hT t hTt
  let phasePrefix : List ℤ :=
    List.ofFn (fun k : Fin (t + 1) => full k)
  let y : ℤ := outputAt G full t
  let nextHistory : List ℤ :=
    phasePrefix ++ [GenLimit.UnionClosedness.negativeCode n]
  let nextForbidden : Finset ℤ :=
    insert y state.forbidden
  have hprefixLength : phasePrefix.length = t + 1 := by
    simp [phasePrefix]
  have hprefixNodup : phasePrefix.Nodup := by
    rw [List.nodup_iff_injective_getElem]
    intro a b hab
    apply Fin.ext
    apply hfullInjective
    simpa only [phasePrefix, List.getElem_ofFn] using hab
  have hhistoryPrefix : state.history <+: phasePrefix := by
    apply List.prefix_iff_getElem.mpr
    refine ⟨by rw [hprefixLength]; omega, ?_⟩
    intro k hk
    simp only [phasePrefix, List.getElem_ofFn]
    exact
      (prefixThenTarget_prefix
        (omissionListInput state.history) tail hrest
        ⟨k, hk⟩).symm
  have hprefixSubsetRange :
      (phasePrefix.toFinset : Set ℤ) ⊆ Set.range full := by
    intro z hz
    change z ∈ phasePrefix.toFinset at hz
    rw [List.mem_toFinset] at hz
    dsimp only [phasePrefix] at hz
    rw [List.mem_ofFn] at hz
    obtain ⟨k, hk⟩ := hz
    exact ⟨k, hk⟩
  have hyNotPrefix : y ∉ phasePrefix := by
    intro hy
    apply hcorrect.2
    rw [observedThrough, GenLimit.Generic.mem_sample_iff]
    dsimp only [phasePrefix] at hy
    rw [List.mem_ofFn] at hy
    obtain ⟨k, hk⟩ := hy
    exact ⟨k, k.isLt, hk⟩
  have hyTarget : y ∈ target := hcorrect.1
  have hyNonnegative : 0 ≤ y := by
    rcases hyTarget with hyInitial | hyTail
    · rcases hyInitial with hyMarker | hyHistory
      · exact omissionMarker_nonnegative hyMarker
      · exact False.elim
          (hyNotPrefix
            (hhistoryPrefix.subset
              (List.mem_toFinset.mp hyHistory)))
    · obtain ⟨k, hk⟩ := hyTail
      rw [← hk]
      exact Int.le_of_lt
        (GenLimit.UnionClosedness.positiveCode_mem (d + k))
  have hnextNegativeNotPrefix :
      GenLimit.UnionClosedness.negativeCode n ∉ phasePrefix := by
    intro hnegPrefix
    have hnegRange :=
      hprefixSubsetRange (List.mem_toFinset.mpr hnegPrefix)
    rw [hrange] at hnegRange
    rcases hnegRange with hnegHistory | hnegTail
    · have := (state.negative_mem_history_iff n).mp
        (List.mem_toFinset.mp hnegHistory)
      omega
    · exact
        Set.disjoint_left.mp
          (positiveTail_disjoint_negativeIntegers d)
          hnegTail
          (GenLimit.UnionClosedness.negativeCode_mem n)
  have hnextHistoryNodup : nextHistory.Nodup := by
    dsimp only [nextHistory]
    rw [List.nodup_append]
    refine ⟨hprefixNodup, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst b
    exact fun hab => hnextNegativeNotPrefix (hab ▸ ha)
  have hfullForbiddenDisjoint :
      Disjoint (Set.range full) (state.forbidden : Set ℤ) := by
    rw [Set.disjoint_left]
    intro z hzRange hzForbidden
    rw [hrange] at hzRange
    rcases hzRange with hzHistory | hzTail
    · exact Finset.disjoint_left.mp
        state.history_forbidden_disjoint hzHistory hzForbidden
    · exact Set.disjoint_left.mp htailForbidden
        hzTail hzForbidden
  have hprefixOldForbidden :
      Disjoint phasePrefix.toFinset state.forbidden := by
    rw [Finset.disjoint_left]
    intro z hzPrefix hzForbidden
    exact Set.disjoint_left.mp hfullForbiddenDisjoint
      (hprefixSubsetRange hzPrefix) hzForbidden
  have hnegativeOldForbidden :
      GenLimit.UnionClosedness.negativeCode n ∉ state.forbidden := by
    intro hmem
    have hnonneg := state.forbidden_nonnegative _ hmem
    exact (Int.not_lt_of_ge hnonneg)
      (GenLimit.UnionClosedness.negativeCode_mem n)
  have hnegativeNeY :
      GenLimit.UnionClosedness.negativeCode n ≠ y := by
    intro heq
    rw [← heq] at hyNonnegative
    exact (Int.not_lt_of_ge hyNonnegative)
      (GenLimit.UnionClosedness.negativeCode_mem n)
  have hnextMarkerDisjoint :
      Disjoint nextHistory.toFinset
        (omissionMarkerFinset i) := by
    rw [Finset.disjoint_left]
    intro z hzNext hzMarker
    rw [List.mem_toFinset] at hzNext
    simp only [nextHistory, List.mem_append, List.mem_singleton] at hzNext
    rcases hzNext with hzPrefix | rfl
    · have hzRange :=
        hprefixSubsetRange (List.mem_toFinset.mpr hzPrefix)
      exact Set.disjoint_left.mp hmarkerRangeDisjoint hzMarker hzRange
    · exact negativeCode_not_marker i n hzMarker
  have hnextForbiddenDisjoint :
      Disjoint nextHistory.toFinset nextForbidden := by
    rw [Finset.disjoint_left]
    intro z hzNext hzForbidden
    rw [Finset.mem_insert] at hzForbidden
    rw [List.mem_toFinset] at hzNext
    simp only [nextHistory, List.mem_append, List.mem_singleton] at hzNext
    rcases hzNext with hzPrefix | rfl
    · rcases hzForbidden with rfl | hzOld
      · exact hyNotPrefix hzPrefix
      · exact Finset.disjoint_left.mp hprefixOldForbidden
          (List.mem_toFinset.mpr hzPrefix) hzOld
    · rcases hzForbidden with heq | hzOld
      · exact hnegativeNeY heq
      · exact hnegativeOldForbidden hzOld
  have hnextNegativeIff :
      ∀ k,
        GenLimit.UnionClosedness.negativeCode k ∈ nextHistory ↔
          k < n + 1 := by
    intro k
    constructor
    · intro hk
      simp only [nextHistory, List.mem_append,
        List.mem_singleton] at hk
      rcases hk with hkPrefix | hkEq
      · have hkRange :=
          hprefixSubsetRange (List.mem_toFinset.mpr hkPrefix)
        rw [hrange] at hkRange
        rcases hkRange with hkHistory | hkTail
        · have hkn :=
            (state.negative_mem_history_iff k).mp
              (List.mem_toFinset.mp hkHistory)
          omega
        · exact False.elim
            (Set.disjoint_left.mp
              (positiveTail_disjoint_negativeIntegers d)
              hkTail
              (GenLimit.UnionClosedness.negativeCode_mem k))
      · have hkn : k = n :=
          GenLimit.UnionClosedness.negativeCode_injective hkEq
        omega
    · intro hk
      have hcases : k < n ∨ k = n := by omega
      rcases hcases with hlt | rfl
      · apply List.mem_append_left
        apply hhistoryPrefix.subset
        exact
          (state.negative_mem_history_iff k).mpr hlt
      · simp [nextHistory]
  let next : FiniteOmissionPhaseState i (n + 1) :=
    { history := nextHistory
      forbidden := nextForbidden
      history_nodup := hnextHistoryNodup
      history_marker_disjoint := hnextMarkerDisjoint
      history_forbidden_disjoint := hnextForbiddenDisjoint
      forbidden_nonnegative := by
        intro z hz
        rw [Finset.mem_insert] at hz
        exact hz.elim (fun h => h ▸ hyNonnegative)
          (state.forbidden_nonnegative z)
      negative_mem_history_iff := hnextNegativeIff }
  have houtputOnNext :
      G (t + 1)
          (fun k =>
            next.history.get
              ⟨k, by
                dsimp [next, nextHistory]
                simp [hprefixLength]
                omega⟩) =
        y := by
    change
      G (t + 1)
          (fun k =>
            nextHistory.get
              ⟨k, by
                simp [nextHistory, hprefixLength]
                omega⟩) =
        outputAt G full t
    unfold outputAt GenLimit.Generic.output
    congr 1
    funext k
    have hkPrefix : k.val < phasePrefix.length := by
      rw [hprefixLength]
      exact k.isLt
    simp only [nextHistory, List.get_eq_getElem]
    rw [List.getElem_append_left hkPrefix]
    simp only [phasePrefix, List.getElem_ofFn]
  refine ⟨{
    next := next
    extends_history :=
      hhistoryPrefix.trans (List.prefix_append phasePrefix _)
    strict_growth := by
      dsimp [next, nextHistory]
      simp [hprefixLength]
      omega
    forbidden_subset := by
      intro z hz
      exact Finset.mem_insert_of_mem hz
    failureTime := t
    old_length_le_failureTime := hhistoryLenT
    failureTime_lt_next := by
      dsimp [next, nextHistory]
      simp [hprefixLength]
      omega
    badOutput := y
    bad_mem_forbidden := by
      dsimp [next, nextForbidden]
      exact Finset.mem_insert_self _ _
    output_on_next := houtputOnNext
  }⟩

/-! ### Iterating the source phases -/

private noncomputable def finiteOmissionPhase
    (G : Generator ℤ) (i n : ℕ)
    (hG :
      IsLimitGeneratorWithOmissions G
        (finiteOmissionClass i) (i + 1))
    (state : FiniteOmissionPhaseState i n) :
    SuccessfulFiniteOmissionPhase G i n state :=
  Classical.choice
    (exists_successfulFiniteOmissionPhase G i n hG state)

private noncomputable def finiteOmissionPhaseState
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithOmissions G
        (finiteOmissionClass i) (i + 1)) :
    (n : ℕ) → FiniteOmissionPhaseState i n
  | 0 => initialFiniteOmissionPhaseState i
  | n + 1 =>
      (finiteOmissionPhase G i n hG
        (finiteOmissionPhaseState G i hG n)).next

private theorem finiteOmissionPhaseState_prefix_succ
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithOmissions G
        (finiteOmissionClass i) (i + 1))
    (n : ℕ) :
    (finiteOmissionPhaseState G i hG n).history <+:
      (finiteOmissionPhaseState G i hG (n + 1)).history := by
  rw [finiteOmissionPhaseState]
  exact
    (finiteOmissionPhase G i n hG
      (finiteOmissionPhaseState G i hG n)).extends_history

private theorem finiteOmissionPhaseState_prefix
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithOmissions G
        (finiteOmissionClass i) (i + 1))
    {n m : ℕ} (hnm : n ≤ m) :
    (finiteOmissionPhaseState G i hG n).history <+:
      (finiteOmissionPhaseState G i hG m).history := by
  induction m, hnm using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ m _ ih =>
      exact ih.trans
        (finiteOmissionPhaseState_prefix_succ G i hG m)

private theorem finiteOmissionPhaseState_length
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithOmissions G
        (finiteOmissionClass i) (i + 1))
    (n : ℕ) :
    n ≤ (finiteOmissionPhaseState G i hG n).history.length := by
  induction n with
  | zero =>
      simp [finiteOmissionPhaseState,
        initialFiniteOmissionPhaseState]
  | succ n ih =>
      have hstep :=
        (finiteOmissionPhase G i n hG
          (finiteOmissionPhaseState G i hG n)).strict_growth
      rw [finiteOmissionPhaseState]
      omega

private theorem finiteOmissionPhaseState_forbidden_succ
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithOmissions G
        (finiteOmissionClass i) (i + 1))
    (n : ℕ) :
    (finiteOmissionPhaseState G i hG n).forbidden ⊆
      (finiteOmissionPhaseState G i hG (n + 1)).forbidden := by
  rw [finiteOmissionPhaseState]
  exact
    (finiteOmissionPhase G i n hG
      (finiteOmissionPhaseState G i hG n)).forbidden_subset

private theorem finiteOmissionPhaseState_forbidden_mono
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithOmissions G
        (finiteOmissionClass i) (i + 1))
    {n m : ℕ} (hnm : n ≤ m) :
    (finiteOmissionPhaseState G i hG n).forbidden ⊆
      (finiteOmissionPhaseState G i hG m).forbidden := by
  induction m, hnm using Nat.le_induction with
  | base => exact fun _ hx => hx
  | succ m _ ih =>
      exact fun z hz =>
        finiteOmissionPhaseState_forbidden_succ G i hG m
          (ih hz)

private noncomputable def finiteOmissionFailureTime
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithOmissions G
        (finiteOmissionClass i) (i + 1))
    (n : ℕ) : ℕ :=
  (finiteOmissionPhase G i n hG
    (finiteOmissionPhaseState G i hG n)).failureTime

private noncomputable def finiteOmissionBadOutput
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithOmissions G
        (finiteOmissionClass i) (i + 1))
    (n : ℕ) : ℤ :=
  (finiteOmissionPhase G i n hG
    (finiteOmissionPhaseState G i hG n)).badOutput

private theorem finiteOmissionFailureTime_ge_stage
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithOmissions G
        (finiteOmissionClass i) (i + 1))
    (n : ℕ) :
    n ≤ finiteOmissionFailureTime G i hG n := by
  exact
    (finiteOmissionPhaseState_length G i hG n).trans
      (finiteOmissionPhase G i n hG
        (finiteOmissionPhaseState G i hG n)).old_length_le_failureTime

private theorem finiteOmissionBadOutput_mem_nextForbidden
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithOmissions G
        (finiteOmissionClass i) (i + 1))
    (n : ℕ) :
    finiteOmissionBadOutput G i hG n ∈
      (finiteOmissionPhaseState G i hG (n + 1)).forbidden := by
  rw [finiteOmissionPhaseState]
  exact
    (finiteOmissionPhase G i n hG
      (finiteOmissionPhaseState G i hG n)).bad_mem_forbidden

private theorem finiteOmissionBadOutput_not_mem_nextHistory
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithOmissions G
        (finiteOmissionClass i) (i + 1))
    (n : ℕ) :
    finiteOmissionBadOutput G i hG n ∉
      (finiteOmissionPhaseState G i hG (n + 1)).history := by
  intro hmem
  exact Finset.disjoint_left.mp
    (finiteOmissionPhaseState G i hG
      (n + 1)).history_forbidden_disjoint
    (List.mem_toFinset.mpr hmem)
    (finiteOmissionBadOutput_mem_nextForbidden G i hG n)

private theorem finiteOmissionBadOutput_not_mem_laterHistory
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithOmissions G
        (finiteOmissionClass i) (i + 1))
    (n m : ℕ) (hnm : n + 1 ≤ m) :
    finiteOmissionBadOutput G i hG n ∉
      (finiteOmissionPhaseState G i hG m).history := by
  intro hmem
  have hbadForbidden :
      finiteOmissionBadOutput G i hG n ∈
        (finiteOmissionPhaseState G i hG m).forbidden :=
    finiteOmissionPhaseState_forbidden_mono G i hG hnm
      (finiteOmissionBadOutput_mem_nextForbidden G i hG n)
  exact Finset.disjoint_left.mp
    (finiteOmissionPhaseState G i hG m).history_forbidden_disjoint
    (List.mem_toFinset.mpr hmem) hbadForbidden

private theorem finiteOmissionBadOutput_not_mem_history
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithOmissions G
        (finiteOmissionClass i) (i + 1))
    (n m : ℕ) :
    finiteOmissionBadOutput G i hG n ∉
      (finiteOmissionPhaseState G i hG m).history := by
  rcases le_total m (n + 1) with hmn | hnm
  · intro hmem
    exact finiteOmissionBadOutput_not_mem_nextHistory G i hG n
      ((finiteOmissionPhaseState_prefix G i hG hmn).subset hmem)
  · exact finiteOmissionBadOutput_not_mem_laterHistory
      G i hG n m hnm

/-! ### The limiting adversarial enumeration -/

private noncomputable def finiteOmissionFinalStream
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithOmissions G
        (finiteOmissionClass i) (i + 1)) :
    Stream ℤ :=
  fun k =>
    let history :=
      (finiteOmissionPhaseState G i hG (k + 1)).history
    history.get ⟨k, by
      have hlen :=
        finiteOmissionPhaseState_length G i hG (k + 1)
      exact lt_of_lt_of_le (Nat.lt_succ_self k) hlen⟩

private theorem finiteOmissionFinalStream_eq_history_get
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithOmissions G
        (finiteOmissionClass i) (i + 1))
    (n k : ℕ)
    (hk :
      k <
        (finiteOmissionPhaseState G i hG n).history.length) :
    finiteOmissionFinalStream G i hG k =
      (finiteOmissionPhaseState G i hG n).history.get
        ⟨k, hk⟩ := by
  rw [finiteOmissionFinalStream]
  have hbound :
      k <
        (finiteOmissionPhaseState G i hG
          (k + 1)).history.length := by
    have hlen :=
      finiteOmissionPhaseState_length G i hG (k + 1)
    omega
  rw [List.get_eq_getElem, List.get_eq_getElem]
  rcases le_total (k + 1) n with hkn | hnk
  · exact
      (List.prefix_iff_getElem.mp
        (finiteOmissionPhaseState_prefix G i hG hkn)).2
          k hbound
  · exact
      ((List.prefix_iff_getElem.mp
        (finiteOmissionPhaseState_prefix G i hG hnk)).2
          k hk).symm

private theorem finiteOmissionHistory_subset_finalRange
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithOmissions G
        (finiteOmissionClass i) (i + 1))
    (n : ℕ) :
    (↑(finiteOmissionPhaseState G i hG n).history.toFinset :
        Set ℤ) ⊆
      Set.range (finiteOmissionFinalStream G i hG) := by
  intro x hx
  change
    x ∈ (finiteOmissionPhaseState G i hG n).history.toFinset
      at hx
  rw [List.mem_toFinset] at hx
  obtain ⟨k, hk⟩ := List.mem_iff_get.mp hx
  refine ⟨k, ?_⟩
  exact
    (finiteOmissionFinalStream_eq_history_get
      G i hG n k k.isLt).trans hk

private theorem finiteOmissionFinalStream_injective
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithOmissions G
        (finiteOmissionClass i) (i + 1)) :
    Function.Injective (finiteOmissionFinalStream G i hG) := by
  intro a b hab
  let n := max a b + 1
  have ha :
      a <
        (finiteOmissionPhaseState G i hG n).history.length := by
    have hlen := finiteOmissionPhaseState_length G i hG n
    dsimp only [n] at hlen ⊢
    omega
  have hb :
      b <
        (finiteOmissionPhaseState G i hG n).history.length := by
    have hlen := finiteOmissionPhaseState_length G i hG n
    dsimp only [n] at hlen ⊢
    omega
  have hget :
      (finiteOmissionPhaseState G i hG n).history.get
          ⟨a, ha⟩ =
        (finiteOmissionPhaseState G i hG n).history.get
          ⟨b, hb⟩ := by
    exact
      (finiteOmissionFinalStream_eq_history_get
        G i hG n a ha).symm.trans
        (hab.trans
          (finiteOmissionFinalStream_eq_history_get
            G i hG n b hb))
  have hfin :
      (⟨a, ha⟩ :
        Fin
          (finiteOmissionPhaseState G i hG n).history.length) =
        ⟨b, hb⟩ :=
    (List.nodup_iff_injective_get.mp
      (finiteOmissionPhaseState G i hG n).history_nodup)
        hget
  exact congrArg Fin.val hfin

private theorem finiteOmissionNegative_mem_nextHistory
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithOmissions G
        (finiteOmissionClass i) (i + 1))
    (n : ℕ) :
    GenLimit.UnionClosedness.negativeCode n ∈
      (finiteOmissionPhaseState G i hG (n + 1)).history := by
  exact
    ((finiteOmissionPhaseState G i hG
      (n + 1)).negative_mem_history_iff n).mpr
        (Nat.lt_succ_self n)

private theorem finiteOmissionNegative_subset_finalRange
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithOmissions G
        (finiteOmissionClass i) (i + 1)) :
    GenLimit.UnionClosedness.negativeIntegers ⊆
      Set.range (finiteOmissionFinalStream G i hG) := by
  rw [← GenLimit.UnionClosedness.range_negativeCode]
  rintro _ ⟨n, rfl⟩
  exact
    finiteOmissionHistory_subset_finalRange G i hG (n + 1)
      (List.mem_toFinset.mpr
        (finiteOmissionNegative_mem_nextHistory G i hG n))

private theorem finiteOmissionFinalRange_marker_disjoint
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithOmissions G
        (finiteOmissionClass i) (i + 1)) :
    Disjoint
      (Set.range (finiteOmissionFinalStream G i hG))
      (↑(omissionMarkerFinset i) : Set ℤ) := by
  rw [Set.disjoint_left]
  rintro z ⟨k, rfl⟩ hzMarker
  have hbound :
      k <
        (finiteOmissionPhaseState G i hG
          (k + 1)).history.length := by
    have hlen :=
      finiteOmissionPhaseState_length G i hG (k + 1)
    omega
  have hmem :
      finiteOmissionFinalStream G i hG k ∈
        (finiteOmissionPhaseState G i hG
          (k + 1)).history := by
    rw [finiteOmissionFinalStream_eq_history_get
      G i hG (k + 1) k hbound]
    exact List.get_mem _ _
  exact Finset.disjoint_left.mp
    (finiteOmissionPhaseState G i hG
      (k + 1)).history_marker_disjoint
    (List.mem_toFinset.mpr hmem) hzMarker

private theorem finiteOmissionFinalLanguage_mem_class
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithOmissions G
        (finiteOmissionClass i) (i + 1)) :
    Set.range (finiteOmissionFinalStream G i hG) ∈
      finiteOmissionClass i := by
  apply Set.mem_union_right
  exact
    ⟨finiteOmissionNegative_subset_finalRange G i hG,
      finiteOmissionFinalRange_marker_disjoint G i hG⟩

private theorem finiteOmissionFinalStream_enumerates_range
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithOmissions G
        (finiteOmissionClass i) (i + 1)) :
    EnumerationWithOmissionsAtMost
      (finiteOmissionFinalStream G i hG)
      (Set.range (finiteOmissionFinalStream G i hG))
      (i + 1) := by
  refine
    ⟨finiteOmissionFinalStream_injective G i hG,
      Set.Subset.rfl, ?_⟩
  refine ⟨∅, ?_, by simp⟩
  ext z
  simp

private theorem finiteOmissionFailureTime_lt_nextHistory
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithOmissions G
        (finiteOmissionClass i) (i + 1))
    (n : ℕ) :
    finiteOmissionFailureTime G i hG n <
      (finiteOmissionPhaseState G i hG (n + 1)).history.length := by
  rw [finiteOmissionFailureTime, finiteOmissionPhaseState]
  exact
    (finiteOmissionPhase G i n hG
      (finiteOmissionPhaseState G i hG n)).failureTime_lt_next

private theorem finiteOmissionBadOutput_eq_outputAt_final
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithOmissions G
        (finiteOmissionClass i) (i + 1))
    (n : ℕ) :
    outputAt G (finiteOmissionFinalStream G i hG)
        (finiteOmissionFailureTime G i hG n) =
      finiteOmissionBadOutput G i hG n := by
  unfold outputAt
  change
    G
        ((finiteOmissionPhase G i n hG
          (finiteOmissionPhaseState G i hG n)).failureTime + 1)
        (fun k => finiteOmissionFinalStream G i hG k) =
      (finiteOmissionPhase G i n hG
        (finiteOmissionPhaseState G i hG n)).badOutput
  convert
    (finiteOmissionPhase G i n hG
      (finiteOmissionPhaseState G i hG n)).output_on_next
      using 1
  congr 1
  funext k
  have hkHistory :
      k.val <
        (finiteOmissionPhaseState G i hG
          (n + 1)).history.length := by
    exact lt_of_lt_of_le k.isLt
      (Nat.succ_le_iff.mpr
        (finiteOmissionFailureTime_lt_nextHistory
          G i hG n))
  have heq :=
    finiteOmissionFinalStream_eq_history_get
      G i hG (n + 1) k hkHistory
  exact heq

private theorem finiteOmissionBadOutput_not_mem_finalRange
    (G : Generator ℤ) (i : ℕ)
    (hG :
      IsLimitGeneratorWithOmissions G
        (finiteOmissionClass i) (i + 1))
    (n : ℕ) :
    finiteOmissionBadOutput G i hG n ∉
      Set.range (finiteOmissionFinalStream G i hG) := by
  rintro ⟨k, hk⟩
  apply finiteOmissionBadOutput_not_mem_history
    G i hG n (k + 1)
  have hbound :
      k <
        (finiteOmissionPhaseState G i hG
          (k + 1)).history.length := by
    have hlen :=
      finiteOmissionPhaseState_length G i hG (k + 1)
    omega
  apply List.mem_iff_get.mpr
  refine ⟨⟨k, hbound⟩, ?_⟩
  exact
    (finiteOmissionFinalStream_eq_history_get
      G i hG (k + 1) k hbound).symm.trans hk

/-! ## Lemma 4.17 and Theorem 4.15 -/

/-- Lemma 4.17: no generator succeeds on the source witness when all
`i+1` markers may be omitted.  The final stream is the union of the nested
finite phases above; it enumerates a second-class target exactly, while every
phase contributes a later incorrect output. -/
theorem lemma_4_17 (i : ℕ) :
    ¬ GeneratableInLimitWithOmissions
      (finiteOmissionClass i) (i + 1) := by
  rintro ⟨G, hG⟩
  let stream := finiteOmissionFinalStream G i hG
  let target : Set ℤ := Set.range stream
  have htarget :
      target ∈ finiteOmissionClass i := by
    exact finiteOmissionFinalLanguage_mem_class G i hG
  have henum :
      EnumerationWithOmissionsAtMost stream target (i + 1) := by
    exact finiteOmissionFinalStream_enumerates_range G i hG
  obtain ⟨T, hT⟩ := hG target htarget stream henum
  have hlate :
      T ≤ finiteOmissionFailureTime G i hG T :=
    finiteOmissionFailureTime_ge_stage G i hG T
  have hcorrect :
      CorrectAt G target stream
        (finiteOmissionFailureTime G i hG T) :=
    hT _ hlate
  have houtput :
      outputAt G stream
          (finiteOmissionFailureTime G i hG T) =
        finiteOmissionBadOutput G i hG T :=
    finiteOmissionBadOutput_eq_outputAt_final G i hG T
  have hbad :
      finiteOmissionBadOutput G i hG T ∉ target :=
    finiteOmissionBadOutput_not_mem_finalRange G i hG T
  apply hbad
  rw [← houtput]
  exact hcorrect.1

/-- Theorem 4.15: every finite omission level is strictly weaker than the
next one. -/
theorem theorem_4_15 :
    ∀ i : ℕ,
      ∃ C : LanguageClass ℤ,
        GenLimit.Generic.UUS C ∧
          GeneratableInLimitWithOmissions C i ∧
          ¬ GeneratableInLimitWithOmissions C (i + 1) := by
  intro i
  exact
    ⟨finiteOmissionClass i, finiteOmissionClass_uus i,
      lemma_4_16 i, lemma_4_17 i⟩

end GenLimit.NoiseLossFeedback
