import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation

/-!
# Noise, Loss, and Feedback: unknown finite noise

Source: Bai--Panigrahi--Zhang, *Language Generation in the Limit:
Noise, Loss, and Feedback*, arXiv:2507.15319v2, Theorem 1.6 and Proof 13.

The source separates a noise bound known to the generator from an arbitrary
finite bound hidden by the adversary.  Its witness is the union of

* the exact positive tails `Pᵢ`; and
* all languages containing every negative integer.

At a known level `i`, the generator tests for `i+1` fixed negative markers.
Seeing all markers certifies the second class; failing the test certifies the
positive-tail class.  For unknown finite noise, a phase construction treats
the entire finite history as noise for a sufficiently remote positive tail,
waits for a fresh positive output, permanently forbids that output, and then
adjoins one new negative value.  The increasing histories have an injective
limit whose range contains every negative integer, while the recorded outputs
remain outside that range at cofinally many times.

This is a semantic formalization.  It makes no computability or running-time
claim.
-/

namespace GenLimit.NoiseLossFeedback

open GenLimit.Generic

/-! ## The literal witness class -/

/-- The source's `Pᵢ = {i,i+1,...}` for a natural index `i`. -/
def unknownFiniteNoiseTail (i : ℕ) : Set ℤ :=
  Set.range (fun k : ℕ => Int.ofNat (i + k))

theorem unknownFiniteNoiseTail_infinite (i : ℕ) :
    (unknownFiniteNoiseTail i).Infinite := by
  apply Set.infinite_range_of_injective
  intro a b hab
  have hi : i + a = i + b := Int.ofNat_inj.mp hab
  omega

theorem unknownFiniteNoiseTail_succ (i : ℕ) :
    unknownFiniteNoiseTail (i + 1) =
      GenLimit.UnionClosedness.positiveTail i := by
  ext z
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    simp [GenLimit.UnionClosedness.positiveCode]
    omega
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    simp [GenLimit.UnionClosedness.positiveCode]
    omega

theorem unknownFiniteNoiseTail_disjoint_negativeIntegers
    (i : ℕ) :
    Disjoint (unknownFiniteNoiseTail i)
      GenLimit.UnionClosedness.negativeIntegers := by
  rw [Set.disjoint_left]
  intro z hzTail hzNegative
  obtain ⟨k, rfl⟩ := hzTail
  have hnonnegative : (0 : ℤ) ≤ Int.ofNat (i + k) :=
    Int.ofNat_zero_le _
  exact (Int.not_lt_of_ge hnonnegative) hzNegative

/-- Proof 13's first class `C₁ = {Pᵢ | i ∈ ℕ}`. -/
def unknownFiniteNoiseTailClass : LanguageClass ℤ :=
  {L | ∃ i, L = unknownFiniteNoiseTail i}

/-- Proof 13's second class
`C₂ = {A ∪ ℤ_{<0} | A ⊆ ℕ}`, written extensionally. -/
def unknownFiniteNoiseNegativeClass : LanguageClass ℤ :=
  {L | GenLimit.UnionClosedness.negativeIntegers ⊆ L}

/-- Theorem 1.6's witness `C = C₁ ∪ C₂`. -/
def unknownFiniteNoiseClass : LanguageClass ℤ :=
  unknownFiniteNoiseTailClass ∪ unknownFiniteNoiseNegativeClass

theorem unknownFiniteNoiseClass_uus :
    GenLimit.Generic.UUS unknownFiniteNoiseClass := by
  intro L hL
  rcases hL with htail | hnegative
  · obtain ⟨i, rfl⟩ := htail
    exact unknownFiniteNoiseTail_infinite i
  · exact
      GenLimit.UnionClosedness.negativeIntegers_infinite.mono
        hnegative

/-! ## Known-noise upper bound -/

/-- The `i+1` negative test markers `-1,...,-(i+1)`. -/
def unknownNoiseMarkerFinset (i : ℕ) : Finset ℤ :=
  (Finset.range (i + 1)).image
    GenLimit.UnionClosedness.negativeCode

theorem unknownNoiseMarkerFinset_card (i : ℕ) :
    (unknownNoiseMarkerFinset i).card = i + 1 := by
  rw [unknownNoiseMarkerFinset, Finset.card_image_of_injective]
  · simp
  · intro a b hab
    exact GenLimit.UnionClosedness.negativeCode_injective hab

theorem unknownNoiseMarker_negative
    {i : ℕ} {z : ℤ}
    (hz : z ∈ unknownNoiseMarkerFinset i) :
    z ∈ GenLimit.UnionClosedness.negativeIntegers := by
  rw [unknownNoiseMarkerFinset] at hz
  obtain ⟨k, _hk, rfl⟩ := Finset.mem_image.mp hz
  exact GenLimit.UnionClosedness.negativeCode_mem k

private noncomputable def unknownNoiseMarkerOccurrence
    {i : ℕ} {stream : Stream ℤ}
    {L : GenLimit.Generic.Language ℤ}
    (henum : NoisyEnumerationWithLevel stream L i)
    (hmarkers :
      (↑(unknownNoiseMarkerFinset i) : Set ℤ) ⊆ L)
    (z : ℤ) : ℕ :=
  if hz : z ∈ unknownNoiseMarkerFinset i then
    Classical.choose (henum.2.1 (hmarkers hz))
  else 0

private theorem unknownNoiseMarkerOccurrence_spec
    {i : ℕ} {stream : Stream ℤ}
    {L : GenLimit.Generic.Language ℤ}
    (henum : NoisyEnumerationWithLevel stream L i)
    (hmarkers :
      (↑(unknownNoiseMarkerFinset i) : Set ℤ) ⊆ L)
    {z : ℤ} (hz : z ∈ unknownNoiseMarkerFinset i) :
    stream (unknownNoiseMarkerOccurrence henum hmarkers z) = z := by
  classical
  simp only [unknownNoiseMarkerOccurrence, dif_pos hz]
  exact Classical.choose_spec (henum.2.1 (hmarkers hz))

/-- Every test marker eventually appears for a target in the negative
half of the witness. -/
theorem unknownNoiseMarkers_eventually_observed
    {i : ℕ} {stream : Stream ℤ}
    {L : GenLimit.Generic.Language ℤ}
    (henum : NoisyEnumerationWithLevel stream L i)
    (hmarkers :
      (↑(unknownNoiseMarkerFinset i) : Set ℤ) ⊆ L) :
    ∃ T, ∀ t, T ≤ t →
      unknownNoiseMarkerFinset i ⊆ observedThrough stream t := by
  classical
  let T :=
    (unknownNoiseMarkerFinset i).sup
      (unknownNoiseMarkerOccurrence henum hmarkers)
  refine ⟨T, ?_⟩
  intro t hT z hz
  apply GenLimit.Generic.mem_sample_iff.mpr
  refine
    ⟨unknownNoiseMarkerOccurrence henum hmarkers z, ?_,
      unknownNoiseMarkerOccurrence_spec henum hmarkers hz⟩
  have hindex :
      unknownNoiseMarkerOccurrence henum hmarkers z ≤ T :=
    Finset.le_sup
      (f := unknownNoiseMarkerOccurrence henum hmarkers) hz
  omega

/-- A level-`i` noisy enumeration of a positive tail cannot contain all
`i+1` negative test markers. -/
theorem unknownNoiseMarkers_not_all_observed_on_tail
    {i j : ℕ} {stream : Stream ℤ}
    (henum :
      NoisyEnumerationWithLevel stream
        (unknownFiniteNoiseTail j) i) :
    ∀ t, ¬unknownNoiseMarkerFinset i ⊆
      observedThrough stream t := by
  intro t hall
  obtain ⟨F, hF, hcard⟩ := henum.2.2
  have hsubset : unknownNoiseMarkerFinset i ⊆ F := by
    intro z hz
    obtain ⟨k, _hk, hkz⟩ :=
      GenLimit.Generic.mem_sample_iff.mp (hall hz)
    have hzRange : z ∈ Set.range stream := ⟨k, hkz⟩
    have hzNotTail :
        z ∉ unknownFiniteNoiseTail j := by
      intro hzTail
      exact
        Set.disjoint_left.mp
          (unknownFiniteNoiseTail_disjoint_negativeIntegers j)
          hzTail (unknownNoiseMarker_negative hz)
    change z ∈ (F : Set ℤ)
    rw [hF]
    exact ⟨hzRange, hzNotTail⟩
  have hmarkersCard : i + 1 ≤ F.card := by
    rw [← unknownNoiseMarkerFinset_card i]
    exact Finset.card_le_card hsubset
  omega

/-- Proof 13's known-bound generator.  The marker test is the only place
where the bound `i` is used. -/
noncomputable def unknownFiniteNoiseSweepGenerator
    (i : ℕ) : Generator ℤ :=
  fun n xs =>
    if unknownNoiseMarkerFinset i ⊆ sequenceSample xs then
      GenLimit.UnionClosedness.descendingNegativeGenerator n xs
    else
      GenLimit.UnionClosedness.ascendingPositiveGenerator n xs

theorem unknownFiniteNoiseSweepGenerator_negative_correct
    {i : ℕ} {L : GenLimit.Generic.Language ℤ}
    (hL : L ∈ unknownFiniteNoiseNegativeClass)
    {stream : Stream ℤ}
    (henum : NoisyEnumerationWithLevel stream L i) :
    ∃ T, ∀ t, T ≤ t →
      CorrectAt (unknownFiniteNoiseSweepGenerator i) L stream t := by
  have hmarkers :
      (↑(unknownNoiseMarkerFinset i) : Set ℤ) ⊆ L :=
    fun _ hz => hL (unknownNoiseMarker_negative hz)
  obtain ⟨T, hT⟩ :=
    unknownNoiseMarkers_eventually_observed henum hmarkers
  refine ⟨T, ?_⟩
  intro t ht
  have hdetect :
      unknownNoiseMarkerFinset i ⊆ observedThrough stream t :=
    hT t ht
  have hsample :
      sequenceSample (fun k : Fin (t + 1) => stream k) =
        observedThrough stream t :=
    sequenceSample_prefix stream (t + 1)
  obtain ⟨n, _hnTime, hout, hfresh⟩ :=
    GenLimit.UnionClosedness.descendingNegativeGenerator_spec
      (fun k : Fin (t + 1) => stream k)
  have hbranch :
      unknownFiniteNoiseSweepGenerator i (t + 1)
          (fun k : Fin (t + 1) => stream k) =
        GenLimit.UnionClosedness.descendingNegativeGenerator
          (t + 1) (fun k : Fin (t + 1) => stream k) := by
    simp [unknownFiniteNoiseSweepGenerator, hsample, hdetect]
  constructor
  · rw [outputAt, GenLimit.Generic.output, hbranch, hout]
    exact hL (GenLimit.UnionClosedness.negativeCode_mem n)
  · rw [outputAt, GenLimit.Generic.output, hbranch, hout]
    rw [← hsample]
    simpa only [hout] using hfresh

theorem unknownFiniteNoiseSweepGenerator_tail_correct
    {i j : ℕ} {stream : Stream ℤ}
    (henum :
      NoisyEnumerationWithLevel stream
        (unknownFiniteNoiseTail j) i) :
    ∃ T, ∀ t, T ≤ t →
      CorrectAt (unknownFiniteNoiseSweepGenerator i)
        (unknownFiniteNoiseTail j) stream t := by
  refine ⟨j, ?_⟩
  intro t ht
  have hnoDetect :
      ¬unknownNoiseMarkerFinset i ⊆ observedThrough stream t :=
    unknownNoiseMarkers_not_all_observed_on_tail henum t
  have hsample :
      sequenceSample (fun k : Fin (t + 1) => stream k) =
        observedThrough stream t :=
    sequenceSample_prefix stream (t + 1)
  obtain ⟨n, hnTime, hout, hfresh⟩ :=
    GenLimit.UnionClosedness.ascendingPositiveGenerator_spec
      (fun k : Fin (t + 1) => stream k)
  have hjn : j ≤ n := by omega
  have htail :
      GenLimit.UnionClosedness.positiveCode n ∈
        unknownFiniteNoiseTail j := by
    refine ⟨n + 1 - j, ?_⟩
    change
      Int.ofNat (j + (n + 1 - j)) =
        Int.ofNat (n + 1)
    apply Int.ofNat_inj.mpr
    omega
  have hbranch :
      unknownFiniteNoiseSweepGenerator i (t + 1)
          (fun k : Fin (t + 1) => stream k) =
        GenLimit.UnionClosedness.ascendingPositiveGenerator
          (t + 1) (fun k : Fin (t + 1) => stream k) := by
    simp [unknownFiniteNoiseSweepGenerator, hsample, hnoDetect]
  constructor
  · rw [outputAt, GenLimit.Generic.output, hbranch, hout]
    exact htail
  · rw [outputAt, GenLimit.Generic.output, hbranch, hout]
    rw [← hsample]
    simpa only [hout] using hfresh

/-- Positive half of Theorem 1.6: a separate generator works at every
known finite noise level. -/
theorem unknownFiniteNoiseLevel_upper (i : ℕ) :
    GeneratableInLimitWithNoiseLevel unknownFiniteNoiseClass i := by
  refine ⟨unknownFiniteNoiseSweepGenerator i, ?_⟩
  intro L hL stream henum
  rcases hL with htail | hnegative
  · obtain ⟨j, rfl⟩ := htail
    exact unknownFiniteNoiseSweepGenerator_tail_correct henum
  · exact
      unknownFiniteNoiseSweepGenerator_negative_correct
        hnegative henum

/-! ## One unknown-noise adversarial phase -/

private def unknownNoiseListInput (l : List α) :
    Fin l.length → α :=
  fun k => l.get k

private theorem sequenceSample_unknownNoiseListInput
    [DecidableEq α] (l : List α) :
    sequenceSample (unknownNoiseListInput l) = l.toFinset := by
  classical
  ext x
  rw [GenLimit.Generic.mem_sequenceSample_iff, List.mem_toFinset]
  exact List.mem_iff_get.symm

private theorem exists_positiveTail_disjoint_unknownNoiseFinset
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
  have hmem : d + k ∈ hbadFinite.toFinset := by
    rw [Set.Finite.mem_toFinset]
    exact hzS
  have hlt : d + k < d := by
    simpa using hd hmem
  omega

private theorem positiveTail_disjoint_negativeIntegers_unknownNoise
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

/-- State after `n` adversarial phases.  The history already contains
exactly the first `n` canonical negative values, and every recorded bad
output is permanently disjoint from it. -/
structure UnknownFiniteNoisePhaseState (n : ℕ) where
  history : List ℤ
  forbidden : Finset ℤ
  history_nodup : history.Nodup
  history_forbidden_disjoint :
    Disjoint history.toFinset forbidden
  forbidden_nonnegative :
    ∀ z, z ∈ forbidden → 0 ≤ z
  negative_mem_history_iff :
    ∀ k,
      GenLimit.UnionClosedness.negativeCode k ∈ history ↔
        k < n

def initialUnknownFiniteNoisePhaseState :
    UnknownFiniteNoisePhaseState 0 where
  history := []
  forbidden := ∅
  history_nodup := by simp
  history_forbidden_disjoint := by simp
  forbidden_nonnegative := by simp
  negative_mem_history_iff := by simp

/-- The auditable finite-phase certificate used in the lower bound. -/
structure SuccessfulUnknownFiniteNoisePhase
    (G : Generator ℤ) (n : ℕ)
    (state : UnknownFiniteNoisePhaseState n) where
  next : UnknownFiniteNoisePhaseState (n + 1)
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

/-- One complete source phase exists for every valid finite state.  The
current history is a finite noisy prefix for a remote positive tail; noisy
success supplies a fresh positive output, which is forbidden before the next
negative target value is appended. -/
theorem exists_successfulUnknownFiniteNoisePhase
    (G : Generator ℤ) (n : ℕ)
    (hG : IsNoisyLimitGenerator G unknownFiniteNoiseClass)
    (state : UnknownFiniteNoisePhaseState n) :
    Nonempty (SuccessfulUnknownFiniteNoisePhase G n state) := by
  classical
  let blocked := state.history.toFinset ∪ state.forbidden
  obtain ⟨d, htailBlocked⟩ :=
    exists_positiveTail_disjoint_unknownNoiseFinset blocked
  let tail := GenLimit.UnionClosedness.positiveTail d
  have htailHistory :
      Disjoint tail (state.history.toFinset : Set ℤ) := by
    rw [Set.disjoint_left] at htailBlocked ⊢
    intro z hzTail hzHistory
    apply htailBlocked hzTail
    exact Finset.mem_union_left _ hzHistory
  have htailForbidden :
      Disjoint tail (state.forbidden : Set ℤ) := by
    rw [Set.disjoint_left] at htailBlocked ⊢
    intro z hzTail hzForbidden
    apply htailBlocked hzTail
    exact Finset.mem_union_right _ hzForbidden
  have hhistorySample :
      sequenceSample (unknownNoiseListInput state.history) =
        state.history.toFinset :=
    sequenceSample_unknownNoiseListInput state.history
  let hrest :
      (tail \
        (sequenceSample
          (unknownNoiseListInput state.history) : Set ℤ)).Infinite :=
    (GenLimit.UnionClosedness.positiveTail_infinite d).diff
      (sequenceSample
        (unknownNoiseListInput state.history)).finite_toSet
  let full : Stream ℤ :=
    prefixThenTarget
      (unknownNoiseListInput state.history) tail hrest
  have hhistoryGetInjective :
      Function.Injective
        (unknownNoiseListInput state.history) :=
    List.nodup_iff_injective_get.mp state.history_nodup
  have hfullInjective : Function.Injective full :=
    prefixThenTarget_injective
      hhistoryGetInjective tail hrest
  have hrange :
      Set.range full =
        (state.history.toFinset : Set ℤ) ∪ tail := by
    have h :=
      range_prefixThenTarget_eq_prefix_union
        (unknownNoiseListInput state.history) tail hrest
    simpa [full, hhistorySample] using h
  have hfullEnum : NoisyEnumeration full tail := by
    refine ⟨hfullInjective, ?_, ?_⟩
    · rw [hrange]
      exact Set.subset_union_right
    · apply state.history.toFinset.finite_toSet.subset
      rintro z ⟨hzRange, hzNotTail⟩
      rw [hrange] at hzRange
      exact hzRange.resolve_right hzNotTail
  have htailClass : tail ∈ unknownFiniteNoiseClass := by
    apply Set.mem_union_left
    exact ⟨d + 1, (unknownFiniteNoiseTail_succ d).symm⟩
  obtain ⟨T, hT⟩ := hG tail htailClass full hfullEnum
  let t := max T state.history.length
  have hTt : T ≤ t := Nat.le_max_left _ _
  have hhistoryLenT : state.history.length ≤ t :=
    Nat.le_max_right _ _
  have hcorrect : CorrectAt G tail full t :=
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
        (unknownNoiseListInput state.history) tail hrest
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
  have hyTail : y ∈ tail := hcorrect.1
  have hyNonnegative : 0 ≤ y := by
    obtain ⟨k, hk⟩ := hyTail
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
    · have hkn :=
        (state.negative_mem_history_iff n).mp
          (List.mem_toFinset.mp hnegHistory)
      omega
    · exact
        Set.disjoint_left.mp
          (positiveTail_disjoint_negativeIntegers_unknownNoise d)
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
      Disjoint (Set.range full)
        (state.forbidden : Set ℤ) := by
    rw [Set.disjoint_left]
    intro z hzRange hzForbidden
    rw [hrange] at hzRange
    rcases hzRange with hzHistory | hzTail
    · exact
        Finset.disjoint_left.mp
          state.history_forbidden_disjoint
          hzHistory hzForbidden
    · exact
        Set.disjoint_left.mp htailForbidden
          hzTail hzForbidden
  have hprefixOldForbidden :
      Disjoint phasePrefix.toFinset state.forbidden := by
    rw [Finset.disjoint_left]
    intro z hzPrefix hzForbidden
    exact
      Set.disjoint_left.mp hfullForbiddenDisjoint
        (hprefixSubsetRange hzPrefix) hzForbidden
  have hnegativeOldForbidden :
      GenLimit.UnionClosedness.negativeCode n ∉
        state.forbidden := by
    intro hmem
    have hnonneg := state.forbidden_nonnegative _ hmem
    exact
      (Int.not_lt_of_ge hnonneg)
        (GenLimit.UnionClosedness.negativeCode_mem n)
  have hnegativeNeY :
      GenLimit.UnionClosedness.negativeCode n ≠ y := by
    intro heq
    rw [← heq] at hyNonnegative
    exact
      (Int.not_lt_of_ge hyNonnegative)
        (GenLimit.UnionClosedness.negativeCode_mem n)
  have hnextForbiddenDisjoint :
      Disjoint nextHistory.toFinset nextForbidden := by
    rw [Finset.disjoint_left]
    intro z hzNext hzForbidden
    rw [Finset.mem_insert] at hzForbidden
    rw [List.mem_toFinset] at hzNext
    simp only [nextHistory, List.mem_append,
      List.mem_singleton] at hzNext
    rcases hzNext with hzPrefix | rfl
    · rcases hzForbidden with rfl | hzOld
      · exact hyNotPrefix hzPrefix
      · exact
          Finset.disjoint_left.mp hprefixOldForbidden
            (List.mem_toFinset.mpr hzPrefix) hzOld
    · rcases hzForbidden with heq | hzOld
      · exact hnegativeNeY heq
      · exact hnegativeOldForbidden hzOld
  have hnextNegativeIff :
      ∀ k,
        GenLimit.UnionClosedness.negativeCode k ∈
            nextHistory ↔
          k < n + 1 := by
    intro k
    constructor
    · intro hk
      simp only [nextHistory, List.mem_append,
        List.mem_singleton] at hk
      rcases hk with hkPrefix | hkEq
      · have hkRange :=
          hprefixSubsetRange
            (List.mem_toFinset.mpr hkPrefix)
        rw [hrange] at hkRange
        rcases hkRange with hkHistory | hkTail
        · have hkn :=
            (state.negative_mem_history_iff k).mp
              (List.mem_toFinset.mp hkHistory)
          omega
        · exact False.elim
            (Set.disjoint_left.mp
              (positiveTail_disjoint_negativeIntegers_unknownNoise d)
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
        exact (state.negative_mem_history_iff k).mpr hlt
      · simp [nextHistory]
  let next : UnknownFiniteNoisePhaseState (n + 1) :=
    { history := nextHistory
      forbidden := nextForbidden
      history_nodup := hnextHistoryNodup
      history_forbidden_disjoint := hnextForbiddenDisjoint
      forbidden_nonnegative := by
        intro z hz
        rw [Finset.mem_insert] at hz
        exact
          hz.elim (fun h => h ▸ hyNonnegative)
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
      hhistoryPrefix.trans
        (List.prefix_append phasePrefix _)
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

/-! ## Iteration and the limiting adversarial enumeration -/

private noncomputable def chosenUnknownFiniteNoisePhase
    (G : Generator ℤ) (n : ℕ)
    (hG : IsNoisyLimitGenerator G unknownFiniteNoiseClass)
    (state : UnknownFiniteNoisePhaseState n) :
    SuccessfulUnknownFiniteNoisePhase G n state :=
  Classical.choice
    (exists_successfulUnknownFiniteNoisePhase G n hG state)

private noncomputable def iteratedUnknownFiniteNoiseState
    (G : Generator ℤ)
    (hG : IsNoisyLimitGenerator G unknownFiniteNoiseClass) :
    (n : ℕ) → UnknownFiniteNoisePhaseState n
  | 0 => initialUnknownFiniteNoisePhaseState
  | n + 1 =>
      (chosenUnknownFiniteNoisePhase G n hG
        (iteratedUnknownFiniteNoiseState G hG n)).next

private theorem iteratedUnknownFiniteNoiseState_prefix_succ
    (G : Generator ℤ)
    (hG : IsNoisyLimitGenerator G unknownFiniteNoiseClass)
    (n : ℕ) :
    (iteratedUnknownFiniteNoiseState G hG n).history <+:
      (iteratedUnknownFiniteNoiseState G hG (n + 1)).history := by
  rw [iteratedUnknownFiniteNoiseState]
  exact
    (chosenUnknownFiniteNoisePhase G n hG
      (iteratedUnknownFiniteNoiseState G hG n)).extends_history

private theorem iteratedUnknownFiniteNoiseState_prefix
    (G : Generator ℤ)
    (hG : IsNoisyLimitGenerator G unknownFiniteNoiseClass)
    {n m : ℕ} (hnm : n ≤ m) :
    (iteratedUnknownFiniteNoiseState G hG n).history <+:
      (iteratedUnknownFiniteNoiseState G hG m).history := by
  induction m, hnm using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ m _ ih =>
      exact ih.trans
        (iteratedUnknownFiniteNoiseState_prefix_succ G hG m)

private theorem iteratedUnknownFiniteNoiseState_length
    (G : Generator ℤ)
    (hG : IsNoisyLimitGenerator G unknownFiniteNoiseClass)
    (n : ℕ) :
    n ≤ (iteratedUnknownFiniteNoiseState G hG n).history.length := by
  induction n with
  | zero =>
      simp [iteratedUnknownFiniteNoiseState,
        initialUnknownFiniteNoisePhaseState]
  | succ n ih =>
      have hstep :=
        (chosenUnknownFiniteNoisePhase G n hG
          (iteratedUnknownFiniteNoiseState G hG n)).strict_growth
      rw [iteratedUnknownFiniteNoiseState]
      omega

private theorem iteratedUnknownFiniteNoiseState_forbidden_succ
    (G : Generator ℤ)
    (hG : IsNoisyLimitGenerator G unknownFiniteNoiseClass)
    (n : ℕ) :
    (iteratedUnknownFiniteNoiseState G hG n).forbidden ⊆
      (iteratedUnknownFiniteNoiseState G hG
        (n + 1)).forbidden := by
  rw [iteratedUnknownFiniteNoiseState]
  exact
    (chosenUnknownFiniteNoisePhase G n hG
      (iteratedUnknownFiniteNoiseState G hG n)).forbidden_subset

private theorem iteratedUnknownFiniteNoiseState_forbidden_mono
    (G : Generator ℤ)
    (hG : IsNoisyLimitGenerator G unknownFiniteNoiseClass)
    {n m : ℕ} (hnm : n ≤ m) :
    (iteratedUnknownFiniteNoiseState G hG n).forbidden ⊆
      (iteratedUnknownFiniteNoiseState G hG m).forbidden := by
  induction m, hnm using Nat.le_induction with
  | base => exact fun _ hx => hx
  | succ m _ ih =>
      exact fun z hz =>
        iteratedUnknownFiniteNoiseState_forbidden_succ G hG m
          (ih hz)

private noncomputable def unknownFiniteNoiseFailureTime
    (G : Generator ℤ)
    (hG : IsNoisyLimitGenerator G unknownFiniteNoiseClass)
    (n : ℕ) : ℕ :=
  (chosenUnknownFiniteNoisePhase G n hG
    (iteratedUnknownFiniteNoiseState G hG n)).failureTime

private noncomputable def unknownFiniteNoiseBadOutput
    (G : Generator ℤ)
    (hG : IsNoisyLimitGenerator G unknownFiniteNoiseClass)
    (n : ℕ) : ℤ :=
  (chosenUnknownFiniteNoisePhase G n hG
    (iteratedUnknownFiniteNoiseState G hG n)).badOutput

private theorem unknownFiniteNoiseFailureTime_ge_stage
    (G : Generator ℤ)
    (hG : IsNoisyLimitGenerator G unknownFiniteNoiseClass)
    (n : ℕ) :
    n ≤ unknownFiniteNoiseFailureTime G hG n := by
  exact
    (iteratedUnknownFiniteNoiseState_length G hG n).trans
      (chosenUnknownFiniteNoisePhase G n hG
        (iteratedUnknownFiniteNoiseState G hG n)).old_length_le_failureTime

private theorem unknownFiniteNoiseBadOutput_mem_nextForbidden
    (G : Generator ℤ)
    (hG : IsNoisyLimitGenerator G unknownFiniteNoiseClass)
    (n : ℕ) :
    unknownFiniteNoiseBadOutput G hG n ∈
      (iteratedUnknownFiniteNoiseState G hG
        (n + 1)).forbidden := by
  rw [iteratedUnknownFiniteNoiseState]
  exact
    (chosenUnknownFiniteNoisePhase G n hG
      (iteratedUnknownFiniteNoiseState G hG n)).bad_mem_forbidden

private theorem unknownFiniteNoiseBadOutput_not_mem_nextHistory
    (G : Generator ℤ)
    (hG : IsNoisyLimitGenerator G unknownFiniteNoiseClass)
    (n : ℕ) :
    unknownFiniteNoiseBadOutput G hG n ∉
      (iteratedUnknownFiniteNoiseState G hG
        (n + 1)).history := by
  intro hmem
  exact
    Finset.disjoint_left.mp
      (iteratedUnknownFiniteNoiseState G hG
        (n + 1)).history_forbidden_disjoint
      (List.mem_toFinset.mpr hmem)
      (unknownFiniteNoiseBadOutput_mem_nextForbidden G hG n)

private theorem unknownFiniteNoiseBadOutput_not_mem_laterHistory
    (G : Generator ℤ)
    (hG : IsNoisyLimitGenerator G unknownFiniteNoiseClass)
    (n m : ℕ) (hnm : n + 1 ≤ m) :
    unknownFiniteNoiseBadOutput G hG n ∉
      (iteratedUnknownFiniteNoiseState G hG m).history := by
  intro hmem
  have hbadForbidden :
      unknownFiniteNoiseBadOutput G hG n ∈
        (iteratedUnknownFiniteNoiseState G hG m).forbidden :=
    iteratedUnknownFiniteNoiseState_forbidden_mono G hG hnm
      (unknownFiniteNoiseBadOutput_mem_nextForbidden G hG n)
  exact
    Finset.disjoint_left.mp
      (iteratedUnknownFiniteNoiseState G hG
        m).history_forbidden_disjoint
      (List.mem_toFinset.mpr hmem) hbadForbidden

private theorem unknownFiniteNoiseBadOutput_not_mem_history
    (G : Generator ℤ)
    (hG : IsNoisyLimitGenerator G unknownFiniteNoiseClass)
    (n m : ℕ) :
    unknownFiniteNoiseBadOutput G hG n ∉
      (iteratedUnknownFiniteNoiseState G hG m).history := by
  rcases le_total m (n + 1) with hmn | hnm
  · intro hmem
    exact
      unknownFiniteNoiseBadOutput_not_mem_nextHistory G hG n
        ((iteratedUnknownFiniteNoiseState_prefix G hG hmn).subset
          hmem)
  · exact
      unknownFiniteNoiseBadOutput_not_mem_laterHistory
        G hG n m hnm

private noncomputable def unknownFiniteNoiseFinalStream
    (G : Generator ℤ)
    (hG : IsNoisyLimitGenerator G unknownFiniteNoiseClass) :
    Stream ℤ :=
  fun k =>
    let history :=
      (iteratedUnknownFiniteNoiseState G hG (k + 1)).history
    history.get ⟨k, by
      have hlen :=
        iteratedUnknownFiniteNoiseState_length G hG (k + 1)
      exact lt_of_lt_of_le (Nat.lt_succ_self k) hlen⟩

private theorem unknownFiniteNoiseFinalStream_eq_history_get
    (G : Generator ℤ)
    (hG : IsNoisyLimitGenerator G unknownFiniteNoiseClass)
    (n k : ℕ)
    (hk :
      k <
        (iteratedUnknownFiniteNoiseState G hG
          n).history.length) :
    unknownFiniteNoiseFinalStream G hG k =
      (iteratedUnknownFiniteNoiseState G hG n).history.get
        ⟨k, hk⟩ := by
  rw [unknownFiniteNoiseFinalStream]
  have hbound :
      k <
        (iteratedUnknownFiniteNoiseState G hG
          (k + 1)).history.length := by
    have hlen :=
      iteratedUnknownFiniteNoiseState_length G hG (k + 1)
    omega
  rw [List.get_eq_getElem, List.get_eq_getElem]
  rcases le_total (k + 1) n with hkn | hnk
  · exact
      (List.prefix_iff_getElem.mp
        (iteratedUnknownFiniteNoiseState_prefix G hG hkn)).2
          k hbound
  · exact
      ((List.prefix_iff_getElem.mp
        (iteratedUnknownFiniteNoiseState_prefix G hG hnk)).2
          k hk).symm

private theorem unknownFiniteNoiseHistory_subset_finalRange
    (G : Generator ℤ)
    (hG : IsNoisyLimitGenerator G unknownFiniteNoiseClass)
    (n : ℕ) :
    (↑(iteratedUnknownFiniteNoiseState G hG
        n).history.toFinset : Set ℤ) ⊆
      Set.range (unknownFiniteNoiseFinalStream G hG) := by
  intro x hx
  change
    x ∈ (iteratedUnknownFiniteNoiseState G hG
      n).history.toFinset at hx
  rw [List.mem_toFinset] at hx
  obtain ⟨k, hk⟩ := List.mem_iff_get.mp hx
  refine ⟨k, ?_⟩
  exact
    (unknownFiniteNoiseFinalStream_eq_history_get
      G hG n k k.isLt).trans hk

private theorem unknownFiniteNoiseFinalStream_injective
    (G : Generator ℤ)
    (hG : IsNoisyLimitGenerator G unknownFiniteNoiseClass) :
    Function.Injective (unknownFiniteNoiseFinalStream G hG) := by
  intro a b hab
  let n := max a b + 1
  have ha :
      a <
        (iteratedUnknownFiniteNoiseState G hG
          n).history.length := by
    have hlen :=
      iteratedUnknownFiniteNoiseState_length G hG n
    dsimp only [n] at hlen ⊢
    omega
  have hb :
      b <
        (iteratedUnknownFiniteNoiseState G hG
          n).history.length := by
    have hlen :=
      iteratedUnknownFiniteNoiseState_length G hG n
    dsimp only [n] at hlen ⊢
    omega
  have hget :
      (iteratedUnknownFiniteNoiseState G hG n).history.get
          ⟨a, ha⟩ =
        (iteratedUnknownFiniteNoiseState G hG n).history.get
          ⟨b, hb⟩ := by
    exact
      (unknownFiniteNoiseFinalStream_eq_history_get
        G hG n a ha).symm.trans
        (hab.trans
          (unknownFiniteNoiseFinalStream_eq_history_get
            G hG n b hb))
  have hfin :
      (⟨a, ha⟩ :
        Fin
          (iteratedUnknownFiniteNoiseState G hG
            n).history.length) =
        ⟨b, hb⟩ :=
    (List.nodup_iff_injective_get.mp
      (iteratedUnknownFiniteNoiseState G hG
        n).history_nodup) hget
  exact congrArg Fin.val hfin

private theorem unknownFiniteNoiseNegative_mem_nextHistory
    (G : Generator ℤ)
    (hG : IsNoisyLimitGenerator G unknownFiniteNoiseClass)
    (n : ℕ) :
    GenLimit.UnionClosedness.negativeCode n ∈
      (iteratedUnknownFiniteNoiseState G hG
        (n + 1)).history := by
  exact
    ((iteratedUnknownFiniteNoiseState G hG
      (n + 1)).negative_mem_history_iff n).mpr
        (Nat.lt_succ_self n)

private theorem unknownFiniteNoiseNegative_subset_finalRange
    (G : Generator ℤ)
    (hG : IsNoisyLimitGenerator G unknownFiniteNoiseClass) :
    GenLimit.UnionClosedness.negativeIntegers ⊆
      Set.range (unknownFiniteNoiseFinalStream G hG) := by
  rw [← GenLimit.UnionClosedness.range_negativeCode]
  rintro _ ⟨n, rfl⟩
  exact
    unknownFiniteNoiseHistory_subset_finalRange G hG (n + 1)
      (List.mem_toFinset.mpr
        (unknownFiniteNoiseNegative_mem_nextHistory G hG n))

private theorem unknownFiniteNoiseBadOutput_not_mem_finalRange
    (G : Generator ℤ)
    (hG : IsNoisyLimitGenerator G unknownFiniteNoiseClass)
    (n : ℕ) :
    unknownFiniteNoiseBadOutput G hG n ∉
      Set.range (unknownFiniteNoiseFinalStream G hG) := by
  rintro ⟨k, hk⟩
  apply unknownFiniteNoiseBadOutput_not_mem_history
    G hG n (k + 1)
  have hbound :
      k <
        (iteratedUnknownFiniteNoiseState G hG
          (k + 1)).history.length := by
    have hlen :=
      iteratedUnknownFiniteNoiseState_length G hG (k + 1)
    omega
  apply List.mem_iff_get.mpr
  refine ⟨⟨k, hbound⟩, ?_⟩
  exact
    (unknownFiniteNoiseFinalStream_eq_history_get
      G hG (k + 1) k hbound).symm.trans hk

private theorem unknownFiniteNoiseFailureTime_lt_nextHistory
    (G : Generator ℤ)
    (hG : IsNoisyLimitGenerator G unknownFiniteNoiseClass)
    (n : ℕ) :
    unknownFiniteNoiseFailureTime G hG n <
      (iteratedUnknownFiniteNoiseState G hG
        (n + 1)).history.length := by
  rw [unknownFiniteNoiseFailureTime,
    iteratedUnknownFiniteNoiseState]
  exact
    (chosenUnknownFiniteNoisePhase G n hG
      (iteratedUnknownFiniteNoiseState G hG n)).failureTime_lt_next

private theorem unknownFiniteNoiseBadOutput_eq_outputAt_final
    (G : Generator ℤ)
    (hG : IsNoisyLimitGenerator G unknownFiniteNoiseClass)
    (n : ℕ) :
    outputAt G (unknownFiniteNoiseFinalStream G hG)
        (unknownFiniteNoiseFailureTime G hG n) =
      unknownFiniteNoiseBadOutput G hG n := by
  unfold outputAt
  change
    G
        ((chosenUnknownFiniteNoisePhase G n hG
          (iteratedUnknownFiniteNoiseState G hG n)).failureTime + 1)
        (fun k => unknownFiniteNoiseFinalStream G hG k) =
      (chosenUnknownFiniteNoisePhase G n hG
        (iteratedUnknownFiniteNoiseState G hG n)).badOutput
  convert
    (chosenUnknownFiniteNoisePhase G n hG
      (iteratedUnknownFiniteNoiseState G hG n)).output_on_next
      using 1
  congr 1
  funext k
  have hkHistory :
      k.val <
        (iteratedUnknownFiniteNoiseState G hG
          (n + 1)).history.length := by
    exact
      lt_of_lt_of_le k.isLt
        (Nat.succ_le_iff.mpr
          (unknownFiniteNoiseFailureTime_lt_nextHistory
            G hG n))
  exact
    unknownFiniteNoiseFinalStream_eq_history_get
      G hG (n + 1) k hkHistory

/-! ## Theorem 1.6 -/

/-- Negative half of Theorem 1.6.  Every proposed noisy-limit generator is
defeated by one exact enumeration of a target in the negative half of the
witness class. -/
theorem unknownFiniteNoiseLevel_lower :
    ¬NoisilyGeneratableInLimit unknownFiniteNoiseClass := by
  rintro ⟨G, hG⟩
  let stream := unknownFiniteNoiseFinalStream G hG
  let target : Set ℤ := Set.range stream
  have htarget : target ∈ unknownFiniteNoiseClass := by
    apply Set.mem_union_right
    exact unknownFiniteNoiseNegative_subset_finalRange G hG
  have henum : NoisyEnumeration stream target := by
    refine
      ⟨unknownFiniteNoiseFinalStream_injective G hG,
        Set.Subset.rfl, ?_⟩
    simp [target]
  obtain ⟨T, hT⟩ := hG target htarget stream henum
  have hlate :
      T ≤ unknownFiniteNoiseFailureTime G hG T :=
    unknownFiniteNoiseFailureTime_ge_stage G hG T
  have hcorrect :
      CorrectAt G target stream
        (unknownFiniteNoiseFailureTime G hG T) :=
    hT _ hlate
  have houtput :
      outputAt G stream
          (unknownFiniteNoiseFailureTime G hG T) =
        unknownFiniteNoiseBadOutput G hG T :=
    unknownFiniteNoiseBadOutput_eq_outputAt_final G hG T
  have hbad :
      unknownFiniteNoiseBadOutput G hG T ∉ target :=
    unknownFiniteNoiseBadOutput_not_mem_finalRange G hG T
  apply hbad
  rw [← houtput]
  exact hcorrect.1

/-- Theorem 1.6, with the source's exact existential quantifiers. -/
theorem theorem_1_6 :
    ∃ C : LanguageClass ℤ,
      (∀ i : ℕ, GeneratableInLimitWithNoiseLevel C i) ∧
        ¬NoisilyGeneratableInLimit C :=
  ⟨unknownFiniteNoiseClass, unknownFiniteNoiseLevel_upper,
    unknownFiniteNoiseLevel_lower⟩

/-- The same explicit witness is a class of infinite languages. -/
theorem theorem_1_6_with_uus :
    ∃ C : LanguageClass ℤ,
      GenLimit.Generic.UUS C ∧
        (∀ i : ℕ, GeneratableInLimitWithNoiseLevel C i) ∧
          ¬NoisilyGeneratableInLimit C :=
  ⟨unknownFiniteNoiseClass, unknownFiniteNoiseClass_uus,
    unknownFiniteNoiseLevel_upper, unknownFiniteNoiseLevel_lower⟩

end GenLimit.NoiseLossFeedback
