import GenLimit.Paper02_LearningTheory.EventuallyUnboundedClosureDiagnostics
import GenLimit.Paper02_LearningTheory.Common.FiniteHistory
import GenLimit.Paper02_LearningTheory.Common.FiniteCandidateRace
import Mathlib.Data.Finset.Max

/-!
# Finite unions of Eventually Unbounded Closure classes

This file formalizes Theorem C.2 of Li--Raman--Tewari,
*Generation through the Lens of Learning Theory*, arXiv:2410.13714v5 /
COLT 2025 (source label `thm:weaksuff`).

The theorem is valid, although the proof sketch immediately preceding it
uses a false reformulation of Eventually Unbounded Closure.  The repaired
proof below uses only Definition C.1.  For each component of the finite cover,
the generator waits until an infinite common core first appears and then
freezes that core.  Along a fixed target presentation, the finitely many
components that ever activate have all activated after a finite time.  The
rest is the finite maximal-enumeration-progress argument used in Theorem 3.10:
a frozen core not contained in the target has bounded progress, while the
frozen core of a component containing the target has unbounded progress.
-/

namespace GenLimit.LiRamanTewari

open Common

/-- A component has activated on a finite history when an infinite common
core occurred at some prefix of that history. -/
private def c2ActivatesOn [Nonempty α]
    (K : GenLimit.Generic.LanguageClass α) {t : ℕ}
    (xs : Fin t → α) : Prop :=
  ∃ r, r ≤ t ∧
    (commonCore K (GenLimit.Generic.sample (extendHistory xs) r)).Infinite

/-- Once a component activates, freeze its common core at its first
activation time.  The empty set is an irrelevant value for an inactive
component. -/
private noncomputable def c2LocalActivationTime [Nonempty α]
    (K : GenLimit.Generic.LanguageClass α) {t : ℕ}
    (xs : Fin t → α) : ℕ := by
  classical
  exact if h : c2ActivatesOn K xs then Nat.find h else 0

private noncomputable def c2FrozenCore [Nonempty α]
    (K : GenLimit.Generic.LanguageClass α) {t : ℕ}
    (xs : Fin t → α) : Set α := by
  classical
  exact if h : c2ActivatesOn K xs then
    commonCore K
      (GenLimit.Generic.sample (extendHistory xs)
        (c2LocalActivationTime K xs))
  else ∅

private theorem c2_localActivationTime_spec [Nonempty α]
    {K : GenLimit.Generic.LanguageClass α} {t : ℕ}
    {xs : Fin t → α} (h : c2ActivatesOn K xs) :
    c2LocalActivationTime K xs ≤ t ∧
      (commonCore K
        (GenLimit.Generic.sample (extendHistory xs)
          (c2LocalActivationTime K xs))).Infinite := by
  classical
  simpa [c2LocalActivationTime, h] using Nat.find_spec h

private noncomputable def c2ActiveIndices [Nonempty α] {n t : ℕ}
    (classes : Fin n → GenLimit.Generic.LanguageClass α)
    (xs : Fin t → α) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i ↦ c2ActivatesOn (classes i) xs)

private theorem c2_mem_activeIndices_iff [Nonempty α]
    {n t : ℕ}
    {classes : Fin n → GenLimit.Generic.LanguageClass α}
    {xs : Fin t → α} {i : Fin n} :
    i ∈ c2ActiveIndices classes xs ↔
      c2ActivatesOn (classes i) xs := by
  classical
  simp [c2ActiveIndices]

private noncomputable def c2WinningIndex
    [Nonempty α] [Countable α] {n t : ℕ}
    (classes : Fin n → GenLimit.Generic.LanguageClass α)
    (xs : Fin t → α) : Option (Fin n) :=
  Common.winningIndex (c2ActiveIndices classes xs)
    (fun i ↦ c2FrozenCore (classes i) xs)
    (GenLimit.Generic.sequenceSample xs)

private theorem c2WinningIndex_spec
    [Nonempty α] [Countable α] {n t : ℕ}
    (classes : Fin n → GenLimit.Generic.LanguageClass α)
    (xs : Fin t → α)
    (hactive : (c2ActiveIndices classes xs).Nonempty) :
    ∃ selected,
      c2WinningIndex classes xs = some selected ∧
      selected ∈ c2ActiveIndices classes xs ∧
      ∀ i, i ∈ c2ActiveIndices classes xs →
        componentProgress (c2FrozenCore (classes i) xs)
            (GenLimit.Generic.sequenceSample xs) ≤
          componentProgress (c2FrozenCore (classes selected) xs)
            (GenLimit.Generic.sequenceSample xs) := by
  simpa only [c2WinningIndex] using
    (Common.winningIndex_spec (c2ActiveIndices classes xs)
      (fun i ↦ c2FrozenCore (classes i) xs)
      (GenLimit.Generic.sequenceSample xs) hactive)

/-- The repaired generator for Theorem C.2. -/
noncomputable def finiteEUCUnionGenerator
    [Nonempty α] [Countable α] {n : ℕ}
    (classes : Fin n → GenLimit.Generic.LanguageClass α) :
    GenLimit.Generic.Generator α := by
  classical
  exact fun _ xs ↦
    let current := GenLimit.Generic.sequenceSample xs
    match c2WinningIndex classes xs with
    | none => Classical.choice inferInstance
    | some i => componentOutput (c2FrozenCore (classes i) xs) current

private def c2EverActivates
    (K : GenLimit.Generic.LanguageClass α)
    (stream : GenLimit.Generic.Stream α) : Prop :=
  ∃ r, (commonCore K (GenLimit.Generic.sample stream r)).Infinite

private noncomputable def c2ActivationTime
    (K : GenLimit.Generic.LanguageClass α)
    (stream : GenLimit.Generic.Stream α) : ℕ := by
  classical
  exact if h : c2EverActivates K stream then Nat.find h else 0

private noncomputable def c2GlobalFrozenCore
    (K : GenLimit.Generic.LanguageClass α)
    (stream : GenLimit.Generic.Stream α) : Set α := by
  classical
  exact if h : c2EverActivates K stream then
    commonCore K
      (GenLimit.Generic.sample stream (c2ActivationTime K stream))
  else ∅

private theorem c2_globalFrozenCore_infinite
    {K : GenLimit.Generic.LanguageClass α}
    {stream : GenLimit.Generic.Stream α}
    (h : c2EverActivates K stream) :
    (c2GlobalFrozenCore K stream).Infinite := by
  classical
  simp only [c2GlobalFrozenCore, dif_pos h]
  simpa [c2ActivationTime, h] using Nat.find_spec h

private theorem c2_activationTime_le_stableTime
    {n : ℕ}
    (classes : Fin n → GenLimit.Generic.LanguageClass α)
    (stream : GenLimit.Generic.Stream α) (i : Fin n) :
    c2ActivationTime (classes i) stream ≤
      Finset.univ.sup
        (fun j : Fin n ↦ c2ActivationTime (classes j) stream) := by
  classical
  exact Finset.le_sup (f :=
    fun j : Fin n ↦ c2ActivationTime (classes j) stream)
    (Finset.mem_univ i)

private theorem c2_local_activates_iff
    [Nonempty α]
    {K : GenLimit.Generic.LanguageClass α}
    {stream : GenLimit.Generic.Stream α} {t : ℕ}
    (hstable : c2ActivationTime K stream ≤ t) :
    c2ActivatesOn K (fun i : Fin t ↦ stream i) ↔
      c2EverActivates K stream := by
  classical
  constructor
  · rintro ⟨r, hrt, hinf⟩
    refine ⟨r, ?_⟩
    rwa [sample_extendHistory_stream_eq hrt] at hinf
  · intro hever
    refine ⟨Nat.find hever, ?_, ?_⟩
    · have htime :
          c2ActivationTime K stream = Nat.find hever := by
        simp [c2ActivationTime, hever]
      simpa [htime] using hstable
    · rw [sample_extendHistory_stream_eq
        (by
          have htime :
              c2ActivationTime K stream = Nat.find hever := by
            simp [c2ActivationTime, hever]
          simpa [htime] using hstable)]
      exact Nat.find_spec hever

private theorem c2_localFrozenCore_eq_global
    [Nonempty α]
    {K : GenLimit.Generic.LanguageClass α}
    {stream : GenLimit.Generic.Stream α} {t : ℕ}
    (hever : c2EverActivates K stream)
    (hstable : c2ActivationTime K stream ≤ t) :
    c2FrozenCore K (fun i : Fin t ↦ stream i) =
      c2GlobalFrozenCore K stream := by
  classical
  let xs : Fin t → α := fun i ↦ stream i
  have hlocal : c2ActivatesOn K xs :=
    (c2_local_activates_iff hstable).2 hever
  have hlocalSpec := c2_localActivationTime_spec hlocal
  have hglobalTime :
      c2ActivationTime K stream = Nat.find hever := by
    simp [c2ActivationTime, hever]
  have hglobalLe : c2ActivationTime K stream ≤ t := hstable
  have hlocalTime :
      c2LocalActivationTime K xs = Nat.find hlocal := by
    simp [c2LocalActivationTime, hlocal]
  have hlocalAt :
      (commonCore K
        (GenLimit.Generic.sample stream
          (c2LocalActivationTime K xs))).Infinite := by
    rw [← sample_extendHistory_stream_eq hlocalSpec.1]
    exact hlocalSpec.2
  have hglobalMin :
      c2ActivationTime K stream ≤ c2LocalActivationTime K xs := by
    rw [hglobalTime, hlocalTime]
    exact Nat.find_min' hever (by simpa [hlocalTime] using hlocalAt)
  have hlocalCandidate :
      c2ActivationTime K stream ≤ t ∧
        (commonCore K
          (GenLimit.Generic.sample (extendHistory xs)
            (c2ActivationTime K stream))).Infinite := by
    refine ⟨hglobalLe, ?_⟩
    rw [sample_extendHistory_stream_eq hglobalLe]
    simpa [c2ActivationTime, hever] using Nat.find_spec hever
  have hlocalMin :
      c2LocalActivationTime K xs ≤ c2ActivationTime K stream := by
    rw [hlocalTime, hglobalTime]
    exact Nat.find_min' hlocal (by
      simpa [hglobalTime] using hlocalCandidate)
  have htimes :
      c2LocalActivationTime K xs = c2ActivationTime K stream :=
    Nat.le_antisymm hlocalMin hglobalMin
  have hlocal' :
      c2ActivatesOn K (fun i : Fin t ↦ stream i) := by
    simpa only [xs] using hlocal
  simp only [c2FrozenCore, dif_pos hlocal', c2GlobalFrozenCore,
    dif_pos hever]
  rw [htimes, sample_extendHistory_stream_eq hglobalLe]

private noncomputable def c2BadIndices [Countable α] {n : ℕ}
    (classes : Fin n → GenLimit.Generic.LanguageClass α)
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i ↦
    c2EverActivates (classes i) stream ∧
      ¬c2GlobalFrozenCore (classes i) stream ⊆ L)

private theorem c2_mem_badIndices_iff [Countable α] {n : ℕ}
    {classes : Fin n → GenLimit.Generic.LanguageClass α}
    {stream : GenLimit.Generic.Stream α}
    {L : GenLimit.Generic.Language α} {i : Fin n} :
    i ∈ c2BadIndices classes stream L ↔
      c2EverActivates (classes i) stream ∧
        ¬c2GlobalFrozenCore (classes i) stream ⊆ L := by
  classical
  simp [c2BadIndices]

private theorem c2BadObstruction_exists [Countable α] {n : ℕ}
    (classes : Fin n → GenLimit.Generic.LanguageClass α)
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α)
    {i : Fin n} (hi : i ∈ c2BadIndices classes stream L) :
    ∃ k,
      infiniteEnumeration (c2GlobalFrozenCore (classes i) stream)
        (c2_globalFrozenCore_infinite
          (c2_mem_badIndices_iff.mp hi).1) k ∉ L := by
  obtain ⟨x, hxCore, hxL⟩ :=
    Set.not_subset.mp (c2_mem_badIndices_iff.mp hi).2
  obtain ⟨k, hk⟩ := infiniteEnumeration_surjective
    (c2GlobalFrozenCore (classes i) stream)
    (c2_globalFrozenCore_infinite
      (c2_mem_badIndices_iff.mp hi).1) hxCore
  exact ⟨k, hk.symm ▸ hxL⟩

private noncomputable def c2BadObstruction [Countable α] {n : ℕ}
    (classes : Fin n → GenLimit.Generic.LanguageClass α)
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) (i : Fin n) : ℕ := by
  classical
  exact if hi : i ∈ c2BadIndices classes stream L then
    Nat.find (c2BadObstruction_exists classes stream L hi)
  else 0

private theorem c2BadObstruction_spec [Countable α] {n : ℕ}
    (classes : Fin n → GenLimit.Generic.LanguageClass α)
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) (i : Fin n)
    (hi : i ∈ c2BadIndices classes stream L) :
    infiniteEnumeration (c2GlobalFrozenCore (classes i) stream)
      (c2_globalFrozenCore_infinite
        (c2_mem_badIndices_iff.mp hi).1)
      (c2BadObstruction classes stream L i) ∉ L := by
  classical
  simp only [c2BadObstruction, dif_pos hi]
  exact Nat.find_spec (c2BadObstruction_exists classes stream L hi)

/-- Repaired proof core for Theorem C.2.  It uses only Definition C.1, not
the false arbitrary-stream reformulation printed immediately before C.2. -/
theorem finite_euc_cover_implies_generatable_in_limit
    [Nonempty α] [Countable α]
    {H : GenLimit.Generic.LanguageClass α}
    {n : ℕ} (classes : Fin n → GenLimit.Generic.LanguageClass α)
    (hcover : IsFiniteCover H classes)
    (hEUC : ∀ i, EventuallyUnboundedClosure (classes i)) :
    GeneratableInLimit H := by
  classical
  let gen := finiteEUCUnionGenerator classes
  refine ⟨gen, ?_⟩
  intro L hLH stream hPresentation
  have hstream : GenLimit.Generic.StreamIn stream L :=
    GenLimit.Generic.streamIn_of_presents hPresentation
  have hLUnion : L ∈ ⋃ i, classes i := by
    rw [← hcover]
    exact hLH
  obtain ⟨target, hLTarget⟩ := Set.mem_iUnion.mp hLUnion
  obtain ⟨targetTime, hTargetInfinite⟩ :=
    hEUC target L hLTarget stream hPresentation
  have hTargetEver : c2EverActivates (classes target) stream :=
    ⟨targetTime, hTargetInfinite⟩
  let stableTime : ℕ :=
    Finset.univ.sup
      (fun i : Fin n ↦ c2ActivationTime (classes i) stream)
  have hTargetStable :
      c2ActivationTime (classes target) stream ≤ stableTime :=
    c2_activationTime_le_stableTime classes stream target
  have hTargetCoreInfinite :
      (c2GlobalFrozenCore (classes target) stream).Infinite :=
    c2_globalFrozenCore_infinite hTargetEver
  have hTargetCoreGood :
      c2GlobalFrozenCore (classes target) stream ⊆ L := by
    have hLVersion :
        L ∈ versionSpace (classes target)
          (GenLimit.Generic.sample stream
            (c2ActivationTime (classes target) stream)) :=
      ⟨hLTarget, sample_subset_of_streamIn hstream _⟩
    simp only [c2GlobalFrozenCore, dif_pos hTargetEver]
    exact commonCore_subset_of_mem_versionSpace hLVersion
  let bad := c2BadIndices classes stream L
  let obstruction : Fin n → ℕ :=
    c2BadObstruction classes stream L
  let badBound : ℕ := bad.sup obstruction
  let goodPrefix : Finset α :=
    (Finset.range (badBound + 1)).image
      (infiniteEnumeration
        (c2GlobalFrozenCore (classes target) stream)
        hTargetCoreInfinite)
  have hGoodPrefixL : (↑goodPrefix : Set α) ⊆ L := by
    intro x hx
    obtain ⟨k, _hk, hkx⟩ := Finset.mem_image.mp hx
    rw [← hkx]
    exact hTargetCoreGood
      (infiniteEnumeration_mem
        (c2GlobalFrozenCore (classes target) stream)
        hTargetCoreInfinite k)
  obtain ⟨prefixTime, hPrefixTime⟩ :=
    GenLimit.Generic.finset_eventually_subset_sample
      hPresentation goodPrefix hGoodPrefixL
  refine ⟨max stableTime prefixTime, ?_⟩
  intro s hs
  have hStableS : stableTime ≤ s :=
    (Nat.le_max_left stableTime prefixTime).trans hs
  have hPrefixS : prefixTime ≤ s :=
    (Nat.le_max_right stableTime prefixTime).trans hs
  let xs : Fin s → α := fun i ↦ stream i
  let current := GenLimit.Generic.sample stream s
  have hSequenceCurrent :
      GenLimit.Generic.sequenceSample xs = current := by
    exact GenLimit.Generic.sequenceSample_prefix stream s
  have hTargetActivationLe :
      c2ActivationTime (classes target) stream ≤ s :=
    hTargetStable.trans hStableS
  have hTargetLocalActive :
      c2ActivatesOn (classes target) xs :=
    (c2_local_activates_iff hTargetActivationLe).2 hTargetEver
  have hTargetActive :
      target ∈ c2ActiveIndices classes xs :=
    c2_mem_activeIndices_iff.mpr hTargetLocalActive
  have hactive : (c2ActiveIndices classes xs).Nonempty :=
    ⟨target, hTargetActive⟩
  have hTargetLocalCore :
      c2FrozenCore (classes target) xs =
        c2GlobalFrozenCore (classes target) stream :=
    c2_localFrozenCore_eq_global hTargetEver hTargetActivationLe
  have hPrefixCurrent : goodPrefix ⊆ current :=
    hPrefixTime.trans (GenLimit.Generic.sample_mono hPrefixS)
  have hTargetProgress :
      badBound <
        progress (c2GlobalFrozenCore (classes target) stream)
          hTargetCoreInfinite current := by
    apply Nat.lt_of_not_ge
    intro hle
    have hmemPrefix :
        infiniteEnumeration
            (c2GlobalFrozenCore (classes target) stream)
            hTargetCoreInfinite
            (progress
              (c2GlobalFrozenCore (classes target) stream)
              hTargetCoreInfinite current) ∈ goodPrefix := by
      apply Finset.mem_image.mpr
      refine ⟨progress
        (c2GlobalFrozenCore (classes target) stream)
        hTargetCoreInfinite current, ?_, rfl⟩
      simp only [Finset.mem_range, Nat.lt_add_one_iff]
      exact hle
    exact (progress_spec
      (c2GlobalFrozenCore (classes target) stream)
      hTargetCoreInfinite current) (hPrefixCurrent hmemPrefix)
  obtain ⟨selected, hwin, hSelectedActive, hmax⟩ :=
    c2WinningIndex_spec classes xs hactive
  have hSelectedLocalActivation :
      c2ActivatesOn (classes selected) xs :=
    c2_mem_activeIndices_iff.mp hSelectedActive
  have hSelectedEver :
      c2EverActivates (classes selected) stream := by
    exact (c2_local_activates_iff
      ((c2_activationTime_le_stableTime classes stream selected).trans
        hStableS)).1 hSelectedLocalActivation
  have hSelectedActivationLe :
      c2ActivationTime (classes selected) stream ≤ s :=
    (c2_activationTime_le_stableTime classes stream selected).trans
      hStableS
  have hSelectedLocalCore :
      c2FrozenCore (classes selected) xs =
        c2GlobalFrozenCore (classes selected) stream :=
    c2_localFrozenCore_eq_global hSelectedEver hSelectedActivationLe
  have hSelectedCoreInfinite :
      (c2GlobalFrozenCore (classes selected) stream).Infinite :=
    c2_globalFrozenCore_infinite hSelectedEver
  have hProgressMax := hmax target hTargetActive
  rw [hSequenceCurrent, hTargetLocalCore,
    componentProgress_of_infinite
      (c2GlobalFrozenCore (classes target) stream)
      current hTargetCoreInfinite,
    hSelectedLocalCore,
    componentProgress_of_infinite
      (c2GlobalFrozenCore (classes selected) stream)
      current hSelectedCoreInfinite] at hProgressMax
  have hSelectedGood :
      c2GlobalFrozenCore (classes selected) stream ⊆ L := by
    by_contra hnotGood
    have hSelectedBad : selected ∈ bad := by
      apply c2_mem_badIndices_iff.mpr
      exact ⟨hSelectedEver, hnotGood⟩
    have hObstructionNotL :=
      c2BadObstruction_spec classes stream L selected hSelectedBad
    have hObstructionNotCurrent :
        infiniteEnumeration
          (c2GlobalFrozenCore (classes selected) stream)
          hSelectedCoreInfinite (obstruction selected) ∉ current := by
      intro hmem
      apply hObstructionNotL
      exact GenLimit.Generic.mem_language_of_mem_sample_of_presents
        hPresentation hmem
    have hSelectedProgressLe :
        progress (c2GlobalFrozenCore (classes selected) stream)
          hSelectedCoreInfinite current ≤ obstruction selected :=
      progress_le_of_not_mem
        (c2GlobalFrozenCore (classes selected) stream)
        hSelectedCoreInfinite current hObstructionNotCurrent
    have hObstructionLe : obstruction selected ≤ badBound :=
      Finset.le_sup (f := obstruction) hSelectedBad
    omega
  have houtput :
      GenLimit.Generic.output gen stream s =
        infiniteEnumeration
          (c2GlobalFrozenCore (classes selected) stream)
          hSelectedCoreInfinite
          (progress (c2GlobalFrozenCore (classes selected) stream)
            hSelectedCoreInfinite current) := by
    unfold GenLimit.Generic.output
    change finiteEUCUnionGenerator classes s xs = _
    simp only [finiteEUCUnionGenerator]
    simp only [hwin]
    rw [hSequenceCurrent, hSelectedLocalCore]
    exact componentOutput_of_infinite
      (c2GlobalFrozenCore (classes selected) stream)
      current hSelectedCoreInfinite
  constructor
  · rw [houtput]
    exact hSelectedGood
      (infiniteEnumeration_mem
        (c2GlobalFrozenCore (classes selected) stream)
        hSelectedCoreInfinite _)
  · rw [houtput]
    exact progress_spec
      (c2GlobalFrozenCore (classes selected) stream)
      hSelectedCoreInfinite current

/-- Theorem C.2 (`thm:weaksuff`), with the paper's countability and UUS
assumptions and its literal finite-cover quantifier order. -/
theorem theorem_C2_finite_eventually_unbounded_closure_cover
    [Nonempty α] [Countable α]
    {H : GenLimit.Generic.LanguageClass α} (_hUUS : UUS H)
    (hcover : ∃ n : ℕ,
      ∃ classes : Fin n → GenLimit.Generic.LanguageClass α,
        IsFiniteCover H classes ∧
          ∀ i, EventuallyUnboundedClosure (classes i)) :
    GeneratableInLimit H := by
  obtain ⟨n, classes, hclasses, hEUC⟩ := hcover
  exact finite_euc_cover_implies_generatable_in_limit
    classes hclasses hEUC

end GenLimit.LiRamanTewari
