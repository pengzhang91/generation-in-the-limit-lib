import GenLimit.Paper02_LearningTheory.Closure
import Mathlib.Data.Finset.Max
import Mathlib.Logic.Denumerable

/-!
# A finite closure-dimension cover generates in the limit

This file formalizes Theorem 3.10 of Li--Raman--Tewari,
*Generation through the Lens of Learning Theory*, arXiv:2410.13714v5 /
COLT 2025 (source label `thm:geninlim`, lines 760--773 of the pinned TeX).

The implementation follows the proof in the paper.  Once sufficiently many
distinct examples have appeared, it freezes the common core of every
consistent class in the finite cover, enumerates those cores, and selects a
core whose longest observed initial segment is maximal.  A core contained in
the target has unbounded progress; every core not contained in the target is
blocked by its first element outside the target.  Finiteness of the cover then
forces the selected core eventually to be a target core.
-/

namespace GenLimit.LiRamanTewari

private noncomputable def coverBound {n : ℕ} (dims : Fin n → ℕ) : ℕ :=
  Finset.univ.sup dims

private theorem le_coverBound {n : ℕ} (dims : Fin n → ℕ) (i : Fin n) :
    dims i ≤ coverBound dims := by
  classical
  exact Finset.le_sup (f := dims) (Finset.mem_univ i)

/-- Extend a finite history by an arbitrary fallback.  Only prefixes no
longer than the original history are used below. -/
private noncomputable def extendHistory [Nonempty α] {t : ℕ} (xs : Fin t → α) :
    GenLimit.Generic.Stream α := by
  classical
  exact fun k ↦ if h : k < t then xs ⟨k, h⟩ else Classical.choice inferInstance

private theorem sample_extendHistory_eq [Nonempty α] {t r : ℕ} (xs : Fin t → α)
    (hrt : r ≤ t) :
    GenLimit.Generic.sample (extendHistory xs) r =
      GenLimit.Generic.sequenceSample (fun i : Fin r ↦ xs ⟨i, i.isLt.trans_le hrt⟩) := by
  classical
  ext x
  simp only [GenLimit.Generic.mem_sample_iff, GenLimit.Generic.mem_sequenceSample_iff]
  constructor
  · rintro ⟨k, hk, hx⟩
    refine ⟨⟨k, hk⟩, ?_⟩
    simpa [extendHistory, hk.trans_le hrt] using hx
  · rintro ⟨k, hx⟩
    refine ⟨k, k.isLt, ?_⟩
    simpa [extendHistory, k.isLt.trans_le hrt] using hx

private theorem sample_extendHistory_full [Nonempty α] {t : ℕ} (xs : Fin t → α) :
    GenLimit.Generic.sample (extendHistory xs) t =
      GenLimit.Generic.sequenceSample xs := by
  simpa using sample_extendHistory_eq xs le_rfl

/-- The first prefix containing `d+1` distinct examples, represented by its
sample.  If no such prefix exists, this is the empty set. -/
private noncomputable def historyAnchor [Nonempty α] (d : ℕ) {t : ℕ}
    (xs : Fin t → α) : Finset α := by
  classical
  let stream := extendHistory xs
  exact if h : ∃ r, (GenLimit.Generic.sample stream r).card = d + 1 then
    GenLimit.Generic.sample stream (Nat.find h)
  else ∅

private theorem historyAnchor_card [Nonempty α] (d : ℕ) {t : ℕ}
    (xs : Fin t → α) (hlarge : d < (GenLimit.Generic.sequenceSample xs).card) :
    (historyAnchor d xs).card = d + 1 := by
  classical
  have hle : d + 1 ≤ (GenLimit.Generic.sample (extendHistory xs) t).card := by
    rw [sample_extendHistory_full]
    exact Nat.succ_le_iff.mpr hlarge
  obtain ⟨r, _hrt, hr⟩ :=
    GenLimit.Generic.exists_sample_card_eq_of_le hle
  have hex : ∃ r, (GenLimit.Generic.sample (extendHistory xs) r).card = d + 1 :=
    ⟨r, hr⟩
  simp only [historyAnchor, dif_pos hex]
  exact Nat.find_spec hex

private theorem historyAnchor_eq_stream [Nonempty α]
    (d : ℕ) {stream : GenLimit.Generic.Stream α}
    (hex : ∃ r, (GenLimit.Generic.sample stream r).card = d + 1)
    {t : ℕ} (hfirst : Nat.find hex ≤ t) :
    historyAnchor d (fun i : Fin t ↦ stream i) =
      GenLimit.Generic.sample stream (Nat.find hex) := by
  classical
  let xs : Fin t → α := fun i ↦ stream i
  let localStream := extendHistory xs
  have hsampleEq : ∀ r ≤ t,
      GenLimit.Generic.sample localStream r = GenLimit.Generic.sample stream r := by
    intro r hrt
    ext x
    simp only [GenLimit.Generic.mem_sample_iff]
    constructor
    · rintro ⟨k, hk, hx⟩
      refine ⟨k, hk, ?_⟩
      simpa [localStream, xs, extendHistory, hk.trans_le hrt] using hx
    · rintro ⟨k, hk, hx⟩
      refine ⟨k, hk, ?_⟩
      simpa [localStream, xs, extendHistory, hk.trans_le hrt] using hx
  have hlocalAtFirst :
      (GenLimit.Generic.sample localStream (Nat.find hex)).card = d + 1 := by
    rw [hsampleEq _ hfirst]
    exact Nat.find_spec hex
  have localHex : ∃ r, (GenLimit.Generic.sample localStream r).card = d + 1 :=
    ⟨Nat.find hex, hlocalAtFirst⟩
  have hlocalLe : Nat.find localHex ≤ Nat.find hex :=
    Nat.find_min' localHex hlocalAtFirst
  have hlocalWithin : Nat.find localHex ≤ t := hlocalLe.trans hfirst
  have hglobalAtLocal :
      (GenLimit.Generic.sample stream (Nat.find localHex)).card = d + 1 := by
    rw [← hsampleEq _ hlocalWithin]
    exact Nat.find_spec localHex
  have hglobalLe : Nat.find hex ≤ Nat.find localHex :=
    Nat.find_min' hex hglobalAtLocal
  have hfind : Nat.find localHex = Nat.find hex :=
    Nat.le_antisymm hlocalLe hglobalLe
  change (if h : ∃ r, (GenLimit.Generic.sample localStream r).card = d + 1 then
      GenLimit.Generic.sample localStream (Nat.find h) else ∅) = _
  simp only [dif_pos localHex]
  rw [hfind, hsampleEq _ hfirst]

/-- A fixed equivalence between `ℕ` and an infinite subset of a countable
example space. -/
private noncomputable def infiniteSetEquiv [Countable α]
    (C : Set α) (hC : C.Infinite) : ℕ ≃ C := by
  letI : Infinite C := Set.Infinite.to_subtype hC
  exact (@Denumerable.eqv C (Classical.choice (nonempty_denumerable C))).symm

/-- A fixed repetition-free enumeration of an infinite subset of a countable
example space. -/
private noncomputable def infiniteEnumeration [Countable α]
    (C : Set α) (hC : C.Infinite) : ℕ → α :=
  fun k ↦ (infiniteSetEquiv C hC k).1

private theorem infiniteEnumeration_mem [Countable α]
    (C : Set α) (hC : C.Infinite) (k : ℕ) :
    infiniteEnumeration C hC k ∈ C := by
  exact (infiniteSetEquiv C hC k).2

private theorem infiniteEnumeration_injective [Countable α]
    (C : Set α) (hC : C.Infinite) :
    Function.Injective (infiniteEnumeration C hC) := by
  intro k l hkl
  have hsub : infiniteSetEquiv C hC k = infiniteSetEquiv C hC l := by
    apply Subtype.ext
    exact hkl
  exact (infiniteSetEquiv C hC).injective hsub

private theorem infiniteEnumeration_surjective [Countable α]
    (C : Set α) (hC : C.Infinite) {x : α} (hx : x ∈ C) :
    ∃ k, infiniteEnumeration C hC k = x := by
  refine ⟨(infiniteSetEquiv C hC).symm ⟨x, hx⟩, ?_⟩
  simp [infiniteEnumeration]

private theorem enumeration_misses_finset [Countable α]
    (C : Set α) (hC : C.Infinite) (S : Finset α) :
    ∃ k, infiniteEnumeration C hC k ∉ S := by
  by_contra hall
  push_neg at hall
  have hrange : Set.range (infiniteEnumeration C hC) ⊆ (↑S : Set α) := by
    rintro x ⟨k, rfl⟩
    exact hall k
  exact (Set.infinite_range_of_injective (infiniteEnumeration_injective C hC))
    (S.finite_toSet.subset hrange)

private noncomputable def progress [Countable α]
    (C : Set α) (hC : C.Infinite) (S : Finset α) : ℕ :=
  by
    classical
    exact Nat.find (enumeration_misses_finset C hC S)

private theorem progress_spec [Countable α]
    (C : Set α) (hC : C.Infinite) (S : Finset α) :
    infiniteEnumeration C hC (progress C hC S) ∉ S :=
  by
    classical
    exact Nat.find_spec (enumeration_misses_finset C hC S)

private theorem mem_of_lt_progress [Countable α]
    (C : Set α) (hC : C.Infinite) (S : Finset α) {k : ℕ}
    (hk : k < progress C hC S) :
    infiniteEnumeration C hC k ∈ S := by
  classical
  unfold progress at hk
  by_contra hnot
  exact Nat.find_min (enumeration_misses_finset C hC S) hk hnot

private theorem progress_le_of_not_mem [Countable α]
    (C : Set α) (hC : C.Infinite) (S : Finset α) {k : ℕ}
    (hk : infiniteEnumeration C hC k ∉ S) :
    progress C hC S ≤ k :=
  by
    classical
    unfold progress
    exact Nat.find_min' (enumeration_misses_finset C hC S) hk

private noncomputable def activeIndices {n : ℕ}
    (classes : Fin n → GenLimit.Generic.LanguageClass α) (anchor : Finset α) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i ↦ (versionSpace (classes i) anchor).Nonempty)

private theorem mem_activeIndices_iff {n : ℕ}
    {classes : Fin n → GenLimit.Generic.LanguageClass α}
    {anchor : Finset α} {i : Fin n} :
    i ∈ activeIndices classes anchor ↔
      (versionSpace (classes i) anchor).Nonempty := by
  simp [activeIndices]

private theorem active_core_infinite {n : ℕ}
    (classes : Fin n → GenLimit.Generic.LanguageClass α)
    (dims : Fin n → ℕ)
    (hDims : ∀ i, HasClosureDimension (classes i) (dims i))
    {anchor : Finset α} (hcard : anchor.card = coverBound dims + 1)
    {i : Fin n} (hi : i ∈ activeIndices classes anchor) :
    (commonCore (classes i) anchor).Infinite := by
  apply (hDims i).1 anchor
  · rw [hcard]
    exact Nat.lt_succ_of_le (le_coverBound dims i)
  · exact mem_activeIndices_iff.mp hi

private noncomputable def componentProgress [Countable α]
    (C : Set α) (current : Finset α) : ℕ := by
  classical
  exact if hC : C.Infinite then progress C hC current
  else 0

private theorem componentProgress_of_infinite [Countable α]
    (C : Set α) (current : Finset α) (hC : C.Infinite) :
    componentProgress C current = progress C hC current := by
  classical
  simp only [componentProgress, dif_pos hC]

private noncomputable def componentOutput [Nonempty α] [Countable α]
    (C : Set α) (current : Finset α) : α := by
  classical
  exact if hC : C.Infinite then
    infiniteEnumeration C hC (progress C hC current)
  else Classical.choice inferInstance

private theorem componentOutput_of_infinite [Nonempty α] [Countable α]
    (C : Set α) (current : Finset α) (hC : C.Infinite) :
    componentOutput C current =
      infiniteEnumeration C hC (progress C hC current) := by
  classical
  simp only [componentOutput, dif_pos hC]

/-- The paper's `argmax` choice among consistent finite-cover components. -/
private noncomputable def winningIndex [Countable α] {n : ℕ}
    (classes : Fin n → GenLimit.Generic.LanguageClass α)
    (anchor current : Finset α) :
    Option (Fin n) := by
  classical
  let active := activeIndices classes anchor
  if hactive : active.Nonempty then
    exact some (Classical.choose (Finset.exists_max_image active
      (fun i ↦ componentProgress (commonCore (classes i) anchor) current) hactive))
  else exact none

private theorem winningIndex_spec [Countable α] {n : ℕ}
    (classes : Fin n → GenLimit.Generic.LanguageClass α)
    (anchor current : Finset α)
    (hactive : (activeIndices classes anchor).Nonempty) :
    ∃ selected,
      winningIndex classes anchor current = some selected ∧
      selected ∈ activeIndices classes anchor ∧
      ∀ i, i ∈ activeIndices classes anchor →
        componentProgress (commonCore (classes i) anchor) current ≤
          componentProgress (commonCore (classes selected) anchor) current := by
  classical
  let active := activeIndices classes anchor
  let score : Fin n → ℕ :=
    fun i ↦ componentProgress (commonCore (classes i) anchor) current
  let chosen := Classical.choose (Finset.exists_max_image active score hactive)
  have hchosen := Classical.choose_spec (Finset.exists_max_image active score hactive)
  refine ⟨chosen, ?_, hchosen.1, ?_⟩
  · simp [winningIndex, active, hactive, score, chosen]
  · intro i hi
    exact hchosen.2 i hi

private noncomputable def badIndices {n : ℕ}
    (classes : Fin n → GenLimit.Generic.LanguageClass α)
    (anchor : Finset α) (L : GenLimit.Generic.Language α) : Finset (Fin n) := by
  classical
  exact (activeIndices classes anchor).filter
    (fun i ↦ ¬ commonCore (classes i) anchor ⊆ L)

private theorem mem_badIndices_iff {n : ℕ}
    {classes : Fin n → GenLimit.Generic.LanguageClass α}
    {anchor : Finset α} {L : GenLimit.Generic.Language α} {i : Fin n} :
    i ∈ badIndices classes anchor L ↔
      i ∈ activeIndices classes anchor ∧
        ¬ commonCore (classes i) anchor ⊆ L := by
  simp [badIndices]

private theorem bad_obstruction_exists [Countable α] {n : ℕ}
    (classes : Fin n → GenLimit.Generic.LanguageClass α)
    (dims : Fin n → ℕ)
    (hDims : ∀ i, HasClosureDimension (classes i) (dims i))
    (anchor : Finset α) (L : GenLimit.Generic.Language α)
    (hcard : anchor.card = coverBound dims + 1)
    {i : Fin n} (hi : i ∈ badIndices classes anchor L) :
    ∃ k,
      infiniteEnumeration (commonCore (classes i) anchor)
        (active_core_infinite classes dims hDims hcard
          (mem_badIndices_iff.mp hi).1) k ∉ L := by
  obtain ⟨x, hxCore, hxL⟩ := Set.not_subset.mp (mem_badIndices_iff.mp hi).2
  obtain ⟨k, hk⟩ := infiniteEnumeration_surjective
    (commonCore (classes i) anchor)
    (active_core_infinite classes dims hDims hcard
      (mem_badIndices_iff.mp hi).1) hxCore
  exact ⟨k, hk.symm ▸ hxL⟩

private noncomputable def badObstruction [Countable α] {n : ℕ}
    (classes : Fin n → GenLimit.Generic.LanguageClass α)
    (dims : Fin n → ℕ)
    (hDims : ∀ i, HasClosureDimension (classes i) (dims i))
    (anchor : Finset α) (L : GenLimit.Generic.Language α)
    (hcard : anchor.card = coverBound dims + 1) (i : Fin n) : ℕ := by
  classical
  exact if hi : i ∈ badIndices classes anchor L then
    Nat.find (bad_obstruction_exists classes dims hDims anchor L hcard hi)
  else 0

private theorem badObstruction_spec [Countable α] {n : ℕ}
    (classes : Fin n → GenLimit.Generic.LanguageClass α)
    (dims : Fin n → ℕ)
    (hDims : ∀ i, HasClosureDimension (classes i) (dims i))
    (anchor : Finset α) (L : GenLimit.Generic.Language α)
    (hcard : anchor.card = coverBound dims + 1) (i : Fin n)
    (hi : i ∈ badIndices classes anchor L) :
    infiniteEnumeration (commonCore (classes i) anchor)
      (active_core_infinite classes dims hDims hcard
        (mem_badIndices_iff.mp hi).1)
      (badObstruction classes dims hDims anchor L hcard i) ∉ L := by
  classical
  simp only [badObstruction, dif_pos hi]
  exact Nat.find_spec
    (bad_obstruction_exists classes dims hDims anchor L hcard hi)

private noncomputable def finiteClosureCoverGenerator [Nonempty α] [Countable α]
    {n : ℕ} (classes : Fin n → GenLimit.Generic.LanguageClass α)
    (dims : Fin n → ℕ) :
    GenLimit.Generic.Generator α := by
  classical
  exact fun _ xs ↦
    let current := GenLimit.Generic.sequenceSample xs
    if hlarge : coverBound dims < current.card then
      let anchor := historyAnchor (coverBound dims) xs
      match winningIndex classes anchor current with
      | none => Classical.choice inferInstance
      | some i => componentOutput (commonCore (classes i) anchor) current
    else Classical.choice inferInstance

private theorem finite_cover_with_chosen_dimensions_generates
    [Nonempty α] [Countable α]
    {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H)
    {n : ℕ} (classes : Fin n → GenLimit.Generic.LanguageClass α)
    (hcover : IsFiniteCover H classes)
    (dims : Fin n → ℕ)
    (hDims : ∀ i, HasClosureDimension (classes i) (dims i)) :
    GeneratableInLimit H := by
  classical
  let d := coverBound dims
  let gen := finiteClosureCoverGenerator classes dims
  refine ⟨gen, ?_⟩
  intro L hLH stream hP
  have hstream : GenLimit.Generic.StreamIn stream L :=
    GenLimit.Generic.streamIn_of_presents hP
  have hLUnion : L ∈ ⋃ i, classes i := by
    rw [← hcover]
    exact hLH
  obtain ⟨target, hLTarget⟩ := Set.mem_iUnion.mp hLUnion
  have hex : ∃ r, (GenLimit.Generic.sample stream r).card = d + 1 :=
    GenLimit.Generic.exists_sample_card_eq_of_presents_infinite
      hP (hUUS L hLH) (d + 1)
  let first := Nat.find hex
  let anchor := GenLimit.Generic.sample stream first
  have hanchorCard : anchor.card = d + 1 := by
    exact Nat.find_spec hex
  have hanchorCard' : anchor.card = coverBound dims + 1 := by
    simpa only [d] using hanchorCard
  have hTargetVS : L ∈ versionSpace (classes target) anchor := by
    exact ⟨hLTarget, sample_subset_of_streamIn hstream first⟩
  have hTargetActive : target ∈ activeIndices classes anchor :=
    mem_activeIndices_iff.mpr ⟨L, hTargetVS⟩
  have hTargetCoreInfinite :
      (commonCore (classes target) anchor).Infinite :=
    active_core_infinite classes dims hDims hanchorCard' hTargetActive
  have hTargetGood : commonCore (classes target) anchor ⊆ L :=
    commonCore_subset_of_mem_versionSpace hTargetVS
  let bad := badIndices classes anchor L
  let obstruction : Fin n → ℕ :=
    badObstruction classes dims hDims anchor L hanchorCard'
  let badBound : ℕ := bad.sup obstruction
  let goodPrefix : Finset α :=
    (Finset.range (badBound + 1)).image
      (infiniteEnumeration (commonCore (classes target) anchor)
        hTargetCoreInfinite)
  have hGoodPrefixL : (↑goodPrefix : Set α) ⊆ L := by
    intro x hx
    obtain ⟨k, _hk, hkx⟩ := Finset.mem_image.mp hx
    rw [← hkx]
    exact hTargetGood
      (infiniteEnumeration_mem (commonCore (classes target) anchor)
        hTargetCoreInfinite k)
  obtain ⟨prefixTime, hPrefixTime⟩ :=
    GenLimit.Generic.finset_eventually_subset_sample hP goodPrefix hGoodPrefixL
  refine ⟨max first prefixTime, ?_⟩
  intro s hs
  have hfirsts : first ≤ s := (Nat.le_max_left _ _).trans hs
  have hprefixs : prefixTime ≤ s := (Nat.le_max_right _ _).trans hs
  let current := GenLimit.Generic.sample stream s
  have hanchorCurrent : anchor ⊆ current :=
    GenLimit.Generic.sample_mono hfirsts
  have hcurrentLarge : d < current.card := by
    have hle : d + 1 ≤ current.card := by
      rw [← hanchorCard]
      exact Finset.card_le_card hanchorCurrent
    exact Nat.lt_of_succ_le hle
  have hlocalAnchor :
      historyAnchor d (fun i : Fin s ↦ stream i) = anchor := by
    simpa only [first, anchor] using historyAnchor_eq_stream d hex hfirsts
  have hlocalAnchor' :
      historyAnchor (coverBound dims) (fun i : Fin s ↦ stream i) = anchor := by
    simpa only [d] using hlocalAnchor
  have hPrefixCurrent : goodPrefix ⊆ current := by
    exact (hPrefixTime.trans (GenLimit.Generic.sample_mono hprefixs))
  have hTargetProgress :
      badBound < progress (commonCore (classes target) anchor)
        hTargetCoreInfinite current := by
    apply Nat.lt_of_not_ge
    intro hle
    have hmemPrefix :
        infiniteEnumeration (commonCore (classes target) anchor)
            hTargetCoreInfinite
            (progress (commonCore (classes target) anchor)
              hTargetCoreInfinite current) ∈ goodPrefix := by
      apply Finset.mem_image.mpr
      refine ⟨progress (commonCore (classes target) anchor)
        hTargetCoreInfinite current, ?_, rfl⟩
      simp only [Finset.mem_range, Nat.lt_add_one_iff]
      exact hle
    exact (progress_spec (commonCore (classes target) anchor)
      hTargetCoreInfinite current) (hPrefixCurrent hmemPrefix)
  have hactive : (activeIndices classes anchor).Nonempty :=
    ⟨target, hTargetActive⟩
  obtain ⟨selected, hwin, hSelectedActive, hmax⟩ :=
    winningIndex_spec classes anchor current hactive
  have hProgressMax := hmax target hTargetActive
  rw [componentProgress_of_infinite (commonCore (classes target) anchor)
      current hTargetCoreInfinite,
    componentProgress_of_infinite (commonCore (classes selected) anchor)
      current (active_core_infinite classes dims hDims hanchorCard'
        hSelectedActive)] at hProgressMax
  have hSelectedGood : commonCore (classes selected) anchor ⊆ L := by
    by_contra hnotGood
    have hSelectedBad : selected ∈ bad := by
      apply mem_badIndices_iff.mpr
      exact ⟨hSelectedActive, hnotGood⟩
    have hObstructionNotL := badObstruction_spec classes dims hDims anchor L
      hanchorCard' selected hSelectedBad
    have hObstructionNotCurrent :
        infiniteEnumeration (commonCore (classes selected) anchor)
          (active_core_infinite classes dims hDims hanchorCard'
            hSelectedActive) (obstruction selected) ∉ current := by
      intro hmem
      apply hObstructionNotL
      exact GenLimit.Generic.mem_language_of_mem_sample_of_presents hP hmem
    have hSelectedProgressLe :
        progress (commonCore (classes selected) anchor)
          (active_core_infinite classes dims hDims hanchorCard'
            hSelectedActive) current ≤ obstruction selected :=
      progress_le_of_not_mem (commonCore (classes selected) anchor)
        (active_core_infinite classes dims hDims hanchorCard'
          hSelectedActive) current hObstructionNotCurrent
    have hObstructionLe : obstruction selected ≤ badBound := by
      exact Finset.le_sup (f := obstruction) hSelectedBad
    omega
  have hSelectedCoreInfinite :
      (commonCore (classes selected) anchor).Infinite :=
    active_core_infinite classes dims hDims hanchorCard' hSelectedActive
  have houtput :
      GenLimit.Generic.output gen stream s =
        infiniteEnumeration (commonCore (classes selected) anchor)
          hSelectedCoreInfinite
          (progress (commonCore (classes selected) anchor)
            hSelectedCoreInfinite current) := by
    unfold GenLimit.Generic.output
    change finiteClosureCoverGenerator classes dims s
      (fun i : Fin s ↦ stream i) = _
    simp only [finiteClosureCoverGenerator,
      GenLimit.Generic.sequenceSample_prefix]
    rw [dif_pos (by simpa only [d, current] using hcurrentLarge)]
    simp only [hlocalAnchor']
    rw [hwin]
    exact componentOutput_of_infinite
      (commonCore (classes selected) anchor) current hSelectedCoreInfinite
  constructor
  · rw [houtput]
    exact hSelectedGood
      (infiniteEnumeration_mem (commonCore (classes selected) anchor)
        hSelectedCoreInfinite _)
  · rw [houtput]
    exact progress_spec (commonCore (classes selected) anchor)
      hSelectedCoreInfinite current

/-- Theorem 3.10 (`thm:geninlim`, Sufficient Condition for Generatability in
the Limit).

This is the paper's literal finite-cover hypothesis: there is one finite
sequence of classes whose union is `H`, and every member of that sequence has
finite closure dimension.  `Nonempty α` records the implicit assumption needed
for a generator to return an arbitrary value before the proof's threshold. -/
theorem finite_closure_dimension_cover_implies_generatable_in_limit
    [Nonempty α] [Countable α]
    {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H)
    (hcover : ∃ n : ℕ,
      ∃ classes : Fin n → GenLimit.Generic.LanguageClass α,
        IsFiniteCover H classes ∧
          ∀ i, HasFiniteClosureDimension (classes i)) :
    GeneratableInLimit H := by
  obtain ⟨n, classes, hclasses, hfinite⟩ := hcover
  choose dims hDims using hfinite
  exact finite_cover_with_chosen_dimensions_generates
    hUUS classes hclasses dims hDims

end GenLimit.LiRamanTewari
