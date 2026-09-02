import GenLimit.Paper28_ContrastiveGeneration.AbsenceCount
import Mathlib.Data.Nat.Pairing

/-!
# Corrupted contrastive/text incomparability

This file formalizes Theorem 6.8 of Li--Han--Jiang--Gao,
*Contrastive Identification and Generation in the Limit*
(arXiv:2605.06211v1).

The first witness is the co-singleton class from Theorems 6.5--6.6.  For the
reverse separation, the source uses an infinite common core `A`, disjoint
blocks `Bᵢ` of size `k+1`, and a nonempty common-negative region.  The
arithmetic realization below uses residues modulo four:

* `4n` is the common core;
* `4 * Nat.pair i r + 2` is the `r`-th point of block `Bᵢ`;
* `4n+1` supplies common-negative points.

Thus the implementation is support-isomorphic to the paper's construction,
but makes countability, block disjointness, and a clean shared contrastive
presentation explicit.
-/

namespace GenLimit
namespace ContrastiveGeneration

open GenLimit.Generic

/-! ## Monotonicity in the corruption budget -/

theorem isKCorruptedTextPresentation_mono
    {k ℓ : ℕ} (hkl : k ≤ ℓ)
    {stream : Stream α} {L : Set α}
    (hP : IsKCorruptedTextPresentation k stream L) :
    IsKCorruptedTextPresentation ℓ stream L :=
  Generic.occurrenceContaminatedPresentationAtMost_mono hkl hP

theorem kTextIdentifiable_antitone
    {k ℓ : ℕ} (hkl : k ≤ ℓ)
    {F : Generic.LanguageFamily α}
    (hF : KTextIdentifiable ℓ F) :
    KTextIdentifiable k F := by
  obtain ⟨M, hM⟩ := hF
  refine ⟨M, ?_⟩
  intro z stream hP
  exact hM z stream
    (isKCorruptedTextPresentation_mono hkl hP)

theorem coSingleton_kContrastivelyIdentifiable (k : ℕ) :
    KContrastivelyIdentifiable k coSingletonFamily := by
  obtain ⟨I, hI⟩ := theorem_6_6
  exact ⟨I, hI k⟩

theorem coSingleton_not_kTextIdentifiable
    {k : ℕ} (hk : 1 ≤ k) :
    ¬KTextIdentifiable k coSingletonFamily := by
  intro h
  exact theorem_6_5 (kTextIdentifiable_antitone hk h)

/-! ## The block witness from the reverse separation -/

/-- The paper's common infinite core `A`. -/
def robustCommonCore : Set ℕ :=
  Set.range fun n => 4 * n

/-- The `r`-th point of the `i`-th `(k+1)`-element block. -/
def robustBlockPoint (i : ℕ) {k : ℕ} (r : Fin (k + 1)) : ℕ :=
  4 * Nat.pair i r.val + 2

/-- The finite block `Bᵢ`. -/
def robustBlock (k i : ℕ) : Finset ℕ :=
  Finset.univ.image fun r : Fin (k + 1) =>
    robustBlockPoint i r

/-- Support `A ∪ Bᵢ`. -/
def robustBlockSupport (k i : ℕ) : Set ℕ :=
  robustCommonCore ∪ (robustBlock k i : Set ℕ)

/-- The indexed class `Hₖ = {A ∪ Bᵢ : i ≥ 0}`. -/
def robustBlockFamily (k : ℕ) : Generic.LanguageFamily ℕ :=
  robustBlockSupport k

theorem robustBlockPoint_pair_injective
    {k i j : ℕ} {r q : Fin (k + 1)}
    (h : robustBlockPoint i r = robustBlockPoint j q) :
    i = j ∧ r = q := by
  have hpair : Nat.pair i r.val = Nat.pair j q.val := by
    unfold robustBlockPoint at h
    omega
  have hunpair := congrArg Nat.unpair hpair
  simp only [Nat.unpair_pair] at hunpair
  constructor
  · exact congrArg Prod.fst hunpair
  · apply Fin.ext
    exact congrArg Prod.snd hunpair

theorem robustBlockPoint_fixed_injective
    (k i : ℕ) :
    Function.Injective (fun r : Fin (k + 1) =>
      robustBlockPoint i r) := by
  intro r q h
  exact (robustBlockPoint_pair_injective h).2

theorem robustBlock_card (k i : ℕ) :
    (robustBlock k i).card = k + 1 := by
  rw [robustBlock, Finset.card_image_iff.mpr]
  · simp
  · intro r _ q _ h
    exact robustBlockPoint_fixed_injective k i h

theorem mem_robustBlock_iff
    {k i x : ℕ} :
    x ∈ robustBlock k i ↔
      ∃ r : Fin (k + 1), robustBlockPoint i r = x := by
  simp [robustBlock]

theorem robustCommonCore_infinite :
    robustCommonCore.Infinite := by
  apply Set.infinite_range_of_injective
  intro m n h
  change 4 * m = 4 * n at h
  omega

theorem robustBlockSupport_infinite
    (k i : ℕ) :
    (robustBlockSupport k i).Infinite :=
  robustCommonCore_infinite.mono Set.subset_union_left

theorem robustBlockPoint_not_mem_commonCore
    {k i : ℕ} (r : Fin (k + 1)) :
    robustBlockPoint i r ∉ robustCommonCore := by
  change ¬∃ n, 4 * n = robustBlockPoint i r
  rintro ⟨n, hn⟩
  unfold robustBlockPoint at hn
  omega

theorem robustBlockPoint_mem_own
    {k i : ℕ} (r : Fin (k + 1)) :
    robustBlockPoint i r ∈ robustBlock k i := by
  exact mem_robustBlock_iff.mpr ⟨r, rfl⟩

theorem robustBlockPoint_not_mem_other
    {k i j : ℕ} (hij : i ≠ j) (r : Fin (k + 1)) :
    robustBlockPoint i r ∉ robustBlock k j := by
  intro hmem
  obtain ⟨q, hq⟩ := mem_robustBlock_iff.mp hmem
  exact hij (robustBlockPoint_pair_injective hq.symm).1

theorem robustBlockPoint_not_mem_otherSupport
    {k i j : ℕ} (hij : i ≠ j) (r : Fin (k + 1)) :
    robustBlockPoint i r ∉ robustBlockSupport k j := by
  rintro (hcore | hblock)
  · exact robustBlockPoint_not_mem_commonCore r hcore
  · exact robustBlockPoint_not_mem_other hij r hblock

theorem robustBlockSupport_ne
    {k i j : ℕ} (hij : i ≠ j) :
    robustBlockSupport k i ≠ robustBlockSupport k j := by
  intro heq
  let r : Fin (k + 1) := ⟨0, Nat.zero_lt_succ k⟩
  have hmemI :
      robustBlockPoint i r ∈ robustBlockSupport k i :=
    Or.inr (robustBlockPoint_mem_own r)
  have hmemJ : robustBlockPoint i r ∈ robustBlockSupport k j := by
    rw [← heq]
    exact hmemI
  exact robustBlockPoint_not_mem_otherSupport hij r hmemJ

/-! ## Identification from `k`-corrupted text -/

/-- Every finite set contained in a stream's range is eventually contained
in every later sample. -/
theorem finset_eventually_subset_sample_of_subset_range
    {stream : Stream α} (F : Finset α)
    (hF : (F : Set α) ⊆ Set.range stream) :
    ∃ T, ∀ t, T ≤ t → F ⊆ Generic.sample stream t := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      exact ⟨0, by simp⟩
  | @insert x F hx ih =>
      have hxRange : x ∈ Set.range stream :=
        hF (by simp)
      obtain ⟨n, hn⟩ := hxRange
      have hFRange : (F : Set α) ⊆ Set.range stream := by
        intro y hy
        exact hF (by simp [hy])
      obtain ⟨T, hT⟩ := ih hFRange
      refine ⟨max (n + 1) T, ?_⟩
      intro t ht y hy
      simp only [Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · rw [Generic.mem_sample_iff]
        exact
          ⟨n,
            lt_of_lt_of_le (Nat.lt_succ_self n)
              ((Nat.le_max_left (n + 1) T).trans ht),
            hn⟩
      · exact hT t ((Nat.le_max_right (n + 1) T).trans ht) hy

/-- A block is complete in a finite text history when all of its `k+1`
points have appeared. -/
def CompleteRobustBlock
    (k i : ℕ) {t : ℕ} (history : Fin t → ℕ) : Prop :=
  robustBlock k i ⊆ sequenceSample history

/-- The source's identifier: output any fully observed block, or zero before
one exists.  The corruption budget guarantees uniqueness on valid inputs. -/
noncomputable def robustBlockTextIdentifier
    (k : ℕ) : GenLimit.Angluin.SemanticIdentifier ℕ :=
  GenLimit.learnerOfFiniteHistory fun _t history => by
    classical
    by_cases h : ∃ i, CompleteRobustBlock k i history
    · exact Classical.choose h
    · exact 0

theorem robustBlockTextIdentifier_spec
    {k t : ℕ} {history : Fin t → ℕ}
    (h : ∃ i, CompleteRobustBlock k i history) :
    CompleteRobustBlock k
      (robustBlockTextIdentifier k (List.ofFn history)) history := by
  classical
  simp only [robustBlockTextIdentifier,
    GenLimit.learnerOfFiniteHistory_ofFn, dif_pos h]
  exact Classical.choose_spec h

/-- Seeing a whole false block would require `k+1` distinct corrupted
occurrences, contradicting the budget `k`. -/
theorem completeRobustBlock_eq_target
    {k i j t : ℕ} {stream : Stream ℕ}
    (hP :
      IsKCorruptedTextPresentation k stream
        (robustBlockSupport k i))
    (hcomplete : robustBlock k j ⊆ Generic.sample stream t) :
    j = i := by
  classical
  by_contra hji
  have hoccurs :
      ∀ r : Fin (k + 1),
        ∃ n, n < t ∧ stream n = robustBlockPoint j r := by
    intro r
    rw [← Generic.mem_sample_iff]
    exact hcomplete (robustBlockPoint_mem_own r)
  let position : Fin (k + 1) → ℕ :=
    fun r => Nat.find (hoccurs r)
  have position_spec (r : Fin (k + 1)) :
      position r < t ∧
        stream (position r) = robustBlockPoint j r :=
    Nat.find_spec (hoccurs r)
  have position_injective : Function.Injective position := by
    intro r q hrq
    apply robustBlockPoint_fixed_injective k j
    calc
      robustBlockPoint j r = stream (position r) :=
        (position_spec r).2.symm
      _ = stream (position q) := congrArg stream hrq
      _ = robustBlockPoint j q := (position_spec q).2
  let embedding : Fin (k + 1) ↪ ℕ :=
    ⟨position, position_injective⟩
  let witnessed : Finset ℕ :=
    Finset.univ.map embedding
  have hwitnessed :
      witnessed ⊆
        hP.1.toFinset := by
    intro n hn
    obtain ⟨r, _hr, hrn⟩ :=
      Finset.mem_map.mp hn
    have hvalue :
        stream n = robustBlockPoint j r := by
      rw [← hrn]
      exact (position_spec r).2
    apply hP.1.mem_toFinset.mpr
    change stream n ∉ robustBlockSupport k i
    rw [hvalue]
    exact robustBlockPoint_not_mem_otherSupport hji r
  have htooMany :
      k + 1 ≤ hP.1.toFinset.card := by
    calc
      k + 1 = witnessed.card := by
        simp [witnessed]
      _ ≤ hP.1.toFinset.card :=
        Finset.card_le_card hwitnessed
  have hcard :
      hP.1.toFinset.card =
        {n : ℕ |
          stream n ∉ robustBlockSupport k i}.ncard := by
    exact (Set.ncard_eq_toFinset_card _ hP.1).symm
  rw [hcard] at htooMany
  have hbudget :
      {n : ℕ |
        stream n ∉ robustBlockSupport k i}.ncard ≤ k :=
    hP.2.1
  omega

theorem robustBlock_kTextIdentifiable (k : ℕ) :
    KTextIdentifiable k (robustBlockFamily k) := by
  classical
  refine ⟨robustBlockTextIdentifier k, ?_⟩
  intro i stream hP
  have hblockRange :
      (robustBlock k i : Set ℕ) ⊆ Set.range stream := by
    intro x hx
    exact hP.2.2 (Or.inr hx)
  obtain ⟨T, hT⟩ :=
    finset_eventually_subset_sample_of_subset_range
      (robustBlock k i) hblockRange
  refine ⟨i, rfl, T, ?_⟩
  intro t ht
  have htarget :
      CompleteRobustBlock k i
        (fun r : Fin t => stream r) := by
    unfold CompleteRobustBlock
    rw [sequenceSample_prefix]
    exact hT t ht
  have hexists :
      ∃ j, CompleteRobustBlock k j
        (fun r : Fin t => stream r) :=
    ⟨i, htarget⟩
  have hchosen :
      robustBlock k
          (robustBlockTextIdentifier k
            (List.ofFn (fun r : Fin t => stream r))) ⊆
        Generic.sample stream t := by
    have hspec :=
      robustBlockTextIdentifier_spec hexists
    unfold CompleteRobustBlock at hspec
    simpa only [sequenceSample_prefix] using hspec
  change robustBlockTextIdentifier k (GenLimit.textPrefix stream t) = i
  rw [GenLimit.textPrefix_eq_ofFn]
  exact completeRobustBlock_eq_target hP hchosen

/-! ## A clean shared contrastive presentation -/

def robustCoreEdge (n : ℕ) : Edge ℕ :=
  ⟨4 * n, 4 * n + 1, by omega⟩

def robustCyclingIndex (k n : ℕ) : Fin (k + 1) :=
  ⟨n % (k + 1), Nat.mod_lt _ (Nat.zero_lt_succ k)⟩

def robustBlockEdge (k n : ℕ) : Edge ℕ :=
  ⟨robustBlockPoint 0 (robustCyclingIndex k n),
    robustBlockPoint 1 (robustCyclingIndex k n),
    by
      intro h
      exact Nat.zero_ne_one
        (robustBlockPoint_pair_injective h).1⟩

/-- Pairing index `0` enumerates core/common-negative edges; every other
first pairing coordinate enumerates block-zero/block-one edges. -/
def robustSharedStream (k : ℕ) (n : ℕ) : Edge ℕ :=
  if (Nat.unpair n).1 = 0 then
    robustCoreEdge (Nat.unpair n).2
  else
    robustBlockEdge k (Nat.unpair n).2

theorem robustCoreEdge_crosses
    (k i n : ℕ) :
    Crosses (robustBlockSupport k i)
      (robustCoreEdge n) := by
  left
  constructor
  · exact Or.inl ⟨n, rfl⟩
  · rintro (⟨m, hm⟩ | hblock)
    · change 4 * m = 4 * n + 1 at hm
      omega
    · obtain ⟨r, hr⟩ := mem_robustBlock_iff.mp hblock
      unfold robustBlockPoint at hr
      change 4 * Nat.pair i r.val + 2 = 4 * n + 1 at hr
      omega

theorem robustBlockEdge_crosses_zero
    (k n : ℕ) :
    Crosses (robustBlockSupport k 0)
      (robustBlockEdge k n) := by
  left
  constructor
  · exact Or.inr
      (robustBlockPoint_mem_own (robustCyclingIndex k n))
  · exact robustBlockPoint_not_mem_otherSupport
      (by omega) (robustCyclingIndex k n)

theorem robustBlockEdge_crosses_one
    (k n : ℕ) :
    Crosses (robustBlockSupport k 1)
      (robustBlockEdge k n) := by
  right
  constructor
  · exact Or.inr
      (robustBlockPoint_mem_own (robustCyclingIndex k n))
  · exact robustBlockPoint_not_mem_otherSupport
      (by omega) (robustCyclingIndex k n)

theorem robustSharedStream_crosses_zero
    (k n : ℕ) :
    Crosses (robustBlockSupport k 0)
      (robustSharedStream k n) := by
  unfold robustSharedStream
  split
  · exact robustCoreEdge_crosses k 0 _
  · exact robustBlockEdge_crosses_zero k _

theorem robustSharedStream_crosses_one
    (k n : ℕ) :
    Crosses (robustBlockSupport k 1)
      (robustSharedStream k n) := by
  unfold robustSharedStream
  split
  · exact robustCoreEdge_crosses k 1 _
  · exact robustBlockEdge_crosses_one k _

theorem robustSharedStream_covers_zero
    (k : ℕ) :
    robustBlockSupport k 0 ⊆
      {x | ∃ n, Incident x (robustSharedStream k n)} := by
  intro x hx
  rcases hx with ⟨m, rfl⟩ | hx
  · refine ⟨Nat.pair 0 m, ?_⟩
    left
    simp [robustSharedStream, robustCoreEdge]
  · obtain ⟨r, rfl⟩ := mem_robustBlock_iff.mp hx
    refine ⟨Nat.pair 1 r.val, ?_⟩
    left
    simp [robustSharedStream, robustBlockEdge,
      robustCyclingIndex, Nat.mod_eq_of_lt r.isLt]

theorem robustSharedStream_covers_one
    (k : ℕ) :
    robustBlockSupport k 1 ⊆
      {x | ∃ n, Incident x (robustSharedStream k n)} := by
  intro x hx
  rcases hx with ⟨m, rfl⟩ | hx
  · refine ⟨Nat.pair 0 m, ?_⟩
    left
    simp [robustSharedStream, robustCoreEdge]
  · obtain ⟨r, rfl⟩ := mem_robustBlock_iff.mp hx
    refine ⟨Nat.pair 1 r.val, ?_⟩
    right
    simp [robustSharedStream, robustBlockEdge,
      robustCyclingIndex, Nat.mod_eq_of_lt r.isLt]

theorem robustSharedStream_presents_zero
    (k : ℕ) :
    IsContrastivePresentation
      (robustSharedStream k) (robustBlockSupport k 0) :=
  ⟨robustSharedStream_crosses_zero k,
    robustSharedStream_covers_zero k⟩

theorem robustSharedStream_presents_one
    (k : ℕ) :
    IsContrastivePresentation
      (robustSharedStream k) (robustBlockSupport k 1) :=
  ⟨robustSharedStream_crosses_one k,
    robustSharedStream_covers_one k⟩

theorem cleanPresentation_is_kCorrupted
    (k : ℕ) {stream : ℕ → Edge α} {L : Set α}
    (hP : IsContrastivePresentation stream L) :
    IsKCorruptedContrastivePresentation k stream L := by
  have hbad :
      Generic.ViolationIndices stream (Crosses L) = ∅ := by
    ext n
    simp [Generic.ViolationIndices, hP.1 n]
  constructor
  · rw [hbad]
    exact Set.finite_empty
  constructor
  · rw [hbad]
    simp
  · exact hP.2

theorem not_kContrastivelyIdentifiable_of_shared
    (k : ℕ) {F : Generic.LanguageFamily α}
    {i j : ℕ} (hij : F i ≠ F j)
    {stream : ℕ → Edge α}
    (hi : IsContrastivePresentation stream (F i))
    (hj : IsContrastivePresentation stream (F j)) :
    ¬KContrastivelyIdentifiable k F := by
  rintro ⟨I, hI⟩
  obtain ⟨a, ha, Ta, hTa⟩ :=
    hI i stream (cleanPresentation_is_kCorrupted k hi)
  obtain ⟨b, hb, Tb, hTb⟩ :=
    hI j stream (cleanPresentation_is_kCorrupted k hj)
  have hab : a = b := by
    exact
      (hTa (max Ta Tb) (Nat.le_max_left _ _)).symm.trans
        (hTb (max Ta Tb) (Nat.le_max_right _ _))
  apply hij
  calc
    F i = F a := ha.symm
    _ = F b := congrArg F hab
    _ = F j := hb

theorem robustBlock_not_kContrastivelyIdentifiable
    (k : ℕ) :
    ¬KContrastivelyIdentifiable k (robustBlockFamily k) := by
  apply not_kContrastivelyIdentifiable_of_shared
      k (i := 0) (j := 1)
      (stream := robustSharedStream k)
  · exact robustBlockSupport_ne (by omega)
  · exact robustSharedStream_presents_zero k
  · exact robustSharedStream_presents_one k

/-- Theorem 6.8: for every positive corruption budget, the co-singleton
class separates corrupted contrastive identification from corrupted text
identification, while the `(k+1)`-block class gives the reverse separation.
-/
theorem theorem_6_8
    (k : ℕ) (hk : 1 ≤ k) :
    (KContrastivelyIdentifiable k coSingletonFamily ∧
      ¬KTextIdentifiable k coSingletonFamily) ∧
    (KTextIdentifiable k (robustBlockFamily k) ∧
      ¬KContrastivelyIdentifiable k (robustBlockFamily k)) := by
  exact
    ⟨⟨coSingleton_kContrastivelyIdentifiable k,
        coSingleton_not_kTextIdentifiable hk⟩,
      ⟨robustBlock_kTextIdentifiable k,
        robustBlock_not_kContrastivelyIdentifiable k⟩⟩

end ContrastiveGeneration
end GenLimit
