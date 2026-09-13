import GenLimit.Paper17_InfiniteContamination.PriorityStabilization
import GenLimit.Support.Asymptotics.SparseSquares
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.FieldSimp

/-!
# A common vanishing-noise presentation of a finite family

Source: Mehrotra--Velegkas--Yu--Zhou,
*Language Generation with Infinite Contamination*,
arXiv:2511.07417v1, necessity proof of Theorem 6.11.

If a finite family has infinite common intersection, the source enumerates
the common intersection on ordinary rounds and schedules all remaining
points on a density-zero set of rounds.  This file makes that construction
literal.  Perfect squares are the sparse rounds.  Both the finite and
infinite exceptional-set cases are handled, so the resulting stream is
injective, covers the union of the family, and has vanishing noise relative
to every member.
-/

namespace GenLimit.InfiniteContamination

open Filter
open scoped Topology

/-- Perfect-square schedule positions, including zero. -/
abbrev SparseSquare : ℕ → Prop := SparseSquares.IsSquare

/-- Ordinary positions in the square-sparse schedule. -/
def SparseNonSquare (n : ℕ) : Prop := ¬ SparseSquare n

noncomputable local instance : DecidablePred SparseSquare :=
  Classical.decPred _

noncomputable local instance : DecidablePred SparseNonSquare :=
  Classical.decPred _

theorem sparseSquare_iff_sqrt (n : ℕ) :
    SparseSquare n ↔ Nat.sqrt n * Nat.sqrt n = n :=
  SparseSquares.isSquare_iff_sqrt n

@[simp] theorem sparseSquare_mul_self (k : ℕ) :
    SparseSquare (k * k) := SparseSquares.isSquare_mul_self k

/-- A canonical nonsquare strictly between consecutive squares. -/
abbrev sparseBetweenSquares : ℕ → ℕ := SparseSquares.betweenSquares

theorem sparseBetweenSquares_nonsquare (k : ℕ) :
    SparseNonSquare (sparseBetweenSquares k) := by
  simpa [SparseNonSquare, SparseSquares.IsNonSquare] using
    SparseSquares.betweenSquares_isNonSquare k

theorem sparseBetweenSquares_strictMono :
    StrictMono sparseBetweenSquares :=
  SparseSquares.betweenSquares_strictMono

theorem sparseNonSquare_infinite :
    {n : ℕ | SparseNonSquare n}.Infinite := by
  simpa [SparseNonSquare, SparseSquares.IsNonSquare] using
    SparseSquares.isNonSquare_infinite

theorem count_sparseSquare_le_sqrt_add_one (n : ℕ) :
    Nat.count SparseSquare n ≤ Nat.sqrt n + 1 :=
  SparseSquares.count_isSquare_le_sqrt_add_one n

theorem tendsto_sparseSqrt_add_one_div :
    Tendsto
      (fun n : ℕ => ((Nat.sqrt n : ℝ) + 1) / (n : ℝ))
      atTop (nhds 0) :=
  SparseSquares.natSqrt_add_one_div_self_tendsto_zero
/-! ## Infinite exceptional set -/

/-- Merge two disjoint infinite languages, placing the second language only
at square positions. -/
noncomputable def squareSparseMerge
    (core exceptional : Set ℕ) (_hcore : core.Infinite)
    (_hexceptional : exceptional.Infinite) : GenLimit.Generic.Stream ℕ :=
  fun n =>
    if _hsquare : SparseSquare n then
      Nat.nth (fun x => x ∈ exceptional) (Nat.sqrt n)
    else
      Nat.nth (fun x => x ∈ core) (Nat.count SparseNonSquare n)

theorem squareSparseMerge_mem_of_square
    (core exceptional : Set ℕ) (hcore : core.Infinite)
    (hexceptional : exceptional.Infinite) {n : ℕ}
    (hn : SparseSquare n) :
    squareSparseMerge core exceptional hcore hexceptional n ∈ exceptional := by
  rw [squareSparseMerge, dif_pos hn]
  exact Nat.nth_mem_of_infinite hexceptional _

theorem squareSparseMerge_mem_of_nonsquare
    (core exceptional : Set ℕ) (hcore : core.Infinite)
    (hexceptional : exceptional.Infinite) {n : ℕ}
    (hn : SparseNonSquare n) :
    squareSparseMerge core exceptional hcore hexceptional n ∈ core := by
  have hn' : ¬ SparseSquare n := hn
  rw [squareSparseMerge, dif_neg hn']
  exact Nat.nth_mem_of_infinite hcore _

theorem squareSparseMerge_injective
    {core exceptional : Set ℕ} (hcore : core.Infinite)
    (hexceptional : exceptional.Infinite)
    (hdisjoint : Disjoint core exceptional) :
    Function.Injective
      (squareSparseMerge core exceptional hcore hexceptional) := by
  intro m n hmn
  classical
  by_cases hm : SparseSquare m
  · by_cases hn : SparseSquare n
    · have hrank : Nat.sqrt m = Nat.sqrt n :=
        Nat.nth_injective hexceptional (by
          simpa [squareSparseMerge, hm, hn] using hmn)
      calc
        m = Nat.sqrt m * Nat.sqrt m :=
          ((sparseSquare_iff_sqrt m).mp hm).symm
        _ = Nat.sqrt n * Nat.sqrt n := by rw [hrank]
        _ = n := (sparseSquare_iff_sqrt n).mp hn
    · have hmException :=
          squareSparseMerge_mem_of_square core exceptional hcore
            hexceptional hm
      have hnCore :=
          squareSparseMerge_mem_of_nonsquare core exceptional hcore
            hexceptional hn
      rw [hmn] at hmException
      exact (Set.disjoint_left.1 hdisjoint hnCore hmException).elim
  · by_cases hn : SparseSquare n
    · have hmCore :=
          squareSparseMerge_mem_of_nonsquare core exceptional hcore
            hexceptional hm
      have hnException :=
          squareSparseMerge_mem_of_square core exceptional hcore
            hexceptional hn
      rw [hmn] at hmCore
      exact (Set.disjoint_left.1 hdisjoint hmCore hnException).elim
    · have hrank :
          Nat.count SparseNonSquare m =
            Nat.count SparseNonSquare n :=
        Nat.nth_injective hcore (by
          simpa [squareSparseMerge, hm, hn] using hmn)
      calc
        m = Nat.nth SparseNonSquare
              (Nat.count SparseNonSquare m) :=
          (Nat.nth_count hm).symm
        _ = Nat.nth SparseNonSquare
              (Nat.count SparseNonSquare n) := by rw [hrank]
        _ = n := Nat.nth_count hn

theorem range_squareSparseMerge
    {core exceptional : Set ℕ} (hcore : core.Infinite)
    (hexceptional : exceptional.Infinite) :
    Set.range (squareSparseMerge core exceptional hcore hexceptional) =
      core ∪ exceptional := by
  classical
  ext x
  constructor
  · rintro ⟨n, rfl⟩
    by_cases hn : SparseSquare n
    · exact Set.mem_union_right _
        (squareSparseMerge_mem_of_square core exceptional hcore
          hexceptional hn)
    · exact Set.mem_union_left _
        (squareSparseMerge_mem_of_nonsquare core exceptional hcore
          hexceptional hn)
  · intro hx
    rcases hx with hxCore | hxExceptional
    · let k := Nat.count (fun y => y ∈ core) x
      let n := Nat.nth SparseNonSquare k
      have hn : SparseNonSquare n :=
        Nat.nth_mem_of_infinite sparseNonSquare_infinite k
      have hn' : ¬ SparseSquare n := hn
      refine ⟨n, ?_⟩
      rw [squareSparseMerge, dif_neg hn']
      rw [Nat.count_nth_of_infinite sparseNonSquare_infinite]
      exact Nat.nth_count hxCore
    · let k := Nat.count (fun y => y ∈ exceptional) x
      refine ⟨k * k, ?_⟩
      simp only [squareSparseMerge, sparseSquare_mul_self, dif_pos]
      rw [Nat.sqrt_eq]
      exact Nat.nth_count hxExceptional

theorem squareSparseMerge_vanishingNoise_of_core_subset
    {core exceptional L : Set ℕ} (hcore : core.Infinite)
    (hexceptional : exceptional.Infinite) (hcoreL : core ⊆ L) :
    VanishingNoise
      (squareSparseMerge core exceptional hcore hexceptional) L := by
  let stream := squareSparseMerge core exceptional hcore hexceptional
  have hcount (n : ℕ) :
      noiseCount stream L n ≤ Nat.count SparseSquare n := by
    classical
    rw [Nat.count_eq_card_filter_range]
    unfold noiseCount
    apply Finset.card_le_card
    intro t ht
    have htBad := (Finset.mem_filter.mp ht).2
    have htRange := (Finset.mem_filter.mp ht).1
    refine Finset.mem_filter.mpr ⟨htRange, ?_⟩
    by_contra htNotSquare
    exact htBad (hcoreL
      (squareSparseMerge_mem_of_nonsquare
        core exceptional hcore hexceptional htNotSquare))
  unfold VanishingNoise
  have hbound :
      ∀ n, empiricalNoiseRate stream L n ≤
        ((Nat.sqrt n : ℝ) + 1) / n := by
    intro n
    by_cases hn : n = 0
    · simp [empiricalNoiseRate, hn]
    · simp only [empiricalNoiseRate, hn, if_false]
      apply div_le_div_of_nonneg_right
      · exact_mod_cast
          (hcount n |>.trans (count_sparseSquare_le_sqrt_add_one n))
      · positivity
  exact squeeze_zero
    (fun n => empiricalNoiseRate_nonneg stream L n)
    hbound tendsto_sparseSqrt_add_one_div

/-! ## Finite exceptional set -/

/-- Merge an infinite common core with a finite exceptional set by listing
all exceptional values first and then the core. -/
noncomputable def finitePrefixMerge
    (core exceptional : Set ℕ) (_hcore : core.Infinite)
    (hexceptional : exceptional.Finite) : GenLimit.Generic.Stream ℕ :=
  fun n =>
    if _hn : n < hexceptional.toFinset.card then
      Nat.nth (fun x => x ∈ exceptional) n
    else
      Nat.nth (fun x => x ∈ core)
        (n - hexceptional.toFinset.card)

theorem finitePrefixMerge_injective
    {core exceptional : Set ℕ} (hcore : core.Infinite)
    (hexceptional : exceptional.Finite)
    (hdisjoint : Disjoint core exceptional) :
    Function.Injective (finitePrefixMerge core exceptional hcore hexceptional) := by
  intro m n hmn
  classical
  let d := hexceptional.toFinset.card
  by_cases hm : m < d
  · by_cases hn : n < d
    · exact Nat.nth_injOn hexceptional hm hn (by
        simpa [finitePrefixMerge, d, hm, hn] using hmn)
    · have hmException :
          finitePrefixMerge core exceptional hcore hexceptional m ∈
            exceptional := by
          simp only [finitePrefixMerge, d, hm, dif_pos]
          exact Nat.nth_mem_of_lt_card hexceptional hm
      have hnCore :
          finitePrefixMerge core exceptional hcore hexceptional n ∈ core := by
        rw [finitePrefixMerge, dif_neg (by simpa [d] using hn)]
        exact Nat.nth_mem_of_infinite hcore _
      rw [hmn] at hmException
      exact (Set.disjoint_left.1 hdisjoint hnCore hmException).elim
  · by_cases hn : n < d
    · have hmCore :
          finitePrefixMerge core exceptional hcore hexceptional m ∈ core := by
        rw [finitePrefixMerge, dif_neg (by simpa [d] using hm)]
        exact Nat.nth_mem_of_infinite hcore _
      have hnException :
          finitePrefixMerge core exceptional hcore hexceptional n ∈
            exceptional := by
        simp only [finitePrefixMerge, d, hn, dif_pos]
        exact Nat.nth_mem_of_lt_card hexceptional hn
      rw [hmn] at hmCore
      exact (Set.disjoint_left.1 hdisjoint hmCore hnException).elim
    · have hsub : m - d = n - d :=
        Nat.nth_injective hcore (by
          simpa [finitePrefixMerge, d, hm, hn] using hmn)
      omega

theorem range_finitePrefixMerge
    {core exceptional : Set ℕ} (hcore : core.Infinite)
    (hexceptional : exceptional.Finite) :
    Set.range (finitePrefixMerge core exceptional hcore hexceptional) =
      core ∪ exceptional := by
  ext x
  classical
  let d := hexceptional.toFinset.card
  constructor
  · rintro ⟨n, rfl⟩
    by_cases hn : n < d
    · exact Set.mem_union_right _ (by
        simp only [finitePrefixMerge, d, hn, dif_pos]
        exact Nat.nth_mem_of_lt_card hexceptional hn)
    · exact Set.mem_union_left _ (by
        rw [finitePrefixMerge, dif_neg (by simpa [d] using hn)]
        exact Nat.nth_mem_of_infinite hcore _)
  · intro hx
    rcases hx with hxCore | hxExceptional
    · let k := Nat.count (fun y => y ∈ core) x
      refine ⟨d + k, ?_⟩
      simp only [finitePrefixMerge, d, Nat.not_lt.mpr (Nat.le_add_right d k),
        Nat.add_sub_cancel_left]
      exact Nat.nth_count hxCore
    · obtain ⟨k, hk, hkx⟩ :=
        Nat.exists_lt_card_finite_nth_eq hexceptional hxExceptional
      refine ⟨k, ?_⟩
      simpa [finitePrefixMerge, d, hk] using hkx

theorem finitePrefixMerge_vanishingNoise_of_core_subset
    {core exceptional L : Set ℕ} (hcore : core.Infinite)
    (hexceptional : exceptional.Finite) (hcoreL : core ⊆ L) :
    VanishingNoise
      (finitePrefixMerge core exceptional hcore hexceptional) L := by
  apply finiteNoise_implies_vanishingNoise
  apply (Set.finite_Iio hexceptional.toFinset.card).subset
  intro n hn
  by_contra hnBound
  have hnBound' : ¬ n < hexceptional.toFinset.card := by
    simpa only [Set.mem_Iio] using hnBound
  have hnCore :
      finitePrefixMerge core exceptional hcore hexceptional n ∈ core := by
    rw [finitePrefixMerge, dif_neg hnBound']
    exact Nat.nth_mem_of_infinite hcore _
  exact hn (hcoreL hnCore)

/-! ## Uniform wrapper -/

/-- A sparse merge chosen by whether the exceptional language is infinite. -/
noncomputable def sparseMergePresentation
    (core exceptional : Set ℕ) (hcore : core.Infinite) :
    GenLimit.Generic.Stream ℕ := by
  classical
  exact if hexceptional : exceptional.Infinite then
      squareSparseMerge core exceptional hcore hexceptional
    else
      finitePrefixMerge core exceptional hcore
        (Set.not_infinite.mp hexceptional)

theorem sparseMergePresentation_injective
    {core exceptional : Set ℕ} (hcore : core.Infinite)
    (hdisjoint : Disjoint core exceptional) :
    Function.Injective (sparseMergePresentation core exceptional hcore) := by
  classical
  by_cases hexceptional : exceptional.Infinite
  · simpa [sparseMergePresentation, hexceptional] using
      squareSparseMerge_injective hcore hexceptional hdisjoint
  · simpa [sparseMergePresentation, hexceptional] using
      finitePrefixMerge_injective hcore
        (Set.not_infinite.mp hexceptional) hdisjoint

theorem range_sparseMergePresentation
    {core exceptional : Set ℕ} (hcore : core.Infinite) :
    Set.range (sparseMergePresentation core exceptional hcore) =
      core ∪ exceptional := by
  classical
  by_cases hexceptional : exceptional.Infinite
  · simpa [sparseMergePresentation, hexceptional] using
      range_squareSparseMerge hcore hexceptional
  · simpa [sparseMergePresentation, hexceptional] using
      range_finitePrefixMerge hcore (Set.not_infinite.mp hexceptional)

theorem sparseMergePresentation_vanishingNoise_of_core_subset
    {core exceptional L : Set ℕ} (hcore : core.Infinite)
    (hcoreL : core ⊆ L) :
    VanishingNoise (sparseMergePresentation core exceptional hcore) L := by
  classical
  by_cases hexceptional : exceptional.Infinite
  · simpa [sparseMergePresentation, hexceptional] using
      squareSparseMerge_vanishingNoise_of_core_subset
        hcore hexceptional hcoreL
  · simpa [sparseMergePresentation, hexceptional] using
      finitePrefixMerge_vanishingNoise_of_core_subset
        hcore (Set.not_infinite.mp hexceptional) hcoreL

/-! ## Application to a finite indexed family -/

/-- Union of a finite family of indexed languages. -/
def finiteIndexedUnion
    (family : ℕ → GenLimit.Generic.Language ℕ)
    (S : Finset ℕ) : GenLimit.Generic.Language ℕ :=
  {x | ∃ i, i ∈ S ∧ x ∈ family i}

theorem family_subset_finiteIndexedUnion
    (family : ℕ → GenLimit.Generic.Language ℕ)
    {S : Finset ℕ} {i : ℕ} (hi : i ∈ S) :
    family i ⊆ finiteIndexedUnion family S := by
  intro x hx
  exact ⟨i, hi, hx⟩

theorem indexedCommonCore_subset
    (family : ℕ → GenLimit.Generic.Language ℕ)
    {S : Finset ℕ} {i : ℕ} (hi : i ∈ S) :
    finiteCommonCore (indexedLanguages family S) ⊆ family i := by
  classical
  apply finiteCommonCore_subset_of_mem
  exact Finset.mem_image.mpr ⟨i, hi, rfl⟩

theorem commonCore_union_exceptional_eq_union
    (family : ℕ → GenLimit.Generic.Language ℕ)
    (S : Finset ℕ) (hS : S.Nonempty) :
    finiteCommonCore (indexedLanguages family S) ∪
        (finiteIndexedUnion family S \
          finiteCommonCore (indexedLanguages family S)) =
      finiteIndexedUnion family S := by
  apply Set.union_diff_cancel
  intro x hx
  obtain ⟨i, hi⟩ := hS
  exact ⟨i, hi,
    indexedCommonCore_subset family hi hx⟩

/-- A finite family with infinite common core has a single injective stream
that covers every member and has vanishing noise relative to every member.
This is the common-adversary construction used in Theorem 6.11 necessity. -/
theorem exists_common_vanishingNoise_presentation
    (family : ℕ → GenLimit.Generic.Language ℕ)
    (S : Finset ℕ)
    (hS : S.Nonempty)
    (hcore :
      (finiteCommonCore (indexedLanguages family S)).Infinite) :
    ∃ stream : GenLimit.Generic.Stream ℕ,
      Function.Injective stream ∧
        ∀ i, i ∈ S →
          VanishingNoiseArbitraryOmissionEnumeration
            stream (family i) := by
  let core := finiteCommonCore (indexedLanguages family S)
  let union := finiteIndexedUnion family S
  let exceptional := union \ core
  have hdisjoint : Disjoint core exceptional := by
    exact Set.disjoint_sdiff_right
  let stream := sparseMergePresentation core exceptional hcore
  have hinjective : Function.Injective stream :=
    sparseMergePresentation_injective hcore hdisjoint
  have hrange : Set.range stream = union := by
    calc
      Set.range stream = core ∪ exceptional :=
        range_sparseMergePresentation hcore
      _ = union := commonCore_union_exceptional_eq_union family S hS
  refine ⟨stream, hinjective, ?_⟩
  intro i hi
  have hcoreFamily : core ⊆ family i :=
    indexedCommonCore_subset family hi
  have hcover : NoOmissions stream (family i) := by
    rw [NoOmissions, hrange]
    exact family_subset_finiteIndexedUnion family hi
  have homissions : ArbitraryOmissions stream (family i) := by
    apply hcore.mono
    intro x hx
    exact ⟨hrange.symm.subset
      (family_subset_finiteIndexedUnion family hi (hcoreFamily hx)),
      hcoreFamily hx⟩
  have hnoise : VanishingNoise stream (family i) :=
    sparseMergePresentation_vanishingNoise_of_core_subset
      hcore hcoreFamily
  exact ⟨hinjective, homissions, hnoise⟩

end GenLimit.InfiniteContamination
