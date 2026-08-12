import GenLimit.Paper11_UnionClosednessOfLanguageGeneration.AlternatingPhaseCore
import GenLimit.Paper11_UnionClosednessOfLanguageGeneration.Definitions
import GenLimit.Paper11_UnionClosednessOfLanguageGeneration.MinimalPairClasses
import GenLimit.Core.Text

/-!
# Shared exact-negative alternating-phase recursion

Source: Hanneke--Karbasi--Mehrotra--Velegkas,
*On Union-Closedness of Language Generation*,
arXiv:2506.18642v1, proofs of detailed Theorems 4.1 and 4.3.

This module constructs the actual infinite sequence of alternating positive
and negative phases under the temporary assumption that a proposed generator
works on the union.  Correctness on a hypothetical one-sided continuation
forces each phase to terminate.  The positive transition output is then
permanently forbidden, while the negative phases extend one fixed descending
tail.

Unlike the source's displayed first negative sweep, this construction starts
at `-1`.  The printed formula can skip a finite initial block, which is enough
for detailed Theorem 4.1 but not for Theorem 4.3.  The cursor-zero invariant
proves exact negative coverage and works for both detailed theorems.  The
recursion is run on the common subfamilies below; each public lower bound then
follows by restriction to its larger paper-facing union.
-/

namespace GenLimit.UnionClosedness.Internal.AlternatingEngine

open GenLimit.Generic

/-! ## The common hard subfamily

The phase construction only uses languages that simultaneously belong to
the corresponding component classes of detailed Theorems 4.1 and 4.3.  We
run the recursion once on this common subfamily and restrict a hypothetical
generator for either paper-facing union to it.  This makes the relationship
between the two lower bounds explicit and avoids duplicating the recursion.
-/

/-- The negative-tail component shared by detailed Theorems 4.1 and 4.3. -/
def alternatingCoreFirstClass : LanguageClass ℤ :=
  theorem43FirstClass ∩ finiteNegativeInfinitePositiveClass

/-- The positive-tail component shared by detailed Theorems 4.1 and 4.3. -/
def alternatingCoreSecondClass : LanguageClass ℤ :=
  theorem43SecondClass ∩ infiniteNegativeFinitePositiveClass

/-- The common subfamily on which the alternating recursion is run. -/
def alternatingCoreClass : LanguageClass ℤ :=
  alternatingCoreFirstClass ∪ alternatingCoreSecondClass

/-- The common hard subfamily lies in the detailed Theorem 4.1 union. -/
theorem alternatingCoreClass_subset_theorem41 :
    alternatingCoreClass ⊆
      finiteNegativeInfinitePositiveClass ∪
        infiniteNegativeFinitePositiveClass := by
  rintro L (hL | hL)
  · exact Or.inl hL.2
  · exact Or.inr hL.2

/-- The common hard subfamily lies in the detailed Theorem 4.3 union. -/
theorem alternatingCoreClass_subset_theorem43 :
    alternatingCoreClass ⊆
      theorem43FirstClass ∪ theorem43SecondClass := by
  rintro L (hL | hL)
  · exact Or.inl hL.1
  · exact Or.inr hL.1

/-- Restrict a proposed detailed Theorem 4.1 generator to the common hard
subfamily. -/
theorem limitGeneratorOnCore_of_theorem41
    {G : Generator ℤ}
    (hG :
      IsLimitGeneratorOnInjectivePresentations G
        (finiteNegativeInfinitePositiveClass ∪
          infiniteNegativeFinitePositiveClass)) :
    IsLimitGeneratorOnInjectivePresentations G
      alternatingCoreClass := by
  intro L hL stream hinjective hpresents
  exact hG L (alternatingCoreClass_subset_theorem41 hL)
    stream hinjective hpresents

/-- Restrict a proposed detailed Theorem 4.3 generator to the common hard
subfamily. -/
theorem limitGeneratorOnCore_of_theorem43
    {G : Generator ℤ}
    (hG :
      IsLimitGeneratorOnInjectivePresentations G
        (theorem43FirstClass ∪ theorem43SecondClass)) :
    IsLimitGeneratorOnInjectivePresentations G
      alternatingCoreClass := by
  intro L hL stream hinjective hpresents
  exact hG L (alternatingCoreClass_subset_theorem43 hL)
    stream hinjective hpresents

/-! ## One-sided continuations -/

/-- Follow a finite history by the canonical positive tail starting at
index `d`. -/
def historyThenPositiveTail
    (history : List ℤ) (d : ℕ) : Stream ℤ :=
  fun t =>
    if h : t < history.length then
      history.get ⟨t, h⟩
    else
      positiveCode (d + (t - history.length))

/-- Follow a finite history by the canonical descending negative tail
starting at index `d`. -/
def historyThenNegativeTail
    (history : List ℤ) (d : ℕ) : Stream ℤ :=
  fun t =>
    if h : t < history.length then
      history.get ⟨t, h⟩
    else
      negativeCode (d + (t - history.length))

@[simp] theorem historyThenPositiveTail_prefix
    (history : List ℤ) (d : ℕ) {t : ℕ}
    (ht : t < history.length) :
    historyThenPositiveTail history d t =
      history.get ⟨t, ht⟩ := by
  simp [historyThenPositiveTail, ht]

@[simp] theorem historyThenNegativeTail_prefix
    (history : List ℤ) (d : ℕ) {t : ℕ}
    (ht : t < history.length) :
    historyThenNegativeTail history d t =
      history.get ⟨t, ht⟩ := by
  simp [historyThenNegativeTail, ht]

@[simp] theorem historyThenPositiveTail_tail
    (history : List ℤ) (d k : ℕ) :
    historyThenPositiveTail history d (history.length + k) =
      positiveCode (d + k) := by
  simp [historyThenPositiveTail]

@[simp] theorem historyThenNegativeTail_tail
    (history : List ℤ) (d k : ℕ) :
    historyThenNegativeTail history d (history.length + k) =
      negativeCode (d + k) := by
  simp [historyThenNegativeTail]

/-- A duplicate-free history followed by a disjoint positive tail is an
injective stream. -/
theorem historyThenPositiveTail_injective
    {history : List ℤ} {d : ℕ}
    (hhistory : history.Nodup)
    (hdisjoint :
      Disjoint (positiveTail d)
        (history.toFinset : Set ℤ)) :
    Function.Injective
      (historyThenPositiveTail history d) := by
  intro i j hij
  by_cases hi : i < history.length
  · by_cases hj : j < history.length
    · have hget :
          history.get ⟨i, hi⟩ =
            history.get ⟨j, hj⟩ := by
        simpa [historyThenPositiveTail, hi, hj] using hij
      have hfin :
          (⟨i, hi⟩ : Fin history.length) =
            ⟨j, hj⟩ :=
        (List.nodup_iff_injective_get.mp hhistory) hget
      exact congrArg Fin.val hfin
    · have hiHistory :
          historyThenPositiveTail history d i ∈
            history.toFinset := by
        rw [historyThenPositiveTail_prefix history d hi]
        exact
          List.mem_toFinset.mpr
            (List.get_mem history ⟨i, hi⟩)
      have hjTail :
          historyThenPositiveTail history d j ∈
            positiveTail d := by
        refine ⟨j - history.length, ?_⟩
        simp [historyThenPositiveTail, hj]
      exact False.elim
        (Set.disjoint_left.mp hdisjoint
          (hij ▸ hjTail) hiHistory)
  · by_cases hj : j < history.length
    · have hiTail :
          historyThenPositiveTail history d i ∈
            positiveTail d := by
        refine ⟨i - history.length, ?_⟩
        simp [historyThenPositiveTail, hi]
      have hjHistory :
          historyThenPositiveTail history d j ∈
            history.toFinset := by
        rw [historyThenPositiveTail_prefix history d hj]
        exact
          List.mem_toFinset.mpr
            (List.get_mem history ⟨j, hj⟩)
      exact False.elim
        (Set.disjoint_left.mp hdisjoint
          hiTail (hij ▸ hjHistory))
    · have hcodes :
          positiveCode (d + (i - history.length)) =
            positiveCode (d + (j - history.length)) := by
        simpa [historyThenPositiveTail, hi, hj] using hij
      have hdiff :
          i - history.length =
            j - history.length := by
        exact Nat.add_left_cancel
          (positiveCode_injective hcodes)
      omega

/-- A duplicate-free history followed by a disjoint negative tail is an
injective stream. -/
theorem historyThenNegativeTail_injective
    {history : List ℤ} {d : ℕ}
    (hhistory : history.Nodup)
    (hdisjoint :
      Disjoint (negativeTail d)
        (history.toFinset : Set ℤ)) :
    Function.Injective
      (historyThenNegativeTail history d) := by
  intro i j hij
  by_cases hi : i < history.length
  · by_cases hj : j < history.length
    · have hget :
          history.get ⟨i, hi⟩ =
            history.get ⟨j, hj⟩ := by
        simpa [historyThenNegativeTail, hi, hj] using hij
      have hfin :
          (⟨i, hi⟩ : Fin history.length) =
            ⟨j, hj⟩ :=
        (List.nodup_iff_injective_get.mp hhistory) hget
      exact congrArg Fin.val hfin
    · have hiHistory :
          historyThenNegativeTail history d i ∈
            history.toFinset := by
        rw [historyThenNegativeTail_prefix history d hi]
        exact
          List.mem_toFinset.mpr
            (List.get_mem history ⟨i, hi⟩)
      have hjTail :
          historyThenNegativeTail history d j ∈
            negativeTail d := by
        refine ⟨j - history.length, ?_⟩
        simp [historyThenNegativeTail, hj]
      exact False.elim
        (Set.disjoint_left.mp hdisjoint
          (hij ▸ hjTail) hiHistory)
  · by_cases hj : j < history.length
    · have hiTail :
          historyThenNegativeTail history d i ∈
            negativeTail d := by
        refine ⟨i - history.length, ?_⟩
        simp [historyThenNegativeTail, hi]
      have hjHistory :
          historyThenNegativeTail history d j ∈
            history.toFinset := by
        rw [historyThenNegativeTail_prefix history d hj]
        exact
          List.mem_toFinset.mpr
            (List.get_mem history ⟨j, hj⟩)
      exact False.elim
        (Set.disjoint_left.mp hdisjoint
          hiTail (hij ▸ hjHistory))
    · have hcodes :
          negativeCode (d + (i - history.length)) =
            negativeCode (d + (j - history.length)) := by
        simpa [historyThenNegativeTail, hi, hj] using hij
      have hdiff :
          i - history.length =
            j - history.length := by
        exact Nat.add_left_cancel
          (negativeCode_injective hcodes)
      omega

theorem range_historyThenPositiveTail
    (history : List ℤ) (d : ℕ) :
    Set.range (historyThenPositiveTail history d) =
      (history.toFinset : Set ℤ) ∪ positiveTail d := by
  classical
  apply Set.Subset.antisymm
  · rintro z ⟨t, rfl⟩
    by_cases ht : t < history.length
    · apply Set.mem_union_left
      change historyThenPositiveTail history d t ∈ history.toFinset
      rw [historyThenPositiveTail_prefix history d ht]
      exact List.mem_toFinset.mpr (List.get_mem history ⟨t, ht⟩)
    · apply Set.mem_union_right
      refine ⟨t - history.length, ?_⟩
      simp [historyThenPositiveTail, ht]
  · intro z hz
    rcases hz with hzHistory | hzTail
    · change z ∈ history.toFinset at hzHistory
      rw [List.mem_toFinset] at hzHistory
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hzHistory
      exact
        ⟨i, (historyThenPositiveTail_prefix
          history d i.isLt).trans hi⟩
    · obtain ⟨k, rfl⟩ := hzTail
      exact
        ⟨history.length + k,
          historyThenPositiveTail_tail history d k⟩

theorem range_historyThenNegativeTail
    (history : List ℤ) (d : ℕ) :
    Set.range (historyThenNegativeTail history d) =
      (history.toFinset : Set ℤ) ∪ negativeTail d := by
  classical
  apply Set.Subset.antisymm
  · rintro z ⟨t, rfl⟩
    by_cases ht : t < history.length
    · apply Set.mem_union_left
      change historyThenNegativeTail history d t ∈ history.toFinset
      rw [historyThenNegativeTail_prefix history d ht]
      exact List.mem_toFinset.mpr (List.get_mem history ⟨t, ht⟩)
    · apply Set.mem_union_right
      refine ⟨t - history.length, ?_⟩
      simp [historyThenNegativeTail, ht]
  · intro z hz
    rcases hz with hzHistory | hzTail
    · change z ∈ history.toFinset at hzHistory
      rw [List.mem_toFinset] at hzHistory
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hzHistory
      exact
        ⟨i, (historyThenNegativeTail_prefix
          history d i.isLt).trans hi⟩
    · obtain ⟨k, rfl⟩ := hzTail
      exact
        ⟨history.length + k,
          historyThenNegativeTail_tail history d k⟩

private theorem positiveIntegers_diff_positiveTail_finite
    (d : ℕ) :
    (positiveIntegers \ positiveTail d).Finite := by
  classical
  apply
    ((Finset.range d).image positiveCode).finite_toSet.subset
  rintro z ⟨hzpos, hznotTail⟩
  obtain ⟨k, rfl⟩ :
      ∃ k, positiveCode k = z := by
    rw [← GenLimit.UnionClosedness.range_positiveCode] at hzpos
    exact hzpos
  apply Finset.mem_image.mpr
  refine ⟨k, Finset.mem_range.mpr ?_, rfl⟩
  by_contra hkd
  have hdk : d ≤ k := Nat.le_of_not_gt hkd
  apply hznotTail
  refine ⟨k - d, ?_⟩
  have hsum : d + (k - d) = k := by omega
  simp [hsum]

private theorem negativeIntegers_diff_negativeTail_finite
    (d : ℕ) :
    (negativeIntegers \ negativeTail d).Finite := by
  classical
  apply
    ((Finset.range d).image negativeCode).finite_toSet.subset
  rintro z ⟨hzneg, hznotTail⟩
  obtain ⟨k, rfl⟩ :
      ∃ k, negativeCode k = z := by
    rw [← range_negativeCode] at hzneg
    exact hzneg
  apply Finset.mem_image.mpr
  refine ⟨k, Finset.mem_range.mpr ?_, rfl⟩
  by_contra hkd
  have hdk : d ≤ k := Nat.le_of_not_gt hkd
  apply hznotTail
  refine ⟨k - d, ?_⟩
  have hsum : d + (k - d) = k := by omega
  simp [hsum]

private theorem positiveTail_disjoint_negativeIntegers
    (d : ℕ) :
    Disjoint (positiveTail d) negativeIntegers := by
  rw [Set.disjoint_left]
  intro z hzTail hzNeg
  obtain ⟨k, rfl⟩ := hzTail
  exact
    (Int.not_lt_of_ge
      (Int.le_of_lt (positiveCode_mem (d + k)))) hzNeg

private theorem negativeTail_disjoint_positiveIntegers
    (d : ℕ) :
    Disjoint (negativeTail d) positiveIntegers := by
  rw [Set.disjoint_left]
  intro z hzTail hzPos
  obtain ⟨k, rfl⟩ := hzTail
  exact
    (Int.not_lt_of_ge
      (Int.le_of_lt hzPos)) (negativeCode_mem (d + k))

private theorem range_eq_signedDeletionLanguage_of_no_zero
    {stream : Stream ℤ}
    (hstream :
      Set.range stream ⊆ negativeIntegers ∪ positiveIntegers) :
    Set.range stream =
      signedDeletionLanguage
        (negativeIntegers \ Set.range stream)
        (positiveIntegers \ Set.range stream) := by
  apply Set.Subset.antisymm
  · intro z hz
    rcases hstream hz with hzneg | hzpos
    · exact Or.inl ⟨hzneg, fun hmissing => hmissing.2 hz⟩
    · exact Or.inr ⟨hzpos, fun hmissing => hmissing.2 hz⟩
  · intro z hz
    rcases hz with hzneg | hzpos
    · by_contra hzrange
      exact hzneg.2 ⟨hzneg.1, hzrange⟩
    · by_contra hzrange
      exact hzpos.2 ⟨hzpos.1, hzrange⟩

private theorem historyThenPositiveTail_no_zero
    {history : List ℤ}
    (hhistory :
      ∀ z, z ∈ history →
        z ∈ negativeIntegers ∪ positiveIntegers)
    (d : ℕ) :
    Set.range (historyThenPositiveTail history d) ⊆
      negativeIntegers ∪ positiveIntegers := by
  rw [range_historyThenPositiveTail]
  intro z hz
  rcases hz with hzHistory | hzTail
  · exact hhistory z (List.mem_toFinset.mp hzHistory)
  · exact Or.inr (by
      obtain ⟨k, rfl⟩ := hzTail
      exact positiveCode_mem (d + k))

private theorem historyThenNegativeTail_no_zero
    {history : List ℤ}
    (hhistory :
      ∀ z, z ∈ history →
        z ∈ negativeIntegers ∪ positiveIntegers)
    (d : ℕ) :
    Set.range (historyThenNegativeTail history d) ⊆
      negativeIntegers ∪ positiveIntegers := by
  rw [range_historyThenNegativeTail]
  intro z hz
  rcases hz with hzHistory | hzTail
  · exact hhistory z (List.mem_toFinset.mp hzHistory)
  · exact Or.inl (by
      obtain ⟨k, rfl⟩ := hzTail
      exact negativeCode_mem (d + k))

/-- A positive-tail continuation whose negative history is exactly an
initial prefix belongs to detailed Theorem 4.3's second class. -/
theorem historyThenPositiveTail_mem_secondClass
    {history : List ℤ}
    (hhistory :
      ∀ z, z ∈ history →
        z ∈ negativeIntegers ∪ positiveIntegers)
    (negativeCursor positiveStart : ℕ)
    (hnegative :
      ∀ k, negativeCode k ∈ history ↔ k < negativeCursor)
    (hzero :
      negativeCursor = 0 →
        history = [] ∧ positiveStart = 0) :
    Set.range
        (historyThenPositiveTail history positiveStart) ∈
      theorem43SecondClass := by
  classical
  let stream :=
    historyThenPositiveTail history positiveStart
  let B := positiveIntegers \ Set.range stream
  have hrange :=
    range_historyThenPositiveTail history positiveStart
  have hBfinite : B.Finite := by
    apply
      (positiveIntegers_diff_positiveTail_finite
        positiveStart).subset
    rintro z ⟨hzPos, hzNotRange⟩
    exact
      ⟨hzPos, fun hzTail =>
        hzNotRange (hrange.symm ▸ Set.mem_union_right _ hzTail)⟩
  refine
    ⟨negativeCursor, B, Set.diff_subset, hBfinite, ?_, ?_⟩
  · intro hcursor
    obtain ⟨hhistory, hstart⟩ := hzero hcursor
    subst history
    subst positiveStart
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact hz.2 (by
      rw [range_historyThenPositiveTail]
      exact Set.mem_union_right _
        (by
          rw [show positiveTail 0 = positiveIntegers by
            simpa [positiveTail] using
              GenLimit.UnionClosedness.range_positiveCode]
          exact hz.1))
  apply Set.Subset.antisymm
  · intro z hz
    rcases
        historyThenPositiveTail_no_zero
          hhistory positiveStart hz with hzNeg | hzPos
    · have hzCode : z ∈ Set.range negativeCode := by
        rw [range_negativeCode]
        exact hzNeg
      obtain ⟨k, rfl⟩ := hzCode
      apply Set.mem_union_left
      rw [negativePrefix_mem_iff]
      apply (hnegative k).mp
      rw [hrange] at hz
      rcases hz with hzHistory | hzTail
      · exact List.mem_toFinset.mp hzHistory
      · exact False.elim
          (Set.disjoint_left.mp
            (positiveTail_disjoint_negativeIntegers
              positiveStart)
            hzTail (negativeCode_mem k))
    · exact Set.mem_union_right _
        ⟨hzPos, fun hzB => hzB.2 hz⟩
  · intro z hz
    rcases hz with hzPrefix | hzPositive
    · have hzCode :
          ∃ k, k < negativeCursor ∧
            negativeCode k = z := by
        change
          z ∈ ((Finset.range negativeCursor).image
            negativeCode : Finset ℤ) at hzPrefix
        obtain ⟨k, hk, hkz⟩ :=
          Finset.mem_image.mp hzPrefix
        exact ⟨k, Finset.mem_range.mp hk, hkz⟩
      obtain ⟨k, hk, rfl⟩ := hzCode
      rw [hrange]
      exact Set.mem_union_left _
        (List.mem_toFinset.mpr ((hnegative k).mpr hk))
    · by_contra hzRange
      exact hzPositive.2 ⟨hzPositive.1, hzRange⟩

/-- A negative-tail continuation after an exact initial negative prefix
contains every negative integer and hence belongs to detailed
Theorem 4.3's first class. -/
theorem historyThenNegativeTail_mem_firstClass
    {history : List ℤ}
    (hhistory :
      ∀ z, z ∈ history →
        z ∈ negativeIntegers ∪ positiveIntegers)
    (negativeCursor : ℕ)
    (hnegative :
      ∀ k, negativeCode k ∈ history ↔ k < negativeCursor) :
    Set.range
        (historyThenNegativeTail history negativeCursor) ∈
      theorem43FirstClass := by
  classical
  let stream :=
    historyThenNegativeTail history negativeCursor
  let A := Set.range stream ∩ positiveIntegers
  have hrange :=
    range_historyThenNegativeTail history negativeCursor
  have hallNegative :
      negativeIntegers ⊆ Set.range stream := by
    intro z hz
    have hzCode : z ∈ Set.range negativeCode := by
      rw [range_negativeCode]
      exact hz
    obtain ⟨k, rfl⟩ := hzCode
    by_cases hk : k < negativeCursor
    · rw [hrange]
      exact Set.mem_union_left _
        (List.mem_toFinset.mpr ((hnegative k).mpr hk))
    · rw [hrange]
      apply Set.mem_union_right
      refine ⟨k - negativeCursor, ?_⟩
      apply congrArg negativeCode
      exact Nat.add_sub_of_le (Nat.le_of_not_gt hk)
  refine ⟨A, Set.inter_subset_right, ?_⟩
  apply Set.Subset.antisymm
  · intro z hz
    rcases
        historyThenNegativeTail_no_zero
          hhistory negativeCursor hz with hzNeg | hzPos
    · exact Set.mem_union_left _ hzNeg
    · exact Set.mem_union_right _ ⟨hz, hzPos⟩
  · intro z hz
    rcases hz with hzNeg | hzPos
    · exact hallNegative hzNeg
    · exact hzPos.1

/-! The same continuations also lie in the two detailed Theorem 4.1
components.  Exact coverage of the negative side is stronger than the
cofinite coverage needed there. -/

private theorem historyThenPositiveTail_mem_theorem41SecondClass
    {history : List ℤ}
    (hhistory :
      ∀ z, z ∈ history →
        z ∈ negativeIntegers ∪ positiveIntegers)
    (d : ℕ) :
    Set.range (historyThenPositiveTail history d) ∈
      infiniteNegativeFinitePositiveClass := by
  classical
  let stream := historyThenPositiveTail history d
  have hrange := range_historyThenPositiveTail history d
  have hnegativeFinite :
      (Set.range stream ∩ negativeIntegers).Finite := by
    apply history.toFinset.finite_toSet.subset
    rintro z ⟨hzRange, hzNeg⟩
    rw [hrange] at hzRange
    rcases hzRange with hzHistory | hzTail
    · exact hzHistory
    · exact False.elim
        (Set.disjoint_left.mp
          (positiveTail_disjoint_negativeIntegers d)
          hzTail hzNeg)
  have hnegativeMissing :
      (negativeIntegers \ Set.range stream).Infinite := by
    apply (negativeIntegers_infinite.diff hnegativeFinite).mono
    rintro z ⟨hzNeg, hzNot⟩
    exact ⟨hzNeg, fun hzRange => hzNot ⟨hzRange, hzNeg⟩⟩
  have hpositiveMissing :
      (positiveIntegers \ Set.range stream).Finite := by
    apply (positiveIntegers_diff_positiveTail_finite d).subset
    rintro z ⟨hzPos, hzNotRange⟩
    exact
      ⟨hzPos, fun hzTail =>
        hzNotRange (hrange.symm ▸ Set.mem_union_right _ hzTail)⟩
  refine
    ⟨negativeIntegers \ Set.range stream,
      positiveIntegers \ Set.range stream,
      Set.diff_subset, hnegativeMissing,
      Set.diff_subset, hpositiveMissing, ?_⟩
  exact
    range_eq_signedDeletionLanguage_of_no_zero
      (historyThenPositiveTail_no_zero hhistory d)

private theorem historyThenNegativeTail_mem_theorem41FirstClass
    {history : List ℤ}
    (hhistory :
      ∀ z, z ∈ history →
        z ∈ negativeIntegers ∪ positiveIntegers)
    (d : ℕ) :
    Set.range (historyThenNegativeTail history d) ∈
      finiteNegativeInfinitePositiveClass := by
  classical
  let stream := historyThenNegativeTail history d
  have hrange := range_historyThenNegativeTail history d
  have hpositiveFinite :
      (Set.range stream ∩ positiveIntegers).Finite := by
    apply history.toFinset.finite_toSet.subset
    rintro z ⟨hzRange, hzPos⟩
    rw [hrange] at hzRange
    rcases hzRange with hzHistory | hzTail
    · exact hzHistory
    · exact False.elim
        (Set.disjoint_left.mp
          (negativeTail_disjoint_positiveIntegers d)
          hzTail hzPos)
  have hpositiveMissing :
      (positiveIntegers \ Set.range stream).Infinite := by
    apply (positiveIntegers_infinite.diff hpositiveFinite).mono
    rintro z ⟨hzPos, hzNot⟩
    exact ⟨hzPos, fun hzRange => hzNot ⟨hzRange, hzPos⟩⟩
  have hnegativeMissing :
      (negativeIntegers \ Set.range stream).Finite := by
    apply (negativeIntegers_diff_negativeTail_finite d).subset
    rintro z ⟨hzNeg, hzNotRange⟩
    exact
      ⟨hzNeg, fun hzTail =>
        hzNotRange (hrange.symm ▸ Set.mem_union_right _ hzTail)⟩
  refine
    ⟨negativeIntegers \ Set.range stream,
      positiveIntegers \ Set.range stream,
      Set.diff_subset, hnegativeMissing,
      Set.diff_subset, hpositiveMissing, ?_⟩
  exact
    range_eq_signedDeletionLanguage_of_no_zero
      (historyThenNegativeTail_no_zero hhistory d)

/-! ## Phase states -/

private theorem exists_positiveTail_disjoint_finset
    (blocked : Finset ℤ) :
    ∃ d : ℕ,
      Disjoint (positiveTail d) (blocked : Set ℤ) := by
  classical
  let badIndices : Set ℕ :=
    positiveCode ⁻¹' (blocked : Set ℤ)
  have hbadFinite : badIndices.Finite := by
    apply blocked.finite_toSet.preimage
    exact Set.injOn_of_injective positiveCode_injective
  obtain ⟨d, hd⟩ :=
    Finset.exists_nat_subset_range hbadFinite.toFinset
  refine ⟨d, ?_⟩
  rw [Set.disjoint_left]
  rintro z ⟨k, rfl⟩ hzBlocked
  have hkBad : d + k ∈ hbadFinite.toFinset := by
    simpa [badIndices] using hzBlocked
  have hklt : d + k < d := by
    simpa using hd hkBad
  omega

/-- Finite data at the beginning of a positive phase.  Negative indices
start at zero, so the final construction enumerates every negative integer
as required by detailed Theorem 4.3. -/
structure AlternatingPhaseState (phase : ℕ) where
  history : List ℤ
  forbidden : Finset ℤ
  negativeCursor : ℕ
  positiveStart : ℕ
  history_nodup : history.Nodup
  history_no_zero :
    ∀ z, z ∈ history →
      z ∈ negativeIntegers ∪ positiveIntegers
  forbidden_positive :
    ∀ z, z ∈ forbidden → z ∈ positiveIntegers
  history_forbidden_disjoint :
    Disjoint history.toFinset forbidden
  negative_mem_history_iff :
    ∀ k, negativeCode k ∈ history ↔ k < negativeCursor
  cursor_lower : phase ≤ negativeCursor
  zero_cursor_initial :
    negativeCursor = 0 → history = [] ∧ positiveStart = 0
  positive_tail_disjoint :
    Disjoint (positiveTail positiveStart)
      ((history.toFinset ∪ forbidden : Finset ℤ) : Set ℤ)

/-- The empty initial history starts at negative index zero. -/
def initialAlternatingPhaseState :
    AlternatingPhaseState 0 where
  history := []
  forbidden := ∅
  negativeCursor := 0
  positiveStart := 0
  history_nodup := by simp
  history_no_zero := by simp
  forbidden_positive := by simp
  history_forbidden_disjoint := by simp
  negative_mem_history_iff := by
    intro k
    simp
  cursor_lower := by omega
  zero_cursor_initial := by simp
  positive_tail_disjoint := by simp

/-- Paper-local name for the shared ordered finite-prefix operation. -/
abbrev streamPrefix (stream : Stream ℤ) (t : ℕ) : List ℤ :=
  GenLimit.textPrefix stream t

@[simp] theorem streamPrefix_length
  (stream : Stream ℤ) (t : ℕ) :
    (streamPrefix stream t).length = t := by
  simp

/-- Every finite prefix of an injective stream has no duplicates. -/
theorem streamPrefix_nodup
    {stream : Stream ℤ}
    (hstream : Function.Injective stream) (t : ℕ) :
    (streamPrefix stream t).Nodup := by
  change (GenLimit.textPrefix stream t).Nodup
  rw [GenLimit.textPrefix_eq_ofFn]
  apply List.nodup_ofFn_ofInjective
  intro i j hij
  apply Fin.ext
  exact hstream hij

theorem streamPrefix_mem_range
    (stream : Stream ℤ) (t : ℕ) :
    ((streamPrefix stream t).toFinset : Set ℤ) ⊆
      Set.range stream := by
  intro z hz
  change z ∈ (GenLimit.textPrefix stream t).toFinset at hz
  rw [List.mem_toFinset] at hz
  rw [GenLimit.textPrefix_eq_ofFn] at hz
  simp only [List.mem_ofFn] at hz
  obtain ⟨k, hk⟩ := hz
  exact ⟨k, hk⟩

theorem streamPrefix_extends_history_positive
    (history : List ℤ) (d t : ℕ)
    (ht : history.length ≤ t) :
    history <+:
      streamPrefix (historyThenPositiveTail history d) t := by
  apply List.prefix_iff_getElem.mpr
  refine ⟨by simpa using ht, ?_⟩
  intro k hk
  simpa only [streamPrefix, GenLimit.textPrefix_eq_ofFn,
      List.getElem_ofFn] using
    (historyThenPositiveTail_prefix history d hk).symm

theorem streamPrefix_extends_history_negative
    (history : List ℤ) (d t : ℕ)
    (ht : history.length ≤ t) :
    history <+:
      streamPrefix (historyThenNegativeTail history d) t := by
  apply List.prefix_iff_getElem.mpr
  refine ⟨by simpa using ht, ?_⟩
  intro k hk
  simpa only [streamPrefix, GenLimit.textPrefix_eq_ofFn,
      List.getElem_ofFn] using
    (historyThenNegativeTail_prefix history d hk).symm

/-- Data recorded by one successful positive/negative phase pair. -/
structure SuccessfulAlternatingPhase
    (G : Generator ℤ) (phase : ℕ)
    (state : AlternatingPhaseState phase) where
  next : AlternatingPhaseState (phase + 1)
  extends_history : state.history <+: next.history
  strict_growth : state.history.length < next.history.length
  forbidden_subset : state.forbidden ⊆ next.forbidden
  transitionTime : ℕ
  old_length_lt_transition :
    state.history.length < transitionTime
  transition_lt_next_length :
    transitionTime < next.history.length
  omittedOutput : ℤ
  omitted_positive : omittedOutput ∈ positiveIntegers
  omitted_not_old_forbidden :
    omittedOutput ∉ state.forbidden
  omitted_mem_next_forbidden :
    omittedOutput ∈ next.forbidden
  output_on_next :
    G transitionTime
        (fun k =>
          next.history.get
            ⟨k, lt_trans k.isLt
              transition_lt_next_length⟩) =
      omittedOutput

private theorem exists_successfulAlternatingPhase
    (G : Generator ℤ)
    (hG :
      IsLimitGeneratorOnInjectivePresentations G
        alternatingCoreClass)
    (phase : ℕ) (state : AlternatingPhaseState phase) :
    Nonempty (SuccessfulAlternatingPhase G phase state) := by
  classical
  let positiveStream :=
    historyThenPositiveTail state.history state.positiveStart
  have hpositiveTailHistory :
      Disjoint (positiveTail state.positiveStart)
        (state.history.toFinset : Set ℤ) := by
    rw [Set.disjoint_left]
    intro z hzTail hzHistory
    exact
      Set.disjoint_left.mp state.positive_tail_disjoint
        hzTail (Finset.mem_union_left _ hzHistory)
  have hpositiveStreamInjective :
      Function.Injective positiveStream := by
    exact
      historyThenPositiveTail_injective
        state.history_nodup hpositiveTailHistory
  have hpositiveTarget :
      Set.range positiveStream ∈
        alternatingCoreSecondClass := by
    refine ⟨?_, ?_⟩
    · exact
        historyThenPositiveTail_mem_secondClass
          state.history_no_zero state.negativeCursor
          state.positiveStart state.negative_mem_history_iff
          state.zero_cursor_initial
    · exact
        historyThenPositiveTail_mem_theorem41SecondClass
          state.history_no_zero state.positiveStart
  obtain ⟨positiveThreshold, hpositiveCorrect⟩ :=
    hG (Set.range positiveStream)
      (Or.inr hpositiveTarget) positiveStream
      hpositiveStreamInjective rfl
  let positiveTime :=
    max positiveThreshold (state.history.length + 1)
  have hpositiveThreshold :
      positiveThreshold ≤ positiveTime :=
    Nat.le_max_left _ _
  have hhistory_lt_positiveTime :
      state.history.length < positiveTime := by
    dsimp only [positiveTime]
    omega
  have hpositiveCorrectAt :
      CorrectAt G (Set.range positiveStream)
        positiveStream positiveTime :=
    hpositiveCorrect positiveTime hpositiveThreshold
  let positivePrefix :=
    streamPrefix positiveStream positiveTime
  let omitted := output G positiveStream positiveTime
  have homittedNotHistory :
      omitted ∉ state.history := by
    intro hmem
    apply hpositiveCorrectAt.2
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hmem
    apply GenLimit.Generic.mem_sample_iff.mpr
    refine
      ⟨i, lt_trans i.isLt hhistory_lt_positiveTime, ?_⟩
    exact
      (historyThenPositiveTail_prefix
        state.history state.positiveStart i.isLt).trans hi
  have homittedTail :
      omitted ∈ positiveTail state.positiveStart := by
    have hrange := hpositiveCorrectAt.1
    rw [range_historyThenPositiveTail] at hrange
    rcases hrange with hhistory | htail
    · exact False.elim
        (homittedNotHistory
          (List.mem_toFinset.mp hhistory))
    · exact htail
  have homittedPositive :
      omitted ∈ positiveIntegers := by
    obtain ⟨k, hk⟩ := homittedTail
    rw [← hk]
    exact positiveCode_mem (state.positiveStart + k)
  have homittedNotOldForbidden :
      omitted ∉ state.forbidden := by
    intro hforbidden
    exact
      Set.disjoint_left.mp state.positive_tail_disjoint
        homittedTail
        (Finset.mem_union_right _ hforbidden)
  have hhistoryPrefixPositive :
      state.history <+: positivePrefix := by
    exact
      streamPrefix_extends_history_positive
        state.history state.positiveStart positiveTime
        (Nat.le_of_lt hhistory_lt_positiveTime)
  have hpositivePrefixNodup :
      positivePrefix.Nodup :=
    streamPrefix_nodup
      hpositiveStreamInjective positiveTime
  have hpositivePrefixNegativeIff :
      ∀ k, negativeCode k ∈ positivePrefix ↔
        k < state.negativeCursor := by
    intro k
    constructor
    · intro hk
      have hkRange :
          negativeCode k ∈ Set.range positiveStream :=
        streamPrefix_mem_range positiveStream positiveTime
          (List.mem_toFinset.mpr hk)
      rw [range_historyThenPositiveTail] at hkRange
      rcases hkRange with hkHistory | hkTail
      · exact
          (state.negative_mem_history_iff k).mp
            (List.mem_toFinset.mp hkHistory)
      · exact False.elim
          (Set.disjoint_left.mp
            (positiveTail_disjoint_negativeIntegers
              state.positiveStart)
            hkTail (negativeCode_mem k))
    · intro hk
      exact
        hhistoryPrefixPositive.subset
          ((state.negative_mem_history_iff k).mpr hk)
  have homittedNotPositivePrefix :
      omitted ∉ positivePrefix := by
    intro hmem
    apply hpositiveCorrectAt.2
    dsimp only [positivePrefix, streamPrefix]
      at hmem
    rw [GenLimit.textPrefix_eq_ofFn] at hmem
    rw [List.mem_ofFn] at hmem
    obtain ⟨i, hi⟩ := hmem
    exact
      GenLimit.Generic.mem_sample_iff.mpr
        ⟨i, i.isLt, hi⟩
  have hpositivePrefixNoZero :
      ∀ z, z ∈ positivePrefix →
        z ∈ negativeIntegers ∪ positiveIntegers := by
    intro z hz
    exact
      historyThenPositiveTail_no_zero
        state.history_no_zero state.positiveStart
        (streamPrefix_mem_range positiveStream positiveTime
          (List.mem_toFinset.mpr hz))
  have hpositiveRangeOldForbidden :
      Disjoint (Set.range positiveStream)
        (state.forbidden : Set ℤ) := by
    rw [range_historyThenPositiveTail, Set.disjoint_left]
    intro z hzRange hzForbidden
    rcases hzRange with hzHistory | hzTail
    · exact
        Finset.disjoint_left.mp
          state.history_forbidden_disjoint
          hzHistory hzForbidden
    · exact
        Set.disjoint_left.mp
          state.positive_tail_disjoint
          hzTail
          (Finset.mem_union_right _ hzForbidden)
  let nextForbidden := insert omitted state.forbidden
  have hpositivePrefixNextForbidden :
      Disjoint positivePrefix.toFinset nextForbidden := by
    rw [Finset.disjoint_left]
    intro z hzPrefix hzForbidden
    rw [Finset.mem_insert] at hzForbidden
    rcases hzForbidden with rfl | hzOld
    · exact
        homittedNotPositivePrefix
          (List.mem_toFinset.mp hzPrefix)
    · exact
        Set.disjoint_left.mp hpositiveRangeOldForbidden
          (streamPrefix_mem_range positiveStream positiveTime
            hzPrefix)
          hzOld
  have hnextForbiddenPositive :
      ∀ z, z ∈ nextForbidden → z ∈ positiveIntegers := by
    intro z hz
    rw [Finset.mem_insert] at hz
    exact hz.elim (fun h => h ▸ homittedPositive)
      (state.forbidden_positive z)
  let negativeStream :=
    historyThenNegativeTail
      positivePrefix state.negativeCursor
  have hnegativeTailPositivePrefix :
      Disjoint (negativeTail state.negativeCursor)
        (positivePrefix.toFinset : Set ℤ) := by
    rw [Set.disjoint_left]
    rintro z ⟨j, rfl⟩ hzPrefix
    have hbounds :=
      (hpositivePrefixNegativeIff
        (state.negativeCursor + j)).mp
        (List.mem_toFinset.mp hzPrefix)
    omega
  have hnegativeStreamInjective :
      Function.Injective negativeStream := by
    exact
      historyThenNegativeTail_injective
        hpositivePrefixNodup hnegativeTailPositivePrefix
  have hnegativeTarget :
      Set.range negativeStream ∈
        alternatingCoreFirstClass := by
    refine ⟨?_, ?_⟩
    · exact
        historyThenNegativeTail_mem_firstClass
          hpositivePrefixNoZero state.negativeCursor
          hpositivePrefixNegativeIff
    · exact
        historyThenNegativeTail_mem_theorem41FirstClass
          hpositivePrefixNoZero state.negativeCursor
  obtain ⟨negativeThreshold, hnegativeCorrect⟩ :=
    hG (Set.range negativeStream)
      (Or.inl hnegativeTarget) negativeStream
      hnegativeStreamInjective rfl
  let negativeTime :=
    max negativeThreshold (positivePrefix.length + 1)
  have hnegativeThreshold :
      negativeThreshold ≤ negativeTime :=
    Nat.le_max_left _ _
  have hpositivePrefix_lt_negativeTime :
      positivePrefix.length < negativeTime := by
    dsimp only [negativeTime]
    omega
  have hnegativeCorrectAt :
      CorrectAt G (Set.range negativeStream)
        negativeStream negativeTime :=
    hnegativeCorrect negativeTime hnegativeThreshold
  have hnegativeOutputNotPrefix :
      output G negativeStream negativeTime ∉
        positivePrefix := by
    intro hmem
    apply hnegativeCorrectAt.2
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hmem
    apply GenLimit.Generic.mem_sample_iff.mpr
    refine
      ⟨i, lt_trans i.isLt
        hpositivePrefix_lt_negativeTime, ?_⟩
    exact
      (historyThenNegativeTail_prefix
        positivePrefix state.negativeCursor i.isLt).trans hi
  have hnegativeOutputTail :
      output G negativeStream negativeTime ∈
        negativeTail state.negativeCursor := by
    have hrange := hnegativeCorrectAt.1
    rw [range_historyThenNegativeTail] at hrange
    rcases hrange with hprefix | htail
    · exact False.elim
        (hnegativeOutputNotPrefix
          (List.mem_toFinset.mp hprefix))
    · exact htail
  let nextHistory :=
    streamPrefix negativeStream negativeTime
  have hnextHistoryNodup :
      nextHistory.Nodup :=
    streamPrefix_nodup
      hnegativeStreamInjective negativeTime
  have hpositivePrefixNextHistory :
      positivePrefix <+: nextHistory := by
    exact
      streamPrefix_extends_history_negative
        positivePrefix state.negativeCursor negativeTime
        (Nat.le_of_lt hpositivePrefix_lt_negativeTime)
  have hnextHistoryNoZero :
      ∀ z, z ∈ nextHistory →
        z ∈ negativeIntegers ∪ positiveIntegers := by
    intro z hz
    exact
      historyThenNegativeTail_no_zero
        hpositivePrefixNoZero state.negativeCursor
        (streamPrefix_mem_range negativeStream negativeTime
          (List.mem_toFinset.mpr hz))
  have hnegativeRangeNextForbidden :
      Disjoint (Set.range negativeStream)
        (nextForbidden : Set ℤ) := by
    rw [range_historyThenNegativeTail, Set.disjoint_left]
    intro z hzRange hzForbidden
    rcases hzRange with hzPrefix | hzTail
    · exact
        Finset.disjoint_left.mp
          hpositivePrefixNextForbidden
          hzPrefix hzForbidden
    · exact
        Set.disjoint_left.mp
          (negativeTail_disjoint_positiveIntegers
            state.negativeCursor)
          hzTail
          (hnextForbiddenPositive z hzForbidden)
  have hnextHistoryForbidden :
      Disjoint nextHistory.toFinset nextForbidden := by
    rw [Finset.disjoint_left]
    intro z hzHistory hzForbidden
    exact
      Set.disjoint_left.mp hnegativeRangeNextForbidden
        (streamPrefix_mem_range negativeStream negativeTime
          hzHistory)
        hzForbidden
  let negativeCount :=
    negativeTime - positivePrefix.length
  have hnegativeCountPositive : 0 < negativeCount := by
    dsimp only [negativeCount]
    omega
  let nextCursor :=
    state.negativeCursor + negativeCount
  have hnextNegativeMemIff :
      ∀ k, negativeCode k ∈ nextHistory ↔
        k < nextCursor := by
    intro k
    constructor
    · intro hk
      dsimp only [nextHistory, streamPrefix] at hk
      rw [GenLimit.textPrefix_eq_ofFn] at hk
      rw [List.mem_ofFn] at hk
      obtain ⟨i, hi⟩ := hk
      by_cases hiPrefix :
          i.val < positivePrefix.length
      · have hkPrefix :
            negativeCode k ∈ positivePrefix := by
          apply List.mem_iff_get.mpr
          refine ⟨⟨i, hiPrefix⟩, ?_⟩
          exact
            (historyThenNegativeTail_prefix
              positivePrefix state.negativeCursor
              hiPrefix).symm.trans hi
        have hkBounds :=
          (hpositivePrefixNegativeIff k).mp hkPrefix
        dsimp only [nextCursor, negativeCount]
        omega
      · have hcodes :
            negativeCode
                (state.negativeCursor +
                  (i.val - positivePrefix.length)) =
              negativeCode k := by
          simpa [negativeStream,
            historyThenNegativeTail, hiPrefix] using hi
        have hindex :
            state.negativeCursor +
                (i.val - positivePrefix.length) =
              k :=
          negativeCode_injective hcodes
        dsimp only [nextCursor, negativeCount]
        omega
    · intro hkNext
      by_cases hkOld : k < state.negativeCursor
      · apply hpositivePrefixNextHistory.subset
        exact (hpositivePrefixNegativeIff k).mpr hkOld
      · have hcursorLe :
            state.negativeCursor ≤ k :=
          Nat.le_of_not_gt hkOld
        have hjlt :
            positivePrefix.length +
                (k - state.negativeCursor) <
              negativeTime := by
          dsimp only [nextCursor, negativeCount] at hkNext
          omega
        dsimp only [nextHistory, streamPrefix]
        rw [GenLimit.textPrefix_eq_ofFn]
        rw [List.mem_ofFn]
        refine
          ⟨⟨positivePrefix.length +
              (k - state.negativeCursor), hjlt⟩, ?_⟩
        change
          historyThenNegativeTail
              positivePrefix state.negativeCursor
              (positivePrefix.length +
                (k - state.negativeCursor)) =
            negativeCode k
        rw [historyThenNegativeTail_tail]
        congr 1
        omega
  have hnextCursorLower :
      phase + 1 ≤ nextCursor := by
    dsimp only [nextCursor, negativeCount]
    have hcursor := state.cursor_lower
    omega
  obtain ⟨nextPositiveStart, hnextPositiveTail⟩ :=
    exists_positiveTail_disjoint_finset
      (nextHistory.toFinset ∪ nextForbidden)
  let nextState : AlternatingPhaseState (phase + 1) :=
    { history := nextHistory
      forbidden := nextForbidden
      negativeCursor := nextCursor
      positiveStart := nextPositiveStart
      history_nodup := hnextHistoryNodup
      history_no_zero := hnextHistoryNoZero
      forbidden_positive := hnextForbiddenPositive
      history_forbidden_disjoint := hnextHistoryForbidden
      negative_mem_history_iff := hnextNegativeMemIff
      cursor_lower := hnextCursorLower
      zero_cursor_initial := by
        intro hzero
        dsimp only [nextCursor, negativeCount] at hzero
        omega
      positive_tail_disjoint := hnextPositiveTail }
  have htransitionOutputOnNext :
      G positiveTime
          (fun k =>
            nextState.history.get
              ⟨k, by
                dsimp only [nextState, nextHistory]
                rw [streamPrefix_length]
                have hlenPositive :
                    positivePrefix.length =
                      positiveTime := by
                  simp only [positivePrefix,
                    streamPrefix_length]
                omega⟩) =
        omitted := by
    change
      G positiveTime
          (fun k =>
            nextHistory.get
              ⟨k, by
                rw [streamPrefix_length]
                have hlenPositive :
                    positivePrefix.length =
                      positiveTime := by
                  simp only [positivePrefix,
                    streamPrefix_length]
                omega⟩) =
        output G positiveStream positiveTime
    unfold output
    congr 1
    funext k
    have hkPositivePrefix :
        k.val < positivePrefix.length := by
      simp only [positivePrefix, streamPrefix_length]
      exact k.isLt
    have hkNext :
        k.val < nextHistory.length := by
      rw [streamPrefix_length]
      exact
        lt_trans hkPositivePrefix
          hpositivePrefix_lt_negativeTime
    rw [List.get_eq_getElem]
    calc
      nextHistory[k.val] =
          positivePrefix[k.val] :=
        (hpositivePrefixNextHistory.getElem
          hkPositivePrefix).symm
      _ = positiveStream k := by
        have hprefix := GenLimit.textPrefix_eq_ofFn
          positiveStream positiveTime
        have hget := congrArg (fun xs => xs[k.val]?) hprefix
        simpa [positivePrefix, streamPrefix,
          List.getElem?_ofFn, k.isLt] using hget
  refine
    ⟨{
      next := nextState
      extends_history :=
        hhistoryPrefixPositive.trans
          hpositivePrefixNextHistory
      strict_growth := by
        dsimp only [nextState, nextHistory]
        rw [streamPrefix_length]
        have hlenPositive :
            positivePrefix.length = positiveTime := by
          simp only [positivePrefix, streamPrefix_length]
        have hpositiveTime_lt_negativeTime :
            positiveTime < negativeTime := by
          rw [← hlenPositive]
          exact hpositivePrefix_lt_negativeTime
        omega
      forbidden_subset := by
        intro z hz
        exact Finset.mem_insert_of_mem hz
      transitionTime := positiveTime
      old_length_lt_transition :=
        hhistory_lt_positiveTime
      transition_lt_next_length := by
        dsimp only [nextState, nextHistory]
        rw [streamPrefix_length]
        have hlenPositive :
            positivePrefix.length = positiveTime := by
          simp only [positivePrefix, streamPrefix_length]
        omega
      omittedOutput := omitted
      omitted_positive := homittedPositive
      omitted_not_old_forbidden :=
        homittedNotOldForbidden
      omitted_mem_next_forbidden := by
        exact Finset.mem_insert_self _ _
      output_on_next := htransitionOutputOnNext
    }⟩

/-! ## Iteration and the limit stream -/

private noncomputable def alternatingPhase
    (G : Generator ℤ)
    (hG :
      IsLimitGeneratorOnInjectivePresentations G
        alternatingCoreClass)
    (phase : ℕ) (state : AlternatingPhaseState phase) :
    SuccessfulAlternatingPhase G phase state :=
  Classical.choice
    (exists_successfulAlternatingPhase G hG phase state)

private noncomputable def alternatingPhaseState
    (G : Generator ℤ)
    (hG :
      IsLimitGeneratorOnInjectivePresentations G
        alternatingCoreClass) :
    (phase : ℕ) → AlternatingPhaseState phase
  | 0 => initialAlternatingPhaseState
  | phase + 1 =>
      (alternatingPhase G hG phase
        (alternatingPhaseState G hG phase)).next

private theorem alternatingPhaseState_prefix_succ
    (G : Generator ℤ)
    (hG :
      IsLimitGeneratorOnInjectivePresentations G
        alternatingCoreClass)
    (phase : ℕ) :
    (alternatingPhaseState G hG phase).history <+:
      (alternatingPhaseState G hG (phase + 1)).history := by
  rw [alternatingPhaseState]
  exact
    (alternatingPhase G hG phase
      (alternatingPhaseState G hG phase)).extends_history

private theorem alternatingPhaseState_prefix
    (G : Generator ℤ)
    (hG :
      IsLimitGeneratorOnInjectivePresentations G
        alternatingCoreClass)
    {n m : ℕ} (hnm : n ≤ m) :
    (alternatingPhaseState G hG n).history <+:
      (alternatingPhaseState G hG m).history := by
  induction m, hnm using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ m _ ih =>
      exact ih.trans
        (alternatingPhaseState_prefix_succ G hG m)

private theorem alternatingPhaseState_length
    (G : Generator ℤ)
    (hG :
      IsLimitGeneratorOnInjectivePresentations G
        alternatingCoreClass)
    (phase : ℕ) :
    phase ≤
      (alternatingPhaseState G hG phase).history.length := by
  induction phase with
  | zero =>
      simp [alternatingPhaseState,
        initialAlternatingPhaseState]
  | succ phase ih =>
      have hgrowth :=
        (alternatingPhase G hG phase
          (alternatingPhaseState G hG phase)).strict_growth
      rw [alternatingPhaseState]
      omega

private theorem alternatingPhaseState_forbidden_succ
    (G : Generator ℤ)
    (hG :
      IsLimitGeneratorOnInjectivePresentations G
        alternatingCoreClass)
    (phase : ℕ) :
    (alternatingPhaseState G hG phase).forbidden ⊆
      (alternatingPhaseState G hG (phase + 1)).forbidden := by
  rw [alternatingPhaseState]
  exact
    (alternatingPhase G hG phase
      (alternatingPhaseState G hG phase)).forbidden_subset

private theorem alternatingPhaseState_forbidden_mono
    (G : Generator ℤ)
    (hG :
      IsLimitGeneratorOnInjectivePresentations G
        alternatingCoreClass)
    {n m : ℕ} (hnm : n ≤ m) :
    (alternatingPhaseState G hG n).forbidden ⊆
      (alternatingPhaseState G hG m).forbidden := by
  induction m, hnm using Nat.le_induction with
  | base => exact fun _ hz => hz
  | succ m _ ih =>
      exact fun z hz =>
        alternatingPhaseState_forbidden_succ G hG m
          (ih hz)

/-- Transition time of the positive half of phase `n`. -/
noncomputable def alternatingTransitionTime
    (G : Generator ℤ)
    (hG :
      IsLimitGeneratorOnInjectivePresentations G
        alternatingCoreClass)
    (phase : ℕ) : ℕ :=
  (alternatingPhase G hG phase
    (alternatingPhaseState G hG phase)).transitionTime

/-- Positive generator output permanently omitted at phase `n`. -/
noncomputable def alternatingOmittedOutput
    (G : Generator ℤ)
    (hG :
      IsLimitGeneratorOnInjectivePresentations G
        alternatingCoreClass)
    (phase : ℕ) : ℤ :=
  (alternatingPhase G hG phase
    (alternatingPhaseState G hG phase)).omittedOutput

theorem alternatingTransitionTime_lt_succ
    (G : Generator ℤ)
    (hG :
      IsLimitGeneratorOnInjectivePresentations G
        alternatingCoreClass)
    (phase : ℕ) :
    alternatingTransitionTime G hG phase <
      alternatingTransitionTime G hG (phase + 1) := by
  let current :=
    alternatingPhase G hG phase
      (alternatingPhaseState G hG phase)
  let next :=
    alternatingPhase G hG (phase + 1)
      (alternatingPhaseState G hG (phase + 1))
  have hcurrent :
      current.transitionTime <
        current.next.history.length :=
    current.transition_lt_next_length
  have hbetween :
      current.next.history.length <
        next.transitionTime := by
    have := next.old_length_lt_transition
    simpa [current, next, alternatingPhaseState] using this
  exact lt_trans hcurrent hbetween

theorem alternatingTransitionTime_strictMono
    (G : Generator ℤ)
    (hG :
      IsLimitGeneratorOnInjectivePresentations G
        alternatingCoreClass) :
    StrictMono (alternatingTransitionTime G hG) :=
  strictMono_nat_of_lt_succ
    (alternatingTransitionTime_lt_succ G hG)

theorem alternatingOmittedOutput_positive
    (G : Generator ℤ)
    (hG :
      IsLimitGeneratorOnInjectivePresentations G
        alternatingCoreClass)
    (phase : ℕ) :
    alternatingOmittedOutput G hG phase ∈
      positiveIntegers :=
  (alternatingPhase G hG phase
    (alternatingPhaseState G hG phase)).omitted_positive

private theorem alternatingOmittedOutput_mem_next_forbidden
    (G : Generator ℤ)
    (hG :
      IsLimitGeneratorOnInjectivePresentations G
        alternatingCoreClass)
    (phase : ℕ) :
    alternatingOmittedOutput G hG phase ∈
      (alternatingPhaseState G hG (phase + 1)).forbidden := by
  rw [alternatingPhaseState]
  exact
    (alternatingPhase G hG phase
      (alternatingPhaseState G hG phase)).omitted_mem_next_forbidden

private theorem alternatingOmittedOutput_not_current_forbidden
    (G : Generator ℤ)
    (hG :
      IsLimitGeneratorOnInjectivePresentations G
        alternatingCoreClass)
    (phase : ℕ) :
    alternatingOmittedOutput G hG phase ∉
      (alternatingPhaseState G hG phase).forbidden :=
  (alternatingPhase G hG phase
    (alternatingPhaseState G hG phase)).omitted_not_old_forbidden

theorem alternatingOmittedOutput_injective
    (G : Generator ℤ)
    (hG :
      IsLimitGeneratorOnInjectivePresentations G
        alternatingCoreClass) :
    Function.Injective (alternatingOmittedOutput G hG) := by
  intro n m hnm
  apply Nat.le_antisymm
  · by_contra hmn
    have hmlt : m < n := Nat.lt_of_not_ge hmn
    have hmForbidden :
        alternatingOmittedOutput G hG m ∈
          (alternatingPhaseState G hG n).forbidden := by
      apply
        alternatingPhaseState_forbidden_mono G hG
          (show m + 1 ≤ n by omega)
      exact
        alternatingOmittedOutput_mem_next_forbidden
          G hG m
    apply
      alternatingOmittedOutput_not_current_forbidden
        G hG n
    rw [hnm]
    exact hmForbidden
  · by_contra hnm'
    have hnlt : n < m := Nat.lt_of_not_ge hnm'
    have hnForbidden :
        alternatingOmittedOutput G hG n ∈
          (alternatingPhaseState G hG m).forbidden := by
      apply
        alternatingPhaseState_forbidden_mono G hG
          (show n + 1 ≤ m by omega)
      exact
        alternatingOmittedOutput_mem_next_forbidden
          G hG n
    apply
      alternatingOmittedOutput_not_current_forbidden
        G hG m
    rw [← hnm]
    exact hnForbidden

/-- Infinite stream determined by the nested completed phase histories. -/
noncomputable def alternatingLimitStream
    (G : Generator ℤ)
    (hG :
      IsLimitGeneratorOnInjectivePresentations G
        alternatingCoreClass) :
    Stream ℤ :=
  fun k =>
    (alternatingPhaseState G hG (k + 1)).history.get
      ⟨k, by
        have hlen :=
          alternatingPhaseState_length G hG (k + 1)
        omega⟩

private theorem alternatingLimitStream_eq_state_get
    (G : Generator ℤ)
    (hG :
      IsLimitGeneratorOnInjectivePresentations G
        alternatingCoreClass)
    (phase k : ℕ)
    (hk :
      k <
        (alternatingPhaseState G hG phase).history.length) :
    alternatingLimitStream G hG k =
      (alternatingPhaseState G hG phase).history.get
        ⟨k, hk⟩ := by
  rw [alternatingLimitStream]
  have hkShort :
      k <
        (alternatingPhaseState G hG (k + 1)).history.length := by
    have hlen :=
      alternatingPhaseState_length G hG (k + 1)
    omega
  rw [List.get_eq_getElem, List.get_eq_getElem]
  rcases le_total (k + 1) phase with hle | hge
  · exact
      (alternatingPhaseState_prefix G hG hle).getElem
        hkShort
  · exact
      ((alternatingPhaseState_prefix G hG hge).getElem
        hk).symm

/-- The limit of the nested, duplicate-free phase histories is itself an
injective enumeration. -/
theorem alternatingLimitStream_injective
    (G : Generator ℤ)
    (hG :
      IsLimitGeneratorOnInjectivePresentations G
        alternatingCoreClass) :
    Function.Injective (alternatingLimitStream G hG) := by
  intro a b hab
  let phase := max a b + 1
  have ha :
      a <
        (alternatingPhaseState G hG phase).history.length := by
    have hlen :=
      alternatingPhaseState_length G hG phase
    dsimp only [phase] at hlen ⊢
    omega
  have hb :
      b <
        (alternatingPhaseState G hG phase).history.length := by
    have hlen :=
      alternatingPhaseState_length G hG phase
    dsimp only [phase] at hlen ⊢
    omega
  have hget :
      (alternatingPhaseState G hG phase).history.get
          ⟨a, ha⟩ =
        (alternatingPhaseState G hG phase).history.get
          ⟨b, hb⟩ := by
    exact
      (alternatingLimitStream_eq_state_get
        G hG phase a ha).symm.trans
        (hab.trans
          (alternatingLimitStream_eq_state_get
            G hG phase b hb))
  have hfin :
      (⟨a, ha⟩ :
        Fin
          (alternatingPhaseState G hG phase).history.length) =
        ⟨b, hb⟩ :=
    (List.nodup_iff_injective_get.mp
      (alternatingPhaseState G hG phase).history_nodup)
        hget
  exact congrArg Fin.val hfin

private theorem alternatingPhaseHistory_subset_limitRange
    (G : Generator ℤ)
    (hG :
      IsLimitGeneratorOnInjectivePresentations G
        alternatingCoreClass)
    (phase : ℕ) :
    ((alternatingPhaseState G hG phase).history.toFinset :
        Set ℤ) ⊆
      Set.range (alternatingLimitStream G hG) := by
  intro z hz
  change
    z ∈ (alternatingPhaseState G hG phase).history.toFinset
      at hz
  rw [List.mem_toFinset] at hz
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hz
  refine ⟨i, ?_⟩
  exact
    (alternatingLimitStream_eq_state_get
      G hG phase i i.isLt).trans hi

private theorem alternatingPhaseForbidden_disjoint_limitRange
    (G : Generator ℤ)
    (hG :
      IsLimitGeneratorOnInjectivePresentations G
        alternatingCoreClass)
    (phase : ℕ) :
    Disjoint
      ((alternatingPhaseState G hG phase).forbidden : Set ℤ)
      (Set.range (alternatingLimitStream G hG)) := by
  rw [Set.disjoint_left]
  rintro z hzForbidden ⟨k, hk⟩
  let later := max phase (k + 1)
  have hphaseLater : phase ≤ later :=
    Nat.le_max_left _ _
  have hkLater : k + 1 ≤ later :=
    Nat.le_max_right _ _
  have hzForbiddenLater :
      z ∈ (alternatingPhaseState G hG later).forbidden :=
    alternatingPhaseState_forbidden_mono G hG
      hphaseLater hzForbidden
  have hkLength :
      k <
        (alternatingPhaseState G hG later).history.length := by
    have hlen :=
      alternatingPhaseState_length G hG later
    omega
  have hget :
      (alternatingPhaseState G hG later).history.get
          ⟨k, hkLength⟩ =
        z := by
    exact
      (alternatingLimitStream_eq_state_get
        G hG later k hkLength).symm.trans hk
  have hzHistory :
      z ∈ (alternatingPhaseState G hG later).history.toFinset := by
    rw [List.mem_toFinset]
    rw [← hget]
    exact
      List.get_mem
        (alternatingPhaseState G hG later).history
        ⟨k, hkLength⟩
  exact
    Finset.disjoint_left.mp
      (alternatingPhaseState G hG later).history_forbidden_disjoint
      hzHistory hzForbiddenLater

theorem alternatingOmittedOutput_omitted_forever
    (G : Generator ℤ)
    (hG :
      IsLimitGeneratorOnInjectivePresentations G
        alternatingCoreClass)
    (phase : ℕ) :
    alternatingOmittedOutput G hG phase ∉
      Set.range (alternatingLimitStream G hG) := by
  exact
    Set.disjoint_left.mp
      (alternatingPhaseForbidden_disjoint_limitRange
        G hG (phase + 1))
      (alternatingOmittedOutput_mem_next_forbidden
        G hG phase)

private theorem alternatingNegativeCode_mem_limitRange
    (G : Generator ℤ)
    (hG :
      IsLimitGeneratorOnInjectivePresentations G
        alternatingCoreClass)
    (k : ℕ) :
    negativeCode k ∈
      Set.range (alternatingLimitStream G hG) := by
  have hcursor :
      k <
        (alternatingPhaseState G hG (k + 1)).negativeCursor := by
    have hlower :=
      (alternatingPhaseState G hG (k + 1)).cursor_lower
    omega
  apply alternatingPhaseHistory_subset_limitRange G hG (k + 1)
  change
    negativeCode k ∈
      (alternatingPhaseState G hG (k + 1)).history.toFinset
  rw [List.mem_toFinset]
  exact
    ((alternatingPhaseState G hG
      (k + 1)).negative_mem_history_iff k).mpr hcursor

/-- The cursor-zero repair enumerates every negative integer. -/
theorem alternatingLimitStream_all_negative
    (G : Generator ℤ)
    (hG :
      IsLimitGeneratorOnInjectivePresentations G
        alternatingCoreClass) :
    negativeIntegers ⊆
      Set.range (alternatingLimitStream G hG) := by
  intro z hz
  have hzCode : z ∈ Set.range negativeCode := by
    rw [range_negativeCode]
    exact hz
  obtain ⟨k, rfl⟩ := hzCode
  exact alternatingNegativeCode_mem_limitRange G hG k

theorem alternatingLimitStream_negative_omissions_finite
    (G : Generator ℤ)
    (hG :
      IsLimitGeneratorOnInjectivePresentations G
        alternatingCoreClass) :
    (negativeIntegers \
      Set.range (alternatingLimitStream G hG)).Finite := by
  apply
    Set.finite_empty.subset
  rintro z ⟨hzNegative, hzNotRange⟩
  exact False.elim
    (hzNotRange
      (alternatingLimitStream_all_negative G hG hzNegative))

theorem alternatingLimitStream_no_zero
    (G : Generator ℤ)
    (hG :
      IsLimitGeneratorOnInjectivePresentations G
        alternatingCoreClass) :
    Set.range (alternatingLimitStream G hG) ⊆
      negativeIntegers ∪ positiveIntegers := by
  rintro z ⟨k, rfl⟩
  apply
    (alternatingPhaseState G hG (k + 1)).history_no_zero
  exact
    List.get_mem
      (alternatingPhaseState G hG (k + 1)).history
      ⟨k, by
        have hlen :=
          alternatingPhaseState_length G hG (k + 1)
        omega⟩

theorem alternating_output_at_transition
    (G : Generator ℤ)
    (hG :
      IsLimitGeneratorOnInjectivePresentations G
        alternatingCoreClass)
    (phase : ℕ) :
    output G (alternatingLimitStream G hG)
        (alternatingTransitionTime G hG phase) =
      alternatingOmittedOutput G hG phase := by
  let step :=
    alternatingPhase G hG phase
      (alternatingPhaseState G hG phase)
  have hnext :
      step.next =
        alternatingPhaseState G hG (phase + 1) := by
    rfl
  change
    G step.transitionTime
        (fun k => alternatingLimitStream G hG k) =
      step.omittedOutput
  calc
    G step.transitionTime
        (fun k => alternatingLimitStream G hG k) =
      G step.transitionTime
        (fun k =>
          step.next.history.get
            ⟨k, lt_trans k.isLt
              step.transition_lt_next_length⟩) := by
        congr 1
        funext k
        have hkState :
            k.val <
              (alternatingPhaseState G hG
                (phase + 1)).history.length := by
          rw [← hnext]
          exact
            lt_trans k.isLt
              step.transition_lt_next_length
        have heq :=
          alternatingLimitStream_eq_state_get
            G hG (phase + 1) k hkState
        simpa only [hnext] using heq
    _ = step.omittedOutput :=
      step.output_on_next

/-- Under the temporary assumption that `G` generates the union, the
alternating recursion produces the infinite-phase certificate that defeats
`G`. -/
noncomputable def alternatingInfinitePhaseCertificate
    (G : Generator ℤ)
    (hG :
      IsLimitGeneratorOnInjectivePresentations G
        alternatingCoreClass) :
    InfinitePhaseCertificate G where
  stream := alternatingLimitStream G hG
  stream_injective :=
    alternatingLimitStream_injective G hG
  transitionTime := alternatingTransitionTime G hG
  omittedOutput := alternatingOmittedOutput G hG
  transitionTime_strictMono :=
    alternatingTransitionTime_strictMono G hG
  omittedOutput_injective :=
    alternatingOmittedOutput_injective G hG
  omittedOutput_positive :=
    alternatingOmittedOutput_positive G hG
  output_at_transition :=
    alternating_output_at_transition G hG
  omitted_forever :=
    alternatingOmittedOutput_omitted_forever G hG
  negative_omissions_finite :=
    alternatingLimitStream_negative_omissions_finite G hG
  no_zero_enumerated :=
    alternatingLimitStream_no_zero G hG

/-- The exact-negative limit target belongs to detailed Theorem 4.3's
first class. -/
theorem alternatingLimitStream_mem_firstClass
    (G : Generator ℤ)
    (hG :
      IsLimitGeneratorOnInjectivePresentations G
        alternatingCoreClass) :
    Set.range (alternatingLimitStream G hG) ∈
      theorem43FirstClass := by
  let target := Set.range (alternatingLimitStream G hG)
  let A := target ∩ positiveIntegers
  refine ⟨A, Set.inter_subset_right, ?_⟩
  apply Set.Subset.antisymm
  · intro z hz
    rcases alternatingLimitStream_no_zero G hG hz with
      hzNegative | hzPositive
    · exact Set.mem_union_left _ hzNegative
    · exact Set.mem_union_right _ ⟨hz, hzPositive⟩
  · intro z hz
    rcases hz with hzNegative | hzPositive
    · exact alternatingLimitStream_all_negative
        G hG hzNegative
    · exact hzPositive.1

/-- The single hard lower bound used by both detailed Theorems 4.1 and 4.3.
The limit stream belongs to the common first component: cursor zero gives
all negative integers, and the omitted transition outputs give infinitely
many missing positive integers. -/
theorem alternatingCoreClass_not_generatable_on_injective_presentations :
    ¬GeneratableInLimitOnInjectivePresentations
      alternatingCoreClass := by
  rintro ⟨G, hG⟩
  let certificate := alternatingInfinitePhaseCertificate G hG
  have htarget43 :
      Set.range certificate.stream ∈ theorem43FirstClass := by
    exact alternatingLimitStream_mem_firstClass G hG
  have htarget41 :
      Set.range certificate.stream ∈
        finiteNegativeInfinitePositiveClass := by
    exact certificate.target_mem_firstClass
  obtain ⟨T, hcorrect⟩ :=
    hG (Set.range certificate.stream)
      (Or.inl ⟨htarget43, htarget41⟩) certificate.stream
      certificate.stream_injective rfl
  obtain ⟨k, hk⟩ := certificate.exists_transition_after T
  exact certificate.transition_not_correct k
    (hcorrect (certificate.transitionTime k) hk)

end GenLimit.UnionClosedness.Internal.AlternatingEngine
