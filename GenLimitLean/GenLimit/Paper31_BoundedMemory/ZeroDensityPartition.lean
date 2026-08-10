import GenLimit.Paper31_BoundedMemory.MemorylessDensity
import Mathlib.Tactic.Linarith

/-!
# A finite partition into zero-lower-density cells

Source: Jon Kleinberg, Anay Mehrotra, Amin Saberi, and Grigoris Velegkas,
*On Language Generation in the Limit with Bounded Memory*,
arXiv:2605.30324v1, Lemma 4.4.

The source starts with `s₀ = 0` and, for `t ≥ 1`, sets

`ℓₜ = t²(1 + sₜ₋₁)` and `sₜ = sₜ₋₁ + ℓₜ`.

It partitions the canonical enumeration into the consecutive blocks
`[sₜ₋₁, sₜ)` and assigns blocks cyclically to the requested cells.  We use
zero-based block numbers, so block `t` is `[sₜ, sₜ₊₁)` and has length
`(t+1)²(1+sₜ)`.  This is exactly the same schedule with its indices shifted
by one.

The block-location API below factors the interval bookkeeping away from the
set and density arguments.  In particular, later applications can use
`paperBlockIndex_bounds`, `paperBlockIndex_boundary`, and
`prefixCount_paperZeroDensityPiece_le` without repeating the least-block
proof.
-/

namespace GenLimit.BoundedMemory

open Filter
open GenLimit.KleinbergWei

/-! ## The paper's rapidly growing block schedule -/

/-- The endpoints `sₜ` in the proof of Lemma 4.4, with zero-based blocks. -/
def paperBlockBoundary : ℕ → ℕ
  | 0 => 0
  | t + 1 =>
      paperBlockBoundary t +
        (t + 1) ^ 2 * (1 + paperBlockBoundary t)

@[simp] theorem paperBlockBoundary_zero :
    paperBlockBoundary 0 = 0 := rfl

@[simp] theorem paperBlockBoundary_succ (t : ℕ) :
    paperBlockBoundary (t + 1) =
      paperBlockBoundary t +
        (t + 1) ^ 2 * (1 + paperBlockBoundary t) := rfl

theorem paperBlockBoundary_lt_succ (t : ℕ) :
    paperBlockBoundary t < paperBlockBoundary (t + 1) := by
  rw [paperBlockBoundary_succ]
  have hpositive :
      0 < (t + 1) ^ 2 * (1 + paperBlockBoundary t) := by
    positivity
  omega

theorem paperBlockBoundary_strictMono :
    StrictMono paperBlockBoundary :=
  strictMono_nat_of_lt_succ paperBlockBoundary_lt_succ

theorem paperBlockBoundary_index_le (t : ℕ) :
    t ≤ paperBlockBoundary t :=
  paperBlockBoundary_strictMono.id_le t

theorem paperBlockBoundary_unbounded (n : ℕ) :
    ∃ t, n < paperBlockBoundary (t + 1) := by
  exact ⟨n, (Nat.lt_succ_self n).trans_le
    (paperBlockBoundary_index_le (n + 1))⟩

/-- The unique block containing the enumeration position `n`. -/
noncomputable def paperBlockIndex (n : ℕ) : ℕ :=
  Nat.find (paperBlockBoundary_unbounded n)

theorem paperBlockIndex_upper (n : ℕ) :
    n < paperBlockBoundary (paperBlockIndex n + 1) :=
  Nat.find_spec (paperBlockBoundary_unbounded n)

theorem paperBlockIndex_lower (n : ℕ) :
    paperBlockBoundary (paperBlockIndex n) ≤ n := by
  by_cases hzero : paperBlockIndex n = 0
  · simp [hzero]
  · obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero hzero
    rw [ht]
    by_contra hnot
    have hwitness : n < paperBlockBoundary (t + 1) :=
      Nat.lt_of_not_ge hnot
    have hminimal :
        paperBlockIndex n ≤ t :=
      Nat.find_min' (paperBlockBoundary_unbounded n) hwitness
    omega

theorem paperBlockIndex_bounds (n : ℕ) :
    paperBlockBoundary (paperBlockIndex n) ≤ n ∧
      n < paperBlockBoundary (paperBlockIndex n + 1) :=
  ⟨paperBlockIndex_lower n, paperBlockIndex_upper n⟩

theorem paperBlockIndex_le_of_lt_boundary
    {n t : ℕ} (h : n < paperBlockBoundary (t + 1)) :
    paperBlockIndex n ≤ t :=
  Nat.find_min' (paperBlockBoundary_unbounded n) h

theorem paperBlockIndex_boundary (t : ℕ) :
    paperBlockIndex (paperBlockBoundary t) = t := by
  apply Nat.le_antisymm
  · exact paperBlockIndex_le_of_lt_boundary
      (paperBlockBoundary_lt_succ t)
  · by_contra hnot
    have hlt : paperBlockIndex (paperBlockBoundary t) < t :=
      Nat.lt_of_not_ge hnot
    have hsucc_le : paperBlockIndex (paperBlockBoundary t) + 1 ≤ t :=
      Nat.succ_le_of_lt hlt
    have hboundary_le :
        paperBlockBoundary
            (paperBlockIndex (paperBlockBoundary t) + 1) ≤
          paperBlockBoundary t :=
      paperBlockBoundary_strictMono.monotone hsucc_le
    exact (paperBlockIndex_upper (paperBlockBoundary t)).not_ge
      hboundary_le

/-! ## Cyclic cells of an ordered language -/

/-- The cell assigned residue `i`: an element belongs to it precisely when
its unique canonical-enumeration position lies in a block numbered `i`
modulo `m`. -/
def paperZeroDensityPiece
    (K : OrderedLanguage) (m : ℕ) (i : Fin m) : Set ℕ :=
  {x | ∃ n, K.enumeration n = x ∧ paperBlockIndex n % m = i.1}

@[simp] theorem enumeration_mem_paperZeroDensityPiece_iff
    (K : OrderedLanguage) (m : ℕ) (i : Fin m) (n : ℕ) :
    K.enumeration n ∈ paperZeroDensityPiece K m i ↔
      paperBlockIndex n % m = i.1 := by
  constructor
  · rintro ⟨k, hk, howner⟩
    have hkn : k = n := K.enumeration_injective hk
    simpa [hkn] using howner
  · intro howner
    exact ⟨n, rfl, howner⟩

theorem paperZeroDensityPiece_subset_carrier
    (K : OrderedLanguage) (m : ℕ) (i : Fin m) :
    paperZeroDensityPiece K m i ⊆ K.carrier := by
  rintro x ⟨n, rfl, -⟩
  rw [← K.range_enumeration]
  exact ⟨n, rfl⟩

theorem paperZeroDensityPieces_pairwiseDisjoint
    (K : OrderedLanguage) (m : ℕ) :
    ∀ i j : Fin m, i ≠ j →
      Disjoint (paperZeroDensityPiece K m i)
        (paperZeroDensityPiece K m j) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro x hxi hxj
  obtain ⟨n, hn, hi⟩ := hxi
  obtain ⟨k, hk, hj⟩ := hxj
  have hnk : n = k :=
    K.enumeration_injective (hn.trans hk.symm)
  apply hij
  apply Fin.ext
  rw [← hi, ← hj, hnk]

theorem paperZeroDensityPieces_cover
    (K : OrderedLanguage) {m : ℕ} (hm : 0 < m) :
    (⋃ i : Fin m, paperZeroDensityPiece K m i) = K.carrier := by
  apply Set.Subset.antisymm
  · intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨i, hxi⟩ := hx
    exact paperZeroDensityPiece_subset_carrier K m i hxi
  · intro x hx
    rw [← K.range_enumeration] at hx
    obtain ⟨n, rfl⟩ := hx
    let i : Fin m :=
      ⟨paperBlockIndex n % m, Nat.mod_lt _ hm⟩
    exact Set.mem_iUnion.mpr
      ⟨i, enumeration_mem_paperZeroDensityPiece_iff K m i n |>.2 rfl⟩

theorem blockNumber_residue (m q : ℕ) (i : Fin m) :
    (m * q + i.1) % m = i.1 := by
  rw [Nat.add_mod, Nat.mul_mod]
  simp [Nat.mod_eq_of_lt i.2]

theorem paperZeroDensityPiece_infinite
    (K : OrderedLanguage) {m : ℕ} (hm : 0 < m) (i : Fin m) :
    (paperZeroDensityPiece K m i).Infinite := by
  let f : ℕ → ℕ :=
    fun q => K.enumeration (paperBlockBoundary (m * q + i.1))
  have hmq : Function.Injective (fun q : ℕ => m * q + i.1) := by
    intro q r h
    have hmul : m * q = m * r := Nat.add_right_cancel h
    exact Nat.eq_of_mul_eq_mul_left
      (show 0 < m from hm)
      hmul
  have hf : Function.Injective f :=
    K.enumeration_injective.comp
      (paperBlockBoundary_strictMono.injective.comp hmq)
  apply (Set.infinite_range_of_injective hf).mono
  rintro x ⟨q, rfl⟩
  apply
    (enumeration_mem_paperZeroDensityPiece_iff K m i
      (paperBlockBoundary (m * q + i.1))).2
  rw [paperBlockIndex_boundary]
  exact blockNumber_residue m q i

/-! ## Counting at the end of a foreign block -/

theorem paperBlockIndex_lt_of_lt_boundary_of_residue_ne
    {m n t r : ℕ}
    (hn : n < paperBlockBoundary (t + 1))
    (howner : paperBlockIndex n % m = r)
    (ht : t % m ≠ r) :
    paperBlockIndex n < t := by
  have hle := paperBlockIndex_le_of_lt_boundary hn
  by_contra hnot
  have heq : paperBlockIndex n = t :=
    Nat.le_antisymm hle (Nat.le_of_not_gt hnot)
  apply ht
  simpa [heq] using howner

theorem index_lt_boundary_of_foreign_block
    {m n t r : ℕ}
    (hn : n < paperBlockBoundary (t + 1))
    (howner : paperBlockIndex n % m = r)
    (ht : t % m ≠ r) :
    n < paperBlockBoundary t := by
  have hindex :
      paperBlockIndex n + 1 ≤ t :=
    Nat.succ_le_of_lt
      (paperBlockIndex_lt_of_lt_boundary_of_residue_ne hn howner ht)
  exact (paperBlockIndex_upper n).trans_le
    (paperBlockBoundary_strictMono.monotone hindex)

/-- At the end of a block owned by another cell, all occurrences of this
cell lie before the start of that block.  This is the finite-count estimate
in the proof of Lemma 4.4. -/
theorem prefixCount_paperZeroDensityPiece_le
    (K : OrderedLanguage) {m : ℕ} (i : Fin m) {t : ℕ}
    (ht : t % m ≠ i.1) :
    K.prefixCount (paperZeroDensityPiece K m i)
        (paperBlockBoundary (t + 1)) ≤
      paperBlockBoundary t := by
  classical
  unfold OrderedLanguage.prefixCount
  rw [← Finset.card_range (paperBlockBoundary t)]
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn
  simp only [Finset.mem_range]
  exact index_lt_boundary_of_foreign_block hn.1
    ((enumeration_mem_paperZeroDensityPiece_iff K m i n).1 hn.2) ht

theorem paperBlockBoundary_ratio_le
    (t : ℕ) :
    (paperBlockBoundary t : ℝ) /
        paperBlockBoundary (t + 1) ≤
      1 / (t + 1 : ℝ) := by
  have ht : (0 : ℝ) < t + 1 := by positivity
  have hboundary :
      (0 : ℝ) < paperBlockBoundary (t + 1) := by
    exact_mod_cast paperBlockBoundary_strictMono (Nat.zero_lt_succ t)
  rw [div_le_div_iff₀ hboundary ht]
  rw [paperBlockBoundary_succ]
  push_cast
  have hs : (0 : ℝ) ≤ paperBlockBoundary t := by positivity
  nlinarith [sq_nonneg (t : ℝ)]

theorem prefixRatio_paperZeroDensityPiece_le
    (K : OrderedLanguage) {m : ℕ} (i : Fin m) {t : ℕ}
    (ht : t % m ≠ i.1) :
    K.prefixRatio (paperZeroDensityPiece K m i)
        (paperBlockBoundary (t + 1)) ≤
      1 / (t + 1 : ℝ) := by
  have hpositive : paperBlockBoundary (t + 1) ≠ 0 :=
    Nat.ne_of_gt
      (paperBlockBoundary_strictMono (Nat.zero_lt_succ t))
  rw [OrderedLanguage.prefixRatio, if_neg hpositive]
  exact (div_le_div_of_nonneg_right
      (by exact_mod_cast prefixCount_paperZeroDensityPiece_le K i ht)
      (Nat.cast_nonneg _)).trans
    (paperBlockBoundary_ratio_le t)

/-! ## Lemma 4.4 -/

theorem orderedLowerDensity_nonneg'
    (K : OrderedLanguage) (A : Set ℕ) :
    0 ≤ K.lowerDensity A := by
  unfold OrderedLanguage.lowerDensity
  apply le_liminf_of_le
  · exact isCoboundedUnder_ge_of_le atTop
      (fun n => K.prefixRatio_le_one A n)
  · exact Filter.Eventually.of_forall
      (fun n => K.prefixRatio_nonneg A n)

/-- For every positive tolerance and every starting point, a foreign block
ends later than that point with the chosen cell's prefix ratio below the
tolerance. -/
theorem frequently_prefixRatio_paperZeroDensityPiece_le
    (K : OrderedLanguage) {m : ℕ} (hm : 2 ≤ m) (i : Fin m)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ n : ℕ in atTop,
      K.prefixRatio (paperZeroDensityPiece K m i) n ≤ ε := by
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (1 / ε)
  let j : Fin m :=
    if hi : i.1 = 0 then
      ⟨1, by omega⟩
    else
      ⟨0, Nat.zero_lt_of_lt hm⟩
  have hji : j ≠ i := by
    intro h
    have hval : j.1 = i.1 := congrArg Fin.val h
    by_cases hi : i.1 = 0
    · have hj : j.1 = 1 := by simp [j, hi]
      omega
    · have hj : j.1 = 0 := by simp [j, hi]
      omega
  rw [Filter.frequently_atTop]
  intro cutoff
  let q := max cutoff N
  let t := m * q + j.1
  refine ⟨paperBlockBoundary (t + 1), ?_, ?_⟩
  · exact
      (show cutoff ≤ t + 1 by
        dsimp [t, q]
        have hm1 : 1 ≤ m := le_trans (by omega) hm
        have hq : cutoff ≤ max cutoff N := Nat.le_max_left _ _
        nlinarith)
      |>.trans (paperBlockBoundary_index_le (t + 1))
  · apply (prefixRatio_paperZeroDensityPiece_le K i
      (t := t) ?_).trans
    · have hqN : N ≤ q := Nat.le_max_right _ _
      have hNt : (N : ℝ) < t + 1 := by
        exact_mod_cast
          (lt_of_le_of_lt hqN
            (show q < t + 1 by
              dsimp [t]
              have hm1 : 1 ≤ m := le_trans (by omega) hm
              nlinarith))
      have hrecip : 1 / ε < (t + 1 : ℝ) :=
        hN.trans hNt
      have htpos : (0 : ℝ) < t + 1 := by positivity
      rw [div_le_iff₀ htpos]
      have := (div_lt_iff₀ hε).1 hrecip
      nlinarith
    · rw [show t % m = j.1 by
          dsimp [t]
          exact blockNumber_residue m q j]
      exact fun h => hji (Fin.ext h)

theorem paperZeroDensityPiece_lowerDensity
    (K : OrderedLanguage) {m : ℕ} (hm : 2 ≤ m) (i : Fin m) :
    K.lowerDensity (paperZeroDensityPiece K m i) = 0 := by
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    simpa only [zero_add] using
      liminf_le_of_frequently_le
        (frequently_prefixRatio_paperZeroDensityPiece_le K hm i hε)
        (isBoundedUnder_of
          ⟨0, fun n =>
            K.prefixRatio_nonneg
              (paperZeroDensityPiece K m i) n⟩)
  · exact orderedLowerDensity_nonneg' K
      (paperZeroDensityPiece K m i)

/-- Lemma 4.4, exactly at the paper's ordered-`liminf` level.

Any canonically ordered countably infinite language is partitioned into
`m ≥ 2` pairwise-disjoint infinite cells, and every cell has lower density
zero in that same canonical ordering. -/
theorem lemma_4_4_zero_lower_density_partition
    (K : OrderedLanguage) (m : ℕ) (hm : 2 ≤ m) :
    ∃ pieces : Fin m → Set ℕ,
      (∀ i j, i ≠ j → Disjoint (pieces i) (pieces j)) ∧
      (⋃ i, pieces i) = K.carrier ∧
      (∀ i, (pieces i).Infinite) ∧
      (∀ i, K.lowerDensity (pieces i) = 0) := by
  refine ⟨paperZeroDensityPiece K m, ?_, ?_, ?_, ?_⟩
  · exact paperZeroDensityPieces_pairwiseDisjoint K m
  · exact paperZeroDensityPieces_cover K (lt_of_lt_of_le Nat.zero_lt_two hm)
  · exact fun i =>
      paperZeroDensityPiece_infinite K
        (lt_of_lt_of_le Nat.zero_lt_two hm) i
  · exact paperZeroDensityPiece_lowerDensity K hm

end GenLimit.BoundedMemory
