import GenLimit.Paper17_InfiniteContamination.ElementObstruction
import GenLimit.Paper17_InfiniteContamination.AlgorithmNine

/-! # Upper bounds for bounded presentations (Theorems 7.9 and 7.11) -/

namespace GenLimit.InfiniteContamination
open Filter GenLimit.KleinbergWei
open scoped Topology

private theorem rank_enumeration (K : OrderedLanguage) (i : ℕ) :
    canonicalRank K K.carrier (K.enumeration i) = i+1 := by
  have h : K.enumeration i ∈ K.carrier := K.range_enumeration ▸ Set.mem_range_self _
  rw [canonicalRank_carrier _ h, K.enumeration_injective (enumeration_canonicalIndex _ h)]

private theorem bounded_pair_of_one_lt (M : ℝ) (hM : 1 < M) :
    ∃ (K : OrderedLanguage) (s : Generic.Stream ℕ),
      K.carrier ⊂ naturalOrder.carrier ∧ VanishingNoiseEnumeration s K.carrier ∧
      VanishingNoiseEnumeration s naturalOrder.carrier ∧ BoundedDisplacement K s K.carrier M ∧
      BoundedDisplacement naturalOrder s naturalOrder.carrier M ∧
      naturalOrder.lowerDensity K.carrier ≤ 1/M ∧ naturalOrder.upperDensity K.carrier ≤ 1/M := by
  classical
  let p := 1 / M
  have hM0 : 0 < M := by linarith
  have hp : 0 < p := one_div_pos.mpr hM0
  have hp1 : p < 1 := (div_lt_one hM0).mpr hM
  let L := floorIncrementLanguage p
  let K := floorIncrementOrder p hp hp1.le
  have hi : L.Infinite := floorIncrementLanguage_infinite p hp hp1.le
  have hd : naturalOrder.upperDensity L = p := floorIncrementLanguage_upperDensity p hp.le hp1.le
  have hc : Lᶜ.Infinite := by
    intro hf
    have h := naturalOrder.upperDensity_diff_finite Set.univ hf
    have hset : Set.univ \ Lᶜ = L := by ext x; simp
    rw [hset, show Set.univ = naturalOrder.carrier from rfl, naturalOrder.upperDensity_carrier] at h
    exact hp1.ne (hd.symm.trans h)
  let s := squareSparseMerge L Lᶜ hi hc
  have hinj : Function.Injective s := squareSparseMerge_injective hi hc disjoint_compl_right
  have hr : Set.range s = Set.univ := (range_squareSparseMerge hi hc).trans (Set.union_compl_self L)
  have hev (A : Set ℕ) (h : L ⊆ A) : VanishingNoiseEnumeration s A :=
    ⟨hinj, fun x _ ↦ hr.symm ▸ Set.mem_univ x, squareSparseMerge_vanishingNoise_of_core_subset hi hc h⟩
  have hsmall : BoundedDisplacement K s K.carrier M := by
    refine ⟨0, fun n _ ↦ ?_⟩
    by_cases h : SparseSquare n
    · have hn : s n ∉ K.carrier := squareSparseMerge_mem_of_square L Lᶜ hi hc h
      simp only [canonicalRank, if_neg hn, Nat.cast_zero]
      positivity
    · have he : s n = K.enumeration (Nat.count SparseNonSquare n) := by
        simp [s, squareSparseMerge, h, K, floorIncrementOrder, floorIncrementStream, L]
      rw [he, rank_enumeration, Nat.cast_add, Nat.cast_one]
      have hle : (Nat.count SparseNonSquare n : ℝ) ≤ n := by exact_mod_cast (Nat.count_le _)
      nlinarith [mul_nonneg (sub_nonneg.mpr hM.le) (show (0:ℝ) ≤ n+1 by positivity)]
  have hcount (n : ℕ) : Nat.count (fun x ↦ x ∈ L) n = ⌊p*n⌋₊ := by
    simpa [OrderedLanguage.prefixCount, naturalOrder, L, Nat.count_eq_card_filter_range]
      using naturalOrder_prefixCount_floorIncrementLanguage p hp.le hp1.le n
  have hthin : ∀ᶠ n : ℕ in atTop, ((Nat.sqrt n : ℝ) + 1) / n < 1-p :=
    tendsto_sparseSqrt_add_one_div.eventually_lt_const (by linarith)
  have hlarge : BoundedDisplacement naturalOrder s naturalOrder.carrier M := by
    apply eventually_atTop.mp
    filter_upwards [hthin, eventually_ge_atTop 1] with n hn hn1
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
    rw [show canonicalRank naturalOrder naturalOrder.carrier (s n) = s n + 1
      from rank_enumeration naturalOrder (s n)]
    by_cases hs : SparseSquare n
    · have hsum : Nat.count (fun x ↦ x ∈ L) n + Nat.count (fun x ↦ x ∈ Lᶜ) n = n := by
        simpa only [Nat.count_eq_card_filter_range, Finset.card_range] using
          (Finset.range n).filter_card_add_filter_neg_card_eq_card (fun x ↦ x ∈ L)
      rw [hcount] at hsum
      have hsum' : (⌊p*n⌋₊ : ℝ) + Nat.count (fun x ↦ x ∈ Lᶜ) n = n := by exact_mod_cast hsum
      have hex : (Nat.sqrt n : ℝ) < Nat.count (fun x ↦ x ∈ Lᶜ) n := by
        linarith [(div_lt_iff₀ hnpos).mp hn, Nat.floor_le (mul_nonneg hp.le hnpos.le)]
      have hindex := Nat.nth_lt_of_lt_count (show Nat.sqrt n < Nat.count (fun x ↦ x ∈ Lᶜ) n by exact_mod_cast hex)
      have hv : s n < n := by simpa only [s, squareSparseMerge, dif_pos hs] using hindex
      have hv' : ((s n + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hv
      nlinarith [mul_nonneg (sub_nonneg.mpr hM.le) hnpos.le]
    · let u := ⌊M*(n+1)⌋₊
      have hnu : M*n ≤ (u : ℝ) := by
        dsimp [u]
        linarith [Nat.lt_floor_add_one (M*(n+1))]
      have hpu : (n : ℝ) ≤ p*u := by
        dsimp [p]
        rw [one_div_mul_eq_div, le_div_iff₀ hM0]
        linarith
      have hncount : n ≤ Nat.count (fun x ↦ x ∈ L) u := by
        rw [hcount]
        exact Nat.le_floor hpu
      have hstrict : Nat.count SparseNonSquare n < n := by
        refine lt_of_le_of_ne (Nat.count_le _) ?_
        intro hall
        exact (Nat.count_iff_forall.mp hall 0 hn1) (sparseSquare_mul_self 0)
      have hv : s n < u := by
        simpa only [s, squareSparseMerge, dif_neg hs] using
          Nat.nth_lt_of_lt_count (hstrict.trans_le hncount)
      exact (show ((s n + 1 : ℕ) : ℝ) ≤ (u : ℝ) by exact_mod_cast hv).trans
        (Nat.floor_le (by positivity))
  refine ⟨K,s,⟨Set.subset_univ _, fun h ↦ ?_⟩,hev _ (by rfl),hev _ (Set.subset_univ _),
    hsmall,hlarge,(floorIncrementLanguage_lowerDensity p hp.le hp1.le).le,hd.le⟩
  exact hp1.not_ge (by simpa only [naturalOrder.upperDensity_carrier, hd] using
    naturalOrder.upperDensity_mono (show naturalOrder.carrier ⊆ L from h))


private def positiveOrder : OrderedLanguage :=
  ⟨Set.range Nat.succ, Nat.succ, Nat.succ_injective, rfl⟩

/-- The sharp examples have a common, fully covering presentation and a
single ambient order. For real M > 1 the language with prefix counts
floor(n/M) replaces the integer multiples in the source construction. -/
theorem bounded_obstruction_pair (M : ℝ) (hM : 1 ≤ M) :
    ∃ (K : OrderedLanguage) (s : Generic.Stream ℕ),
      K.carrier ⊂ naturalOrder.carrier ∧ VanishingNoiseEnumeration s K.carrier ∧
      VanishingNoiseEnumeration s naturalOrder.carrier ∧ BoundedDisplacement K s K.carrier M ∧
      BoundedDisplacement naturalOrder s naturalOrder.carrier M ∧
      naturalOrder.lowerDensity K.carrier ≤ 1/M ∧ naturalOrder.upperDensity K.carrier ≤ 1/M := by
  rcases hM.lt_or_eq with h | rfl
  · exact bounded_pair_of_one_lt M h
  have hav (L : Set ℕ) (h : Lᶜ.Finite) : VanishingNoiseEnumeration id L := by
    apply finiteNoiseEnumeration_implies_vanishingNoiseEnumeration
    exact ⟨Function.injective_id, fun x _ ↦ ⟨x,rfl⟩, h⟩
  have hp : positiveOrder.carrierᶜ ⊆ ({0} : Set ℕ) := by
    rintro (_ | n) hn
    · rfl
    · exact (hn ⟨n,rfl⟩).elim
  refine ⟨positiveOrder, id, ⟨Set.subset_univ _, fun h ↦ ?_⟩,
    hav _ ((Set.finite_singleton 0).subset hp), hav _ (by simp [naturalOrder]), ?_, ?_, ?_, ?_⟩
  · have := h (Set.mem_univ 0)
    simp [positiveOrder] at this
  · refine ⟨1, ?_⟩
    rintro (_ | n) ht
    · omega
    rw [show canonicalRank positiveOrder positiveOrder.carrier (id (n+1)) = n+1
      from rank_enumeration positiveOrder n]
    push_cast
    linarith
  · refine ⟨0, fun n _ ↦ ?_⟩
    rw [show canonicalRank naturalOrder naturalOrder.carrier (id n) = n+1
      from rank_enumeration naturalOrder n]
    simp
  · simpa using naturalOrder.lowerDensity_le_one positiveOrder.carrier
  · simpa using naturalOrder.upperDensity_le_one positiveOrder.carrier

/-- Theorems 7.9 and 7.11 hold on the very same stream. -/
theorem bounded_obstruction_both (M : ℝ) (hM : 1 ≤ M) :
    ∃ (K : OrderedLanguage) (s : Generic.Stream ℕ),
      K.carrier ⊂ naturalOrder.carrier ∧ VanishingNoiseEnumeration s K.carrier ∧
      VanishingNoiseEnumeration s naturalOrder.carrier ∧ BoundedDisplacement K s K.carrier M ∧
      BoundedDisplacement naturalOrder s naturalOrder.carrier M ∧
      (∀ gen, GeneratesSetInLimitOn gen K.carrier s →
        setBasedUpperDensity gen naturalOrder s ≤ 1/M) ∧
      (∀ gen, GeneratesElementInLimitOn gen K.carrier s →
        elementBasedUpperDensity gen naturalOrder s ≤ 1/M) := by
  obtain ⟨K,s,hsub,hK,hN,hbK,hbN,hl,hu⟩ := bounded_obstruction_pair M hM
  refine ⟨K,s,hsub,hK,hN,hbK,hbN,?_,fun gen hg ↦
    (elementBasedUpperDensity_le_of_generates naturalOrder hg).trans hu⟩
  intro gen hg
  obtain ⟨T,hT⟩ := hg
  apply (setBasedUpperDensity_le_of_eventually_subset gen naturalOrder s K.carrier ?_).trans hl
  exact eventually_atTop.mpr ⟨T,fun t ht ↦ (hT t ht).1⟩

end GenLimit.InfiniteContamination
