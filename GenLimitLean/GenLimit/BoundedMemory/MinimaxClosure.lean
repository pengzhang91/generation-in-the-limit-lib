import GenLimit.BoundedMemory.SpernerAchievability
import GenLimit.BoundedMemory.ZeroDensityPartition
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Exact memoryless minimax density closure

Source: Jon Kleinberg, Anay Mehrotra, Amin Saberi, and Grigoris Velegkas,
*On Language Generation in the Limit with Bounded Memory*,
arXiv:2605.30324v1, Definition 9 and Theorems 4.1--4.2.

This file adds an order-robust specialization of the paper's outer minimax
layer to the previously checked Section 4.1 ingredients.  In particular, the
guarantee below is stated using the second `limsup` from Definition 9:

`limsup_t upperDensity_K (G (stream t))`.

Thus the supremum is not replaced by an eventual or pointwise proxy.  The
source fixes one canonical order of the universe; the declaration below
strengthens that convention by quantifying over every duplicate-free ordered
realization of each target.
The exact upper-density value follows from Lemmas 4.7 and 4.8.  The exact
lower-density obstruction follows from Lemmas 4.3 and 4.4.
-/

namespace GenLimit.BoundedMemory

open Filter
open GenLimit.KleinbergWei
open scoped Topology

/-! ## Run density and the order-robust Definition 9 specialization -/

/-- The outer `limsup_t` in Definition 9, applied to the ordered upper
density of the set output on round `t`. -/
noncomputable def memorylessRunUpperDensity
    (K : OrderedLanguage) (G : MemorylessSetGenerator ℕ)
    (stream : ℕ → ℕ) : ℝ :=
  limsup (fun t => K.upperDensity (G (stream t))) atTop

/-- The property whose admissible values are supremized in the order-robust
specialization of Definition 9, with a size-`k` collection represented by an
injective `Fin k` indexing.

The collection may tailor its generator to the family.  The adversary then
chooses the target, its duplicate-free density order, and a finitely
repeating exact presentation. -/
def MemorylessUpperDensityGuarantee (k : ℕ) (σ : ℝ) : Prop :=
  ∀ (langs : Fin k → Set ℕ),
    Function.Injective langs →
    (∀ i, (langs i).Infinite) →
    ∃ G : MemorylessSetGenerator ℕ,
      IsFinitelyRepeatingMemorylessGenerator G (Set.range langs) ∧
      ∀ (target : Fin k) (K : OrderedLanguage),
        K.carrier = langs target →
        ∀ stream : ℕ → ℕ,
          GenLimit.Generic.Presents stream K.carrier →
          FinitelyRepeating stream →
          σ ≤ memorylessRunUpperDensity K G stream

/-- The subset of `[0,1]` appearing inside the supremum in Definition 9. -/
def memorylessAdmissibleUpperDensities (k : ℕ) : Set ℝ :=
  Set.Icc (0 : ℝ) 1 ∩
    {σ | MemorylessUpperDensityGuarantee k σ}

/-- The order-robust `ℕ` specialization of Definition 9 for memoryless
generators. -/
noncomputable def memorylessMinimaxUpperDensity (k : ℕ) : ℝ :=
  sSup (memorylessAdmissibleUpperDensities k)

/-- The reciprocal Boolean-lattice width in Theorem 4.1. -/
noncomputable def memorylessSpernerValue (k : ℕ) : ℝ :=
  1 / (Nat.choose (k - 1) ((k - 1) / 2) : ℝ)

theorem orderedUpperDensity_nonneg'
    (K : OrderedLanguage) (A : Set ℕ) :
    0 ≤ K.upperDensity A := by
  unfold OrderedLanguage.upperDensity
  apply le_limsup_of_frequently_le
  · exact Filter.Frequently.of_forall
      (fun n => K.prefixRatio_nonneg A n)
  · exact isBoundedUnder_of
      ⟨1, fun n => K.prefixRatio_le_one A n⟩

theorem orderedUpperDensity_carrier_eq_one
    (K : OrderedLanguage) :
    K.upperDensity K.carrier = 1 := by
  have htendsto :
      Tendsto (K.prefixRatio K.carrier) atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    simp [OrderedLanguage.prefixRatio_carrier, hn]
  exact htendsto.limsup_eq

theorem orderedLowerDensity_carrier_eq_one
    (K : OrderedLanguage) :
    K.lowerDensity K.carrier = 1 := by
  have htendsto :
      Tendsto (K.prefixRatio K.carrier) atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    simp [OrderedLanguage.prefixRatio_carrier, hn]
  exact htendsto.liminf_eq

theorem memorylessRunUpperDensity_le_one
    (K : OrderedLanguage) (G : MemorylessSetGenerator ℕ)
    (stream : ℕ → ℕ) :
    memorylessRunUpperDensity K G stream ≤ 1 := by
  unfold memorylessRunUpperDensity
  apply limsup_le_of_le
  · exact isCoboundedUnder_le_of_le atTop
      (fun t => orderedUpperDensity_nonneg' K (G (stream t)))
  · exact Filter.Eventually.of_forall
      (fun t => orderedUpperDensity_le_one K (G (stream t)))

theorem memorylessRunUpperDensity_ge_of_frequently
    (K : OrderedLanguage) (G : MemorylessSetGenerator ℕ)
    (stream : ℕ → ℕ) {σ : ℝ}
    (hσ : ∃ᶠ t : ℕ in atTop,
      σ ≤ K.upperDensity (G (stream t))) :
    σ ≤ memorylessRunUpperDensity K G stream := by
  unfold memorylessRunUpperDensity
  exact le_limsup_of_frequently_le hσ
    (isBoundedUnder_of
      ⟨1, fun t => orderedUpperDensity_le_one K (G (stream t))⟩)

theorem memorylessRunUpperDensity_le_of_eventually
    (K : OrderedLanguage) (G : MemorylessSetGenerator ℕ)
    (stream : ℕ → ℕ) {σ : ℝ}
    (hσ : ∀ᶠ t : ℕ in atTop,
      K.upperDensity (G (stream t)) ≤ σ) :
    memorylessRunUpperDensity K G stream ≤ σ := by
  unfold memorylessRunUpperDensity
  apply limsup_le_of_le
  · exact isCoboundedUnder_le_of_le atTop
      (fun t => orderedUpperDensity_nonneg' K (G (stream t)))
  · exact hσ

theorem memorylessSpernerValue_mem_Icc
    (k : ℕ) :
    memorylessSpernerValue k ∈ Set.Icc (0 : ℝ) 1 := by
  have hchooseNat :
      1 ≤ Nat.choose (k - 1) ((k - 1) / 2) :=
    Nat.succ_le_iff.mpr (middleWidth_pos (k - 1))
  have hchooseReal :
      (1 : ℝ) ≤ Nat.choose (k - 1) ((k - 1) / 2) := by
    exact_mod_cast hchooseNat
  constructor
  · unfold memorylessSpernerValue
    positivity
  · unfold memorylessSpernerValue
    simpa using
      one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num)
        hchooseReal

/-! ## The lower half of Theorem 4.1 -/

theorem memorylessSpernerValue_guaranteed
    (k : ℕ) (hk : 1 ≤ k) :
    MemorylessUpperDensityGuarantee k
      (memorylessSpernerValue k) := by
  cases k with
  | zero => omega
  | succ n =>
      intro langs _hInjective hInfinite
      refine
        ⟨canonicalDensityGenerator langs,
          canonicalDensityGenerator_succeeds langs, ?_⟩
      intro target K hK stream hP _hRepeat
      apply memorylessRunUpperDensity_ge_of_frequently
      simpa [memorylessSpernerValue] using
        canonicalDensityGenerator_frequently_sperner_dense
          langs target K hK stream hP

theorem memorylessSpernerValue_admissible
    (k : ℕ) (hk : 1 ≤ k) :
    memorylessSpernerValue k ∈
      memorylessAdmissibleUpperDensities k := by
  exact ⟨memorylessSpernerValue_mem_Icc k,
    memorylessSpernerValue_guaranteed k hk⟩

/-! ## The upper half of Theorem 4.1 -/

theorem admissibleUpperDensity_le_spernerValue
    (k : ℕ) (hk : 1 ≤ k) {σ : ℝ}
    (hσ : σ ∈ memorylessAdmissibleUpperDensities k) :
    σ ≤ memorylessSpernerValue k := by
  by_cases hkOne : k = 1
  · subst k
    simpa [memorylessSpernerValue] using hσ.1.2
  · have hkTwo : 2 ≤ k := by omega
    obtain
      ⟨K, langs, target, hInjective, hInfinite,
        hTarget, hHard⟩ :=
      lemma_4_7_sperner_hard_instance k hkTwo
    obtain ⟨G, hG, hGuarantee⟩ :=
      hσ.2 langs hInjective hInfinite
    let stream := K.enumeration
    have hP :
        GenLimit.Generic.Presents stream K.carrier := by
      exact K.range_enumeration
    have hStreamInjective : Function.Injective stream :=
      K.enumeration_injective
    obtain ⟨T, hT⟩ :=
      hHard G hG stream hP hStreamInjective
    have hEventually :
        ∀ᶠ t : ℕ in atTop,
          K.upperDensity (G (stream t)) ≤
            memorylessSpernerValue k := by
      filter_upwards [eventually_ge_atTop T] with t ht
      simpa [memorylessSpernerValue] using hT t ht
    have hRunUpper :
        memorylessRunUpperDensity K G stream ≤
          memorylessSpernerValue k :=
      memorylessRunUpperDensity_le_of_eventually
        K G stream hEventually
    have hRunLower :
        σ ≤ memorylessRunUpperDensity K G stream :=
      hGuarantee target K hTarget.symm stream hP
        (injective_finitelyRepeating hStreamInjective)
    exact hRunLower.trans hRunUpper

theorem memorylessAdmissibleUpperDensities_bddAbove
    (k : ℕ) :
    BddAbove (memorylessAdmissibleUpperDensities k) := by
  refine ⟨1, ?_⟩
  intro σ hσ
  exact hσ.1.2

/-- Theorem 4.1 for the order-robust specialization, including the actual
supremum and outer run `limsup`. -/
theorem theorem_4_1_memoryless_minimax_upper_density
    (k : ℕ) (hk : 1 ≤ k) :
    memorylessMinimaxUpperDensity k =
      1 / (Nat.choose (k - 1) ((k - 1) / 2) : ℝ) := by
  change memorylessMinimaxUpperDensity k =
    memorylessSpernerValue k
  unfold memorylessMinimaxUpperDensity
  apply le_antisymm
  · apply csSup_le
    · exact
        ⟨memorylessSpernerValue k,
          memorylessSpernerValue_admissible k hk⟩
    · intro σ hσ
      exact admissibleUpperDensity_le_spernerValue k hk hσ
  · exact le_csSup
      (memorylessAdmissibleUpperDensities_bddAbove k)
      (memorylessSpernerValue_admissible k hk)

/-! ## Theorem 4.2 -/

/-- The source's hard family for Theorem 4.2, written with `m+2`
members: the target followed by the `m+1` zero-lower-density cells. -/
noncomputable def zeroLowerDensityHardFamily (m : ℕ) :
    Fin (m + 2) → Set ℕ :=
  Fin.cases spernerTargetOrder.carrier
    (paperZeroDensityPiece spernerTargetOrder (m + 1))

@[simp] theorem zeroLowerDensityHardFamily_zero (m : ℕ) :
    zeroLowerDensityHardFamily m 0 =
      spernerTargetOrder.carrier := by
  simp [zeroLowerDensityHardFamily]

@[simp] theorem zeroLowerDensityHardFamily_succ
    (m : ℕ) (i : Fin (m + 1)) :
    zeroLowerDensityHardFamily m i.succ =
      paperZeroDensityPiece spernerTargetOrder (m + 1) i := by
  simp [zeroLowerDensityHardFamily]

theorem zeroLowerDensityPieces_injective
    (m : ℕ) (hm : 1 ≤ m) :
    Function.Injective
      (paperZeroDensityPiece spernerTargetOrder (m + 1)) := by
  intro i j hij
  by_contra hne
  have hDisjoint :
      Disjoint
        (paperZeroDensityPiece spernerTargetOrder (m + 1) i)
        (paperZeroDensityPiece spernerTargetOrder (m + 1) j) :=
    paperZeroDensityPieces_pairwiseDisjoint
      spernerTargetOrder (m + 1) i j hne
  obtain ⟨x, hx⟩ :=
    (paperZeroDensityPiece_infinite spernerTargetOrder
      (by omega : 0 < m + 1) i).nonempty
  exact (Set.disjoint_left.1 hDisjoint) hx
    (by simpa [hij] using hx)

theorem zeroLowerDensityPiece_ne_carrier
    (m : ℕ) (hm : 1 ≤ m) (i : Fin (m + 1)) :
    paperZeroDensityPiece spernerTargetOrder (m + 1) i ≠
      spernerTargetOrder.carrier := by
  intro hEq
  have hzero :
      spernerTargetOrder.lowerDensity
        (paperZeroDensityPiece spernerTargetOrder (m + 1) i) = 0 :=
    paperZeroDensityPiece_lowerDensity
      spernerTargetOrder (by omega) i
  rw [hEq, orderedLowerDensity_carrier_eq_one] at hzero
  norm_num at hzero

theorem zeroLowerDensityHardFamily_injective
    (m : ℕ) (hm : 1 ≤ m) :
    Function.Injective (zeroLowerDensityHardFamily m) := by
  intro a
  refine Fin.cases ?_ (fun i => ?_) a
  · intro b
    refine Fin.cases (fun _ => rfl) (fun j hab => ?_) b
    exfalso
    exact zeroLowerDensityPiece_ne_carrier m hm j
      (by simpa using hab.symm)
  · intro b
    refine Fin.cases ?_ (fun j hij => ?_) b
    · intro hab
      exfalso
      exact zeroLowerDensityPiece_ne_carrier m hm i
        (by simpa using hab)
    · apply congrArg Fin.succ
      apply zeroLowerDensityPieces_injective m hm
      simpa using hij

theorem zeroLowerDensityHardFamily_infinite
    (m : ℕ) (hm : 1 ≤ m) :
    ∀ i, (zeroLowerDensityHardFamily m i).Infinite := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using Set.infinite_univ
  · exact paperZeroDensityPiece_infinite spernerTargetOrder
      (by omega) j

theorem zeroLowerDensityHardFamily_partition
    (m : ℕ) (hm : 1 ≤ m) :
    IsFinitePartition
      (paperZeroDensityPiece spernerTargetOrder (m + 1))
      spernerTargetOrder.carrier := by
  constructor
  · exact paperZeroDensityPieces_pairwiseDisjoint
      spernerTargetOrder (m + 1)
  · exact paperZeroDensityPieces_cover
      spernerTargetOrder (by omega)

theorem zeroLowerDensityPartition_maximum_eq_zero
    (m : ℕ) (hm : 1 ≤ m) :
    maximumPartitionLowerDensity spernerTargetOrder
      (paperZeroDensityPiece spernerTargetOrder (m + 1)) = 0 := by
  classical
  unfold maximumPartitionLowerDensity
  simp [paperZeroDensityPiece_lowerDensity
    spernerTargetOrder (show 2 ≤ m + 1 by omega)]

theorem theorem_4_2_indexed
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ (K : OrderedLanguage) (langs : Fin (m + 2) → Set ℕ)
        (target : Fin (m + 2)),
      Function.Injective langs ∧
      (∀ i, (langs i).Infinite) ∧
      langs target = K.carrier ∧
      ∀ G : MemorylessSetGenerator ℕ,
        IsFinitelyRepeatingMemorylessGenerator G (Set.range langs) →
        ∀ stream : ℕ → ℕ,
          GenLimit.Generic.Presents stream K.carrier →
          Function.Injective stream →
          (∃ T, ∀ t, T ≤ t →
            K.lowerDensity (G (stream t)) = 0) ∧
          (∀ σ : ℝ, 0 < σ →
            ¬ ∃ᶠ t : ℕ in atTop,
              σ ≤ K.lowerDensity (G (stream t))) := by
  let pieces :=
    paperZeroDensityPiece spernerTargetOrder (m + 1)
  refine
    ⟨spernerTargetOrder, zeroLowerDensityHardFamily m, 0,
      zeroLowerDensityHardFamily_injective m hm,
      zeroLowerDensityHardFamily_infinite m hm, rfl, ?_⟩
  intro G hG stream hP hInjective
  have hGpieces :
      ∀ i, IsRepetitionFreeMemorylessGeneratorOn G (pieces i) := by
    intro i pieceStream hPieceP hPieceInjective
    apply hG (pieces i)
      (by
        refine ⟨i.succ, ?_⟩
        simp [pieces])
      pieceStream hPieceP
      (injective_finitelyRepeating hPieceInjective)
  obtain ⟨T, hT⟩ :=
    lemma_4_3_lower_density_bound_from_partition
      spernerTargetOrder pieces
      (by
        simpa [pieces] using
          zeroLowerDensityHardFamily_partition m hm)
      (by
        intro i
        exact paperZeroDensityPiece_infinite
          spernerTargetOrder (by omega) i)
      G hGpieces stream hP hInjective
  have hZero (t : ℕ) (ht : T ≤ t) :
      spernerTargetOrder.lowerDensity (G (stream t)) = 0 := by
    apply le_antisymm
    · simpa [pieces,
        zeroLowerDensityPartition_maximum_eq_zero m hm] using hT t ht
    · exact orderedLowerDensity_nonneg'
        spernerTargetOrder (G (stream t))
  have hEventuallyZero :
      ∀ᶠ t : ℕ in atTop,
        spernerTargetOrder.lowerDensity (G (stream t)) = 0 := by
    filter_upwards [eventually_ge_atTop T] with t ht
    exact hZero t ht
  constructor
  · exact ⟨T, hZero⟩
  · intro σ hσ
    rw [Filter.not_frequently]
    exact hEventuallyZero.mono fun t ht hσt => by
      rw [ht] at hσt
      linarith

/-- Theorem 4.2 with the paper's literal `k ≥ 3` indexing. -/
theorem theorem_4_2_no_uniform_positive_lower_density
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ (K : OrderedLanguage) (langs : Fin k → Set ℕ)
        (target : Fin k),
      Function.Injective langs ∧
      (∀ i, (langs i).Infinite) ∧
      langs target = K.carrier ∧
      ∀ G : MemorylessSetGenerator ℕ,
        IsFinitelyRepeatingMemorylessGenerator G (Set.range langs) →
        ∀ stream : ℕ → ℕ,
          GenLimit.Generic.Presents stream K.carrier →
          Function.Injective stream →
          (∃ T, ∀ t, T ≤ t →
            K.lowerDensity (G (stream t)) = 0) ∧
          (∀ σ : ℝ, 0 < σ →
            ¬ ∃ᶠ t : ℕ in atTop,
              σ ≤ K.lowerDensity (G (stream t))) := by
  let m := k - 2
  have hm : 1 ≤ m := by
    dsimp [m]
    omega
  have hkEq : k = m + 2 := by
    dsimp [m]
    omega
  rw [hkEq]
  exact theorem_4_2_indexed m hm

end GenLimit.BoundedMemory
