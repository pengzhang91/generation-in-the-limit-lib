import GenLimit.Paper31_BoundedMemory.SpernerHardInstance
import Mathlib.Combinatorics.SetFamily.LYM
import Mathlib.Order.Preorder.Finite
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Achieving the Sperner upper-density bound

Source: Jon Kleinberg, Anay Mehrotra, Amin Saberi, and Grigoris Velegkas,
*On Language Generation in the Limit with Bounded Memory*,
arXiv:2605.30324v1, Lemma 4.8.

The source proves the density half using a symmetric-chain decomposition.
Mathlib currently contains Sperner's theorem, but no Boolean-lattice
symmetric-chain decomposition.  We prove the same exact statement by a
closely related antichain argument.

For a fixed target, consider the relative signatures whose exact regions are
infinite, and retain the inclusion-minimal ones.  They form an antichain, so
Sperner bounds their number by the central binomial coefficient.  Their
upward intersections cover the target after discarding the finitely many
finite exact regions.  Finite subadditivity of ordered upper density then
forces one such intersection to have density at least the reciprocal
Sperner width.  Its exact region is infinite, so every target enumeration
visits it infinitely often, and the canonical generator outputs that
intersection at all of those times.
-/

namespace GenLimit.BoundedMemory

open Filter
open scoped BigOperators Topology
open GenLimit.KleinbergWei

/-! ## Relative signatures and regions -/

/-- Indices of family members other than the selected target. -/
abbrev OtherIndex {n : ℕ} (target : Fin (n + 1)) :=
  {j : Fin (n + 1) // j ≠ target}

@[simp] theorem otherIndex_card
    {n : ℕ} (target : Fin (n + 1)) :
    Fintype.card (OtherIndex target) = n := by
  classical
  change Fintype.card {j : Fin (n + 1) // ¬j = target} = n
  rw [Fintype.card_subtype_compl]
  simp

/-- Signature of `x`, restricted to the `n` non-target languages. -/
noncomputable def relativeSignature
    {n : ℕ} (langs : Fin (n + 1) → Set ℕ)
    (target : Fin (n + 1)) (x : ℕ) :
    Finset (OtherIndex target) := by
  classical
  exact Finset.univ.filter fun j => x ∈ langs j.1

@[simp] theorem mem_relativeSignature_iff
    {n : ℕ} (langs : Fin (n + 1) → Set ℕ)
    (target : Fin (n + 1)) (x : ℕ)
    (j : OtherIndex target) :
    j ∈ relativeSignature langs target x ↔ x ∈ langs j.1 := by
  simp [relativeSignature]

/-- Exact relative region `R'_B` from Lemma 4.8. -/
def relativeRegion
    {n : ℕ} (langs : Fin (n + 1) → Set ℕ)
    (target : Fin (n + 1))
    (B : Finset (OtherIndex target)) : Set ℕ :=
  {x | x ∈ langs target ∧ relativeSignature langs target x = B}

/-- The upward intersection `I'_B`. -/
def relativeCore
    {n : ℕ} (langs : Fin (n + 1) → Set ℕ)
    (target : Fin (n + 1))
    (B : Finset (OtherIndex target)) : Set ℕ :=
  {x | x ∈ langs target ∧
    ∀ j : OtherIndex target, j ∈ B → x ∈ langs j.1}

theorem relativeRegion_subset_target
    {n : ℕ} (langs : Fin (n + 1) → Set ℕ)
    (target : Fin (n + 1))
    (B : Finset (OtherIndex target)) :
    relativeRegion langs target B ⊆ langs target :=
  fun _ hx => hx.1

theorem relativeRegion_subset_relativeCore
    {n : ℕ} (langs : Fin (n + 1) → Set ℕ)
    (target : Fin (n + 1))
    (B : Finset (OtherIndex target)) :
    relativeRegion langs target B ⊆
      relativeCore langs target B := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  intro j hj
  exact (mem_relativeSignature_iff langs target x j).1
    (hx.2.symm ▸ hj)

theorem mem_relativeCore_iff_signature_superset
    {n : ℕ} (langs : Fin (n + 1) → Set ℕ)
    (target : Fin (n + 1))
    (B : Finset (OtherIndex target)) (x : ℕ) :
    x ∈ relativeCore langs target B ↔
      x ∈ langs target ∧
        B ⊆ relativeSignature langs target x := by
  constructor
  · intro hx
    refine ⟨hx.1, ?_⟩
    intro j hj
    exact (mem_relativeSignature_iff langs target x j).2
      (hx.2 j hj)
  · intro hx
    refine ⟨hx.1, ?_⟩
    intro j hj
    exact (mem_relativeSignature_iff langs target x j).1
      (hx.2 hj)

theorem finiteFamilyCore_eq_relativeCore
    {n : ℕ} (langs : Fin (n + 1) → Set ℕ)
    (target : Fin (n + 1))
    {B : Finset (OtherIndex target)} {x : ℕ}
    (hx : x ∈ relativeRegion langs target B) :
    finiteFamilyCore langs x = relativeCore langs target B := by
  ext y
  constructor
  · intro hy
    refine ⟨hy target hx.1, ?_⟩
    intro j hj
    apply hy j.1
    exact (mem_relativeSignature_iff langs target x j).1
      (hx.2.symm ▸ hj)
  · intro hy j hxj
    by_cases hj : j = target
    · simpa [hj] using hy.1
    · let other : OtherIndex target := ⟨j, hj⟩
      have hother :
          other ∈ relativeSignature langs target x :=
        (mem_relativeSignature_iff langs target x other).2 hxj
      have hotherB : other ∈ B := hx.2 ▸ hother
      exact hy.2 other hotherB

/-! ## Infinite signatures and their minimal antichain -/

/-- All relative signatures with infinite exact region. -/
noncomputable def infiniteRelativeSignatures
    {n : ℕ} (langs : Fin (n + 1) → Set ℕ)
    (target : Fin (n + 1)) :
    Finset (Finset (OtherIndex target)) := by
  classical
  exact (Finset.univ.powerset).filter fun B =>
    (relativeRegion langs target B).Infinite

@[simp] theorem mem_infiniteRelativeSignatures_iff
    {n : ℕ} (langs : Fin (n + 1) → Set ℕ)
    (target : Fin (n + 1))
    (B : Finset (OtherIndex target)) :
    B ∈ infiniteRelativeSignatures langs target ↔
      (relativeRegion langs target B).Infinite := by
  classical
  simp [infiniteRelativeSignatures]

/-- Inclusion-minimal signatures with infinite exact region. -/
noncomputable def minimalInfiniteSignatures
    {n : ℕ} (langs : Fin (n + 1) → Set ℕ)
    (target : Fin (n + 1)) :
    Finset (Finset (OtherIndex target)) := by
  classical
  exact (infiniteRelativeSignatures langs target).filter fun B =>
    Minimal (· ∈ infiniteRelativeSignatures langs target) B

theorem mem_minimalInfiniteSignatures_iff
    {n : ℕ} (langs : Fin (n + 1) → Set ℕ)
    (target : Fin (n + 1))
    (B : Finset (OtherIndex target)) :
    B ∈ minimalInfiniteSignatures langs target ↔
      Minimal (· ∈ infiniteRelativeSignatures langs target) B := by
  classical
  simp only [minimalInfiniteSignatures, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨h.1, h⟩

theorem minimalInfiniteRegion_infinite
    {n : ℕ} (langs : Fin (n + 1) → Set ℕ)
    (target : Fin (n + 1))
    {B : Finset (OtherIndex target)}
    (hB : B ∈ minimalInfiniteSignatures langs target) :
    (relativeRegion langs target B).Infinite := by
  rw [mem_minimalInfiniteSignatures_iff] at hB
  exact (mem_infiniteRelativeSignatures_iff langs target B).1 hB.1

theorem minimalInfiniteSignatures_antichain
    {n : ℕ} (langs : Fin (n + 1) → Set ℕ)
    (target : Fin (n + 1)) :
    IsAntichain (· ⊆ ·)
      (minimalInfiniteSignatures langs target : Set
        (Finset (OtherIndex target))) := by
  intro A hA B hB hne hAB
  change A ∈ minimalInfiniteSignatures langs target at hA
  change B ∈ minimalInfiniteSignatures langs target at hB
  rw [mem_minimalInfiniteSignatures_iff] at hA hB
  apply hne
  exact Finset.Subset.antisymm hAB (hB.2 hA.1 hAB)

theorem minimalInfiniteSignatures_card_le
    {n : ℕ} (langs : Fin (n + 1) → Set ℕ)
    (target : Fin (n + 1)) :
    (minimalInfiniteSignatures langs target).card ≤
      Nat.choose n (n / 2) := by
  have h :=
    (minimalInfiniteSignatures_antichain langs target).sperner
  simpa [otherIndex_card] using h

/-- Every infinite relative signature contains an inclusion-minimal infinite
signature. -/
theorem exists_minimalInfiniteSignature_subset
    {n : ℕ} (langs : Fin (n + 1) → Set ℕ)
    (target : Fin (n + 1))
    {C : Finset (OtherIndex target)}
    (hC : (relativeRegion langs target C).Infinite) :
    ∃ B ∈ minimalInfiniteSignatures langs target, B ⊆ C := by
  classical
  let candidates :=
    (infiniteRelativeSignatures langs target).filter fun B => B ⊆ C
  have hCmem : C ∈ candidates := by
    simp [candidates, hC]
  obtain ⟨B, hBminimal⟩ :=
    candidates.exists_minimal ⟨C, hCmem⟩
  have hBinf :
      B ∈ infiniteRelativeSignatures langs target :=
    (Finset.mem_filter.mp hBminimal.1).1
  have hBC : B ⊆ C :=
    (Finset.mem_filter.mp hBminimal.1).2
  have hBglobal :
      Minimal (· ∈ infiniteRelativeSignatures langs target) B := by
    refine ⟨hBinf, ?_⟩
    intro D hDinf hDB
    have hDC : D ⊆ C := hDB.trans hBC
    exact hBminimal.2
      (Finset.mem_filter.mpr ⟨hDinf, hDC⟩) hDB
  exact
    ⟨B,
      (mem_minimalInfiniteSignatures_iff langs target B).2 hBglobal,
      hBC⟩

/-! ## Ordered upper-density calculus -/

theorem orderedPrefixCount_union_le
    (K : OrderedLanguage) (A B : Set ℕ) (n : ℕ) :
    K.prefixCount (A ∪ B) n ≤
      K.prefixCount A n + K.prefixCount B n := by
  classical
  unfold OrderedLanguage.prefixCount
  let left :=
    (Finset.range n).filter fun i => K.enumeration i ∈ A
  let right :=
    (Finset.range n).filter fun i => K.enumeration i ∈ B
  have hsubset :
      (Finset.range n).filter
          (fun i => K.enumeration i ∈ A ∪ B) ⊆
        left ∪ right := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range,
      Set.mem_union] at hi
    rcases hi.2 with hiA | hiB
    · exact Finset.mem_union_left _ (by
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr hi.1, hiA⟩)
    · exact Finset.mem_union_right _ (by
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr hi.1, hiB⟩)
  simpa [left, right] using
    (Finset.card_le_card hsubset).trans
      (Finset.card_union_le left right)

theorem orderedPrefixRatio_union_le
    (K : OrderedLanguage) (A B : Set ℕ) (n : ℕ) :
    K.prefixRatio (A ∪ B) n ≤
      K.prefixRatio A n + K.prefixRatio B n := by
  by_cases hn : n = 0
  · simp [hn]
  · simp only [OrderedLanguage.prefixRatio, hn, if_false]
    rw [← add_div]
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast orderedPrefixCount_union_le K A B n)
      (Nat.cast_nonneg n)

theorem orderedUpperDensity_union_le
    (K : OrderedLanguage) (A B : Set ℕ) :
    K.upperDensity (A ∪ B) ≤
      K.upperDensity A + K.upperDensity B := by
  unfold OrderedLanguage.upperDensity
  have hpoint :
      limsup (K.prefixRatio (A ∪ B)) atTop ≤
        limsup
          (fun n => K.prefixRatio A n + K.prefixRatio B n)
          atTop := by
    apply Filter.limsup_le_limsup
    · exact Filter.Eventually.of_forall
        (orderedPrefixRatio_union_le K A B)
    · exact isCoboundedUnder_le_of_le atTop
        (fun n => K.prefixRatio_nonneg (A ∪ B) n)
    · exact isBoundedUnder_of
        ⟨2, fun n => by
          linarith [K.prefixRatio_le_one A n,
            K.prefixRatio_le_one B n]⟩
  apply hpoint.trans
  apply limsup_add_le
  · exact isBoundedUnder_of
      ⟨0, fun n => K.prefixRatio_nonneg A n⟩
  · exact isBoundedUnder_of
      ⟨1, fun n => K.prefixRatio_le_one A n⟩
  · exact isCoboundedUnder_le_of_le atTop
      (fun n => K.prefixRatio_nonneg B n)
  · exact isBoundedUnder_of
      ⟨1, fun n => K.prefixRatio_le_one B n⟩

/-- Union of a finite indexed family. -/
def indexedUnion {ι : Type*}
    (S : Finset ι) (sets : ι → Set ℕ) : Set ℕ :=
  ⋃ i ∈ S, sets i

@[simp] theorem indexedUnion_empty
    {ι : Type*} (sets : ι → Set ℕ) :
    indexedUnion ∅ sets = ∅ := by
  simp [indexedUnion]

theorem indexedUnion_insert
    {ι : Type*} [DecidableEq ι]
    (sets : ι → Set ℕ) {a : ι} {S : Finset ι} :
    indexedUnion (insert a S) sets =
      sets a ∪ indexedUnion S sets := by
  ext x
  simp [indexedUnion]

theorem indexedUnion_finite
    {ι : Type*} [DecidableEq ι]
    (sets : ι → Set ℕ) (S : Finset ι)
    (hfinite : ∀ i ∈ S, (sets i).Finite) :
    (indexedUnion S sets).Finite := by
  have hlarge :
      (⋃ i : S, sets i.1).Finite :=
    Set.finite_iUnion fun i : S => hfinite i.1 i.2
  apply hlarge.subset
  intro x hx
  simp only [indexedUnion, Set.mem_iUnion] at hx ⊢
  obtain ⟨i, hiS, hxi⟩ := hx
  exact ⟨⟨i, hiS⟩, hxi⟩

theorem orderedUpperDensity_indexedUnion_le_sum
    {ι : Type*} [DecidableEq ι]
    (K : OrderedLanguage) (sets : ι → Set ℕ)
    (S : Finset ι) :
    K.upperDensity (indexedUnion S sets) ≤
      ∑ i ∈ S, K.upperDensity (sets i) := by
  induction S using Finset.induction_on with
  | empty =>
      rw [show indexedUnion (∅ : Finset ι) sets = ∅ by
        ext x
        simp [indexedUnion]]
      unfold OrderedLanguage.upperDensity
      rw [show K.prefixRatio (∅ : Set ℕ) = fun _ => 0 by
        funext n
        exact K.prefixRatio_empty n]
      simp
  | @insert a S ha ih =>
      rw [indexedUnion_insert sets, Finset.sum_insert ha]
      exact (orderedUpperDensity_union_le K (sets a)
        (indexedUnion S sets)).trans
        (add_le_add_left ih _)

theorem orderedUpperDensity_finite_eq_zero
    (K : OrderedLanguage) {A : Set ℕ} (hA : A.Finite) :
    K.upperDensity A = 0 := by
  classical
  let c := hA.toFinset.card
  have hcount (n : ℕ) : K.prefixCount A n ≤ c := by
    unfold OrderedLanguage.prefixCount
    let values :=
      ((Finset.range n).filter
        fun i => K.enumeration i ∈ A).image K.enumeration
    have hcard :
        values.card =
          ((Finset.range n).filter
            fun i => K.enumeration i ∈ A).card := by
      dsimp [values]
      rw [Finset.card_image_iff.mpr]
      intro i _ j _ hij
      exact K.enumeration_injective hij
    rw [← hcard]
    apply Finset.card_le_card
    intro x hx
    simp only [values, Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact hA.mem_toFinset.mpr (Finset.mem_filter.mp hi).2
  have hratio (n : ℕ) :
      K.prefixRatio A n ≤ (c : ℝ) / n := by
    by_cases hn : n = 0
    · simp [hn]
    · rw [OrderedLanguage.prefixRatio, if_neg hn]
      exact div_le_div_of_nonneg_right
        (by exact_mod_cast hcount n) (Nat.cast_nonneg n)
  have hbound :
      Tendsto (fun n : ℕ => (c : ℝ) / (n : ℝ))
        atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hratioTendsto :
      Tendsto (K.prefixRatio A) atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall
        (fun n => K.prefixRatio_nonneg A n)
    · exact Filter.Eventually.of_forall hratio
    · exact hbound
  exact hratioTendsto.limsup_eq

/-! ## Covering the target by minimal upward intersections -/

/-- The finite union of all finite exact relative regions. -/
noncomputable def finiteRelativeRegionEnvelope
    {n : ℕ} (langs : Fin (n + 1) → Set ℕ)
    (target : Fin (n + 1)) : Set ℕ := by
  classical
  exact indexedUnion
    ((Finset.univ.powerset).filter fun B =>
      (relativeRegion langs target B).Finite)
    (relativeRegion langs target)

theorem finiteRelativeRegionEnvelope_finite
    {n : ℕ} (langs : Fin (n + 1) → Set ℕ)
    (target : Fin (n + 1)) :
    (finiteRelativeRegionEnvelope langs target).Finite := by
  classical
  unfold finiteRelativeRegionEnvelope
  apply indexedUnion_finite
  intro B hB
  exact (Finset.mem_filter.mp hB).2

/-- Union of the upward cores selected by the minimal infinite signatures. -/
noncomputable def minimalInfiniteCoreUnion
    {n : ℕ} (langs : Fin (n + 1) → Set ℕ)
    (target : Fin (n + 1)) : Set ℕ :=
  indexedUnion (minimalInfiniteSignatures langs target)
    (relativeCore langs target)

theorem target_subset_finiteEnvelope_union_minimalCores
    {n : ℕ} (langs : Fin (n + 1) → Set ℕ)
    (target : Fin (n + 1)) :
    langs target ⊆
      finiteRelativeRegionEnvelope langs target ∪
        minimalInfiniteCoreUnion langs target := by
  classical
  intro x hx
  let C := relativeSignature langs target x
  by_cases hCfinite : (relativeRegion langs target C).Finite
  · apply Or.inl
    unfold finiteRelativeRegionEnvelope indexedUnion
    apply Set.mem_iUnion.mpr
    refine ⟨C, Set.mem_iUnion.mpr ?_⟩
    exact ⟨by simp [hCfinite], ⟨hx, rfl⟩⟩
  · have hCinfinite :
        (relativeRegion langs target C).Infinite :=
      hCfinite
    obtain ⟨B, hBminimal, hBC⟩ :=
      exists_minimalInfiniteSignature_subset
        langs target hCinfinite
    apply Or.inr
    unfold minimalInfiniteCoreUnion indexedUnion
    apply Set.mem_iUnion.mpr
    refine ⟨B, Set.mem_iUnion.mpr ?_⟩
    refine ⟨hBminimal, ?_⟩
    exact (mem_relativeCore_iff_signature_superset
      langs target B x).2 ⟨hx, hBC⟩

theorem minimalInfiniteCoreUnion_upperDensity_eq_one
    {n : ℕ} (langs : Fin (n + 1) → Set ℕ)
    (target : Fin (n + 1))
    (K : OrderedLanguage)
    (hK : K.carrier = langs target) :
    K.upperDensity (minimalInfiniteCoreUnion langs target) = 1 := by
  have htarget :
      K.upperDensity K.carrier = 1 := by
    have htendsto :
        Tendsto (K.prefixRatio K.carrier) atTop (𝓝 1) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ne_atTop 0] with n hn
      simp [OrderedLanguage.prefixRatio_carrier, hn]
    exact htendsto.limsup_eq
  have hcover :
      K.carrier ⊆
        finiteRelativeRegionEnvelope langs target ∪
          minimalInfiniteCoreUnion langs target := by
    rw [hK]
    exact target_subset_finiteEnvelope_union_minimalCores langs target
  have hfiniteZero :
      K.upperDensity (finiteRelativeRegionEnvelope langs target) = 0 :=
    orderedUpperDensity_finite_eq_zero K
      (finiteRelativeRegionEnvelope_finite langs target)
  have honeLe :
      1 ≤ K.upperDensity
        (minimalInfiniteCoreUnion langs target) := by
    calc
      1 = K.upperDensity K.carrier := htarget.symm
      _ ≤ K.upperDensity
          (finiteRelativeRegionEnvelope langs target ∪
            minimalInfiniteCoreUnion langs target) :=
        orderedUpperDensity_mono K hcover
      _ ≤ K.upperDensity
            (finiteRelativeRegionEnvelope langs target) +
          K.upperDensity
            (minimalInfiniteCoreUnion langs target) :=
        orderedUpperDensity_union_le K _ _
      _ = K.upperDensity
          (minimalInfiniteCoreUnion langs target) := by
        rw [hfiniteZero, zero_add]
  exact le_antisymm
    (orderedUpperDensity_le_one K
      (minimalInfiniteCoreUnion langs target))
    honeLe

theorem exists_minimalInfiniteCore_large_density
    {n : ℕ}
    (langs : Fin (n + 1) → Set ℕ)
    (target : Fin (n + 1))
    (K : OrderedLanguage)
    (hK : K.carrier = langs target) :
    ∃ B ∈ minimalInfiniteSignatures langs target,
      1 / (Nat.choose n (n / 2) : ℝ) ≤
        K.upperDensity (relativeCore langs target B) := by
  classical
  let M := minimalInfiniteSignatures langs target
  let density :=
    fun B : Finset (OtherIndex target) =>
      K.upperDensity (relativeCore langs target B)
  have hUnion :
      K.upperDensity (minimalInfiniteCoreUnion langs target) ≤
        ∑ B ∈ M, density B := by
    exact orderedUpperDensity_indexedUnion_le_sum
      K (relativeCore langs target) M
  have hsumOne : 1 ≤ ∑ B ∈ M, density B := by
    rw [minimalInfiniteCoreUnion_upperDensity_eq_one
      langs target K hK] at hUnion
    exact hUnion
  have hMnonempty : M.Nonempty := by
    by_contra hM
    have : M = ∅ := Finset.not_nonempty_iff_eq_empty.mp hM
    norm_num [this] at hsumOne
  have hNpos : 0 < Nat.choose n (n / 2) :=
    middleWidth_pos n
  by_contra hnot
  push_neg at hnot
  have hsumLt :
      (∑ B ∈ M, density B) <
        ∑ B ∈ M, (1 / (Nat.choose n (n / 2) : ℝ)) := by
    apply Finset.sum_lt_sum_of_nonempty hMnonempty
    intro B hBM
    exact hnot B hBM
  have hcard :
      M.card ≤ Nat.choose n (n / 2) :=
    minimalInfiniteSignatures_card_le langs target
  have hcardBound :
      (∑ B ∈ M, (1 / (Nat.choose n (n / 2) : ℝ))) ≤ 1 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcast : (M.card : ℝ) ≤ Nat.choose n (n / 2) := by
      exact_mod_cast hcard
    have hNreal : (0 : ℝ) < Nat.choose n (n / 2) := by
      exact_mod_cast hNpos
    calc
      (M.card : ℝ) * (1 / (Nat.choose n (n / 2) : ℝ)) ≤
          (Nat.choose n (n / 2) : ℝ) *
            (1 / (Nat.choose n (n / 2) : ℝ)) :=
        mul_le_mul_of_nonneg_right hcast (by positivity)
      _ = 1 := by field_simp
  linarith

/-! ## Infinite recurrence and the canonical output -/

theorem frequently_mem_infinite_subset_of_presents
    {stream : ℕ → ℕ} {K A : Set ℕ}
    (hP : GenLimit.Generic.Presents stream K)
    (hA : A.Infinite) (hAK : A ⊆ K) :
    ∃ᶠ t : ℕ in atTop, stream t ∈ A := by
  rw [Filter.frequently_atTop]
  intro cutoff
  let prefixValues := (Finset.range cutoff).image stream
  obtain ⟨x, hxA, hxPrefix⟩ :=
    hA.exists_notMem_finset prefixValues
  have hxK := hAK hxA
  rw [← hP] at hxK
  obtain ⟨t, ht⟩ := hxK
  have htCutoff : cutoff ≤ t := by
    by_contra hlt
    apply hxPrefix
    apply Finset.mem_image.mpr
    exact ⟨t, Finset.mem_range.mpr (Nat.lt_of_not_ge hlt), ht⟩
  exact ⟨t, htCutoff, ht ▸ hxA⟩

theorem canonicalDensityGenerator_eq_relativeCore
    {n : ℕ} (langs : Fin (n + 1) → Set ℕ)
    (target : Fin (n + 1))
    {B : Finset (OtherIndex target)} {x : ℕ}
    (hx : x ∈ relativeRegion langs target B)
    (hCore : (relativeCore langs target B).Infinite) :
    canonicalDensityGenerator langs x =
      relativeCore langs target B := by
  have hEq :=
    finiteFamilyCore_eq_relativeCore langs target hx
  simp [canonicalDensityGenerator, hEq, hCore]

/-- The positive-density half of Lemma 4.8 for the canonical generator. -/
theorem canonicalDensityGenerator_frequently_sperner_dense
    {n : ℕ}
    (langs : Fin (n + 1) → Set ℕ)
    (target : Fin (n + 1))
    (K : OrderedLanguage)
    (hK : K.carrier = langs target)
    (stream : ℕ → ℕ)
    (hP : GenLimit.Generic.Presents stream K.carrier) :
    ∃ᶠ t : ℕ in atTop,
      1 / (Nat.choose n (n / 2) : ℝ) ≤
        K.upperDensity
          (canonicalDensityGenerator langs (stream t)) := by
  obtain ⟨B, hBminimal, hBdense⟩ :=
    exists_minimalInfiniteCore_large_density
      langs target K hK
  have hBregion :
      (relativeRegion langs target B).Infinite :=
    minimalInfiniteRegion_infinite langs target hBminimal
  have hNpos : (0 : ℝ) <
      1 / (Nat.choose n (n / 2) : ℝ) := by
    apply one_div_pos.mpr
    exact_mod_cast middleWidth_pos n
  have hBcore :
      (relativeCore langs target B).Infinite := by
    by_contra hnot
    have hfinite :
        (relativeCore langs target B).Finite :=
      Set.not_infinite.mp hnot
    have hdensityZero :=
      orderedUpperDensity_finite_eq_zero K hfinite
    rw [hdensityZero] at hBdense
    linarith
  have hfrequent :
      ∃ᶠ t : ℕ in atTop,
        stream t ∈ relativeRegion langs target B := by
    apply frequently_mem_infinite_subset_of_presents
      hP hBregion
    intro x hx
    rw [hK]
    exact hx.1
  exact hfrequent.mono fun t ht => by
    rw [canonicalDensityGenerator_eq_relativeCore
      langs target ht hBcore]
    exact hBdense

/-- Lemma 4.8: the canonical memoryless intersection generator both
generates every member of a finite family under finitely repeating
enumerations and achieves the exact reciprocal-Sperner upper-density bound
infinitely often on every target. -/
theorem lemma_4_8_sperner_achievability
    {n : ℕ} (_hn : 1 ≤ n)
    (langs : Fin (n + 1) → Set ℕ)
    (_hInfinite : ∀ i, (langs i).Infinite) :
    ∃ G : MemorylessSetGenerator ℕ,
      IsFinitelyRepeatingMemorylessGenerator G (Set.range langs) ∧
      ∀ (target : Fin (n + 1)) (K : OrderedLanguage),
        K.carrier = langs target →
        ∀ stream : ℕ → ℕ,
          GenLimit.Generic.Presents stream K.carrier →
          FinitelyRepeating stream →
          ∃ᶠ t : ℕ in atTop,
            1 / (Nat.choose n (n / 2) : ℝ) ≤
              K.upperDensity (G (stream t)) := by
  refine
    ⟨canonicalDensityGenerator langs,
      canonicalDensityGenerator_succeeds langs, ?_⟩
  intro target K hK stream hP _hRepeat
  exact canonicalDensityGenerator_frequently_sperner_dense
    langs target K hK stream hP

end GenLimit.BoundedMemory
