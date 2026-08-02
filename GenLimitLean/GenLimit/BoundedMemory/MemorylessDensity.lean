import GenLimit.BoundedMemory.OutputSeparations
import GenLimit.Core.OrderedDensity
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Set.Finite.Range

/-!
# Density bounds for memoryless generators

Source: Jon Kleinberg, Anay Mehrotra, Amin Saberi, and Grigoris Velegkas,
*On Language Generation in the Limit with Bounded Memory*,
arXiv:2605.30324v1, Section 4.1.

This module formalizes the exact ordered upper/lower-density operators used
by the paper, their monotonicity, Lemma 4.3's finite-error partition bound,
and the complete validity part of the canonical intersection generator in
Lemma 4.8.  The later Sperner/symmetric-chain density calculation is kept
separate: nothing here packages that external combinatorial theorem as an
assumption or silently replaces the analytic density conclusion.
-/

namespace GenLimit.BoundedMemory

open Filter
open GenLimit.KleinbergWei

/-! ## Ordered-density monotonicity -/

theorem orderedPrefixCount_mono
    (K : OrderedLanguage) {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    K.prefixCount A n ≤ K.prefixCount B n := by
  classical
  unfold OrderedLanguage.prefixCount
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, hAB hi.2⟩

theorem orderedPrefixRatio_mono
    (K : OrderedLanguage) {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    K.prefixRatio A n ≤ K.prefixRatio B n := by
  by_cases hn : n = 0
  · simp [hn]
  · simp only [OrderedLanguage.prefixRatio, hn, if_false]
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast orderedPrefixCount_mono K hAB n)
      (Nat.cast_nonneg n)

/-- Monotonicity of the literal lower-density operator in Definition 8. -/
theorem orderedLowerDensity_mono
    (K : OrderedLanguage) {A B : Set ℕ} (hAB : A ⊆ B) :
    K.lowerDensity A ≤ K.lowerDensity B := by
  unfold OrderedLanguage.lowerDensity
  apply Filter.liminf_le_liminf
  · exact Filter.Eventually.of_forall
      (orderedPrefixRatio_mono K hAB)
  · exact isBoundedUnder_of
      ⟨0, fun n => K.prefixRatio_nonneg A n⟩
  · exact isCoboundedUnder_ge_of_le atTop
      (fun n => K.prefixRatio_le_one B n)

/-- Monotonicity of the literal upper-density operator in Definition 8. -/
theorem orderedUpperDensity_mono
    (K : OrderedLanguage) {A B : Set ℕ} (hAB : A ⊆ B) :
    K.upperDensity A ≤ K.upperDensity B := by
  unfold OrderedLanguage.upperDensity
  apply Filter.limsup_le_limsup
  · exact Filter.Eventually.of_forall
      (orderedPrefixRatio_mono K hAB)
  · exact isCoboundedUnder_le_of_le atTop
      (fun n => K.prefixRatio_nonneg A n)
  · exact isBoundedUnder_of
      ⟨1, fun n => K.prefixRatio_le_one B n⟩

/-! ## Finite exceptional sets -/

/-- Repetition-free version of the paper's memoryless success predicate. -/
def IsRepetitionFreeMemorylessGeneratorOn
    (G : MemorylessSetGenerator ℕ) (K : Set ℕ) : Prop :=
  ∀ stream : ℕ → ℕ,
    GenLimit.Generic.Presents stream K →
      Function.Injective stream →
        ∃ T, ∀ t, T ≤ t → ValidSetOutput G K (stream t)

/-- Inputs of `K` on which the memoryless output is not contained in `K`. -/
def densityBadInputs
    (G : MemorylessSetGenerator ℕ) (K : Set ℕ) : Set ℕ :=
  {x | x ∈ K ∧ ¬G x ⊆ K}

/-- The finite-error observation used in Lemmas 4.3, 4.7, and 4.8:
eventual success on every repetition-free enumeration forces the set of bad
inputs inside each target language to be finite. -/
theorem densityBadInputs_finite
    {G : MemorylessSetGenerator ℕ} {K : Set ℕ}
    (hK : K.Infinite)
    (hG : IsRepetitionFreeMemorylessGeneratorOn G K) :
    (densityBadInputs G K).Finite := by
  by_contra hnot
  have hBad : (densityBadInputs G K).Infinite :=
    hnot
  let stream := infiniteEnumeration K hK
  obtain ⟨T, hT⟩ :=
    hG stream (infiniteEnumeration_presents K hK)
      (infiniteEnumeration_injective K hK)
  let finitePrefix : Set ℕ := Set.range (fun s : Fin T => stream s)
  have hPrefix : finitePrefix.Finite := Set.finite_range _
  have hRemain : (densityBadInputs G K \ finitePrefix).Infinite :=
    hBad.diff hPrefix
  obtain ⟨x, hxBad, hxPrefix⟩ := hRemain.nonempty
  have hxK : x ∈ K := hxBad.1
  rw [← infiniteEnumeration_presents K hK] at hxK
  obtain ⟨t, ht⟩ := hxK
  have htT : T ≤ t := by
    by_contra hlt
    exact hxPrefix ⟨⟨t, Nat.lt_of_not_ge hlt⟩, ht⟩
  have hValid := hT t htT
  exact hxBad.2 (ht ▸ hValid.2)

/-! ## Lemma 4.3: partitions force a density bound -/

/-- A finite indexed partition of a target language. -/
def IsFinitePartition
    {m : ℕ} (pieces : Fin (m + 1) → Set ℕ) (K : Set ℕ) : Prop :=
  (∀ i j, i ≠ j → Disjoint (pieces i) (pieces j)) ∧
    (⋃ i, pieces i) = K

/-- The union of all per-piece exceptional inputs. -/
def partitionBadInputs
    {m : ℕ} (G : MemorylessSetGenerator ℕ)
    (pieces : Fin (m + 1) → Set ℕ) : Set ℕ :=
  ⋃ i, densityBadInputs G (pieces i)

theorem partitionBadInputs_finite
    {m : ℕ} {G : MemorylessSetGenerator ℕ}
    {pieces : Fin (m + 1) → Set ℕ}
    (hInfinite : ∀ i, (pieces i).Infinite)
    (hG : ∀ i, IsRepetitionFreeMemorylessGeneratorOn G (pieces i)) :
    (partitionBadInputs G pieces).Finite := by
  unfold partitionBadInputs
  exact Set.finite_iUnion fun i =>
    densityBadInputs_finite (hInfinite i) (hG i)

/-- Maximum lower density among the finitely many partition pieces. -/
noncomputable def maximumPartitionLowerDensity
    {m : ℕ} (K : OrderedLanguage)
    (pieces : Fin (m + 1) → Set ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun i => K.lowerDensity (pieces i))

theorem piece_lowerDensity_le_maximum
    {m : ℕ} (K : OrderedLanguage)
    (pieces : Fin (m + 1) → Set ℕ) (i : Fin (m + 1)) :
    K.lowerDensity (pieces i) ≤
      maximumPartitionLowerDensity K pieces := by
  exact Finset.le_sup'
    (fun j => K.lowerDensity (pieces j))
    (Finset.mem_univ i)

/-- Lemma 4.3, with the paper's actual `liminf` lower density.

After a finite exceptional time, every output is contained in the unique
partition piece containing the current example and hence has lower density
at most the maximum lower density of a piece.  Uniqueness is not needed for
the inequality, so the proof consumes only coverage, although the literal
partition predicate retains pairwise disjointness. -/
theorem lemma_4_3_lower_density_bound_from_partition
    {m : ℕ} (K : OrderedLanguage)
    (pieces : Fin (m + 1) → Set ℕ)
    (hPartition : IsFinitePartition pieces K.carrier)
    (hInfinite : ∀ i, (pieces i).Infinite)
    (G : MemorylessSetGenerator ℕ)
    (hG : ∀ i, IsRepetitionFreeMemorylessGeneratorOn G (pieces i))
    (stream : ℕ → ℕ)
    (hP : GenLimit.Generic.Presents stream K.carrier)
    (hInjective : Function.Injective stream) :
    ∃ T, ∀ t, T ≤ t →
      K.lowerDensity (G (stream t)) ≤
        maximumPartitionLowerDensity K pieces := by
  have hBadFinite :=
    partitionBadInputs_finite hInfinite hG
  obtain ⟨T, hAvoid⟩ :=
    finitelyRepeating_avoids_finite_set
      (injective_finitelyRepeating hInjective) hBadFinite
  refine ⟨T, ?_⟩
  intro t ht
  have hxtK : stream t ∈ K.carrier := by
    rw [← hP]
    exact ⟨t, rfl⟩
  have hxtUnion : stream t ∈ ⋃ i, pieces i := by
    rw [hPartition.2]
    exact hxtK
  simp only [Set.mem_iUnion] at hxtUnion
  obtain ⟨i, hxi⟩ := hxtUnion
  have hSubset : G (stream t) ⊆ pieces i := by
    by_contra hnot
    have hbad :
        stream t ∈ partitionBadInputs G pieces := by
      apply Set.mem_iUnion.mpr
      exact ⟨i, hxi, hnot⟩
    exact hAvoid t ht hbad
  exact (orderedLowerDensity_mono K hSubset).trans
    (piece_lowerDensity_le_maximum K pieces i)

/-! ## Canonical finite-family intersection generator (Lemma 4.8) -/

/-- Signature of the current example with respect to a finite family. -/
noncomputable def finiteFamilySignature
    {m : ℕ} (langs : Fin (m + 1) → Set ℕ) (x : ℕ) :
    Finset (Fin (m + 1)) := by
  classical
  exact Finset.univ.filter fun i => x ∈ langs i

/-- Intersection of a finite subfamily. -/
def finiteFamilyIntersection
    {m : ℕ} (langs : Fin (m + 1) → Set ℕ)
    (signature : Finset (Fin (m + 1))) : Set ℕ :=
  {y | ∀ i, i ∈ signature → y ∈ langs i}

/-- `I_x`, the intersection of every family member containing `x`. -/
def finiteFamilyCore
    {m : ℕ} (langs : Fin (m + 1) → Set ℕ) (x : ℕ) : Set ℕ :=
  {y | ∀ i, x ∈ langs i → y ∈ langs i}

theorem finiteFamilyCore_eq_intersection
    {m : ℕ} (langs : Fin (m + 1) → Set ℕ) (x : ℕ) :
    finiteFamilyCore langs x =
      finiteFamilyIntersection langs (finiteFamilySignature langs x) := by
  classical
  ext y
  simp [finiteFamilyCore, finiteFamilyIntersection, finiteFamilySignature]

theorem mem_finiteFamilyCore
    {m : ℕ} (langs : Fin (m + 1) → Set ℕ) (x : ℕ) :
    x ∈ finiteFamilyCore langs x := by
  intro i hxi
  exact hxi

theorem finiteFamilyCore_subset
    {m : ℕ} {langs : Fin (m + 1) → Set ℕ}
    {i : Fin (m + 1)} {x : ℕ} (hxi : x ∈ langs i) :
    finiteFamilyCore langs x ⊆ langs i := by
  intro y hy
  exact hy i hxi

/-- The modified canonical intersection generator from Lemma 4.8. -/
noncomputable def canonicalDensityGenerator
    {m : ℕ} (langs : Fin (m + 1) → Set ℕ) :
    MemorylessSetGenerator ℕ := by
  classical
  exact fun x =>
    if (finiteFamilyCore langs x).Infinite then
      finiteFamilyCore langs x
    else
      Set.univ

theorem canonicalDensityGenerator_infinite
    {m : ℕ} (langs : Fin (m + 1) → Set ℕ) (x : ℕ) :
    (canonicalDensityGenerator langs x).Infinite := by
  classical
  unfold canonicalDensityGenerator
  split_ifs with h
  · exact h
  · exact Set.infinite_univ

/-- One finite piece in the source's union over signatures with finite
intersection. -/
noncomputable def finiteSignaturePiece
    {m : ℕ} (langs : Fin (m + 1) → Set ℕ)
    (signature : Finset (Fin (m + 1))) : Set ℕ := by
  classical
  exact if (finiteFamilyIntersection langs signature).Finite then
    finiteFamilyIntersection langs signature
  else
    ∅

theorem finiteSignaturePiece_finite
    {m : ℕ} (langs : Fin (m + 1) → Set ℕ)
    (signature : Finset (Fin (m + 1))) :
    (finiteSignaturePiece langs signature).Finite := by
  classical
  unfold finiteSignaturePiece
  split_ifs with h
  · exact h
  · exact Set.finite_empty

/-- Global set of inputs whose consistent-family intersection is finite. -/
def finiteCoreInputs
    {m : ℕ} (langs : Fin (m + 1) → Set ℕ) : Set ℕ :=
  {x | (finiteFamilyCore langs x).Finite}

theorem finiteCoreInputs_finite
    {m : ℕ} (langs : Fin (m + 1) → Set ℕ) :
    (finiteCoreInputs langs).Finite := by
  classical
  let envelope : Set ℕ :=
    ⋃ signature : Finset (Fin (m + 1)),
      finiteSignaturePiece langs signature
  have hEnvelope : envelope.Finite :=
    Set.finite_iUnion fun signature =>
      finiteSignaturePiece_finite langs signature
  apply hEnvelope.subset
  intro x hx
  apply Set.mem_iUnion.mpr
  refine ⟨finiteFamilySignature langs x, ?_⟩
  have hIntersection :
      (finiteFamilyIntersection langs
        (finiteFamilySignature langs x)).Finite := by
    rw [← finiteFamilyCore_eq_intersection langs x]
    exact hx
  simp only [finiteSignaturePiece, if_pos hIntersection]
  rw [← finiteFamilyCore_eq_intersection langs x]
  exact mem_finiteFamilyCore langs x

/-- The canonical generator is valid for every member of the finite family
under every finitely repeating exact presentation.  This is the full
generation-in-the-limit part of Lemma 4.8. -/
theorem canonicalDensityGenerator_succeeds
    {m : ℕ} (langs : Fin (m + 1) → Set ℕ) :
    IsFinitelyRepeatingMemorylessGenerator
      (canonicalDensityGenerator langs) (Set.range langs) := by
  classical
  intro K hK stream hP hRepeat
  obtain ⟨i, rfl⟩ := hK
  obtain ⟨T, hAvoid⟩ :=
    finitelyRepeating_avoids_finite_set hRepeat
      (finiteCoreInputs_finite langs)
  refine ⟨T, ?_⟩
  intro t ht
  have hxt : stream t ∈ langs i := by
    rw [← hP]
    exact ⟨t, rfl⟩
  have hCoreInfinite :
      (finiteFamilyCore langs (stream t)).Infinite := by
    by_contra hnot
    exact hAvoid t ht (Set.not_infinite.mp hnot)
  have hOutput :
      canonicalDensityGenerator langs (stream t) =
        finiteFamilyCore langs (stream t) := by
    simp [canonicalDensityGenerator, hCoreInfinite]
  change
    (canonicalDensityGenerator langs (stream t)).Infinite ∧
      canonicalDensityGenerator langs (stream t) ⊆ langs i
  rw [hOutput]
  exact ⟨hCoreInfinite, finiteFamilyCore_subset hxt⟩

end GenLimit.BoundedMemory
