import GenLimit.Paper17_InfiniteContamination.FiniteExpansionTransfer
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationNecessity
import GenLimit.Paper17_InfiniteContamination.NoiselessSetDensity
import Mathlib.Combinatorics.Colex

/-!
# Finite-contamination lower-density sufficiency

Source: Mehrotra--Velegkas--Yu--Zhou,
*Language Generation with Infinite Contamination*,
arXiv:2511.07417v1, Lemma 6.9 and the sufficiency direction of Theorem 6.5.

This file completes the source reduction rather than postulating an expanded
family.  Natural numbers encode triples consisting of a base-language index,
a finite set to add, and a finite set to remove.  The resulting indexed
family contains every finite expansion.  Lemma 6.8 runs on that family;
`FiniteExpansionTransfer` then transfers correctness back to the base target.
Density is measured in the original target's canonical order, so only finite
perturbations of the measured output set are needed.
-/

namespace GenLimit.InfiniteContamination

open GenLimit.KleinbergWei

/-- Code data for one member of Algorithm 2's expanded collection. -/
abbrev FiniteExpansionCode := ℕ × ℕ × ℕ

/-- Decode a natural number as finite-expansion data, with a harmless default
on codes outside the range of the standard `Encodable` instance. -/
def finiteExpansionCode (n : ℕ) : FiniteExpansionCode :=
  let outer := Nat.unpair n
  let inner := Nat.unpair outer.2
  (outer.1, inner.1, inner.2)

/-- Explicit inverse code for finite-expansion data. -/
def encodeFiniteExpansionCode (data : FiniteExpansionCode) : ℕ :=
  Nat.pair data.1 (Nat.pair data.2.1 data.2.2)

@[simp] theorem finiteExpansionCode_encode
    (data : FiniteExpansionCode) :
    finiteExpansionCode (encodeFiniteExpansionCode data) = data := by
  simp [finiteExpansionCode, encodeFiniteExpansionCode, Nat.unpair_pair]

/-- Base-language index carried by an expansion code. -/
def finiteExpansionBaseIndex (n : ℕ) : ℕ :=
  (finiteExpansionCode n).1

/-- The explicitly enumerated finite-expansion family from Algorithm 2. -/
noncomputable def finiteExpansionLanguage
    (O : GenLimit.OracleFamily) (n : ℕ) : Set ℕ :=
  let data := finiteExpansionCode n
  finiteExpansion (O.language data.1)
    (Finset.equivBitIndices data.2.1 : Set ℕ)
    (Finset.equivBitIndices data.2.2 : Set ℕ)

theorem finiteExpansionLanguage_infinite
    (O : GenLimit.OracleFamily) (n : ℕ) :
    (finiteExpansionLanguage O n).Infinite := by
  let data := finiteExpansionCode n
  exact
    ((O.infinite' data.1).mono
      (Set.subset_union_left : O.language data.1 ⊆
        O.language data.1 ∪
          (Finset.equivBitIndices data.2.1 : Set ℕ))).diff
      (Finset.equivBitIndices data.2.2).finite_toSet

/-- Oracle-family packaging of the full finite-expansion enumeration. -/
noncomputable def finiteExpansionOracleFamily
    (O : GenLimit.OracleFamily) : GenLimit.OracleFamily where
  language := finiteExpansionLanguage O
  infinite' := finiteExpansionLanguage_infinite O
  query n x := by
    classical
    exact if x ∈ finiteExpansionLanguage O n then true else false
  query_spec n x := by
    classical
    simp

@[simp] theorem finiteExpansionOracleFamily_language
    (O : GenLimit.OracleFamily) (n : ℕ) :
    (finiteExpansionOracleFamily O).language n =
      finiteExpansionLanguage O n := rfl

/-- Finite expansions differ from their base language by only finitely many
points in either direction. -/
theorem finiteExpansion_symmetricDifference_finite
    (L : Set ℕ) (add remove : Finset ℕ) :
    ((finiteExpansion L (add : Set ℕ) (remove : Set ℕ) \ L).Finite ∧
      (L \ finiteExpansion L (add : Set ℕ) (remove : Set ℕ)).Finite) := by
  constructor
  · apply add.finite_toSet.subset
    intro x hx
    exact hx.1.1.resolve_left hx.2
  · apply remove.finite_toSet.subset
    intro x hx
    by_contra hxRemove
    exact hx.2 ⟨Or.inl hx.1, hxRemove⟩

/-- Every finite-contamination stream is an exact presentation of a coded
member of the expanded family, and that code remembers the original target
index. -/
theorem exists_finiteExpansion_index_for_stream
    (O : GenLimit.OracleFamily) {z : ℕ}
    {stream : GenLimit.Generic.Stream ℕ}
    (hcontam :
      FiniteNoiseFiniteOmissionEnumeration stream (O.language z)) :
    ∃ j,
      finiteExpansionBaseIndex j = z ∧
        GenLimit.Generic.Presents stream
          ((finiteExpansionOracleFamily O).language j) := by
  let addFinite := displayedNoise_finite hcontam.2.1
  let removeFinite := hcontam.2.2
  let data : FiniteExpansionCode :=
    (z, Finset.equivBitIndices.symm addFinite.toFinset,
      Finset.equivBitIndices.symm removeFinite.toFinset)
  let j := encodeFiniteExpansionCode data
  refine ⟨j, ?_, ?_⟩
  · simp [finiteExpansionBaseIndex, j, data]
  · change Set.range stream = finiteExpansionLanguage O j
    have hadd :
        (↑addFinite.toFinset : Set ℕ) =
          displayedNoise stream (O.language z) := by
      exact Set.Finite.coe_toFinset addFinite
    have hremove :
        (↑removeFinite.toFinset : Set ℕ) =
          displayedOmissions stream (O.language z) := by
      exact Set.Finite.coe_toFinset removeFinite
    rw [finiteExpansionLanguage]
    simp only [j, data, finiteExpansionCode_encode]
    simp only [Equiv.apply_symm_apply]
    rw [hadd, hremove]
    exact
      (finiteExpansion_displayedNoise_displayedOmissions
        stream (O.language z)).symm

/-- The original target order associated with a coded expansion. -/
noncomputable def finiteExpansionMeasure
    (orders : ℕ → OrderedLanguage) (j : ℕ) : OrderedLanguage :=
  orders (finiteExpansionBaseIndex j)

/-- Lemma 6.9's pairwise density inheritance for the explicitly enumerated
expanded collection. -/
theorem finiteExpansion_pair_lowerDensity
    (O : GenLimit.OracleFamily)
    (orders : ℕ → OrderedLanguage)
    (c : ℝ)
    (hpair :
      ∀ i j,
        (O.language i \ O.language j).Finite →
          c ≤ (orders j).lowerDensity (O.language i))
    (i j : ℕ)
    (hdiff :
      ((finiteExpansionOracleFamily O).language i \
        (finiteExpansionOracleFamily O).language j).Finite) :
    c ≤ (finiteExpansionMeasure orders j).lowerDensity
      ((finiteExpansionOracleFamily O).language i) := by
  let dataI := finiteExpansionCode i
  let dataJ := finiteExpansionCode j
  have hbaseDiff :
      (O.language dataI.1 \ O.language dataJ.1).Finite := by
    change
      (finiteExpansion
          (O.language dataI.1)
            (Finset.equivBitIndices dataI.2.1 : Set ℕ)
            (Finset.equivBitIndices dataI.2.2 : Set ℕ) \
        finiteExpansion
          (O.language dataJ.1)
            (Finset.equivBitIndices dataJ.2.1 : Set ℕ)
            (Finset.equivBitIndices dataJ.2.2 : Set ℕ)).Finite at hdiff
    exact finite_base_diff_of_finite_expansion_diff
      (Finset.equivBitIndices dataJ.2.1).finite_toSet
      (Finset.equivBitIndices dataI.2.2).finite_toSet hdiff
  have hbase :
      c ≤ (orders dataJ.1).lowerDensity (O.language dataI.1) :=
    hpair dataI.1 dataJ.1 hbaseDiff
  have hsymm :=
    finiteExpansion_symmetricDifference_finite
      (O.language dataI.1)
      (Finset.equivBitIndices dataI.2.1)
      (Finset.equivBitIndices dataI.2.2)
  have heq :
      (orders dataJ.1).lowerDensity
          (finiteExpansion
            (O.language dataI.1)
              (Finset.equivBitIndices dataI.2.1 : Set ℕ)
              (Finset.equivBitIndices dataI.2.2 : Set ℕ)) =
        (orders dataJ.1).lowerDensity (O.language dataI.1) :=
    (orders dataJ.1).lowerDensity_eq_of_finite_symmetricDifference
      hsymm.1 hsymm.2
  change c ≤ (orders dataJ.1).lowerDensity
    (finiteExpansion
      (O.language dataI.1)
        (Finset.equivBitIndices dataI.2.1 : Set ℕ)
        (Finset.equivBitIndices dataI.2.2 : Set ℕ))
  exact hbase.trans_eq heq.symm

/-- Lemma 6.9, including the concrete finite-expansion enumeration, the
noiseless positive-density subroutine, and correctness transfer back to the
original target. -/
theorem lemma_6_9_finiteContamination_sufficiency
    (O : GenLimit.OracleFamily)
    (orders : ℕ → OrderedLanguage)
    (hcarrier : ∀ i, (orders i).carrier = O.language i)
    (c : ℝ)
    (hpair :
      ∀ i j,
        (O.language i \ O.language j).Finite →
          c ≤ (orders j).lowerDensity (O.language i))
    {z : ℕ} {stream : GenLimit.Generic.Stream ℕ}
    (hcontam :
      FiniteNoiseFiniteOmissionEnumeration stream (O.language z)) :
    GeneratesInfiniteSetInLimitOn
        (noiselessDensityGenerator (finiteExpansionOracleFamily O))
        (orders z).carrier stream ∧
      c ≤ setBasedLowerDensity
        (noiselessDensityGenerator (finiteExpansionOracleFamily O))
        (orders z) stream := by
  obtain ⟨j, hjBase, hjPresents⟩ :=
    exists_finiteExpansion_index_for_stream O hcontam
  have hrun :=
    lemma_6_8_noiseless_setDensity_with_measure
      (finiteExpansionOracleFamily O)
      (finiteExpansionMeasure orders) c
      (finiteExpansion_pair_lowerDensity O orders c hpair)
      hjPresents hcontam.1
  constructor
  · rw [hcarrier z]
    apply lemma_4_3_infiniteSet_finiteExpansion_transfer hcontam
    rw [← hjPresents] at hrun
    exact hrun.1
  · simpa [finiteExpansionMeasure, hjBase] using hrun.2

/-- Sufficiency direction of Theorem 6.5 for an explicitly indexed countable
family.  One generator works simultaneously for every target and every
finite-noise, finite-omission enumeration. -/
theorem theorem_6_5_lowerDensity_sufficiency_enumerated
    (O : GenLimit.OracleFamily)
    (orders : ℕ → OrderedLanguage)
    (hcarrier : ∀ i, (orders i).carrier = O.language i)
    (c : ℝ)
    (hpair :
      ∀ i j,
        (O.language i \ O.language j).Finite →
          c ≤ (orders j).lowerDensity (O.language i)) :
    ∃ gen : SetGenerator ℕ,
      IsInfiniteSetGenerator gen ∧
        ∀ z,
          GeneratesSetUnderFiniteContaminationOn
              gen (orders z).carrier ∧
            GuaranteesSetBasedLowerDensityUnderFiniteContaminationOn
              gen (orders z) c := by
  let gen :=
    noiselessDensityGenerator (finiteExpansionOracleFamily O)
  refine ⟨gen, noiselessDensityGenerator_infinite _, ?_⟩
  intro z
  constructor
  · intro stream hcontam
    have hcontam' :
        FiniteNoiseFiniteOmissionEnumeration stream (O.language z) := by
      simpa [hcarrier z] using hcontam
    exact
      (lemma_6_9_finiteContamination_sufficiency
        O orders hcarrier c hpair hcontam').1.generatesSetInLimitOn
  · intro stream hcontam
    have hcontam' :
        FiniteNoiseFiniteOmissionEnumeration stream (O.language z) := by
      simpa [hcarrier z] using hcontam
    exact
      (lemma_6_9_finiteContamination_sufficiency
        O orders hcarrier c hpair hcontam').2

/-- Theorem 6.5, combining the existing alternating-adversary necessity with
Lemma 6.9's explicit finite-expansion sufficiency. -/
theorem theorem_6_5_lowerDensity_characterization_enumerated
    (O : GenLimit.OracleFamily)
    (orders : ℕ → OrderedLanguage)
    (hcarrier : ∀ i, (orders i).carrier = O.language i)
    (c : ℝ) :
    (∃ gen : SetGenerator ℕ,
      IsInfiniteSetGenerator gen ∧
        ∀ z,
          GeneratesSetUnderFiniteContaminationOn
              gen (orders z).carrier ∧
            GuaranteesSetBasedLowerDensityUnderFiniteContaminationOn
              gen (orders z) c) ↔
      ∀ i j,
        (O.language i \ O.language j).Finite →
          c ≤ (orders j).lowerDensity (O.language i) := by
  constructor
  · rintro ⟨gen, _hinfinite, hgen⟩ i j hdiff
    have hnecessity :=
      theorem_6_5_lowerDensity_complete_necessity
        gen (Set.range orders) c
        (fun K hK => by
          obtain ⟨z, rfl⟩ := hK
          exact (hgen z).1)
        (fun K hK => by
          obtain ⟨z, rfl⟩ := hK
          exact (hgen z).2)
    have hdiff' :
        ((orders i).carrier \ (orders j).carrier).Finite := by
      simpa [hcarrier i, hcarrier j] using hdiff
    have h :=
      hnecessity (L := orders i) (L' := orders j)
        ⟨i, rfl⟩ ⟨j, rfl⟩ hdiff'
    simpa [hcarrier i] using h
  · intro hpair
    exact theorem_6_5_lowerDensity_sufficiency_enumerated
      O orders hcarrier c hpair

end GenLimit.InfiniteContamination
