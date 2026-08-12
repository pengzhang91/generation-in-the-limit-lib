import GenLimit.Paper11_UnionClosednessOfLanguageGeneration.SweepGenerators

/-!
# The two language classes in detailed Theorem 4.1

Source: Hanneke--Karbasi--Mehrotra--Velegkas,
*On Union-Closedness of Language Generation*,
arXiv:2506.18642v1, detailed Theorem 4.1.

The theorem uses languages over `ℤ` which delete finitely many points on one
side of zero and infinitely many on the other.  This module defines the
literal two classes and verifies the positive half of the theorem: each
class is non-uniformly generatable by a one-sided sweep.
-/

namespace GenLimit.UnionClosedness

/-- A language obtained by deleting `A` from the negative side and `B` from
the positive side. -/
def signedDeletionLanguage (A B : Set ℤ) : Set ℤ :=
  (negativeIntegers \ A) ∪ (positiveIntegers \ B)

/-- Detailed Theorem 4.1's first class: finite negative deletion and
infinite positive deletion. -/
def finiteNegativeInfinitePositiveClass :
    GenLimit.Generic.LanguageClass ℤ :=
  {L | ∃ A B : Set ℤ,
    A ⊆ negativeIntegers ∧ A.Finite ∧
    B ⊆ positiveIntegers ∧ B.Infinite ∧
    L = signedDeletionLanguage A B}

/-- Detailed Theorem 4.1's second class: infinite negative deletion and
finite positive deletion. -/
def infiniteNegativeFinitePositiveClass :
    GenLimit.Generic.LanguageClass ℤ :=
  {L | ∃ A B : Set ℤ,
    A ⊆ negativeIntegers ∧ A.Infinite ∧
    B ⊆ positiveIntegers ∧ B.Finite ∧
    L = signedDeletionLanguage A B}

/-- The first class's descending negative sweep. -/
theorem finiteNegativeInfinitePositiveClass_nonuniformlyGeneratable :
    GenLimit.Generic.NonuniformlyGeneratable
      finiteNegativeInfinitePositiveClass := by
  classical
  refine ⟨descendingNegativeGenerator, ?_⟩
  intro L hL
  obtain ⟨A, B, hAneg, hAfin, _hBpos, _hBinf, rfl⟩ := hL
  let badIndices : Set ℕ := negativeCode ⁻¹' A
  have hbadFinite : badIndices.Finite := by
    apply hAfin.preimage
    exact Set.injOn_of_injective negativeCode_injective
  obtain ⟨d, hd⟩ := Finset.exists_nat_subset_range hbadFinite.toFinset
  refine ⟨d, ?_⟩
  intro stream _hstream t ht s hts
  have hdt : d ≤ t := by
    rw [← ht]
    exact GenLimit.Generic.sample_card_le stream t
  have hds : d ≤ s := le_trans hdt hts
  obtain ⟨n, hsn, hout, hfresh⟩ :=
    descendingNegativeGenerator_spec (fun i : Fin s => stream i)
  have hdn : d ≤ n := le_trans hds hsn
  have hnA : negativeCode n ∉ A := by
    intro hnA
    have hnfin : n ∈ hbadFinite.toFinset := by
      simpa [badIndices] using hnA
    have hnlt : n < d := by simpa using hd hnfin
    exact (Nat.not_lt_of_ge hdn) hnlt
  have houtput :
      GenLimit.Generic.output descendingNegativeGenerator stream s =
        negativeCode n := hout
  constructor
  · rw [houtput]
    exact Or.inl ⟨negativeCode_mem n, hnA⟩
  · rw [houtput]
    simpa [hout, GenLimit.Generic.sequenceSample_prefix] using hfresh

/-- The second class's ascending positive sweep. -/
theorem infiniteNegativeFinitePositiveClass_nonuniformlyGeneratable :
    GenLimit.Generic.NonuniformlyGeneratable
      infiniteNegativeFinitePositiveClass := by
  classical
  refine ⟨ascendingPositiveGenerator, ?_⟩
  intro L hL
  obtain ⟨A, B, _hAneg, _hAinf, hBpos, hBfin, rfl⟩ := hL
  let badIndices : Set ℕ := positiveCode ⁻¹' B
  have hbadFinite : badIndices.Finite := by
    apply hBfin.preimage
    exact Set.injOn_of_injective positiveCode_injective
  obtain ⟨d, hd⟩ := Finset.exists_nat_subset_range hbadFinite.toFinset
  refine ⟨d, ?_⟩
  intro stream _hstream t ht s hts
  have hdt : d ≤ t := by
    rw [← ht]
    exact GenLimit.Generic.sample_card_le stream t
  have hds : d ≤ s := le_trans hdt hts
  obtain ⟨n, hsn, hout, hfresh⟩ :=
    ascendingPositiveGenerator_spec (fun i : Fin s => stream i)
  have hdn : d ≤ n := le_trans hds hsn
  have hnB : positiveCode n ∉ B := by
    intro hnB
    have hnfin : n ∈ hbadFinite.toFinset := by
      simpa [badIndices] using hnB
    have hnlt : n < d := by simpa using hd hnfin
    exact (Nat.not_lt_of_ge hdn) hnlt
  have houtput :
      GenLimit.Generic.output ascendingPositiveGenerator stream s =
        positiveCode n := hout
  constructor
  · rw [houtput]
    exact Or.inr ⟨positiveCode_mem n, hnB⟩
  · rw [houtput]
    simpa [hout, GenLimit.Generic.sequenceSample_prefix] using hfresh

/-- The positive half of detailed Theorem 4.1. -/
theorem theorem_4_1_individual_classes :
    GenLimit.Generic.NonuniformlyGeneratable
        finiteNegativeInfinitePositiveClass ∧
      GenLimit.Generic.NonuniformlyGeneratable
        infiniteNegativeFinitePositiveClass :=
  ⟨finiteNegativeInfinitePositiveClass_nonuniformlyGeneratable,
    infiniteNegativeFinitePositiveClass_nonuniformlyGeneratable⟩

end GenLimit.UnionClosedness
