import GenLimit.Paper11_UnionClosednessOfLanguageGeneration.Theorem41Cardinality
import GenLimit.Paper02_LearningTheory.EventuallyUnboundedClosure

/-!
# The uncountable EUC counterexample in overview Theorem 3.3

Source: Hanneke--Karbasi--Mehrotra--Velegkas,
*On Union-Closedness of Language Generation*,
arXiv:2506.18642v1, overview Theorem 3.3 and detailed Theorem 4.1.

Overview Theorem 3.3 points to the first class from Theorem 3.1 / detailed
Theorem 4.1.  That class is uncountable and non-uniformly generatable.
The source's separate detailed proof instead substitutes the finite-deletion
class from detailed Theorem 4.4, which is countable.

This module supplies the missing argument for the class named by the
overview.  The target `negativeIntegers` belongs to the first Theorem 4.1
class: it has no negative deletions and deletes every positive integer.
After any finite prefix of its canonical enumeration, every unseen negative
integer can still be deleted by a version-space language.  Consequently the
common core is exactly the observed finite sample, so EUC fails.
-/

namespace GenLimit.UnionClosedness

open GenLimit.LiRamanTewari

/-- The all-negative target belongs to the first detailed Theorem 4.1 class. -/
theorem negativeIntegers_mem_finiteNegativeInfinitePositiveClass :
    negativeIntegers ∈ finiteNegativeInfinitePositiveClass := by
  refine
    ⟨∅, positiveIntegers, Set.empty_subset _, Set.finite_empty,
      Set.Subset.rfl, ?_, ?_⟩
  · apply (positiveTail_infinite 0).mono
    rintro z ⟨k, rfl⟩
    simpa using positiveCode_mem k
  · simp [signedDeletionLanguage]

/-- For a finite negative sample, the first Theorem 4.1 class has no
unobserved point in its common core. -/
theorem commonCore_finiteNegativeInfinitePositiveClass_eq
    (S : Finset ℤ) (hS : (↑S : Set ℤ) ⊆ negativeIntegers) :
    GenLimit.LiRamanTewari.commonCore
        finiteNegativeInfinitePositiveClass S =
      (↑S : Set ℤ) := by
  apply Set.Subset.antisymm
  · intro z hz
    have htargetVS :
        negativeIntegers ∈
          GenLimit.LiRamanTewari.versionSpace
            finiteNegativeInfinitePositiveClass S :=
      ⟨negativeIntegers_mem_finiteNegativeInfinitePositiveClass, hS⟩
    have hzneg : z ∈ negativeIntegers := hz negativeIntegers htargetVS
    by_contra hzS
    let Lz : Set ℤ := negativeIntegers \ {z}
    have hpositiveInfinite : positiveIntegers.Infinite := by
      apply (positiveTail_infinite 0).mono
      rintro y ⟨k, rfl⟩
      simpa using positiveCode_mem k
    have hLzClass :
        Lz ∈ finiteNegativeInfinitePositiveClass := by
      refine
        ⟨{z}, positiveIntegers, ?_, Set.finite_singleton z,
          Set.Subset.rfl, hpositiveInfinite, ?_⟩
      · simpa only [Set.singleton_subset_iff] using hzneg
      · simp [Lz, signedDeletionLanguage]
    have hSLz : (↑S : Set ℤ) ⊆ Lz := by
      intro y hy
      refine ⟨hS hy, ?_⟩
      simp only [Set.mem_singleton_iff]
      intro hyz
      subst y
      exact hzS hy
    have hLzVS :
        Lz ∈ GenLimit.LiRamanTewari.versionSpace
          finiteNegativeInfinitePositiveClass S :=
      ⟨hLzClass, hSLz⟩
    have hzLz := hz Lz hLzVS
    exact hzLz.2 (by simp)
  · exact GenLimit.LiRamanTewari.sample_subset_commonCore

/-- The uncountable class named by overview Theorem 3.3 violates EUC. -/
theorem
    finiteNegativeInfinitePositiveClass_not_eventuallyUnboundedClosure :
    ¬EventuallyUnboundedClosure
      finiteNegativeInfinitePositiveClass := by
  intro hEUC
  obtain ⟨t, hinfinite⟩ :=
    hEUC negativeIntegers
      negativeIntegers_mem_finiteNegativeInfinitePositiveClass
      negativeCode range_negativeCode
  have hsample :
      (↑(GenLimit.Generic.sample negativeCode t) : Set ℤ) ⊆
        negativeIntegers := by
    intro z hz
    obtain ⟨s, _hst, rfl⟩ :=
      GenLimit.Generic.mem_sample_iff.mp hz
    exact negativeCode_mem s
  rw [commonCore_finiteNegativeInfinitePositiveClass_eq _ hsample] at hinfinite
  exact hinfinite (GenLimit.Generic.sample negativeCode t).finite_toSet

/-- Repaired exact witness for overview Theorem 3.3: use the first
uncountable class from detailed Theorem 4.1, as the overview specifies,
rather than detailed Theorem 4.4's countable finite-deletion class. -/
theorem theorem_3_3_witness :
    ¬finiteNegativeInfinitePositiveClass.Countable ∧
      GenLimit.Generic.NonuniformlyGeneratable
        finiteNegativeInfinitePositiveClass ∧
      ¬EventuallyUnboundedClosure
        finiteNegativeInfinitePositiveClass :=
  ⟨finiteNegativeInfinitePositiveClass_uncountable,
    finiteNegativeInfinitePositiveClass_nonuniformlyGeneratable,
    finiteNegativeInfinitePositiveClass_not_eventuallyUnboundedClosure⟩

end GenLimit.UnionClosedness
