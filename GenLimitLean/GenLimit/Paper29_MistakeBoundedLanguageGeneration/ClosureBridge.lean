import GenLimit.Core.ClosureDimension
import GenLimit.Paper29_MistakeBoundedLanguageGeneration.FiniteWeightedAlgorithm

/-!
# Bridge to the shared positive-closure API

Paper 29 states its finite-class closure parameter by intersecting arbitrary
subcollections of an indexed family.  The shared Core API instead takes the
common core of the positive version space selected by a finite sample.  This
module records the exact representation bridge and shows that the paper's
upper-bound predicate implies Core's `ClosureDimensionAtMost` predicate.

The converse is not asserted: an arbitrary subcollection need not be the
version space selected by a positive sample.
-/

namespace GenLimit.MistakeBounded

open GenLimit.Generic

attribute [local instance] Classical.propDecidable

/-- For a finite indexed family, the Core common core is exactly the
intersection of those indices whose languages contain the sample. -/
theorem commonCore_range_eq_finiteClassIntersection
    {N : ℕ} (language : Fin N → Set α) (S : Finset α) :
    commonCore (Set.range language) S =
      finiteClassIntersection language
        (Finset.univ.filter
          (fun i => (↑S : Set α) ⊆ language i)) := by
  classical
  ext x
  constructor
  · intro hx i hi
    have hiContains : (↑S : Set α) ⊆ language i :=
      (Finset.mem_filter.mp hi).2
    exact hx (language i) ⟨⟨i, rfl⟩, hiContains⟩
  · intro hx L hL
    obtain ⟨i, rfl⟩ := hL.1
    exact hx i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hL.2⟩)

/-- The finite-class structural assumption used by Paper 29 is a sufficient
upper bound for the shared positive closure dimension of the corresponding
set-valued class. -/
theorem finiteClassClosureDimensionAtMost_implies_core
    {N : ℕ} (language : Fin N → Set α) {d : ℕ}
    (hdim : FiniteClassClosureDimensionAtMost language d) :
    ClosureDimensionAtMost (Set.range language) d := by
  classical
  intro S hd _hVersion
  rw [commonCore_range_eq_finiteClassIntersection]
  by_contra hnotInfinite
  have hfinite :
      (finiteClassIntersection language
        (Finset.univ.filter
          (fun i => (↑S : Set α) ⊆ language i))).Finite :=
    Set.not_infinite.mp hnotInfinite
  have hsampleSubset :
      (↑S : Set α) ⊆
        finiteClassIntersection language
          (Finset.univ.filter
            (fun i => (↑S : Set α) ⊆ language i)) := by
    intro x hx i hi
    exact (Finset.mem_filter.mp hi).2 hx
  have hcard :
      S.card ≤
        (finiteClassIntersection language
          (Finset.univ.filter
            (fun i => (↑S : Set α) ⊆ language i))).ncard := by
    simpa using Set.ncard_le_ncard hsampleSubset hfinite
  have hupper :=
    hdim
      (Finset.univ.filter
        (fun i => (↑S : Set α) ⊆ language i)) hfinite
  omega

end GenLimit.MistakeBounded
