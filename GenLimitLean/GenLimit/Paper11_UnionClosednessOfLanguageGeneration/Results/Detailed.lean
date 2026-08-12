import GenLimit.Paper11_UnionClosednessOfLanguageGeneration.AlternatingPhaseRecursion
import GenLimit.Paper11_UnionClosednessOfLanguageGeneration.Theorem43
import GenLimit.Paper11_UnionClosednessOfLanguageGeneration.EventuallyUnboundedClosure

/-!
# Detailed results for union-closedness

This is the public facade for detailed Theorems 4.1, 4.3, and 4.4 of
Hanneke--Karbasi--Mehrotra--Velegkas,
*On Union-Closedness of Language Generation* (arXiv:2506.18642v1).

The imported numbered theorems `theorem_4_1` and `theorem_4_3` use the
paper's duplicate-free (injective) presentation convention.  The explicitly
named `*_all_presentations` corollaries use the library's stronger convention,
which requires success on every exact presentation, repetitions included.
`theorem_4_4` has no presentation-semantics distinction.

Only paper-facing facts are added here.  The alternating-recursion machinery
remains in the implementation modules imported above.
-/

namespace GenLimit.UnionClosedness

open GenLimit.Generic

/-! ## Standing infinite-language convention -/

/-- The first class in detailed Theorem 4.1 satisfies the paper's standing
infinite-language convention. -/
theorem finiteNegativeInfinitePositiveClass_uus :
    UUS finiteNegativeInfinitePositiveClass := by
  intro L hL
  obtain ⟨A, B, _hAneg, hAfin, _hBpos, _hBinf, rfl⟩ := hL
  apply (negativeIntegers_infinite.diff hAfin).mono
  intro z hz
  exact Or.inl hz

/-- The second class in detailed Theorem 4.1 satisfies the paper's standing
infinite-language convention. -/
theorem infiniteNegativeFinitePositiveClass_uus :
    UUS infiniteNegativeFinitePositiveClass := by
  intro L hL
  obtain ⟨A, B, _hAneg, _hAinf, _hBpos, hBfin, rfl⟩ := hL
  apply (positiveIntegers_infinite.diff hBfin).mono
  intro z hz
  exact Or.inr hz

/-- Both component classes in detailed Theorem 4.1 satisfy the paper's
standing infinite-language convention. -/
theorem theorem_4_1_classes_uus :
    UUS finiteNegativeInfinitePositiveClass ∧
      UUS infiniteNegativeFinitePositiveClass :=
  ⟨finiteNegativeInfinitePositiveClass_uus,
    infiniteNegativeFinitePositiveClass_uus⟩

/-! ## All-presentations corollaries -/

/-- Detailed Theorem 4.1 under the library's stronger all-exact-presentations
semantics.  The source-facing numbered theorem `theorem_4_1` uses injective
presentations. -/
theorem theorem_4_1_all_presentations :
    NonuniformlyGeneratable finiteNegativeInfinitePositiveClass ∧
      NonuniformlyGeneratable infiniteNegativeFinitePositiveClass ∧
      ¬GeneratableInLimit
        (finiteNegativeInfinitePositiveClass ∪
          infiniteNegativeFinitePositiveClass) :=
  ⟨theorem_4_1_individual_classes.1,
    theorem_4_1_individual_classes.2,
    theorem_4_1_union_not_generatable⟩

/-- Detailed Theorem 4.3 under the library's stronger all-exact-presentations
semantics.  The source-facing numbered theorem `theorem_4_3` uses injective
presentations. -/
theorem theorem_4_3_all_presentations :
    ¬theorem43FirstClass.Countable ∧
      UniformlyGeneratable theorem43FirstClass ∧
      theorem43SecondClass.Countable ∧
      NonuniformlyGeneratable theorem43SecondClass ∧
      ¬GeneratableInLimit
        (theorem43FirstClass ∪ theorem43SecondClass) :=
  ⟨theorem43FirstClass_uncountable,
    theorem43FirstClass_uniformlyGeneratable,
    theorem43SecondClass_countable,
    theorem43SecondClass_nonuniformlyGeneratable,
    theorem_4_3_union_not_generatable⟩

end GenLimit.UnionClosedness
