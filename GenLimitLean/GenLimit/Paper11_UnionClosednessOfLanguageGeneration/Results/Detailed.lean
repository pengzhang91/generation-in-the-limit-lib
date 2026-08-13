import GenLimit.Paper11_UnionClosednessOfLanguageGeneration.AlternatingPhaseRecursion
import GenLimit.Paper11_UnionClosednessOfLanguageGeneration.Theorem43
import GenLimit.Paper11_UnionClosednessOfLanguageGeneration.EventuallyUnboundedClosure

/-!
# Detailed results for union-closedness

This is the public facade for detailed Theorems 4.1, 4.3, and 4.4 of
Hanneke--Karbasi--Mehrotra--Velegkas,
*On Union-Closedness of Language Generation* (arXiv:2506.18642v1).

The imported numbered theorems `theorem_4_1` and `theorem_4_3` use the
paper's duplicate-free (injective) presentation convention.  Their union
lower bounds imply the library's stronger all-presentations lower bounds via
the Paper11 bridge in `Definitions`.  `theorem_4_4` has no
presentation-semantics distinction.

The proof of detailed Theorem 4.3 additionally exposes its two autonomous
output schedules through `theorem_4_3_classes_without_adversary_input`; the
numbered wrapper retains the source's displayed standard generation clauses.

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

end GenLimit.UnionClosedness
