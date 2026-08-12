import GenLimit.Paper11_UnionClosednessOfLanguageGeneration.MinimalPairRecursion

/-!
# Detailed Theorem 4.3

Source: Hanneke--Karbasi--Mehrotra--Velegkas,
*On Union-Closedness of Language Generation*,
arXiv:2506.18642v1, detailed Theorem 4.3.

This file packages the exact paper-facing theorem around the reusable
cursor-zero alternating-phase core.  The source's displayed first negative
sweep can skip a finite initial block.  That cofinite property suffices for
detailed Theorem 4.1, but Theorem 4.3's first class contains every negative
integer.  `MinimalPairCore` repairs the construction by beginning at `-1`
and proves exact negative coverage.
-/

namespace GenLimit.UnionClosedness

open GenLimit.LiRamanTewari

/-- Detailed Theorem 4.3's union lower bound under the paper's explicit
injective-enumeration convention. -/
theorem theorem_4_3_union_not_generatable_on_injective_presentations :
    ¬GeneratableInLimitOnInjectivePresentations
      (theorem43FirstClass ∪ theorem43SecondClass) :=
  MinimalPairCore.theorem43_union_not_generatable_on_injective_presentations

/-- The same lower bound in the library's stronger all-exact-presentations
semantics, where repetitions are also permitted. -/
theorem theorem_4_3_union_not_generatable :
    ¬GenLimit.Generic.GeneratableInLimit
      (theorem43FirstClass ∪ theorem43SecondClass) :=
  MinimalPairCore.theorem43_union_not_generatable

/-- Both detailed Theorem 4.3 classes satisfy the standing
infinite-language convention. -/
theorem theorem_4_3_classes_uus :
    GenLimit.Generic.UUS theorem43FirstClass ∧
      GenLimit.Generic.UUS theorem43SecondClass :=
  ⟨theorem43FirstClass_uus, theorem43SecondClass_uus⟩

/-- Detailed Theorem 4.3 in full: the first class is uncountable and
uniformly generatable; the second is countable and non-uniformly
generatable; their union is not generatable on the paper's injective
presentations. -/
theorem theorem_4_3 :
    ¬theorem43FirstClass.Countable ∧
      GenLimit.Generic.UniformlyGeneratable theorem43FirstClass ∧
      theorem43SecondClass.Countable ∧
      GenLimit.Generic.NonuniformlyGeneratable theorem43SecondClass ∧
      ¬GeneratableInLimitOnInjectivePresentations
        (theorem43FirstClass ∪ theorem43SecondClass) :=
  ⟨theorem43FirstClass_uncountable,
    theorem43FirstClass_uniformlyGeneratable,
    theorem43SecondClass_countable,
    theorem43SecondClass_nonuniformlyGeneratable,
    theorem_4_3_union_not_generatable_on_injective_presentations⟩

end GenLimit.UnionClosedness
