import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Results.Detailed
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Theorem41Cardinality
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Theorem33UncountableEUC
import GenLimit.Paper02_LearningTheory.FiniteEUCUnion

/-!
# Overview results for union-closedness

This module is the public facade for overview Theorems 3.1--3.3 of
Hanneke--Karbasi--Mehrotra--Velegkas,
*On Union-Closedness of Language Generation* (arXiv:2506.18642v1).

The numbered theorems are existential, source-facing statements.  Their
corresponding `*_witness` theorems expose the concrete classes used by the
formalization.  Theorems 3.1 and 3.2 use the source's injective-presentation
convention.  The Paper10 bridge in `Definitions` immediately yields the
stronger library lower bounds for presentations with repetitions when needed.
-/

namespace GenLimit.UnionClosedness

open GenLimit.Generic

/-! ## Overview Theorem 3.1 -/

/-- Overview Theorem 3.1.  The union lower bound uses duplicate-free exact
presentations, as in the source. -/
theorem theorem_3_1 :
    ∃ H₁ H₂ : LanguageClass ℤ,
      ¬H₁.Countable ∧ NonuniformlyGeneratable H₁ ∧
      ¬H₂.Countable ∧ NonuniformlyGeneratable H₂ ∧
      ¬GeneratableInLimitOnInjectivePresentations (H₁ ∪ H₂) :=
  ⟨finiteNegativeInfinitePositiveClass,
    infiniteNegativeFinitePositiveClass, theorem_3_1_witness⟩

/-- The fixed Theorem 3.1 witnesses also satisfy the paper's standing
infinite-language convention. -/
theorem theorem_3_1_witness_uus :
    UUS finiteNegativeInfinitePositiveClass ∧
      UUS infiniteNegativeFinitePositiveClass :=
  theorem_4_1_classes_uus

/-! ## Overview Theorem 3.2 -/

/-- The fixed witnesses for overview Theorem 3.2, ordered as in the paper:
the countable non-uniform class first and the uncountable uniform class
second.  Both generators are represented by autonomous schedules that require
no adversary-provided examples. -/
theorem theorem_3_2_witness :
    theorem43SecondClass.Countable ∧
      NonuniformlyGeneratableWithoutAdversaryInput theorem43SecondClass ∧
      ¬theorem43FirstClass.Countable ∧
      UniformlyGeneratableWithoutAdversaryInput theorem43FirstClass ∧
      ¬GeneratableInLimitOnInjectivePresentations
        (theorem43SecondClass ∪ theorem43FirstClass) := by
  refine
    ⟨theorem43SecondClass_countable,
      theorem_4_3_classes_without_adversary_input.2,
      theorem43FirstClass_uncountable,
      theorem_4_3_classes_without_adversary_input.1, ?_⟩
  simpa [Set.union_comm] using
    theorem_4_3_union_not_generatable_on_injective_presentations

/-- Compatibility projection of the fixed witnesses to the repository's
standard uniform and non-uniform generation predicates. -/
theorem theorem_3_2_witness_standard :
    theorem43SecondClass.Countable ∧
      NonuniformlyGeneratable theorem43SecondClass ∧
      ¬theorem43FirstClass.Countable ∧
      UniformlyGeneratable theorem43FirstClass ∧
      ¬GeneratableInLimitOnInjectivePresentations
        (theorem43SecondClass ∪ theorem43FirstClass) :=
  ⟨theorem_3_2_witness.1,
    nonuniformlyGeneratable_of_withoutAdversaryInput
      theorem_3_2_witness.2.1,
    theorem_3_2_witness.2.2.1,
    uniformlyGeneratable_of_withoutAdversaryInput
      theorem_3_2_witness.2.2.2.1,
    theorem_3_2_witness.2.2.2.2⟩

/-- The fixed Theorem 3.2 witnesses also satisfy the paper's standing
infinite-language convention. -/
theorem theorem_3_2_witness_uus :
    UUS theorem43SecondClass ∧ UUS theorem43FirstClass :=
  ⟨uus_of_nonuniformWithoutAdversaryInput theorem_3_2_witness.2.1,
    uus_of_uniformWithoutAdversaryInput theorem_3_2_witness.2.2.2.1⟩

/-- Overview Theorem 3.2, ordered as in the source: a countable
non-uniformly generatable class followed by an uncountable uniformly
generatable class, neither requiring adversary-provided elements, whose union
is not generatable on injective presentations. -/
theorem theorem_3_2 :
    ∃ H₁ H₂ : LanguageClass ℤ,
      H₁.Countable ∧
      NonuniformlyGeneratableWithoutAdversaryInput H₁ ∧
      ¬H₂.Countable ∧
      UniformlyGeneratableWithoutAdversaryInput H₂ ∧
      ¬GeneratableInLimitOnInjectivePresentations (H₁ ∪ H₂) :=
  ⟨theorem43SecondClass, theorem43FirstClass, theorem_3_2_witness⟩

/-- Overview Theorem 3.2 projected to the standard generation predicates. -/
theorem theorem_3_2_standard :
    ∃ H₁ H₂ : LanguageClass ℤ,
      H₁.Countable ∧ NonuniformlyGeneratable H₁ ∧
      ¬H₂.Countable ∧ UniformlyGeneratable H₂ ∧
      ¬GeneratableInLimitOnInjectivePresentations (H₁ ∪ H₂) :=
  ⟨theorem43SecondClass, theorem43FirstClass,
    theorem_3_2_witness_standard⟩

/-! ## Overview Theorem 3.3 -/

/-- The logical link between overview Theorems 3.1 and 3.3.  If both
components of the Theorem 3.1 witness had Eventually Unbounded Closure,
P02's finite-EUC-cover theorem would generate their union in the library's
all-presentations semantics.  Restricting that generator to injective
presentations contradicts Theorem 3.1's union lower bound. -/
theorem theorem_3_3_of_theorem_3_1 :
    ¬GenLimit.LiRamanTewari.EventuallyUnboundedClosure
          finiteNegativeInfinitePositiveClass ∨
      ¬GenLimit.LiRamanTewari.EventuallyUnboundedClosure
          infiniteNegativeFinitePositiveClass := by
  by_contra hneither
  push_neg at hneither
  let classes : Fin 2 → LanguageClass ℤ :=
    fun i => if i = 0 then
      finiteNegativeInfinitePositiveClass
    else
      infiniteNegativeFinitePositiveClass
  have hcover :
      GenLimit.LiRamanTewari.IsFiniteCover
        (finiteNegativeInfinitePositiveClass ∪
          infiniteNegativeFinitePositiveClass) classes := by
    ext L
    constructor
    · intro hL
      rcases hL with hL | hL
      · rw [Set.mem_iUnion]
        refine ⟨⟨0, by omega⟩, ?_⟩
        simpa [classes] using hL
      · rw [Set.mem_iUnion]
        refine ⟨⟨1, by omega⟩, ?_⟩
        simpa [classes] using hL
    · rw [Set.mem_iUnion]
      rintro ⟨i, hi⟩
      have hiCases : i = (0 : Fin 2) ∨ i = (1 : Fin 2) := by
        have hiValue : i.1 = 0 ∨ i.1 = 1 := by omega
        rcases hiValue with hzero | hone
        · exact Or.inl (Fin.ext hzero)
        · exact Or.inr (Fin.ext hone)
      rcases hiCases with rfl | rfl
      · exact Or.inl (by simpa [classes] using hi)
      · exact Or.inr (by simpa [classes] using hi)
  have hEUC :
      ∀ i, GenLimit.LiRamanTewari.EventuallyUnboundedClosure
        (classes i) := by
    intro i
    have hiCases : i = (0 : Fin 2) ∨ i = (1 : Fin 2) := by
      have hiValue : i.1 = 0 ∨ i.1 = 1 := by omega
      rcases hiValue with hzero | hone
      · exact Or.inl (Fin.ext hzero)
      · exact Or.inr (Fin.ext hone)
    rcases hiCases with rfl | rfl
    · simpa [classes] using hneither.1
    · simpa [classes] using hneither.2
  have hgeneratable :
      GeneratableInLimit
        (finiteNegativeInfinitePositiveClass ∪
          infiniteNegativeFinitePositiveClass) :=
    GenLimit.LiRamanTewari.finite_euc_cover_implies_generatable_in_limit
      classes hcover hEUC
  exact theorem_4_1_union_not_generatable hgeneratable

/-- Overview Theorem 3.3.  The disjunction
`theorem_3_3_of_theorem_3_1` explains why Theorem 3.1 already forces such a
class to exist.  This wrapper chooses the concrete first component, for which
`theorem_3_3_witness` proves the stronger direct statement. -/
theorem theorem_3_3 :
    ∃ H : LanguageClass ℤ,
      ¬H.Countable ∧ NonuniformlyGeneratable H ∧
        ¬GenLimit.LiRamanTewari.EventuallyUnboundedClosure H :=
  ⟨finiteNegativeInfinitePositiveClass,
    theorem_3_3_witness.1,
    theorem_3_3_witness.2.1,
    theorem_3_3_witness.2.2⟩

/-- The fixed Theorem 3.3 witness also satisfies the paper's standing
infinite-language convention. -/
theorem theorem_3_3_witness_uus :
    UUS finiteNegativeInfinitePositiveClass :=
  theorem_4_1_classes_uus.1

end GenLimit.UnionClosedness
