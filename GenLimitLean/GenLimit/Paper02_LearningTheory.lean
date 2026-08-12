import GenLimit.Paper02_LearningTheory.Definitions
import GenLimit.Paper02_LearningTheory.Hierarchy
import GenLimit.Paper02_LearningTheory.Closure
import GenLimit.Paper02_LearningTheory.UniformSampleComplexity
import GenLimit.Paper02_LearningTheory.NonuniformCharacterization
import GenLimit.Paper02_LearningTheory.GenerationInLimitCharacterization
import GenLimit.Paper02_LearningTheory.FiniteConeCover
import GenLimit.Paper02_LearningTheory.LimitVsNonuniformSeparation
import GenLimit.Paper02_LearningTheory.CountableUnionSeparation
import GenLimit.Paper02_LearningTheory.EarlierSectionThreeExamples
import GenLimit.Paper02_LearningTheory.Prediction
import GenLimit.Paper02_LearningTheory.EventuallyUnboundedClosure
import GenLimit.Paper02_LearningTheory.EventuallyUnboundedClosureDiagnostics
import GenLimit.Paper02_LearningTheory.FiniteEUCUnion
import GenLimit.Paper02_LearningTheory.Relationships
import GenLimit.Paper02_LearningTheory.PromptedDefinitions
import GenLimit.Paper02_LearningTheory.PromptedClosure
import GenLimit.Paper02_LearningTheory.PromptedNonuniform
import GenLimit.Paper02_LearningTheory.PromptedInfinitePromptExample

/-!
# #02 Learning Theory

Independent umbrella for *Generation through the Lens of Learning Theory*.
Most declarations are organized by topic in the modules imported above;
the short declarations below package results proved later in the paper under
their introductory source numbers.

Numbered entry points:

* Proposition 2.1 and Theorems 2.4--2.5 are packaged below.
* Theorems 3.3, 3.5, and 3.10 are in `Closure`,
  `NonuniformCharacterization`, and `GenerationInLimitCharacterization`.
* Theorem 4.1's explicitly delimited VC/Littlestone combinatorial core is in
  `Prediction`.
* Theorems 5.1--5.2 are in `PromptedClosure` and `PromptedNonuniform`.
* Theorems C.2 and C.4 are in `FiniteEUCUnion` and
  `EventuallyUnboundedClosure`.

Theorem 2.2 and the corrected countable form of Theorem 2.3 reuse the Gold
and Angluin developments.  They therefore remain in `GenLimit.Bridges` and
are deliberately not imported by this independent paper umbrella.  Import
`GenLimit` for the paper modules together with all cross-paper bridges.
-/

namespace GenLimit.LiRamanTewari

/-- Proposition 2.1 (`prop:gencomp`): both reverse implications in the
generation hierarchy fail.  This source-facing package reuses the formalized
Lemma 3.9 and Lemma 3.12 witnesses.  Following those lemmas, the two clauses
are instantiated on explicit countably infinite universes; the source's
literal arbitrary-countable-`X` wording cannot hold when `X` is finite. -/
theorem proposition_2_1 :
    (∃ H : GenLimit.Generic.LanguageClass BlockUniverse,
      UUS H ∧ NonuniformlyGeneratable H ∧ ¬UniformlyGeneratable H) ∧
    (∃ H : GenLimit.Generic.LanguageClass ℤ,
      UUS H ∧ GeneratableInLimit H ∧ ¬NonuniformlyGeneratable H) := by
  constructor
  · obtain ⟨H, _hCountable, hUUS, hNonuniform, hNotUniform⟩ :=
      exists_countable_nonuniform_not_uniform_class
    exact ⟨H, hUUS, hNonuniform, hNotUniform⟩
  · exact exists_generatable_in_limit_not_nonuniformly_generatable

/-- Theorem 2.4: every countable class of infinite languages is generatable
in the limit.  The formal development proves the stronger intermediate
non-uniform conclusion in Corollary 3.6. -/
theorem theorem_2_4
    {α : Type*} [Nonempty α] [Countable α]
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : UUS H) (hCountable : H.Countable) :
    GeneratableInLimit H :=
  nonuniform_implies_limit hUUS
    (countable_classes_are_nonuniformly_generatable
      hUUS hCountable)

/-- Theorem 2.5: every finite UUS class is uniformly generatable.  The proof
factors through the finite-class closure bound and Theorem 3.3 rather than
duplicating the earlier KM construction. -/
theorem theorem_2_5
    {α : Type*} [Nonempty α] [Countable α]
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : UUS H) (hFinite : H.Finite) :
    UniformlyGeneratable H :=
  finite_closure_dimension_implies_uniform hUUS
    (finite_language_class_has_finite_closure_dimension hFinite)

end GenLimit.LiRamanTewari
