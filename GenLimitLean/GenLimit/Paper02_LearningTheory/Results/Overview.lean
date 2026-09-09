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
import GenLimit.Paper02_LearningTheory.Introductory

/-!
# #02 Learning Theory: main results

This public facade exposes the native main results of Li--Raman--Tewari,
*Generation through the Lens of Learning Theory* (arXiv:2410.13714v5 /
COLT 2025). The declarations in `GenLimit.LiRamanTewari.Results` are thin
wrappers around the canonical proof modules and do not duplicate proofs.

Proposition 2.1 and Theorems 2.4--2.5 use explicit countably infinite or
nonempty countable universes where required. Theorems 3.3, 3.5, 3.10,
5.1--5.2, C.2, and C.4 are complete at the paper's semantic boundary.
Theorem 4.1 is exposed only at the finite-VC/finite-Littlestone combinatorial
characterization boundary: literal PAC probability spaces, PAC learners,
online interaction, and regret are not formalized.

Theorem 2.2 and the corrected countable form of Theorem 2.3 live in
`GenLimit.Bridges`; importing them here would make the native P02 development
depend on the separate Gold and Angluin formalizations. The printed
arbitrary-class Theorem 2.3 is false and has a bridge diagnostic.

Appendix C's printed arbitrary-stream reformulation of EUC is also false.
The C.2 and C.4 proofs use Definition C.1 directly. The unnumbered strictness
claim following C.2 is exposed below using the explicit spine/tails witness:
EUC does not imply uniform generatability.
-/

namespace GenLimit.LiRamanTewari

/-! ## Stable main-results surface -/

namespace Results

/-- Proposition 2.1: both generation-hierarchy reverse implications fail. -/
theorem proposition_2_1 :
    ∃ α : Type, Countable α ∧ Infinite α ∧ GenerationHierarchyStrictOn α :=
  GenLimit.LiRamanTewari.proposition_2_1

/-- Theorem 2.4: every countable UUS class is generatable in the limit. -/
theorem theorem_2_4
    {α : Type*} [Nonempty α] [Countable α]
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : UUS H) (hCountable : H.Countable) :
    GeneratableInLimit H :=
  GenLimit.LiRamanTewari.theorem_2_4 hUUS hCountable

/-- Theorem 2.5: every finite UUS class is uniformly generatable. -/
theorem theorem_2_5
    {α : Type*} [Nonempty α] [Countable α]
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : UUS H) (hFinite : H.Finite) :
    UniformlyGeneratable H :=
  GenLimit.LiRamanTewari.theorem_2_5 hUUS hFinite

/-- Theorem 3.3: uniform generation iff finite closure dimension. -/
theorem theorem_3_3
    [Nonempty α] [Countable α]
    {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H) :
    UniformlyGeneratable H ↔ HasFiniteClosureDimension H :=
  GenLimit.LiRamanTewari.uniform_generatability_iff_finite_closure_dimension
    hUUS

/-- The quantitative conclusion following Theorem 3.3. -/
theorem theorem_3_3_sample_complexity_bounds
    [Nonempty α] [Countable α]
    {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H)
    {d : ℕ} (hC : HasClosureDimension H d) :
    (d : WithTop ℕ) ≤ optimalUniformGenerationSampleComplexity H ∧
      optimalUniformGenerationSampleComplexity H ≤
        ((d + 1 : ℕ) : WithTop ℕ) :=
  GenLimit.LiRamanTewari.optimal_uniform_generation_sample_complexity_bounds
    hUUS hC

/-- Theorem 3.5: the nondecreasing finite-closure-cover characterization. -/
theorem theorem_3_5
    [Nonempty α] [Countable α]
    {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H) :
    NonuniformlyGeneratable H ↔
      ∃ classes : ℕ → GenLimit.Generic.LanguageClass α,
        IsNondecreasingCover H classes ∧
          ∀ n, HasFiniteClosureDimension (classes n) :=
  GenLimit.LiRamanTewari.nonuniform_generatability_iff_nondecreasing_finite_closure_cover
    hUUS

/-- Theorem 3.10: finite closure-dimension covers generate in the limit. -/
theorem theorem_3_10
    [Nonempty α] [Countable α]
    {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H)
    (hcover : ∃ n : ℕ,
      ∃ classes : Fin n → GenLimit.Generic.LanguageClass α,
        IsFiniteCover H classes ∧
          ∀ i, HasFiniteClosureDimension (classes i)) :
    GeneratableInLimit H :=
  GenLimit.LiRamanTewari.finite_closure_dimension_cover_implies_generatable_in_limit
    hUUS hcover

/-- Theorem 4.1 at the paper's cited VC/Littlestone characterization
boundary, not at the literal PAC/online algorithmic boundary. -/
theorem theorem_4_1_combinatorial_core :
    (∃ H : GenLimit.Generic.LanguageClass ℤ,
      H.Countable ∧ UniformlyGeneratable H ∧
        ¬PACLearnableViaVC H) ∧
    (∃ H : GenLimit.Generic.LanguageClass BlockUniverse,
      H.Countable ∧ OnlineLearnableViaLittlestone H ∧
        ¬UniformlyGeneratable H) ∧
    (∃ H : GenLimit.Generic.LanguageClass ℤ,
      H.Countable ∧ OnlineLearnableViaLittlestone H ∧
        UniformlyGeneratable H) ∧
    (∃ H : GenLimit.Generic.LanguageClass ThresholdBlockUniverse,
      H.Countable ∧ PACLearnableViaVC H ∧
        ¬OnlineLearnableViaLittlestone H ∧
        ¬UniformlyGeneratable H) ∧
    (∃ H : GenLimit.Generic.LanguageClass ℕ,
      H.Countable ∧ PACLearnableViaVC H ∧
        UniformlyGeneratable H ∧
        ¬OnlineLearnableViaLittlestone H) ∧
    (∃ H : GenLimit.Generic.LanguageClass ℕ,
      H.Countable ∧ ¬PACLearnableViaVC H ∧
        ¬UniformlyGeneratable H) :=
  GenLimit.LiRamanTewari.theorem_4_1_combinatorial_core

/-- Theorem 5.1: prompted uniform generation iff finite prompted closure
dimension. -/
theorem theorem_5_1
    [Nonempty α] [Countable α] [Countable ι]
    {H : MulticlassHypothesisClass α ι} (hPUUS : PUUS H) :
    PromptedUniformlyGeneratable H ↔
      HasFinitePromptedClosureDimension H :=
  GenLimit.LiRamanTewari.prompted_uniform_generatability_iff_finite_prompted_closure_dimension
    hPUUS

/-- Theorem 5.2: the prompted nondecreasing finite-closure-cover
characterization. -/
theorem theorem_5_2
    [Nonempty α] [Countable α] [Countable ι]
    {H : MulticlassHypothesisClass α ι} (hPUUS : PUUS H) :
    PromptedNonuniformlyGeneratable H ↔
      ∃ classes : ℕ → MulticlassHypothesisClass α ι,
        IsPromptedNondecreasingCover H classes ∧
          ∀ n, HasFinitePromptedClosureDimension (classes n) :=
  GenLimit.LiRamanTewari.prompted_nonuniform_generatability_iff_nondecreasing_finite_closure_cover
    hPUUS

/-- Theorem C.2: a finite EUC cover suffices for generation in the limit. -/
theorem theorem_C_2
    [Nonempty α] [Countable α]
    {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H)
    (hcover : ∃ n : ℕ,
      ∃ classes : Fin n → GenLimit.Generic.LanguageClass α,
        IsFiniteCover H classes ∧
          ∀ i, EventuallyUnboundedClosure (classes i)) :
    GeneratableInLimit H :=
  GenLimit.LiRamanTewari.theorem_C2_finite_eventually_unbounded_closure_cover
    hUUS hcover

/-- Theorem C.4: a nondecreasing EUC cover suffices for generation in the
limit. -/
theorem theorem_C_4
    [Nonempty α] [Countable α]
    {H : GenLimit.Generic.LanguageClass α} (hUUS : UUS H)
    (hcover : ∃ classes : ℕ → GenLimit.Generic.LanguageClass α,
      IsNondecreasingCover H classes ∧
        ∀ n, EventuallyUnboundedClosure (classes n)) :
    GeneratableInLimit H :=
  GenLimit.LiRamanTewari.theorem_C4_eventually_unbounded_closure
    hUUS hcover

/-- The unnumbered strictness assertion following Theorem C.2: EUC does not
imply uniform generation. -/
theorem euc_not_imply_uniform :
    ∃ H : GenLimit.Generic.LanguageClass SpineTailUniverse,
      H.Countable ∧ UUS H ∧ EventuallyUnboundedClosure H ∧
        ¬UniformlyGeneratable H :=
  GenLimit.LiRamanTewari.exists_eventuallyUnboundedClosure_not_uniformlyGeneratable

end Results
end GenLimit.LiRamanTewari
