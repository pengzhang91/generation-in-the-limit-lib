import GenLimit.Paper27_FeedbackQueriesAndMistakes.ElementMistake
import GenLimit.Paper27_FeedbackQueriesAndMistakes.SourceSetMistake
import GenLimit.Paper27_FeedbackQueriesAndMistakes.SourceQuery
import GenLimit.Paper27_FeedbackQueriesAndMistakes.SourceQuerySeparation
import GenLimit.Paper27_FeedbackQueriesAndMistakes.CountableUnion
import GenLimit.Paper27_FeedbackQueriesAndMistakes.ZeroExamples
import GenLimit.Paper27_FeedbackQueriesAndMistakes.EventuallyCorrect
import GenLimit.Paper27_FeedbackQueriesAndMistakes.NoFeedbackEquivalence
import GenLimit.Paper27_FeedbackQueriesAndMistakes.NoFeedbackLockingGap
import GenLimit.Paper27_FeedbackQueriesAndMistakes.FiniteWitnessConversion

/-!
# Paper 27: main-results overview

This module is the public results facade for Hanneke--Karbasi--Mehrotra--
Velegkas, *Language Generation with Feedback: Queries and Mistakes*
(ICML 2026, OpenReview forum `jvfXyIcQ8a`).  The declarations below are thin
wrappers around the canonical proofs and do not duplicate them.

## Coverage boundary

The exact semantic/classical statements of Theorems 3.1--3.4 and Corollaries
3.6--3.8 are formalized.
Theorem 3.1 characterizes element-valued mistake-feedback generation by a
countable inner cover; Theorem 3.2 equates the source's element- and
set-valued mistake models; Theorem 3.3 gives the literal three-point block
separation between source-timed element and set query generation; and Theorem
3.4 gives the corresponding one-query characterization for set generation.
Corollary 3.6 gives countable-union closure, Corollary 3.7 removes positive
examples, and Corollary 3.8 characterizes both models under eventually correct
feedback, even for arbitrary example streams.

`QuerySeparation.lean` contains a differently modeled auxiliary separation,
which remains intentionally separate from the source theorem in
`SourceQuerySeparation.lean`.  For no-feedback Theorem 3.9, the set-to-element
direction and the paper's element-to-set self-simulation under its explicit
self-locking premise are checked.  `NoFeedbackLockingGap.lean` gives a
kernel-checked counterexample to Appendix Lemma A.8's claim that every fresh
successful sequence generator has such a prefix along every presentation.
The finite-witness characterization supplies an independent proof of the
unrestricted reverse implication. All five clauses of Theorem 3.10 follow,
including the countably inner-covered but nongeneratable union of P02 cones.
-/

namespace GenLimit.FeedbackQueries.Results

open GenLimit.Generic
open GenLimit.FeedbackQueries

/-- Overview Theorem 3.1: element-valued generation with truthful mistake
feedback is possible exactly for classes admitting a countable inner cover. -/
theorem theorem_3_1
    [Countable α] [Infinite α]
    (targets : LanguageClass α)
    (hinfinite : ∀ L, L ∈ targets → L.Infinite) :
    SourceElementMistakeGeneratable targets ↔
      HasCountableInnerCover targets :=
  theorem_3_1_elementMistake_characterization targets hinfinite

/-- Overview Theorem 3.2: the source-faithful set- and element-valued
mistake-feedback models have the same generatable classes. -/
theorem theorem_3_2
    [Countable α] [Infinite α]
    (targets : LanguageClass α)
    (hinfinite : ∀ L, L ∈ targets → L.Infinite) :
    SourceSetMistakeGeneratable targets ↔
      SourceElementMistakeGeneratable targets :=
  theorem_3_2_setElementMistake_equivalence targets hinfinite

/-- Overview Theorem 3.3: the paper's explicit three-point block class is
generatable by a source-timed element-valued one-query strategy but not by
any source-timed set-valued one-query strategy. -/
theorem theorem_3_3 :
    ∃ targets : LanguageClass ℕ,
      SourceElementQueryGeneratable targets ∧
        ¬ SourceSetQueryGeneratable targets :=
  GenLimit.FeedbackQueries.theorem_3_3

/-- Overview Theorem 3.4: source-timed set generation with one membership
query per round is possible exactly under the same inner-cover condition. -/
theorem theorem_3_4
    [Countable α] [Infinite α]
    (targets : LanguageClass α)
    (hinfinite : ∀ L, L ∈ targets → L.Infinite) :
    SourceSetQueryGeneratable targets ↔
      HasCountableInnerCover targets :=
  theorem_3_4_sourceSetQuery_characterization targets hinfinite

/-- Overview Corollary 3.6: both feedback models are closed under countable
unions of classes of infinite languages. -/
theorem corollary_3_6
    [Countable α] [Infinite α]
    (classes : ℕ → LanguageClass α)
    (hinfinite : ∀ i L, L ∈ classes i → L.Infinite) :
    ((∀ i, SourceElementMistakeGeneratable (classes i)) →
      SourceElementMistakeGeneratable (⋃ i, classes i)) ∧
    ((∀ i, SourceSetQueryGeneratable (classes i)) →
      SourceSetQueryGeneratable (⋃ i, classes i)) :=
  ⟨corollary_A_2_countableUnion_mistake classes hinfinite,
    corollary_A_3_countableUnion_query classes hinfinite⟩

/-- Overview Corollary 3.7: positive examples can be removed from both
feedback models. -/
theorem corollary_3_7
    [Countable α] [Infinite α]
    (targets : LanguageClass α)
    (hinfinite : ∀ L, L ∈ targets → L.Infinite) :
    (SourceElementMistakeGeneratable targets →
      ZeroExampleElementMistakeGeneratable targets) ∧
    (SourceSetQueryGeneratable targets →
      ZeroExampleSetQueryGeneratable targets) :=
  ⟨corollary_A_4_zeroExamples_mistake targets hinfinite,
    corollary_A_5_zeroExamples_query targets hinfinite⟩

/-- Overview Corollary 3.8: eventually correct mistake and query feedback
have exactly the countable-inner-cover generability boundary. -/
theorem corollary_3_8
    [Countable α] [Infinite α]
    (targets : LanguageClass α)
    (hinfinite : ∀ L, L ∈ targets → L.Infinite) :
    (EventuallyCorrectMistakeGeneratable targets ↔
      HasCountableInnerCover targets) ∧
    (EventuallyCorrectQueryGeneratable targets ↔
      HasCountableInnerCover targets) :=
  ⟨theorem_A_6_eventuallyCorrectMistake_characterization
      targets hinfinite,
    theorem_A_7_eventuallyCorrectQuery_characterization
      targets hinfinite⟩

/-- Theorem 3.9. Without feedback, set and element generation in the limit are
equivalent for classes of infinite languages over a countably infinite universe.
The element-to-set direction uses the finite-witness argument in
`FiniteWitnessConversion.lean`. The paper's proof uses the self-locking claim
in Appendix Lemma A.8. Its counterexample, `NoFeedbackLockingGap.appendix_A_8_not_derivable`,
gives a fresh, successful generator with an exact presentation that has no self-locking prefix. -/
theorem theorem_3_9 [Countable α] [Infinite α] (targets : LanguageClass α)
    (hinfinite : UUS targets) :
    SetGeneratableInLimit targets ↔ GeneratableInLimit targets :=
  noFeedback_generation_iff_set_generation targets hinfinite

/-- Theorem 3.10, including all three separation and compatibility examples.
The concrete witness universes are countably infinite. -/
theorem theorem_3_10 [Countable α] [Infinite α] (H : LanguageClass α) (hH : UUS H) :
    (HasFiniteInnerCover H → GeneratableInLimit H) ∧
    (GeneratableInLimit H → HasCountableInnerCover H) ∧
    (∃ K : LanguageClass LiRamanTewari.CountableUnionUniverse,
      UUS K ∧ HasCountableInnerCover K ∧ ¬GeneratableInLimit K) ∧
    (∃ K : LanguageClass ℕ, UUS K ∧ GeneratableInLimit K ∧ HasCountableInnerCover K) ∧
    (∃ K : LanguageClass (ℕ × ℕ), UUS K ∧ GeneratableInLimit K ∧ ¬HasFiniteInnerCover K) :=
  ⟨theorem_A_9, theorem_A_10 hH, theorem_A_11, theorem_A_12, theorem_A_13⟩

end GenLimit.FeedbackQueries.Results
