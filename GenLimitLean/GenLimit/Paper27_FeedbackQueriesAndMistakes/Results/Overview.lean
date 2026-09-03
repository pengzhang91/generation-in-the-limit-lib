import GenLimit.Paper27_FeedbackQueriesAndMistakes.ElementMistake
import GenLimit.Paper27_FeedbackQueriesAndMistakes.SourceSetMistake
import GenLimit.Paper27_FeedbackQueriesAndMistakes.SourceQuery
import GenLimit.Paper27_FeedbackQueriesAndMistakes.SourceQuerySeparation
import GenLimit.Paper27_FeedbackQueriesAndMistakes.CountableUnion
import GenLimit.Paper27_FeedbackQueriesAndMistakes.ZeroExamples
import GenLimit.Paper27_FeedbackQueriesAndMistakes.EventuallyCorrect
import GenLimit.Paper27_FeedbackQueriesAndMistakes.NoFeedbackEquivalence
import GenLimit.Paper27_FeedbackQueriesAndMistakes.NoFeedbackLockingGap
import GenLimit.Paper27_FeedbackQueriesAndMistakes.NoFeedbackInnerCovers

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
The unrestricted reverse implication is deliberately deferred.  Of Theorem
3.10's five Appendix components, A.9, A.12, and A.13 are fully checked without
Theorem 3.9: finite inner covers suffice, a generatable class with a countable
inner cover exists, and a generatable class without a finite inner cover
exists.  A.10 and the source proof of A.11 depend on the unrestricted Theorem
3.9 conversion and remain open.  The development is semantic and makes no
machine-level computability or running-time claim.
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

/-- The fully checked set-to-element direction of no-feedback Theorem 3.9. -/
theorem theorem_3_9_set_to_element
    {targets : LanguageClass α} :
    SetGeneratableInLimit targets → GeneratableInLimit targets :=
  setGeneratableInLimit_implies_generatableInLimit

/-- Theorem 3.9 under the explicit self-locking normal-form premise used by
Appendix A.6.1 for its element-to-set direction. -/
theorem theorem_3_9_of_selfLocking
    [Infinite α] [DecidableEq α]
    (targets : LanguageClass α)
    (hnormal : ∀ gen, IsLimitGenerator gen targets →
      SelfLocksAlongEveryPresentation (freshenedGenerator gen) targets) :
    SetGeneratableInLimit targets ↔ GeneratableInLimit targets :=
  GenLimit.FeedbackQueries.theorem_3_9_of_selfLocking targets hnormal

/-- Appendix Lemma A.8's unrestricted inference is false for ordered-history
generators: a fresh successful generator may have a presentation with no
self-locking prefix. -/
theorem theorem_3_9_appendix_A_8_gap :
    IsLimitGenerator NoFeedbackLockingGap.generator
        ({NoFeedbackLockingGap.target} :
          LanguageClass NoFeedbackLockingGap.GapUniverse) ∧
      EverywhereFresh NoFeedbackLockingGap.generator ∧
      Generic.Presents NoFeedbackLockingGap.basePresentation
        NoFeedbackLockingGap.target ∧
      ¬∃ n, IsSelfLockingHistory NoFeedbackLockingGap.generator
        NoFeedbackLockingGap.target
        (GenLimit.textPrefix NoFeedbackLockingGap.basePresentation n) :=
  NoFeedbackLockingGap.appendix_A_8_not_derivable

/-- Theorem 3.10 / Appendix Theorem A.9: a finite inner cover is sufficient
for no-feedback generation in the limit. -/
theorem theorem_3_10_finiteInnerCover_sufficient
    [Nonempty α] [Countable α]
    {targets : LanguageClass α}
    (hinner : HasFiniteInnerCover targets) :
    GeneratableInLimit targets :=
  GenLimit.FeedbackQueries.theorem_A_9 hinner

/-- Theorem 3.10 / Appendix Theorem A.12: a no-feedback-generatable class
with a countable inner cover exists. -/
theorem theorem_3_10_countableInnerCover_example :
    ∃ targets : LanguageClass ℕ,
      UUS targets ∧ GeneratableInLimit targets ∧
        HasCountableInnerCover targets :=
  GenLimit.FeedbackQueries.theorem_A_12

/-- Theorem 3.10 / Appendix Theorem A.13: a no-feedback-generatable class
without any finite inner cover exists. -/
theorem theorem_3_10_noFiniteInnerCover_example :
    ∃ targets : LanguageClass (ℕ × ℕ),
      UUS targets ∧ GeneratableInLimit targets ∧
        ¬HasFiniteInnerCover targets :=
  GenLimit.FeedbackQueries.theorem_A_13

end GenLimit.FeedbackQueries.Results
