# Paper 27: Language Generation with Feedback: Queries and Mistakes

This map records the correspondence between Steve Hanneke, Amin Karbasi,
Anay Mehrotra, and Grigoris Velegkas, *Language Generation with Feedback:
Queries and Mistakes*, and the Lean development under
`GenLimit.Paper27_FeedbackQueriesAndMistakes`.

## Source edition and scope

- Formalization source: the ICML 2026 OpenReview record, forum
  `jvfXyIcQ8a`.
- Lean umbrella: `GenLimit.Paper27_FeedbackQueriesAndMistakes`.
- Main-results entry point:
  [`Results/Overview.lean`](../GenLimit/Paper27_FeedbackQueriesAndMistakes/Results/Overview.lean).
- All nine Section 3 theorems and corollaries have semantic Lean proofs, including both directions of 3.9 and all five clauses of 3.10. Appendix Lemma A.8 has a separate counterexample.
- The current development assumes a countable infinite universe and classes
  of infinite languages explicitly. It does not claim a machine-level
  implementation, computability, query complexity, or running-time bound.
- Shuangping Li completed a Level 1 human statement audit of twelve Overview
  statements on 13 November 2026 at checkpoint `a19851f`; see item 4 below.
  The locally inspected source snapshot has SHA-256
  `e3467ab76be2eae001490a43e461865d2c704633e2656bd05ff2eb477b4b1319`,
  pinned in the registry metadata.

## Claim-to-Lean correspondence

| Paper item | Lean declaration / file | Coverage | Qualification |
|---|---|---|---|
| Definition 4 | `CountableInnerCover`, `HasCountableInnerCover` in [`Definitions.lean`](../GenLimit/Paper27_FeedbackQueriesAndMistakes/Definitions.lean) | Full semantic interface | A countable cover is represented as `ℕ → Set α`; every cover member is infinite and every target contains at least one cover member. Repetition is harmless. |
| Theorem 3.1 | `Results.theorem_3_1` in [`Results/Overview.lean`](../GenLimit/Paper27_FeedbackQueriesAndMistakes/Results/Overview.lean), delegating to `theorem_3_1_elementMistake_characterization` in [`ElementMistake.lean`](../GenLimit/Paper27_FeedbackQueriesAndMistakes/ElementMistake.lean) | Full at the semantic/classical boundary | Element-valued generation with truthful mistake feedback is equivalent to the existence of a countable inner cover. |
| Theorem 3.2 | `Results.theorem_3_2` in [`Results/Overview.lean`](../GenLimit/Paper27_FeedbackQueriesAndMistakes/Results/Overview.lean), delegating to `theorem_3_2_setElementMistake_equivalence` in [`SourceSetMistake.lean`](../GenLimit/Paper27_FeedbackQueriesAndMistakes/SourceSetMistake.lean) | Full at the semantic/classical boundary | The source-faithful set- and element-valued mistake-feedback models generate exactly the same classes. |
| Theorem 3.3 | `Results.theorem_3_3` in [`Results/Overview.lean`](../GenLimit/Paper27_FeedbackQueriesAndMistakes/Results/Overview.lean), delegating to `theorem_3_3` in [`SourceQuerySeparation.lean`](../GenLimit/Paper27_FeedbackQueriesAndMistakes/SourceQuerySeparation.lean) | Full at the semantic/classical boundary | The source's class on `ℕ` is represented by the equivalent zero-based partition `Nat.divModEquiv 3`. The source-timed element strategy queries the indicator of a wholly unseen block and emits the certified pair or singleton point. The set-query impossibility diagonalizes against every countable inner cover and invokes Theorem 3.4. [`QuerySeparation.lean`](../GenLimit/Paper27_FeedbackQueriesAndMistakes/QuerySeparation.lean) remains a materially different auxiliary model and is not the source theorem. |
| Theorem 3.4 | `Results.theorem_3_4` in [`Results/Overview.lean`](../GenLimit/Paper27_FeedbackQueriesAndMistakes/Results/Overview.lean), delegating to `theorem_3_4_sourceSetQuery_characterization` in [`SourceQuery.lean`](../GenLimit/Paper27_FeedbackQueriesAndMistakes/SourceQuery.lean) | Full at the semantic/classical boundary | Source-timed set generation with one membership query per round is equivalent to the same countable-inner-cover condition. |
| Corollary 3.6 / Corollaries A.2--A.3 | `Results.corollary_3_6` in [`Results/Overview.lean`](../GenLimit/Paper27_FeedbackQueriesAndMistakes/Results/Overview.lean), backed by [`CountableUnion.lean`](../GenLimit/Paper27_FeedbackQueriesAndMistakes/CountableUnion.lean) | Full at the semantic/classical boundary | `CountableInnerCover.iUnion` flattens the component covers with `Nat.pair`; Theorems 3.1 and 3.4 then give countable-union closure in the mistake- and query-feedback models. |
| Corollary 3.7 / Corollaries A.4--A.5 | `Results.corollary_3_7` in [`Results/Overview.lean`](../GenLimit/Paper27_FeedbackQueriesAndMistakes/Results/Overview.lean), backed by [`ZeroExamples.lean`](../GenLimit/Paper27_FeedbackQueriesAndMistakes/ZeroExamples.lean) | Full at the semantic/classical boundary | The zero-example interfaces literally omit the positive-example argument. The mistake construction sees only prior mistake bits; the query construction sees only query answers and reuses the fair one-query scheduler. |
| Definitions 5--7; Corollary 3.8 / Theorems A.6--A.7 | `Results.corollary_3_8` in [`Results/Overview.lean`](../GenLimit/Paper27_FeedbackQueriesAndMistakes/Results/Overview.lean), backed by [`EventuallyCorrect.lean`](../GenLimit/Paper27_FeedbackQueriesAndMistakes/EventuallyCorrect.lean) | Full at the semantic/classical boundary | The model quantifies over arbitrary example streams and external Boolean streams that agree with the interaction's correct bits after an arbitrary finite prefix. Lean uses an infinitely repeated cover and removes queried points from set outputs; this proves the published characterization but is an alternative semantic robustification rather than a line-by-line implementation of the appendix's finite-expansion construction. |
| Theorem 3.9 and Lemma A.8 | `Results.theorem_3_9`, `NoFeedbackLockingGap.appendix_A_8_not_derivable` | Full equivalence and separate refutation | Conversion to finite witnesses normalizes arbitrary sequence-dependent element generators. At each stage the active common core minus the observed points supplies an infinite set. |
| Theorem 3.10(1); Appendix Theorem A.9 | `Results.theorem_3_10` in [`Results/Overview.lean`](../GenLimit/Paper27_FeedbackQueriesAndMistakes/Results/Overview.lean), proved by `theorem_A_9` in [`NoFeedbackInnerCovers.lean`](../GenLimit/Paper27_FeedbackQueriesAndMistakes/NoFeedbackInnerCovers.lean) | Full at the semantic/classical boundary | A finite inner cover embeds the target class into a finite union of upward cones. Lean reuses P02's finite-cone generation theorem and restricts its generator to the original class. |
| Theorem 3.10(2), A.10 | `theorem_A_10`, `Results.theorem_3_10` | Full | The set generator has at most countably many finite transcripts. Every target contains one of its infinite outputs. |
| Theorem 3.10, first separation, A.11 | `theorem_A_11`, `Results.theorem_3_10` | Full | The countable union of P02 upward cones has a countable inner cover and fails ordinary generation. |
| Theorem 3.10, countable-cover example; Appendix Theorem A.12 | `Results.theorem_3_10` in [`Results/Overview.lean`](../GenLimit/Paper27_FeedbackQueriesAndMistakes/Results/Overview.lean), proved by `theorem_A_12` in [`NoFeedbackInnerCovers.lean`](../GenLimit/Paper27_FeedbackQueriesAndMistakes/NoFeedbackInnerCovers.lean) | Full at the semantic/classical boundary | Lean first proves the stronger reusable fact that every countable UUS class over a countably infinite universe is generatable and has a countable inner cover, reusing P02's countable-class generation result. `theorem_A_12` uses the singleton class containing the whole universe. |
| Theorem 3.10, no-finite-cover example; Appendix Theorem A.13 | `Results.theorem_3_10` in [`Results/Overview.lean`](../GenLimit/Paper27_FeedbackQueriesAndMistakes/Results/Overview.lean), proved by `theorem_A_13` in [`NoFeedbackInnerCovers.lean`](../GenLimit/Paper27_FeedbackQueriesAndMistakes/NoFeedbackInnerCovers.lean) | Full at the semantic/classical boundary | This follows the source's vertical fibers `L_i = {(i,j) | j ∈ ℕ}` on `ℕ × ℕ`. The first sample identifies the fiber, and a finite family of infinite cover members can represent only finitely many pairwise-disjoint fibers. |
| Auxiliary feedback normalizations | [`MistakeFeedback.lean`](../GenLimit/Paper27_FeedbackQueriesAndMistakes/MistakeFeedback.lean), [`QueryFeedback.lean`](../GenLimit/Paper27_FeedbackQueriesAndMistakes/QueryFeedback.lean), [`AdaptiveQueryNormalization.lean`](../GenLimit/Paper27_FeedbackQueriesAndMistakes/AdaptiveQueryNormalization.lean), [`PositiveSequence.lean`](../GenLimit/Paper27_FeedbackQueriesAndMistakes/PositiveSequence.lean), and [`QueryScheduling.lean`](../GenLimit/Paper27_FeedbackQueriesAndMistakes/QueryScheduling.lean) | Supporting infrastructure | Whole-set-validity, square-batch, adaptive-to-complete-table, finite-positive-sequence, and pre-sample scheduling results are useful semantic normal forms. They are not registered as additional source headline theorems. |

## Shared infrastructure and cross-paper reuse

- [`Core/Text.lean`](../GenLimit/Core/Text.lean) owns the ordered finite
  positive history. P27's `streamPrefix` is a compatibility abbreviation for
  `GenLimit.textPrefix`, not a second implementation.
- [`Core/SetGeneration.lean`](../GenLimit/Core/SetGeneration.lean) owns the
  generic infinite-set generator interface and the unconditional
  set-to-element projection used by Theorem 3.9. P17 retains compatibility
  abbreviations and exact bridge lemmas rather than a duplicate public API.
- [`Paper02_LearningTheory/FiniteConeCover.lean`](../GenLimit/Paper02_LearningTheory/FiniteConeCover.lean)
  supplies the stronger finite-upward-cone result used by Appendix A.9.
  [`Paper02_LearningTheory/NonuniformCharacterization.lean`](../GenLimit/Paper02_LearningTheory/NonuniformCharacterization.lean)
  supplies countable-class generation for the reusable A.12 argument. P27
  adds only its inner-cover packaging and source-facing wrappers.
- [`Support/EnumerationProgress.lean`](../GenLimit/Support/EnumerationProgress.lean)
  supplies the infinite enumeration and progress facts used in the
  constructions. P27 no longer reaches through an old P06 module path for
  this neutral infrastructure.
- [`Support/Locking.lean`](../GenLimit/Support/Locking.lean) supplies the
  generic locking-sequence theorem used by the necessity direction of
  Theorem 3.1. P27 does not import a P14-local copy.
- That generic locking theorem does not imply Appendix Lemma A.8's stronger
  per-presentation, all-finite-continuations self-locking assertion.
  [`NoFeedbackLockingGap.lean`](../GenLimit/Paper27_FeedbackQueriesAndMistakes/NoFeedbackLockingGap.lean)
  records the distinction with an explicit counterexample.
- Paper-local files retain the feedback state machines, replay arguments,
  query scheduling, and the countable-inner-cover characterization. These
  concepts are specific to P27 and are not moved into Core.
- [`SourceQuerySeparation.lean`](../GenLimit/Paper27_FeedbackQueriesAndMistakes/SourceQuerySeparation.lean)
  reuses the source-timed set-query API and Theorem 3.4. Its element-valued
  companion interface and concrete three-point-block witness remain
  paper-local.
- [`CountableUnion.lean`](../GenLimit/Paper27_FeedbackQueriesAndMistakes/CountableUnion.lean)
  reuses the two characterization theorems rather than constructing new
  union generators from scratch.
- [`ZeroExamples.lean`](../GenLimit/Paper27_FeedbackQueriesAndMistakes/ZeroExamples.lean)
  erases unused positive inputs from the existing fair query scheduler.
- [`EventuallyCorrect.lean`](../GenLimit/Paper27_FeedbackQueriesAndMistakes/EventuallyCorrect.lean)
  keeps feedback-corruption semantics paper-local. It does not misuse Core's
  finite-contamination API, which concerns corrupted example streams rather
  than corrupted feedback bits.

## Independent proof and audit history

The unrestricted reverse direction uses the finite-witness characterization of Xiaoyu Li, Andi Han, Jiaojiao Jiang and Junbin Gao. The six modules under `GenLimit/FiniteWitness` are from their Apache-2.0 reference release at revision `0b3178f0`. The paper-specific conversion, output enumeration, and separation witness are in [FiniteWitnessConversion.lean](../GenLimit/Paper27_FeedbackQueriesAndMistakes/FiniteWitnessConversion.lean). [Characterization paper](https://arxiv.org/abs/2609.10525), [reference release](https://github.com/xiaoyulics/language-generation-characterization/tree/0b3178f0).

Shuangping Li completed a Level 1 human audit of the Overview statements
   of Theorems 3.1--3.4, Corollaries 3.6--3.8, the set-to-element direction of
   Theorem 3.9, the Appendix Lemma A.8 counterexample, and Theorem 3.10
   components A.9, A.12, and A.13 on 13 November 2026 at checkpoint
   `a19851f`; the
   [human-audit ledger](../AuditRecords/Human/README.md#27-language-generation-with-feedback-section-3-results-level-1)
   records the scope. `theorem_3_9_of_selfLocking`, whose premise fails even
   for a one-language class, and construction/proof correspondence are
   outside that audit.

Every P27 declaration currently exposed through `Results/Overview.lean` is
kernel-checked and the P27 development contains no `sorry` or `admit`.
