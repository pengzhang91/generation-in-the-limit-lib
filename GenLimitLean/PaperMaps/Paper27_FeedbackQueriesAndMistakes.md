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
- Status: **Theorems 3.1--3.4 and Corollaries 3.6--3.8 are fully formalized at
  the semantic/classical boundary. Theorem 3.9 is partial: its set-to-element
  direction is unconditional, while the reverse is checked under the
  self-locking premise used in Appendix A.6.1. Theorem 3.10 is partial:
  Appendix Theorems A.9, A.12, and A.13 are fully checked, while A.10 and the
  source proof of A.11 depend on the unrestricted Theorem 3.9 conversion.**
- The current development assumes a countable infinite universe and classes
  of infinite languages explicitly. It does not claim a machine-level
  implementation, computability, query complexity, or running-time bound.
- No completed human statement-correspondence audit is claimed. The locally
  inspected source snapshot has SHA-256
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
| Theorem 3.9; Appendix Lemma A.8 | `Results.theorem_3_9_set_to_element`, `Results.theorem_3_9_of_selfLocking`, and `Results.theorem_3_9_appendix_A_8_gap` in [`Results/Overview.lean`](../GenLimit/Paper27_FeedbackQueriesAndMistakes/Results/Overview.lean), backed by [`NoFeedbackEquivalence.lean`](../GenLimit/Paper27_FeedbackQueriesAndMistakes/NoFeedbackEquivalence.lean) and [`NoFeedbackLockingGap.lean`](../GenLimit/Paper27_FeedbackQueriesAndMistakes/NoFeedbackLockingGap.lean) | Partial | Projection from an eventually correct infinite set output to a fresh element is fully checked. The self-simulation construction proves the reverse from the exact self-locking premise used in the appendix. The source's Lemma A.8 claims this premise for every fixed presentation after freshening, but Lean constructs a fresh singleton-class generator that succeeds on every presentation and has one presentation with no self-locking prefix. This refutes that proof step, not the headline equivalence itself. |
| Theorem 3.10(1); Appendix Theorem A.9 | `Results.theorem_3_10_finiteInnerCover_sufficient` in [`Results/Overview.lean`](../GenLimit/Paper27_FeedbackQueriesAndMistakes/Results/Overview.lean), backed by [`NoFeedbackInnerCovers.lean`](../GenLimit/Paper27_FeedbackQueriesAndMistakes/NoFeedbackInnerCovers.lean) | Full at the semantic/classical boundary | A finite inner cover embeds the target class into a finite union of upward cones. Lean reuses P02's finite-cone generation theorem and restricts its generator to the original class. |
| Theorem 3.10(2); Appendix Theorem A.10 | — | Open / deliberately deferred | The source proof first invokes unrestricted Theorem 3.9 to obtain a set generator and then enumerates its possible outputs. That conversion is not available after the Appendix Lemma A.8 gap; no replacement proof is attempted here. |
| Theorem 3.10, first separation; Appendix Theorem A.11 | — | Open / deliberately deferred | The source proof invokes A.10 for the two generatable classes in a known finite-union counterexample. Consequently the proof inherits the same unresolved dependency. |
| Theorem 3.10, countable-cover example; Appendix Theorem A.12 | `Results.theorem_3_10_countableInnerCover_example` in [`Results/Overview.lean`](../GenLimit/Paper27_FeedbackQueriesAndMistakes/Results/Overview.lean), backed by [`NoFeedbackInnerCovers.lean`](../GenLimit/Paper27_FeedbackQueriesAndMistakes/NoFeedbackInnerCovers.lean) | Full at the semantic/classical boundary | Lean first proves the stronger reusable fact that every countable UUS class over a countably infinite universe is generatable and has a countable inner cover, reusing P02's countable-class generation result. The public source wrapper supplies an explicit singleton witness. |
| Theorem 3.10, no-finite-cover example; Appendix Theorem A.13 | `Results.theorem_3_10_noFiniteInnerCover_example` in [`Results/Overview.lean`](../GenLimit/Paper27_FeedbackQueriesAndMistakes/Results/Overview.lean), backed by [`NoFeedbackInnerCovers.lean`](../GenLimit/Paper27_FeedbackQueriesAndMistakes/NoFeedbackInnerCovers.lean) | Full at the semantic/classical boundary | This follows the source's vertical fibers `L_i = {(i,j) | j ∈ ℕ}` on `ℕ × ℕ`. The first sample identifies the fiber, and a finite family of infinite cover members can represent only finitely many pairwise-disjoint fibers. |
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

## Remaining formalization work and deferrals

1. **Deliberately deferred:** do not continue proof search for the
   unrestricted element-to-set direction of Theorem 3.9, and do not construct
   further counterexamples. The existing kernel-checked Appendix Lemma A.8
   counterexample is retained as the record of the source proof gap. Revisit
   this item only if a corrected source statement or an independent new proof
   becomes available.
2. **Deliberately deferred:** Appendix Theorem A.10 and the source proof of
   A.11, both of which depend on the unrestricted Theorem 3.9 conversion.
   Appendix Theorems A.9, A.12, and A.13 are complete.
3. Only after an explicit effective model is introduced, connect the
   semantic strategies to the paper's machine-level and complexity claims.
4. Complete a human statement-correspondence audit before promoting the
   current AI-assisted mapping to human-audited status.

Every P27 declaration currently exposed through `Results/Overview.lean` is
kernel-checked and the P27 development contains no `sorry` or `admit`.
