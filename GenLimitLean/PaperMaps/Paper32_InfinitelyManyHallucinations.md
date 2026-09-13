# Paper 32: Generating in the Limit with Infinitely Many Hallucinations

This map records the correspondence between Irene Strauss, Alexandra Butoi,
and Ryan Cotterell, *Generating in the Limit with Infinitely Many
Hallucinations*, and the Lean development under
`GenLimit.Paper32_InfinitelyManyHallucinations`.

## Source edition and scope

- Formalization source: arXiv:2606.28354v1, submitted 8 June 2026.
- Audited PDF SHA-256:
  `67aefbbc734d010380daf4da5d2f19ceed51592e8f9004c322fefc0e43359975`.
- Lean umbrella: `GenLimit.Paper32_InfinitelyManyHallucinations`.
- Main-results entry point:
  [`Results/Overview.lean`](../GenLimit/Paper32_InfinitelyManyHallucinations/Results/Overview.lean).
- Scope: deterministic semantic mathematics over `ℕ`, including finite-set
  exhaustions, precision/recall/tail precision, novelty, sparse schedules,
  and the explicit no-novelty construction.  No executable extraction,
  runtime, or query-complexity result is claimed.
- Overall status: **Theorem 2.1, Lemma 2.2, Proposition 2.4, Proposition 3.3,
  Theorem 4.3, Lemma 4.7, and the appendix parrot baseline are complete.
  Theorem 2.1 makes the source's standing infinite-guess assumption explicit
  and repairs the appendix's finite-valid-part case.  Lemma 4.5 and Theorems
  4.8--4.9 have checked analytic/certificate endgames, while the dynamic
  batched-pod construction and Lemma 4.6 remain open.**

The source works over the Kleene closure of a finite nonempty alphabet.  Lean
uses `ℕ` as an explicit coding of that countably infinite universe.  The
source's displayed generator type receives only the current adversarial set
and previous generated set, although its algorithms maintain earlier input,
counters, chains, intersections, and pods.  Lean therefore makes the state
dependence explicit by giving a generator the finite adversarial history and
previous cumulative guess.  This is a semantic, history-sensitive interface,
not a claim that the printed stateless function type can reconstruct that
history.

## Claim-to-Lean correspondence

| Paper item | Lean declaration / file | Coverage | Qualification |
|---|---|---|---|
| Theorem 2.1 | `Results.theorem_2_1` in [`Results/Overview.lean`](../GenLimit/Paper32_InfinitelyManyHallucinations/Results/Overview.lean), proved in [`BoundedPrecision.lean`](../GenLimit/Paper32_InfinitelyManyHallucinations/BoundedPrecision.lean) | Full source repair | The supremum over target exhaustions satisfying the same pointwise `f` bound equals the guess's membership-side lower precision.  Lean states explicitly the paper's standing assumption that the guess limit is infinite.  The proof separates the finite valid-part case and uses a capacity-preserving sparse completion in the infinite case, avoiding the printed appendix's unjustified exact-cardinality assertion.  The paper's cumulative-capacity divergence assumption is redundant once an infinite `f`-bounded guess is supplied. |
| Lemma 2.2 | `Results.lemma_2_2` in [`Results/Overview.lean`](../GenLimit/Paper32_InfinitelyManyHallucinations/Results/Overview.lean), proved in [`SupremumCharacterizations.lean`](../GenLimit/Paper32_InfinitelyManyHallucinations/SupremumCharacterizations.lean) | Full | For every fixed target exhaustion, the supremum of exhaustion-level lower recall over all guess exhaustions equals the lower coverage ratio of the guess language along that target exhaustion.  This is the source's general exhaustion statement; the ordered-density API remains available for the canonical duplicate-free target order. |
| Proposition 2.4 | `Results.proposition_2_4_single_step` and `Results.proposition_2_4_constant_step` in [`Results/Overview.lean`](../GenLimit/Paper32_InfinitelyManyHallucinations/Results/Overview.lean), proved in [`TailPrecision.lean`](../GenLimit/Paper32_InfinitelyManyHallucinations/TailPrecision.lean) | Full | The single-step value is binary, and every constant-step-bounded tail-precision sequence attains its liminf in the precise finite-time sense stated in the source footnote. |
| Definitions 3.1--3.2 and Proposition 3.3 | `EventuallyValid`, `TailPrecisionOneFromFiniteTime`, and `Results.proposition_3_3` | Full semantic interface and theorem | Empty batches have step precision one, exactly as in the source.  The proposition proves the equivalence with eventual validity at the exhaustion trace level. |
| Definitions 3.4 and 3.7 | `GeneratorNovel`, `Novel`, `novelHistory`, and `GammaNovel` in [`Definitions.lean`](../GenLimit/Paper32_InfinitelyManyHallucinations/Definitions.lean) | Full semantic interface | `GeneratorNovel` is the literal raw-batch constraint.  `Novel` is its extensional trace consequence; `GeneratorNovel.traceNovel` proves the implication.  Lean counts distinct cumulative generated values for fractional novelty, matching the source's increasing finite-set exhaustions. |
| Restated Theorems 3.5--3.6 | `Results.theorem_3_5_fixed_pod_endgame`, imported from P15 | Partial / dependency | P32 does not duplicate the earlier Kleinberg--Wei result.  P15 checks the fixed-pod limiting passage for Theorem 3.5 but not the complete growing-pod run, and the matching upper theorem is not complete there. |
| Definitions 4.1--4.2 and existence of `γ`-admissible schedules | `ExplorationSet`, `GammaAdmissible`, `quadraticExplorationSet`, and `Results.gamma_admissible_exploration_exists` in [`Exploration.lean`](../GenLimit/Paper32_InfinitelyManyHallucinations/Exploration.lean) | Full specialization | Lean uses the quadratic schedule `M(k+1)^2` rather than the source's exponential example and proves its zero prefix density and every finite-prefix quota. |
| Algorithm / Theorem 4.3 | `Results.theorem_4_3` in [`Results/Overview.lean`](../GenLimit/Paper32_InfinitelyManyHallucinations/Results/Overview.lean), proved in [`NoNoveltyExploration.lean`](../GenLimit/Paper32_InfinitelyManyHallucinations/NoNoveltyExploration.lean) | Full specialization | A concrete history-sensitive generator schedules exploration by crossed adversary-cardinality thresholds, fills unused capacity with adversarial increments, preserves every `f` bound, covers the whole `ℕ` universe, and has precision and recall one.  This proves the source theorem at the normalized countable-universe interface; it is an extensionally justified construction rather than a line-by-line transcription of the appendix pseudocode. |
| Lemma 4.5 | `Results.lemma_4_5_of_trace_certificate` in [`Results/Overview.lean`](../GenLimit/Paper32_InfinitelyManyHallucinations/Results/Overview.lean), backed by [`Certificates.lean`](../GenLimit/Paper32_InfinitelyManyHallucinations/Certificates.lean) | Partial | The exact `1/(k+1)` ordered-density endgame, trace novelty, precision, and tail-precision conclusions are checked from a `BatchedPodsCertificate`.  The dynamic chain/pod machine has not been proved to produce that certificate or the stronger raw-batch `GeneratorNovel` predicate. |
| Lemma 4.6 | No source-shaped Lean endpoint | Open | The matching adaptive sparse-repetition upper-bound construction has not been formalized. |
| Lemma 4.7 | `Results.lemma_4_7` in [`Results/Overview.lean`](../GenLimit/Paper32_InfinitelyManyHallucinations/Results/Overview.lean), proved in [`Recall.lean`](../GenLimit/Paper32_InfinitelyManyHallucinations/Recall.lean) | Full | Reuses the shared exact complement identity `lowerDensity (K \ A) = 1 - upperDensity A`. |
| Algorithm / Theorem 4.8 | `Results.theorem_4_8_of_trace_certificate` in [`Results/Overview.lean`](../GenLimit/Paper32_InfinitelyManyHallucinations/Results/Overview.lean) | Partial | Lean checks sparse-error precision and the `max (1-β) (α/3)` recall assembly from explicit trace-novelty obligations.  The two-batched safe pod run and its raw-batch `GeneratorNovel` proof are still open. |
| Algorithm / Theorem 4.9 and its full-exhaustion corollary | `Results.theorem_4_9_of_trace_certificate` in [`Results/Overview.lean`](../GenLimit/Paper32_InfinitelyManyHallucinations/Results/Overview.lean) | Partial | Lean derives finite-prefix `γ`-novelty, recall one, and precision one from a `GammaNoveltyCertificate`.  The admissible exploration schedule is concrete, but the source's complete safe-pod trace has not been constructed. |
| Appendix theorem: no novelty with perfect tail precision | `Results.appendix_valid_generation_without_novelty` in [`Results/Overview.lean`](../GenLimit/Paper32_InfinitelyManyHallucinations/Results/Overview.lean), proved in [`NoNovelty.lean`](../GenLimit/Paper32_InfinitelyManyHallucinations/NoNovelty.lean) | Full specialization | The explicit parrot generator preserves the adversary's bound and recall and attains precision and tail precision one for an infinite valid adversarial limit. |
| Appendix lemma: tail precision one implies precision one | `Results.tail_precision_one_finite_guess_counterexample` in [`Results/Overview.lean`](../GenLimit/Paper32_InfinitelyManyHallucinations/Results/Overview.lean), proved in [`Diagnostics.lean`](../GenLimit/Paper32_InfinitelyManyHallucinations/Diagnostics.lean) | Source diagnostic | The printed statement omits the infinite-guess hypothesis used by its proof.  A one-error-then-stop exhaustion has lower tail precision one and lower membership precision zero.  The repaired infinite-output implication remains to be packaged. |
| Appendix theorem/corollary for `γ < 1` with perfect tail precision | Certificate infrastructure only | Partial | The novelty accounting and relevant precision/recall endgames are present, but the scheduled repetition plus safe-pod state machine and its tightness construction are not end-to-end Lean theorems. |

## Shared infrastructure and code reuse

- [`Core/OrderedDensity.lean`](../GenLimit/Core/OrderedDensity.lean) supplies
  ordered lower/upper density and now the reusable carrier-complement identity
  used by Lemma 4.7.
- [`Paper15_PartialEnumeration`](../GenLimit/Paper15_PartialEnumeration.lean)
  owns the Kleinberg--Wei pod-density development reused by restated Theorems
  3.5--3.6 and the safe components of Section 4.  P32 does not create a second
  ordered-density API.
- The exhaustion and finite-set batch-generator APIs remain paper-local:
  Core's ordinary generator emits one element from a strict sample prefix and
  does not represent the paper's cumulative finite batches.
- The exploration, precision-envelope, and trace-certificate lemmas isolate
  proof obligations reusable across Theorems 4.3, 4.8, and 4.9 without
  pretending that a certificate is the missing algorithm.

## Remaining formalization work

1. Prove the repaired infinite-output version of the appendix
   tail-precision-to-precision lemma.
2. Complete the P15 growing-pod trace, then lift it to the `k`-batched machine
   needed by Lemma 4.5.
3. Formalize the Lemma 4.6 adaptive upper-bound construction.
4. Instantiate the strict- and relaxed-novelty certificates with the actual
   Algorithms for Theorems 4.8--4.9 and the appendix perfect-tail result.

The P32 declarations contain no `sorry`, `admit`, or paper-local axioms.
This map is an AI-assisted source comparison against the pinned arXiv v1 PDF;
no independent human correspondence audit is claimed.
