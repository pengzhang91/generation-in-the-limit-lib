# Paper 32: Generating in the Limit with Infinitely Many Hallucinations

This map records the correspondence between Irene Strauss, Alexandra Butoi,
and Ryan Cotterell, *Generating in the Limit with Infinitely Many
Hallucinations*, and the Lean development under
`GenLimit.Paper32_InfinitelyManyHallucinations`.

## Current main results

The [public statements](../GenLimit/Paper32_InfinitelyManyHallucinations/Results/Overview.lean) use finite input histories. Section 2.2 assumes an infinite guess limit, and Section 3 assumes an infinite adversarial limit. Single-step exhaustions may pause. The strict lower bounds use target orders compatible with one ambient order.

| Paper result | Kernel-checked result and scope |
|---|---|
| 2.1 | The bounded-exhaustion supremum equals membership precision. The proof also handles a finite valid part of the guess. |
| 2.4 and 3.3 | Bounded-step tail precision is attained. The eventual-validity equivalence holds for new words. On raw output batches, re-emitting one old invalid word violates the equivalence. [Proposition 3.3 counterexample](../GenLimit/Paper32_InfinitelyManyHallucinations/RawValidity.lean) |
| 3.5 | A strictly novel single-step generator attains tail precision and precision one, and at least half the input lower recall. It uses the P39-to-P15 construction and checks novelty at the raw output of every round. [Proof](../GenLimit/Paper32_InfinitelyManyHallucinations/SingleStepSafe.lean) |
| 3.6 | On the full natural-order target every eligible generator admits a single-step adversarial presentation forcing even upper output recall to be at most one half. [Batched counting argument](../GenLimit/Paper32_InfinitelyManyHallucinations/BatchedRace.lean) |
| 4.3 | A concrete generator preserves the input batch bound and attains precision and recall one when novelty is unrestricted. |
| 4.5 | Algorithm 2 achieves strict novelty, precision one and tail precision one. Its claimed lower recall fails for every allowed batch cap, even on a full single-step input with the suggested pod sizes. [Positive clauses](../GenLimit/Paper32_InfinitelyManyHallucinations/PodResults.lean) · [Counterexample](../GenLimit/Paper32_InfinitelyManyHallucinations/PodCounterexample.lean) |
| 4.6 | For each positive batch cap k and each input recall α in [0,1], an adversary forces upper output recall at most α/(k+1) for a strictly novel single-step generator with perfect tail precision on the smaller target. The construction includes α = 0 and α = 1. [Proof](../GenLimit/Paper32_InfinitelyManyHallucinations/PartialRace.lean) |
| 4.8 | Algorithm 6 achieves strict novelty, precision one and recall at least 1 − β. Its α/3 term fails on the full input below. A different generator achieves the stronger bound max(1 − β, α/2), where α and β are lower and upper input recall. [Algorithm 6](../GenLimit/Paper32_InfinitelyManyHallucinations/PodResults.lean) · [Alternative generator](../GenLimit/Paper32_InfinitelyManyHallucinations/StrictExploration.lean) |
| 4.9 and Corollary I.2 | Algorithm 7 satisfies the novelty quota at every prefix and achieves precision and recall one for every admissible schedule, positive pod sizes and exploration enumeration. On exploration rounds it may recover input words. [Proof](../GenLimit/Paper32_InfinitelyManyHallucinations/PodResults.lean) |
| E.1, I.3 and I.4 | `Results.theorem_E_1` combines the copying guarantee and its constant-batch tightness bound. A fractional-novelty generator covers the input with perfect tail precision, giving I.3 and its full-input corollary I.4. For each α in [0,1], the same transcript gives the matching recall ceiling α for every generator with bounded increments and perfect tail precision on the smaller target. [Construction](../GenLimit/Paper32_InfinitelyManyHallucinations/ValidRepetition.lean) · [Sharpness statement](../GenLimit/Paper32_InfinitelyManyHallucinations/Results/Overview.lean) |

### The counterexample to the pod recall bound

1. Fix the natural word order, target ℕ and the ordered family consisting of ℕ followed by ℕ ∖ {0}, ℕ ∖ {1}, and so on. Every finite input excludes only finitely many of these languages, so the filtered consistency list stays infinite throughout this example. Set b₀ = 0 and bₙ₊₁ = (n+1)(bₙ+8)². Present each interval [bₙ,bₙ₊₁) in reverse. This is a bijective single-step text for the whole target, so both input recalls equal one. Use the paper’s example pod sizes 1, 2, 3, … . [Input construction](../GenLimit/Paper32_InfinitelyManyHallucinations/DescendingBlocks.lean)
2. Algorithm 4 filters and compresses the consistency chain. When the chain changes, it resets to the last common infinite level before the first difference. Within a descending block, after a safe update the identified set consists of the words below bₙ together with those at least the last revealed word. Two successive such sets are nested. After the first six rounds of the block, every candidate below bₙ₊₁ is already revealed, so new safe pods cannot capture it. [Chain reset](../GenLimit/Paper32_InfinitelyManyHallucinations/DeletionChain.lean) · [Block estimate](../GenLimit/Paper32_InfinitelyManyHallucinations/PodBlockLoss.lean)
3. Write R(m) for the number of exploration rounds through time m. At most (bₙ+8)² + R(bₙ₊₁) distinct outputs in the entire run lie below bₙ₊₁. Strict novelty prevents later recovery of those already revealed. Dividing by bₙ₊₁ gives at most 1/(n+1) + R(bₙ₊₁)/bₙ₊₁. This tends to zero, both with no exploration (Algorithm 2) and with each source-admissible sparse exploration schedule (Algorithm 6, using the natural exploration order). [Prefix counting and zero-recall proofs](../GenLimit/Paper32_InfinitelyManyHallucinations/PodCounterexample.lean)

Appendix G.1 assigns a missed word to an earlier round at which the very same intersection had already been selected. Algorithm 4 only establishes that the intersection occurs at a common level of two chains. A round's cursor can reset to that level before it has ever selected it. For example, the first block reveals 63 and then 62. Its first identified set is ℕ and its second is {62, 63, …}. During the interior of each much larger block the reset formula above applies again. The counting proof uses all block endpoints to establish the asymptotic violation beyond any finite initialization. [Algorithm 4](https://arxiv.org/html/2606.28354v1#alg4) · [Proof of Lemma G.1](https://arxiv.org/html/2606.28354v1#A7.Thmtheorem1)

Thus Equation (27a) fails for Algorithm 2, and Equation (32) fails for Algorithm 6 on an input where its right-hand side is 1/3. The counterexample concerns the update rules printed in P32 v1. Theorem 3.5 is an existence statement and has an independent proof. Whether another algorithm achieves the general batched lower bound in (27a) is a separate question. [Paper, Sections 4.2 and Appendices F–H](https://arxiv.org/html/2606.28354v1#S4.SS2)

### Proposition 3.3 and repeated raw outputs

Definition 3.2 checks every word returned in a round. Tail precision checks only new words in the cumulative guess. Take the positive integers as the target and enumerate them. A generator that returns the observed positives together with 0 at every round has tail precision exactly one from the second round onward, even though every raw batch contains 0. Both limiting sets are infinite. Lean proves the equivalence for cumulative increments, and also for raw batches under the extra assumption that every batch is disjoint from all previous guesses. [Raw-batch counterexample and repaired equivalence](../GenLimit/Paper32_InfinitelyManyHallucinations/RawValidity.lean)

## Source edition and earlier checkpoint

The remaining sections describe the earlier audited declarations. The new algorithm proofs and counterexamples have received kernel checks. The historical human correspondence review covered the statements listed in its record.

- Source edition [arXiv:2606.28354v1](https://arxiv.org/abs/2606.28354v1), submitted 8 June 2026.
- Audited PDF SHA-256 `67aefbbc734d010380daf4da5d2f19ceed51592e8f9004c322fefc0e43359975`.
- Lean umbrella `GenLimit.Paper32_InfinitelyManyHallucinations`.

The source works over the Kleene closure of a finite nonempty alphabet.  Lean
uses `ℕ` as an explicit coding of that countably infinite universe.  The
source's displayed generator type receives only the current adversarial set
and previous generated set, although its algorithms maintain earlier input,
counters, chains, intersections, and pods.  Lean therefore makes the state
dependence explicit by giving a generator the finite adversarial history and
previous cumulative guess.  This is a semantic, history-sensitive interface,
not a claim that the printed stateless function type can reconstruct that
history.

## Claim-to-Lean correspondence at the earlier checkpoint

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
| Appendix Theorem E.1: copying guarantee and c-step tightness | `Results.appendix_valid_generation_without_novelty` in [`Results/Overview.lean`](../GenLimit/Paper32_InfinitelyManyHallucinations/Results/Overview.lean), proved in [`NoNovelty.lean`](../GenLimit/Paper32_InfinitelyManyHallucinations/NoNovelty.lean) | Partial: copying guarantee full; tightness open | The same explicit parrot generator preserves the adversary's batch bound and recall and attains precision and tail precision one for an infinite valid adversarial limit. The separate upper-bound/tightness clause for c-step generators with family-wide perfect tail precision is not formalized. |
| Appendix Lemma D.1: tail precision one implies precision one | `Results.appendix_lemma_D_1_of_limit_infinite` and `Results.tail_precision_one_finite_guess_counterexample` in [`Results/Overview.lean`](../GenLimit/Paper32_InfinitelyManyHallucinations/Results/Overview.lean), proved in [`TailPrecision.lean`](../GenLimit/Paper32_InfinitelyManyHallucinations/TailPrecision.lean) and [`Diagnostics.lean`](../GenLimit/Paper32_InfinitelyManyHallucinations/Diagnostics.lean) | Full source-context implication; supplementary boundary diagnostic | Section 2.2 assumes infinite target and guess languages throughout. Lean makes guess infinitude explicit and proves the implication for arbitrary target sets, including the source case. The finite-output example lies outside the standing domain and does not refute Lemma D.1; no source-statement repair is needed. |
| Appendix theorem/corollary for `γ < 1` with perfect tail precision | Certificate infrastructure only | Partial | The novelty accounting and relevant precision/recall endgames are present, but the scheduled repetition plus safe-pod state machine and its tightness construction are not end-to-end Lean theorems. |

The [14 November 2026 adjudication](../AuditRecords/Paper32_InfinitelyManyHallucinations/evidence/adjudication.md)
identified that the earlier D.1 refutation label ignored Section 2.2's global
assumption. The current map and registry correct that attribution; the frozen
audit evidence and existing human-review scope are preserved.

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
  does not represent the paper's cumulative finite batches.  Reusable
  ambient, restricted, and cardinality-clocked exhaustion constructors are
  isolated in
  [`ExhaustionOperations.lean`](../GenLimit/Paper32_InfinitelyManyHallucinations/ExhaustionOperations.lean).
- The exploration, precision-envelope, and trace-certificate lemmas isolate
  proof obligations reusable across Theorems 4.3, 4.8, and 4.9 without
  pretending that a certificate is the missing algorithm.

## Work outstanding at the earlier checkpoint

1. Complete the P15 growing-pod trace, then lift it to the `k`-batched machine
   needed by Lemma 4.5.
2. Formalize the Lemma 4.6 adaptive upper-bound construction.
3. Instantiate the strict- and relaxed-novelty certificates with the actual
   Algorithms for Theorems 4.8--4.9 and the appendix perfect-tail result.
4. Formalize Theorem E.1's c-step tightness clause; the completed copying
   guarantee alone does not establish the whole source theorem.

The P32 declarations contain no `sorry`, `admit`, or paper-local axioms.
This map is an AI-assisted source comparison against the pinned arXiv v1 PDF.
Shuangping Li later completed a Level 1 human statement audit of ten Overview
statements (see the final section).

## Human statement audit

Shuangping Li completed a Level 1 human audit of ten `Results/Overview.lean`
statements and their defining interfaces on 13 November 2026 at checkpoint `c828be2`;
the [human-audit ledger](../AuditRecords/Human/README.md#32-infinitely-many-hallucinations-arxiv-v1-overview-level-1)
records the scope. The Theorem 3.5 endgame, the certificate wrappers for
Lemma 4.5 and Theorems 4.8--4.9, the finite-guess Lemma D.1 diagnostic, and
construction/proof correspondence are outside that audit.
