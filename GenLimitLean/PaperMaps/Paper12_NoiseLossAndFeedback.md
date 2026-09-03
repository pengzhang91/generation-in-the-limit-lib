# Paper 12: Language Generation in the Limit — Noise, Loss, and Feedback

This map records the correspondence between Yannan Bai, Debmalya Panigrahi,
and Ian Zhang, *Language Generation in the Limit: Noise, Loss, and Feedback*,
and the Lean development under `GenLimit.Paper12_NoiseLossAndFeedback`.

## Source edition and scope

- Formalization source: [arXiv:2507.15319v2](https://arxiv.org/abs/2507.15319v2),
  version dated 5 February 2026.
- Audited official PDF SHA-256:
  `ef6dc568b5815b6fe052c5dd52bef89d01a1d7d4eed86e946c368305078c42e5`.
- Lean umbrella:
  [`GenLimit.Paper12_NoiseLossAndFeedback`](../GenLimit/Paper12_NoiseLossAndFeedback.lean).
- Main-results entry point:
  [`Results/Overview.lean`](../GenLimit/Paper12_NoiseLossAndFeedback/Results/Overview.lean).
- Machine-readable claim inventory:
  [`registry/papers/P12.json`](../../registry/papers/P12.json).
- Overall status: **Full for the nineteen-group custom claim inventory**.
  The eight summary theorems and the selected detailed definitions,
  algorithms, lemmas, and theorems all have maintained Lean endpoints.
- The development formalizes deterministic semantic mathematics. It does not
  claim an executable representation of arbitrary language classes,
  machine-level computability, runtime bounds, or query-complexity bounds.
- Source correspondence is AI-assisted and each linked declaration is covered
  by the generated kernel audit. No human correspondence certification has
  been recorded.

## Main entry points

- `GenLimit.NoiseLossFeedback.Results.theorem_1_1` through
  `GenLimit.NoiseLossFeedback.Results.theorem_1_8` provide the stable summary
  theorem surface.
- `WithoutSamples.lean`, `NoisyWithoutSamples.lean`, and
  `NoSampleCharacterization.lean` contain the autonomous-generation and noisy
  equivalence results.
- `FiniteOmissionSeparation.lean`, `FiniteNoiseSeparation.lean`, and
  `UnknownFiniteNoiseSeparation.lean` contain the finite-level hierarchies.
- `TotalFeedback.lean`, `InfiniteFeedback.lean`, and `FiniteFeedback.lean`
  contain the mandatory-query, infinite-feedback, and finite-feedback models.
- `FeedbackIdentification.lean` contains Algorithm 6 and summary Theorem 1.8.
- `Repetitions.lean` contains the Appendix A first-occurrence adapter and the
  three repetition-equivalence results.

## Representation and model interfaces

| Paper object | Lean representation |
|---|---|
| Language and language class | `GenLimit.Generic.Language α = Set α` and `LanguageClass α = Set (Language α)` |
| Repetition-free exact presentation | An injective stream whose range covers the target; the paper's inclusive time convention is bridged to Core's finite-prefix convention |
| Noisy enumeration | An injective target-covering stream with finitely many **distinct values** outside the target |
| Omission model | An injective stream contained in the target, with either an infinite observed subset or an explicit finite bound on missing target values |
| Generation without samples | `WithoutSamplesGenerator`, an autonomous injective output stream with uniform or target-dependent eventual correctness |
| Repetition-allowing presentation | A full stream with repetitions; uniform and nonuniform thresholds are measured by distinct observations, while limit success uses raw time |
| Infinite feedback | The source-facing `TotalFeedbackGenerator` issues one membership query every round; an optional-query controller is retained only as proof infrastructure |
| Finite feedback | `HasAtMostQueries` counts the finite set of real queries and `removeFiniteFeedback` simulates the truthful finite transcript from positive data |
| Feedback identification | An explicitly indexed family `ℕ → Language ℕ`; duplicate names are allowed and the conclusion identifies the target extensionally |

## Summary-theorem correspondence

| Paper item | Lean declaration / file | Coverage | Qualification |
|---|---|---|---|
| Theorem 1.1 | `Results.theorem_1_1` in [`Results/Overview.lean`](../GenLimit/Paper12_NoiseLossAndFeedback/Results/Overview.lean) | **Full** | The P12 wrapper transports the concurrent #10 fixed witness from `ℤ` to `ℕ`; P12's source proof is independent, so this is Lean reuse rather than source attribution. |
| Theorem 1.2 | `Results.theorem_1_2` in [`Results/Overview.lean`](../GenLimit/Paper12_NoiseLossAndFeedback/Results/Overview.lean) | **Full with proof repair** | Packages Theorems 4.4--4.5. The reverse reductions use an ordered-prefix continuation because a finite probe `0, …, t` is not by itself a noisy enumeration of an arbitrary target. |
| Theorem 1.3 | `Results.theorem_1_3` in [`Results/Overview.lean`](../GenLimit/Paper12_NoiseLossAndFeedback/Results/Overview.lean) | **Full** | Preserves the nondecreasing subclass cover, union, and infinite-common-core quantifiers. |
| Theorem 1.4 | `Results.theorem_1_4` in [`Results/Overview.lean`](../GenLimit/Paper12_NoiseLossAndFeedback/Results/Overview.lean) | **Full with proof repair** | The same generator and threshold are retained under infinite omissions; Lean supplies the finite-prefix extension omitted from the printed proof. |
| Theorem 1.5 | `Results.theorem_1_5` in [`Results/Overview.lean`](../GenLimit/Paper12_NoiseLossAndFeedback/Results/Overview.lean) | **Full with qualification** | One marker-and-tail class simultaneously realizes both adjacent omission and known-noise separations; this resolves the summary's potentially ambiguous “or/either” wording using the detailed theorems. |
| Theorem 1.6 | `Results.theorem_1_6` in [`Results/Overview.lean`](../GenLimit/Paper12_NoiseLossAndFeedback/Results/Overview.lean) | **Full source repair** | Formalizes the intended known-versus-unknown finite-noise separation after correcting an element/subset typo and phase/time-index defects in the printed diagonal proof. |
| Theorem 1.7 | `Results.theorem_1_7` in [`Results/Overview.lean`](../GenLimit/Paper12_NoiseLossAndFeedback/Results/Overview.lean); `finiteFeedback_iff_noFeedback` in [`FiniteFeedback.lean`](../GenLimit/Paper12_NoiseLossAndFeedback/FiniteFeedback.lean) | **Full** | Infinite mandatory-query feedback is strictly stronger on the fixed witness, while every fixed finite budget has exactly the no-feedback power. The finite-feedback proof uses transcript agreement instead of the source's inconsistent tree-branch convention. |
| Theorem 1.8 | `Results.theorem_1_8` in [`Results/Overview.lean`](../GenLimit/Paper12_NoiseLossAndFeedback/Results/Overview.lean); `algorithmSix` in [`FeedbackIdentification.lean`](../GenLimit/Paper12_NoiseLossAndFeedback/FeedbackIdentification.lean) | **Full for the explicit indexed-family interface** | The source itself writes the countable collection as `C = {L₀,L₁,…}`. A separate native wrapper also obtains an indexing for a nonempty countable extensional class. |

## Detailed-result and definition correspondence

| Paper item | Lean declaration / file | Coverage | Qualification |
|---|---|---|---|
| Definitions 2.8--2.13 | `NoisyEnumeration`, the three noisy success predicates, `languageProjection`, and `classProjection` in [`NoisyWithoutSamples.lean`](../GenLimit/Paper12_NoiseLossAndFeedback/NoisyWithoutSamples.lean) and [`Projection.lean`](../GenLimit/Paper12_NoiseLossAndFeedback/Projection.lean) | **Full semantic interface** | Noise counts distinct out-of-target values because presentations are injective; finite projections are discarded under the standing infinite-language convention. |
| Definitions 4.1--4.3 | `WithoutSamplesGenerator` and the uniform/nonuniform/limit predicates in [`WithoutSamples.lean`](../GenLimit/Paper12_NoiseLossAndFeedback/WithoutSamples.lean) | **Full semantic interface** | Injectivity is built into the autonomous generator; eventual correctness is target membership rather than presentation-relative freshness. |
| Algorithms 1--2 / Theorems 4.4--4.5 | `noisyGeneratorFromWithoutSamples`, `recordSubsequence`, `theorem_4_4`, and `theorem_4_5` in [`NoisyWithoutSamples.lean`](../GenLimit/Paper12_NoiseLossAndFeedback/NoisyWithoutSamples.lean) | **Full with proof repair** | Forward and reverse reductions are present; the reverse direction uses a proved continuation of every ordered injective prefix. |
| Theorem 4.6 / Algorithm 3 / Theorem 4.7 | `theorem_4_6`, `generatorFromInfiniteCoreChain`, and `theorem_4_7` in [`WithoutSamples.lean`](../GenLimit/Paper12_NoiseLossAndFeedback/WithoutSamples.lean) and [`NoSampleCharacterization.lean`](../GenLimit/Paper12_NoiseLossAndFeedback/NoSampleCharacterization.lean) | **Full** | Infinite common intersection characterizes the uniform model; the increasing-core construction gives the countable-class/general-cover form. |
| Definitions 4.8--4.10 / Theorems 4.11--4.12 | `InfiniteOmissionEnumeration`, the two omission-success predicates, `theorem_4_11`, and `theorem_4_12` in [`InfiniteOmissions.lean`](../GenLimit/Paper12_NoiseLossAndFeedback/InfiniteOmissions.lean) | **Full with proof repair** | Lean proves the missing extension of every finite lossy prefix to a full exact presentation before reusing the original generator. |
| Definitions 4.13--4.14 / Lemmas 4.16--4.17 / Theorem 4.15 | The omission-bound predicates and numbered results in [`FiniteOmissionSeparation.lean`](../GenLimit/Paper12_NoiseLossAndFeedback/FiniteOmissionSeparation.lean) | **Full source repair** | The marker-and-tail lower bound uses a repaired Lemma 4.17 premise and corrected phase/time bookkeeping. |
| Definitions 5.1--5.3 and 5.5--5.6 | The known-noise presentation and limit/nonuniform predicates in [`FiniteNoiseSeparation.lean`](../GenLimit/Paper12_NoiseLossAndFeedback/FiniteNoiseSeparation.lean) | **Full semantic interface** | Item 5.4 is a lemma, not a definition. The stream covers the target and the bound concerns range values outside it, not omitted target values. |
| Lemma 5.4 / Theorem 5.7 | `lemma_5_4` and `theorem_5_7` in [`FiniteNoiseSeparation.lean`](../GenLimit/Paper12_NoiseLossAndFeedback/FiniteNoiseSeparation.lean) | **Full** | Projection, isomorphic transport, and the exact adjacent-level marker separation are formalized with the positive generator receiving the known level. |
| Definitions 6.1--6.2 / Algorithm 4 / Theorem 6.3 / Corollary 6.4 | `TotalFeedbackGenerator` and `IsLimitTotalFeedbackGenerator` in [`TotalFeedback.lean`](../GenLimit/Paper12_NoiseLossAndFeedback/TotalFeedback.lean); the constructions and theorems in [`InfiniteFeedback.lean`](../GenLimit/Paper12_NoiseLossAndFeedback/InfiniteFeedback.lean) | **Full mandatory-query realization** | A causal adapter issues dummy query `0` on optional wait/skip rounds, masks those answers, and proves exact output simulation. The printed non-strict cursor behavior is proved separately from the stronger strict-sweep invariant mentioned in the prose. |
| Definitions 6.5--6.6 / Algorithm 5 / Theorem 6.7 | `HasAtMostQueries`, `IsLimitFeedbackGeneratorWithQueries`, `removeFiniteFeedback`, and `theorem_6_7` in [`FiniteFeedback.lean`](../GenLimit/Paper12_NoiseLossAndFeedback/FiniteFeedback.lean) | **Full with proof repair** | A finite real-query-set argument and transcript induction replace the printed proof's inconsistent left/right decision-tree convention. |
| Definitions A.1--A.3 / Algorithm 7 / Lemmas A.4--A.6 | The repetition predicates, `repetitionAdapter`, and `lemma_a_4`--`lemma_a_6` in [`Repetitions.lean`](../GenLimit/Paper12_NoiseLossAndFeedback/Repetitions.lean) | **Full source repair** | First-occurrence filtering removes repetitions. Lean repairs the raw-time/distinct-cardinality mismatch with threshold `T+1`, and repairs A.6's wrong generator type and undefined threshold using a presentation-dependent burn-in. |

## Source qualifications and repairs

The formalization retains the paper's mathematical conclusions, but several
printed proofs need explicit repairs. These are reflected in theorem names,
registry `source_assessment` fields, and the correspondence tables above:

1. The noisy-to-no-sample reverse reductions require a continuation from each
   finite ordered probe prefix to a complete noisy enumeration.
2. The infinite-omission proofs require the analogous continuation from each
   finite lossy prefix to an exact presentation.
3. Lemma 4.17 and the unknown-finite-noise diagonal construction contain
   premise, phase, and time-index defects; Lean formalizes the intended
   marker-and-tail and nested-phase arguments with corrected invariants.
4. Algorithm 4's pseudocode retains its cursor after a positive response,
   whereas one proof sentence describes strict progress. Lean proves the
   literal non-strict controller and a separate strict-sweep invariant, then
   causally totalizes the optional controller to the source's one-query-per-
   round interface.
5. Theorem 6.7's proof reverses its stated decision-tree branch convention.
   Lean instead proves eventual equality of the finite actual-query transcript.
6. Appendix Lemmas A.4--A.6 mix raw time with distinct-observation thresholds;
   A.6 also begins with the wrong generator type and an undefined `d*`. The
   first-occurrence proof uses the appropriate threshold for each model.

These are proof and presentation repairs, not weakened theorem statements.
All nineteen registered claim groups therefore retain full coverage, with the
qualification made visible rather than silently absorbed.

## Shared infrastructure and cross-paper reuse

- [`Core/GenericGeneration.lean`](../GenLimit/Core/GenericGeneration.lean),
  [`Core/ClassGeneration.lean`](../GenLimit/Core/ClassGeneration.lean), and
  [`Core/ClassCovers.lean`](../GenLimit/Core/ClassCovers.lean) provide the
  paper-independent generation and cover vocabulary.
- [`Core/FiniteContamination.lean`](../GenLimit/Core/FiniteContamination.lean)
  separates occurrence-counted noise from distinct-value contamination.
  `Support/FiniteContamination.lean` preserves older compatibility names used
  by P12.
- [`Support/PrefixCompletion.lean`](../GenLimit/Support/PrefixCompletion.lean),
  `Support/Presentations.lean`, `Support/ClassIntersection.lean`, and
  `Support/Renaming.lean` provide reusable completion, intersection, and
  transport arguments. Prefix completion is also used by #17.
- Theorems 1.1 and 1.7 reuse the concurrent #10 union-nonclosure witness
  through explicit P12 wrappers and an `ℤ ≃ ℕ` renaming. P12 does not duplicate
  the witness proof.
- [`Bridges/NoisyExamples.lean`](../GenLimit/Paper12_NoiseLossAndFeedback/Bridges/NoisyExamples.lean)
  proves that P12's injective distinct-value noisy presentation agrees with
  #06's occurrence-counted presentation under injectivity, and relates P12
  Theorem 4.6 to #06 Theorem 3.1.
- The infinite-feedback construction reuses #02 finite closure dimension and
  nonuniform-cover infrastructure. These are proof dependencies rather than
  duplicate P12 source claims.
- Feedback identification reuses the Gold complete-informant elimination
  theorem to analyze the canonical query-all-elements transcript.

## Remaining boundary

There is no missing Lean result inside the declared nineteen-group custom
inventory. The remaining limitations concern a stronger implementation layer:

- arbitrary semantic language classes are not supplied with effective codes
  or decidable membership procedures;
- the classical generators are not extracted as machines;
- the development does not prove runtime or asymptotic query-complexity bounds;
- no human source-to-Lean correspondence audit has been recorded.

The generated `RegistryAudit.lean` checks declaration existence, defining
modules, and the project's axiom allowlist. It does not by itself certify the
paper correspondence described in this map.
