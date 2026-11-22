# #05 Hallucinations, Breadth, and Stability map

Lean module: `GenLimit.Paper05_HallucinationsBreadthAndStability`.
Declaration namespace: `GenLimit.BreadthCharacterizations`.

## Pinned source

- Alkis Kalavasis, Anay Mehrotra, and Grigoris Velegkas,
  *On Characterizations for Language Generation: Interplay of Hallucinations,
  Breadth, and Stability*.
- Formalization source:
  [arXiv:2412.18530v2](https://arxiv.org/abs/2412.18530v2).
- The website reading list uses the shorter title *Characterizations of
  Language Generation With Breadth* for the same arXiv entry.
- Peng Zhang reported a Level 1 human audit on 12 November 2026 of the three
  semantic Overview declarations listed below and their relevant definitions.
  The [human-audit ledger](../AuditRecords/Human/README.md#05-hallucinations-breadth-and-stability-three-semantic-statements-level-1)
  records the exact non-P38 snapshot and the supplied local PDF SHA-256.
  Other P05 statements and source-conflict findings are outside this review.

## Scope and status

The [P05 Overview](../GenLimit/Paper05_HallucinationsBreadthAndStability/Results/Overview.lean) explicitly states the 10 original numbered theorems and three corollaries from Sections 3–8 of arXiv v2. The [supporting results](../GenLimit/Paper05_HallucinationsBreadthAndStability/Results/Supporting.lean) collect the three propositions, four Section 7 construction lemmas, figures, examples and appendix items. The three headline results in the introduction correspond to Theorems 3.3, 3.8, and 3.15. Lean proves the first two equivalences and the stable approximate-breadth clause of the third. Its stable exact-breadth clause depends on how the support treats previously observed words.

The [P05 registry](../../registry/papers/P05.json) groups the material into **31 claim cards**. Twenty-four have positive proofs under their documented conventions. Seven record counterexamples to a literal statement or a proposed construction. Five of these concern stability, one concerns the rightmost column label in Figures 3 and 4, and one concerns the generator printed in Example 8.12. These are counts of cards. A single theorem can contribute several clauses, and a card can cover more than one paper item.

Section 4 has a second issue independent of freshness. Equation (2) permits finitely many hallucinations in the current exhaustive enumeration. A generator that always enumerates all natural numbers meets that equation for the full target and for each co-singleton. Its range is stable from the start, although this family has no strong tell-tales. Lean proves the weak-tell-tale characterization for stable exhaustive generation on encoded words. [Theorem 4.5 and Equation (2)](https://arxiv.org/html/2412.18530v2#S4.Thmtheorem5)

## Human audit

Peng Zhang's Level 1 review, reported 12 November 2026, covered the following declarations at the reviewed checkpoint.

- `Results.theorem_3_3_semantic` (retired);
- `Results.theorem_3_8_sufficiency_semantic` (retired, sufficiency only);
- `Results.theorem_3_15_approximate_semantic` (retired, approximate breadth over `Nat`).

The statement-relevant definitions are included. The
[applicability manifest](../AuditRecords/Human/Fingerprints/P05_SemanticTheorems3_3_3_8_3_15_Level1.json)
retains the original fingerprints. All three reviewed declarations have been retired. The combined manifest is marked `needs-review`. The current Theorems 3.3, 3.8 and 3.15 include oracle constructions and require a new human review. Construction and
proof correspondence, effective guarantees, Theorem 3.8 necessity, other
Theorem 3.15 clauses and universe transports, and the source-conflict findings
below remain outside this human audit. This record does not change the
formalization coverage or the earlier LLM audit evidence.

## Paper-to-Lean correspondence

| Paper item | Lean declaration | Module | Status |
|---|---|---|---|
| Definition 2.1, raw support validity | `GeneratesInLimitCorrectAt`, `IsLimitGenerator`; diagnostic `emptySupportAlgorithm_isLimitGenerator` | `Definitions`, `SemanticBoundary` | Complete literal validity predicate.  It constrains every produced element but imposes no lower bound on the support; the kernel-checked empty-support regression makes that boundary explicit. |
| Definition 3.1, exact breadth | `ExactBreadthCorrectAt`, `IsExactBreadthGenerator`, `ExactBreadthGeneratable` | `Definitions` | Complete literal fresh-output predicate. |
| Definition 3.2, approximate breadth | `ApproximateBreadthCorrectAt`, `IsApproximateBreadthGenerator`, `ApproximateBreadthGeneratable` | `Definitions` | Complete semantic support predicate. |
| Theorem 3.3 | `Results.theorem_3_3`, `exactBreadthGeneratable_iff_conditionTwo` | `Results.Overview`, `ExactBreadth`, `EffectiveBreadth` | The equivalence holds on a countable alphabet. On encoded words the same statement also gives the exact-breadth sampler for any supplied strong tell-tale enumeration. |
| Theorems 3.5 and 3.10 | `theorem_3_5`, `theorem_3_10` | `Uniqueness` | Common prefix locking gives the uniqueness and finite non-uniqueness lower bounds. |
| Definition 3.7, weak Angluin condition | `IsWeakTellTale`, `WeakAngluinCondition` | `Definitions` | Complete indexed predicate. |
| Theorem 3.8 | `Results.theorem_3_8`, `Results.finite_query_training` | `Results.Overview`, `Results.Supporting`, `Uniqueness`, `CriticalSampler`, `WeakSampling` | Both directions, with membership/subset and membership/weak-tell-tale constructions on encoded words. Each trained index depends only on its finite list of oracle answers. |
| Definition 3.14, stability | `IsStableGenerator` | `Definitions` | Complete literal raw-support stabilization predicate. |
| Theorem 3.15, approximate clause | `Results.theorem_3_15`, `theorem_3_15_approximate_countable` | `StableAndUnambiguous`, `Results.Overview` | Countable-universe equivalence and stable whole-target sampling. |
| Theorem 3.15, exact clause | `Results.theorem_3_15`, literal clause; supporting `no_stable_exactBreadth_for_infinite_family` | `Results.Overview`, `StabilityGap` | Definition 3.1 requires unseen support, whereas Definition 3.14 requires that support to stop changing. The literal conjunction fails on every complete presentation of an infinite target. |
| Corrected stable exact statement | `Results.theorem_3_15`, whole-target clause; internal `stableWholeTargetGeneratable_iff_conditionTwo` | `Results.Overview`, `CorrectedStability` | Whole-target/sample-restored support gives the positive characterization when repetitions are allowed (footnote 3). |
| Theorems 4.3 and 4.5 | `Results.theorem_4_3`, `Results.theorem_4_5`, `theorem_4_5_stable_exhaustive_counterexample` | `Results.Overview`, `StableAndUnambiguous`, `ExhaustiveGeneration` | Both unambiguous clauses and the exhaustive equivalence hold. The stable exhaustive necessity direction fails under Equation (2). |
| Figures 3 and 4 | `figures_3_4_finite_hallucinations`, `figure_3_infinite_present`, `figures_3_4_unrestricted`, `infinite_errors_impossible_on_full_target` | `HallucinationTables` | The first two rows with a finite error allowance are equivalent to weak Angluin, with or without stability. See the table notes below. |
| Theorems 5.2 and 5.3 | `theorem_5_2`, `theorem_5_3` | `StatisticalRates` | IID upper and lower bounds for arbitrary PMFs. The last clause of Theorem 5.3 concerns exact breadth as printed. |
| Corollary 6.1 | `corollary_6_1` | `DiagonalEnumeration` | Given a nonidentifiable family and an approximate-breadth generator, one complete target text has strictly increasing rounds witnessing pairwise distinct proper sublanguages. The witnesses are distinct as sets, even in a family with duplicate indices for a language. |
| Lemma 7.1 and Corollary 7.2 | `lemma_7_1`, `corollary_7_2`, `criticalSampler_oracles` | `CriticalSampler` | One KM last-critical sampler uses membership and subset queries. It achieves exact breadth under strong tell-tales, approximate breadth under weak tell-tales, and fresh infinite coverage in every case. |
| Lemmas 7.3 and 7.7 | `lemma_7_3`, `lemma_7_7` | `WeakSampling`, `ExhaustiveGeneration` | Each algorithm takes an arbitrary valid weak tell-tale enumeration and a membership oracle. The former gives approximate breadth and the latter exhaustive generation. Both have ordinary computability guarantees for computable inputs. |
| Lemma 7.5 | `lemma_7_5` | `ConsistentExhaustive` | The same enumerator satisfies Equation (2) and eventually has its entire range within the unseen target. It uses membership and subset queries. It queries the finite-difference oracle only on strictly nested pairs. |
| Definition 8.3, infinite coverage | `InfiniteCoverageCorrectAt`, `IsInfiniteCoverageGenerator` | `Definitions` | Complete literal valid, unseen, infinite-support predicate. |
| Proposition 8.4 | `proposition_8_4` | `InfiniteCoverage` | Full-support geometric seeds produce infinitely many eventually valid unseen outputs. |
| Example 8.6 and Theorem 8.7 | `Results.example_8_6`, `Results.theorem_8_7` | `Results.Supporting`, `Results.Overview`, `InfiniteCoverage`, `SharedSupport` | The full language and its co-singletons satisfy weak but not strong Angluin. They defeat stable infinite coverage even when the generator may repeat observations. |
| Proposition 8.10 and Corollary 8.11(2) | `Results.proposition_8_10_literal_specification_inconsistent`; supporting `no_stable_infiniteCoverage_for_infinite_family` | `Results.Supporting`, `StabilityGap` | Literal freshness precludes stable coverage. In `FrozenCoverage`, `proposition_8_10_sampleAllowing` and `finite_stableCoverage_membership` realize the sample-allowing versions after d+1 distinct observations. |
| Corollary 8.11(1) | `Results.corollary_8_11`, `no_stable_exactBreadth_for_infinite_family`, `finite_stableWhole_membership` | `Results.Overview`, `StabilityGap`, `FrozenCoverage` | The finite-range membership learner gives the whole-target correction. |
| Example 8.12 | `example_8_12`, `example_8_12_printed_support_fails` | `SharedSupport` | On the stated integer-ray family, the ray starting at the first observation gives stable sample-allowing infinite coverage. The printed support contains 1 forever on a presentation of the ray starting at 3. |
| Proposition 8.14 | `proposition_8_14_sampleAllowing`, `increasing_literal_incompatible` | `IncreasingCoverage` | Integer rays realize the footnote 17 convention. Even eventual monotonicity contradicts literal fresh infinite coverage. |
| Section 8.3, approximate breadth with strictly increasing coverage | `increasing_approximate_wholeTarget`, `increasing_approximate_requires_conditionTwo` | `IncreasingCoverage` | At a stage minimizing the finite number of missing words, any further strict growth would decrease that minimum. The support reaches the whole target and stays there. |
| Observations A.1–A.2 and cited Theorem B.2 | `Results.observation_A_1`, `Results.observation_A_2`, `Results.theorem_B_2_oracle`, `Results.theorem_B_2_effective` | `Results.Supporting` | Unambiguous targets are unique. Two targets compatible with the same exhaustive round differ finitely. Angluin's identification result uses a tell-tale oracle, with effective necessity on uniformly decidable indexed families. |

## Reading Figures 3 and 4

The rows count missed target words or require infinitely many target words in the support. Under the figures’ whole-target convention, the zero-error columns use the 3.3, 3.8, 3.15, 8.4 and 8.7 results according to the row and the presence of stability. The finite-error column permits finitely many extra words. In its top two rows, weak tell-tales suffice even to stabilize on a superset of the target with finitely many extras. In Figure 3 the bottom row follows from a generator with infinitely many valid words and zero errors. [Figure 3](https://arxiv.org/html/2412.18530v2#S4.F3)

The rightmost column is universal when hallucinations are unrestricted. A constant support equal to the whole alphabet proves every row. The label printed under the column requires *infinitely many actual errors*. For a target equal to the entire alphabet every support has zero errors. In the bottom row of Figure 4 the authors leave two characterizations open. With zero errors, Theorem 8.7 proves that some families fail. With a finite error allowance, the paper also leaves universality open. [Figure 4 and its proof sketch](https://arxiv.org/html/2412.18530v2#S4.F4)

## Reuse and ownership

- `SupportAlgorithm` is a P05-local `List α → Set α` interface.  It is not
  moved into Core and does not inherit P03's Boolean support-membership oracle.
- Theorem 3.3 directly reuses
  `GenLimit.Angluin.constantTellTaleApproximation` and
  `semanticLearner_semanticallyIdentifies`; P05 has no duplicate tell-tale
  choice or approximation declarations.
- The constructive half of Theorem 3.8 reuses P04's last-critical-language
  infrastructure, but retains a P05-native support-valued algorithm because
  P04 exhaustive generation allows a different output interface.
- `Relationships` adds a semantic Boolean membership adapter solely to reuse
  P03's `stable_approximateBreadthInLimit_implies_identifiableInLimit`.  The
  adapter uses classical decidability and certifies no implementation.
- Pure P04/P05 comparison statements live in
  `GenLimit.Bridges.Paper04ToPaper05`, outside both native paper umbrellas.
- No P05-specific definition or theorem was added to the lightweight Core.

## Source qualifications exposed by Lean

The following is a Codex-assisted formalization finding, not a named human
audit result:

- The raw Definition 2.1 predicate is support-validity only: the generator
  whose support is always empty satisfies `IsLimitGenerator` for every
  family.  `SemanticBoundary.lean` also verifies that infinite-target exact
  breadth, approximate breadth, and infinite coverage exclude this behavior.
- Literal exact breadth removes the growing observed sample, so its support
  cannot eventually be raw-constant on a complete presentation of an
  infinite language.  This contradicts the exact clause of Theorem 3.15.
- The same raw-stability versus unseen-output conflict makes the literal
  conclusion of Proposition 8.10 and Corollary 8.11(2) impossible.
- The paper's stability discussion informally treats consistent exact support
  as the whole target.  Lean records that convention separately through
  `restoreObserved`.
- For Corollary 8.11, `Results.corollary_8_11_literal_counterexample` exhibits the one-language collection consisting of ℕ. Both literal stability requirements fail already on that finite collection.

These findings await human source-correspondence review.

## Suggested reading order

1. `Definitions.lean` and `SemanticBoundary.lean`
2. `ExactBreadth.lean`
3. `ApproximateBreadth.lean`
4. `Relationships.lean` and `StableApproximate.lean`
5. `StabilityGap.lean`
6. `CorrectedStability.lean`
7. `Results/Overview.lean`
8. `Uniqueness.lean`, `EffectiveBreadth.lean`, and `WeakSampling.lean`
9. `StableAndUnambiguous.lean`, `ExhaustiveGeneration.lean`, and `StatisticalRates.lean`
10. `DiagonalEnumeration.lean`, `CriticalSampler.lean`, and `ConsistentExhaustive.lean`
11. `InfiniteCoverage.lean`, `FrozenCoverage.lean`, `SharedSupport.lean`, `IncreasingCoverage.lean`, and `HallucinationTables.lean`

## Verification

```text
lake build GenLimit.Paper05_HallucinationsBreadthAndStability
lake build GenLimit.Bridges.Paper04ToPaper05
```

No `sorry`, `admit`, or project-defined axiom occurs in the P05 modules.
