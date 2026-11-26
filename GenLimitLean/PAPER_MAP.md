# Paper-to-Lean registry

This file is the repository-level index.  Each paper has its own detailed
map, while cross-paper reuse is recorded separately rather than hidden inside
one paper's development.

## Repository layers

```text
GenLimit.Core       shared semantic foundations
GenLimit.Support    neutral proof infrastructure

GenLimit.Paper00_LanguageIdentification
GenLimit.Paper00A_PositiveDataInference
GenLimit.Paper01_LanguageGeneration
GenLimit.Paper02_LearningTheory
GenLimit.Paper03_HallucinationAndModeCollapse
GenLimit.Paper04_ExploringFacetsOfLanguageGeneration
GenLimit.Paper05_HallucinationsBreadthAndStability
GenLimit.Paper06_NoisyExamples
GenLimit.Paper07_DensityMeasuresForLanguageGeneration
GenLimit.Paper08_HallucinationDetection
GenLimit.Paper09_RepresentativeLanguageGeneration
GenLimit.Paper10_UnionClosednessOfLanguageGeneration
GenLimit.Paper14_ListLanguageIdentification
GenLimit.Paper15_PartialEnumeration
GenLimit.Paper16_ComplexityBarriers
GenLimit.Paper17_InfiniteContamination
GenLimit.Paper18_SafeLanguageGeneration
GenLimit.Paper20_AgnosticLanguageIdentificationAndGeneration
GenLimit.Paper21_GenerationInMetricSpaces
GenLimit.Paper22_LanguageGenerationWithReplay
GenLimit.Paper23_BanachDensityTopologyAndGeometry
GenLimit.Paper26_IdentificationWithComputationalTrace
GenLimit.Paper27_FeedbackQueriesAndMistakes
GenLimit.Paper28_ContrastiveGeneration
GenLimit.Paper29_MistakeBoundedLanguageGeneration
GenLimit.Paper30_TimeSensitiveLanguageGeneration
GenLimit.Paper31_BoundedMemory
GenLimit.Paper32_InfinitelyManyHallucinations
GenLimit.Paper39_DenseGeneration

GenLimit.Bridges  (explicit cross-paper results)
```

- `GenLimit.Core` contains paper-independent definitions and semantic lemmas.
- `GenLimit.Support` contains neutral reusable proof infrastructure that is
  shared across papers but deliberately omitted from the lightweight Core
  umbrella.
- The numbered `GenLimit.PaperID_ShortTitle` modules are independently
  buildable paper paths. Numeric IDs follow the modern reading-list inventory;
  `#0A` is the adjacent foundational Angluin entry between `#0` and `#01`.
  Existing declaration namespaces, including `GenLimit.Angluin`, are retained
  for API compatibility.
- `GenLimit.Bridges` contains declarations whose statements mention both
  identification and generation vocabulary from multiple developments.
- `GenLimit` imports all layers for users who want the whole library.

The filesystem follows the same ownership rule:

```text
GenLimit/Core/           shared definitions, ordered text, identification, and stability
GenLimit/Support/        neutral reusable proof infrastructure kept outside the Core umbrella
GenLimit/Paper00_LanguageIdentification/    #0 abstract, text, and informant identification
GenLimit/Paper00A_PositiveDataInference/    #0A semantic/effective positive-data inference
GenLimit/Paper01_LanguageGeneration/        #01 semantic, observed-set, finite-query, and finite-family proofs
GenLimit/Paper02_LearningTheory/            #02 ordinary, prompted, prediction-proxy, and EUC results
GenLimit/Paper03_HallucinationAndModeCollapse/  #03 online PMF/MOP and statistical identification/generation rates
GenLimit/Paper04_ExploringFacetsOfLanguageGeneration/  #04 non-uniform, membership-query, exhaustive, breadth, and feedback results
GenLimit/Paper05_HallucinationsBreadthAndStability/  #05 exact/approximate breadth, stability, and source-gap results
GenLimit/Paper06_NoisyExamples/             #06 noisy-generation models, characterizations, and appendices
GenLimit/Paper07_DensityMeasuresForLanguageGeneration/  #07 selector, rank forest/fallback, charging, and diagnostics
GenLimit/Paper08_HallucinationDetection/    #08 detection and reduction results
GenLimit/Paper09_RepresentativeLanguageGeneration/  #09 representative generation, group closure, and query impossibility
GenLimit/Paper10_UnionClosednessOfLanguageGeneration/  union witnesses, randomized diagonal, and alternating columns
GenLimit/Paper14_ListLanguageIdentification/        #14 list identification, k-Angluin characterization, and stratification
GenLimit/Paper15_PartialEnumeration/        #15 Algorithm 1, priority run, density, and full-text topology/learners
GenLimit/Paper16_ComplexityBarriers/        #16 CFG, regular, LTT, and non-erasing pattern sample bounds
GenLimit/Paper17_InfiniteContamination/     #17 contamination regimes, priority generation, and density obstructions
GenLimit/Paper18_SafeLanguageGeneration/   #18 safe identification/generation, reductions, impossibility, and infinite differences
GenLimit/Paper19_EffectOfNoise/            #19 noisy generation, separation, and numerical closure dimension
GenLimit/Paper20_AgnosticLanguageIdentificationAndGeneration/  #20 agnostic identification and generation rates
GenLimit/Paper21_GenerationInMetricSpaces/  #21 v2 metric generation, internal closure, union separation, and scale invariance
GenLimit/Paper22_LanguageGenerationWithReplay/  #22 replay generation, Witness Protection, and proper-generation separations
GenLimit/Paper23_BanachDensityTopologyAndGeometry/  #23 absolute density, finite ranks, and finite trees
GenLimit/Paper26_IdentificationWithComputationalTrace/  #26 identification from perfect and corrupted traces
GenLimit/Paper27_FeedbackQueriesAndMistakes/  #27 feedback characterizations and query separation
GenLimit/Paper28_ContrastiveGeneration/     #28 geometry, generation, hierarchy, and corruption
GenLimit/Paper29_MistakeBoundedLanguageGeneration/  #29 weighted mistake bounds and diagnostics
GenLimit/Paper30_TimeSensitiveLanguageGeneration/  #30 randomized timely-density obstructions and sharp upper density
GenLimit/Paper31_BoundedMemory/             #31 memoryless, density, buffer, and incremental results
GenLimit/Paper32_InfinitelyManyHallucinations/  #32 precision, recall, novelty, and sparse exploration
GenLimit/Paper39_DenseGeneration/           #39 exact- and partial-enumeration patient-scope results
GenLimit/Bridges/                           explicit cross-paper comparisons
```

## Formalized papers

| Paper | Formalized result | Lean umbrella | Detailed map | Kernel status |
|---|---|---|---|---|
| **#0 Language Identification** | Theorem 7.1, the three §8 language conclusions, learning-time optimality, §11 index translations, and Appendix I.1–I.9 | `GenLimit.Paper00_LanguageIdentification` | [#0 map](PaperMaps/Paper00_LanguageIdentification.md) | 16 proved under the documented conventions. The printed p. 464 direction is refuted and its reversal proved. |
| **#0A Inductive Inference from Positive Data** | Positive-data inference, tell-tale separations, and conservative learning | `GenLimit.Paper00A_PositiveDataInference` | [#0A map](PaperMaps/Paper00A_PositiveDataInference.md) | All five theorems and three corollaries formalized, plus the semantic characterization |
| **#01 Language Generation** | NeurIPS round-indexed Section 4 guarantee; literal finite-set interface for repeated presentations; proceedings finite-query Theorem 2.1; fixed-sample finite-family Theorem 2.2; robust string-prompt Theorem 7.1; and explicit universe transports | `GenLimit.Paper01_LanguageGeneration` | [#01 map](PaperMaps/Paper01_LanguageGeneration.md) | Theorems 2.1, 2.2, and 7.1 are complete in the documented membership-oracle models; both countable-family distinct-output modifications and the finite-set-only universe transport are proved |
| **#02 Learning Theory** | Ordinary and prompted generation characterizations; closure and sample-complexity bounds; hierarchy separations; finite-cover and EUC results; Theorem 4.1 in the IID PAC and online mistake models | `GenLimit.Paper02_LearningTheory` | [#02 map](PaperMaps/Paper02_LearningTheory.md) | Complete for the listed deterministic generation scope; optional `Results.Background` collects earlier Theorems 2.2--2.5 outside the independent umbrella; finite-universe counterexamples are linked alongside the countably infinite separations |
| **#03 On the Limits of Language Generation** | Theorem 3.1 rate dichotomy with a separate derived oracle-based exponential upper bound; full oracle-relative Theorems 3.2--3.3; Theorem 3.4 in an encoded computable token-machine model; intended statistical Theorem 3.6 with corrected failure loss; statistical approximate-breadth Theorem 3.8; certified subset-oracle Proposition 3.10; full online PMF/MOP Theorems 3.5, 3.7, 3.9 in the documented oracle model; certified membership-only exponential rates for Propositions 3.11--3.12; full labeled exponential Theorem 3.13 | `GenLimit.Paper03_HallucinationAndModeCollapse` | [#03 map](PaperMaps/Paper03_HallucinationAndModeCollapse.md) | Theorem 3.1 has a direct Baire no-rate proof; Theorem 3.2 has matching generation rates on infinite languages and certified membership-only computation; Theorem 3.3 has the statistical breadth separation with certified sampling and explicit MOP/computation boundaries; Theorem 3.4 derives ordinary word-support decidability from every-tape local termination with explicit auxiliary paths and EOS; Theorem 3.6 reuses statistical necessity through a proof-only semantic classifier and retains the source stability/MOP hypotheses; Theorem 3.8 uses support locking, positive IID-prefix mass, and finite tell-tales; Proposition 3.10 implements the last-critical subset-query learner and proves its exponential IID rate without tell-tale access; Propositions 3.11--3.12 certify the finite version-space program; Theorem 3.13 proves the labeled full-support/correct-label model and optimal exponential rates via finite separators and a randomized lower bound; online bounded identifiers have fixed-index convergence; fresh/repeating samplers and support deciders have explicit computation certificates; effective online corollaries require uniform MOP; Proposition 3.12 proof repaired |
| **#04 Exploring Facets of Language Generation in the Limit** | Overview Theorems 1--5; original detailed Theorems 6--7; Propositions 6.1--6.3 and 7.1; Claim 5.2 and Examples 9--10; recalled Theorem 8 supplied by canonical Angluin Theorem 1 | `GenLimit.Paper04_ExploringFacetsOfLanguageGeneration` | [#04 map](PaperMaps/Paper04_ExploringFacetsOfLanguageGeneration.md) | Complete for the listed original scope; Theorem 7 uses a kernel-checked completion-driven adaptive diagonal, while Theorem 8 is not duplicated |
| **#05 Hallucinations, Breadth, and Stability** | All numbered main results in Sections 3–8, including Corollaries 6.1 and 7.2 and the Section 7 constructions | `GenLimit.Paper05_HallucinationsBreadthAndStability` | [#05 map](PaperMaps/Paper05_HallucinationsBreadthAndStability.md) | Of 31 registered claims, 24 have positive proofs under the documented conventions and seven have literal counterexamples. Figure 4 leaves two characterizations open. The [Level 1 human review](AuditRecords/Human/README.md#05-hallucinations-breadth-and-stability-three-semantic-statements-level-1) covered three semantic statements at the reviewed checkpoint. All three reviewed declarations have since been replaced and await a new source review. |
| **#06 Noisy Examples** | Numbered results, numerical noisy closure dimension, optimal sample complexity, and the one-based cover bound | `GenLimit.Paper06_NoisyExamples` | [#06 map](PaperMaps/Paper06_NoisyExamples.md) | Kernel checked for the semantic results, with an explicit counterexample to the D.1 prose gloss |
| **#07 Density Measures for Language Generation** | All overview results and detailed main theorems. Chronological witnesses, set-driven minimax, rank-two set-only counterexamples, and the separate Claim 6.11 replay counterexample | `GenLimit.Paper07_DensityMeasuresForLanguageGeneration` | [#07 map](PaperMaps/Paper07_DensityMeasuresForLanguageGeneration.md) | The numerical bounds have a patient-scope proof. The original infinite-rank charge is conditional. The [Level 1 human audit](AuditRecords/Human/README.md#07-density-measures-theorem-21-level-1) covers the fixed-selector Theorem 2.1. The new public finite-history statement needs review. |
| **#08 Hallucination Detection** | All numbered definitions and valid results: detection/identification equivalence, finite-tell-tale characterization, complete labeled negative-example detection, and Appendix results; the Example 1 impossibility inference is corrected | `GenLimit.Paper08_HallucinationDetection` | [#08 map](PaperMaps/Paper08_HallucinationDetection.md) | Complete at the semantic oracle level; consistency queries counted exactly and the full-support iid extension verified; [Level 1 human audit](AuditRecords/Human/README.md#08-hallucination-detection-theorems-21-and-23-level-1) covers Theorems 2.1 and 2.3 and their defining interfaces only |
| **#09 Representative Language Generation** | Group-closure and nondecreasing-cover characterizations; finite-class/partition consequences and separation; finite-support necessity and criticality; finite-query impossibility; counterexample to the printed finite-support theorem and separately named exact-profile repairs | `GenLimit.Paper09_RepresentativeLanguageGeneration` | [#09 map](PaperMaps/Paper09_RepresentativeLanguageGeneration.md) | Partial for the declared published-result inventory: eight results full, Corollary 3.6 holds precisely on infinite countable domains, and printed Lemma 4.8/Theorem 4.4 disputed and uncovered; their repairs do not count as source-claim coverage |
| **Paper10 Union-Closedness of Language Generation** | Theorems 3.1–3.3 and 4.1, 4.3, 4.4, autonomous schedules, Remark 4.2, Propositions A.1–A.2, and Remark A.3 | `GenLimit.Paper10_UnionClosednessOfLanguageGeneration` | [Paper10 map](PaperMaps/Paper10_UnionClosednessOfLanguageGeneration.md) | Kernel-checked, including the randomized diagonal and exact membership of the alternating-column limit |
| **#14 A Characterization of List Language Identification in the Limit** | Deterministic Theorems 1 and 2; Algorithm 1 and Claim 5.1; detailed upper/lower Theorems 6 and 7 | `GenLimit.Paper14_ListLanguageIdentification` | [#14 map](PaperMaps/Paper14_ListLanguageIdentification.md) | Complete for the deterministic semantic characterization and stratification; statistical Theorem 3 and Sections 8--10 remain open |
| **#15 Partial Enumeration** | Theorem 2.1/Overview 1.5; Lemma 2.3; concrete Algorithm 1 and Lemma 2.5; Theorems 2.2/2.4/Overview 1.8; concrete warm-up priority run and Lemma 3.2; conditional latest-return charge and corrected `α/3` endgame; source-shaped pod `α/2` limit; full-text Theorem 4.9 and repaired exact-text Corollaries 4.10–4.11 | `GenLimit.Paper15_PartialEnumeration` | [#15 map](PaperMaps/Paper15_PartialEnumeration.md) | Kernel-checked for the listed scope; unconditional Lemma 3.4 is blocked by skipped resets, the dynamic pod bridge has a cumulative-pod gap, the printed arbitrary-partial-text Corollary 4.10 is false, and the partial topology is ambiguous |
| **#16 Complexity Barriers** | Theorems 3.1, 4.1, 5.1, and 6.1 on uniform generation from finite samples | `GenLimit.Paper16_ComplexityBarriers` | [#16 map](PaperMaps/Paper16_ComplexityBarriers.md) | All four are covered. The pattern construction exists exactly for positive sizes. |
| **#17 Infinite Contamination** | Membership-query generation, set and element density, bounded displacement, and the sharp finite-class threshold | `GenLimit.Paper17_InfiniteContamination` | [#17 map](PaperMaps/Paper17_InfiniteContamination.md) | 26 of 27 claim groups fully covered. Printed Theorem 7.7 refuted and a corrected bound proved. |
| **#18 Safe Language Generation in the Limit** | Safe identification and generation, including the effective impossibility in Corollary 6.1 | `GenLimit.Paper18_SafeLanguageGeneration` | [#18 map](PaperMaps/Paper18_SafeLanguageGeneration.md) | Five theorems and one corollary under the recorded repairs and machine representation. |
| **#19 Effect of Noise** | The four noise characterizations and separation theorems, numerical closure dimension and its square-root inequality | `GenLimit.Paper19_EffectOfNoise` | [#19 map](PaperMaps/Paper19_EffectOfNoise.md) | All selected results. |
| **#20 Agnostic Language Identification and Generation** | Nine theorems and one corollary on identification and generation rates | `GenLimit.Paper20_AgnosticLanguageIdentificationAndGeneration` | [#20 map](PaperMaps/Paper20_AgnosticLanguageIdentificationAndGeneration.md) | All main statistical results in Sections 2–3 of arXiv v4. |
| **#21 On Generation in Metric Spaces** | All nine main theorems, three corollaries, Proposition D.1, all five examples, Lemmas 2.1/C.1/C.2, and the orthogonal covering estimate | `GenLimit.Paper21_GenerationInMetricSpaces` | [#21 map](PaperMaps/Paper21_GenerationInMetricSpaces.md) | Complete for the listed arXiv v2 semantic scope; [Level 1 human audit](AuditRecords/Human/README.md#21-on-generation-in-metric-spaces-arxiv-v2-level-1) covers all 20 Overview theorem statements and their defining interfaces. Implementation and oracle execution are outside scope |
| **#22 Language Generation with Replay** | Theorems 4.1, 5.1, 6.1, 6.6, 7.1, and 7.3 | `GenLimit.Paper22_LanguageGenerationWithReplay` | [#22 map](PaperMaps/Paper22_LanguageGenerationWithReplay.md) | All six main theorems. Theorem 6.1 includes finite-query execution on the natural-number universe. Theorem 7.1 gives the proper membership-query lower bound over recursive families. |
| **#23 Banach Density, Topology, and Geometry** | Unrestricted and rectangular obstructions, sharp finite-rank and centered-cube density, and structural claims | `GenLimit.Paper23_BanachDensityTopologyAndGeometry` | [#23 map](PaperMaps/Paper23_BanachDensityTopologyAndGeometry.md) | Theorems 2.2, 4.5, 5.1, and 5.8 and Corollaries 4.2–4.3 and 4.6–4.7 are proved. Both rectangle-growth premises in 5.1 hold. The ambient-coordinate version of 4.1 is proved on a sparse target. Its rank-relative version has a counterexample. The filtered-rectangle generation guarantee is proved on a common monotone chain, on ordered rows with logarithmic row counts, and under positive-occupancy hypotheses, including on stretched product grids. A separate Lean replay proves 5.5 and 5.6 on arbitrary finite-rank targets whenever the filter eventually dominates a positive logarithmic power. For arbitrary divergent filters exact half is proved on the whole integer line. The unrestricted higher-dimensional claims in 2.5, 5.5, and 5.6 remain unproved. The local pairing estimate (28) has a counterexample. Corollary 5.4 has a necessary and sufficient growth restriction on its rectangle filter. The geometric-length 5.9 inequality has a unit-box counterexample and its lattice-site-length repair is proved. The fixed-shape density clause of 5.7 is proved. Its exact-identification clause has a rank-two counterexample. |
| **#24 Price of Privacy** | Private identification and generation under IID sampling | `GenLimit.Paper24_PriceOfPrivacy` | [#24 map](PaperMaps/Paper24_PriceOfPrivacy.md) | All six main theorems are proved, including both mechanisms in each upper bound. |
| **#25 Private Generation and Identification** | Private identification and generation under continual release | `GenLimit.Paper25_PrivateGenerationAndIdentification` | [#25 map](PaperMaps/Paper25_PrivateGenerationAndIdentification.md) | Theorems 1.1, 1.2, 1.5 and 1.6 are proved. Both bounds in 1.3 are proved for k ≥ 2. The singleton case contradicts Definition 2. Counterexamples refute the stronger C.3 coefficient when ε may grow with k. Algorithm 2 satisfies the C.5 online identification guarantee. |
| **#26 Identification with Computational Trace** | Identification with perfect traces and three noise thresholds | `GenLimit.Paper26_IdentificationWithComputationalTrace` | [#26 map](PaperMaps/Paper26_IdentificationWithComputationalTrace.md) | Theorems 3.1, 4.1, 4.3 and 4.5, including both lower bounds. |
| **#27 Language Generation with Feedback: Queries and Mistakes** | Theorems 3.1–3.4 and 3.9–3.10, Corollaries 3.6–3.8 | `GenLimit.Paper27_FeedbackQueriesAndMistakes` | [#27 map](PaperMaps/Paper27_FeedbackQueriesAndMistakes.md) | All nine main results. Appendix Lemma A.8 refuted, with an independent proof of 3.9. |
| **#28 Contrastive Generation** | Theorems 4.3, 4.7, 5.4–5.5, 5.13–5.14, 6.5–6.6 and 6.8 | `GenLimit.Paper28_ContrastiveGeneration` | [#28 map](PaperMaps/Paper28_ContrastiveGeneration.md) | Includes the strict clean hierarchy, general infinite-defect identification and unordered observation transport. |
| **#29 Mistake-Bounded Language Generation** | Qualified 4.1 and 5.1, tightness 5.3, logarithmic bound 6.1, refutation of pointwise 6.4, and noisy bounds 7.1–7.2 | `GenLimit.Paper29_MistakeBoundedLanguageGeneration` | [#29 map](PaperMaps/Paper29_MistakeBoundedLanguageGeneration.md) | The weighted bound needs positive target weight. Generator-first timing gives a one-round shift in 5.1. |
| **#30 Time-Sensitive Language Generation** | Almost-sure impossibilities 1–2, uniform-rate refutation for 3, sharp timely upper density 1/2 for 4 | `GenLimit.Paper30_TimeSensitiveLanguageGeneration` | [#30 map](PaperMaps/Paper30_TimeSensitiveLanguageGeneration.md) | Theorem 4 uses a queue-totalized generator with a matching adaptive exact presentation. |
| **#31 Bounded Memory** | Memoryless and sliding-window density, adaptive buffers and incremental generation and identification | `GenLimit.Paper31_BoundedMemory` | [#31 map](PaperMaps/Paper31_BoundedMemory.md) | All 9 numbered main-text results and 4 appendix results in Overview, with one fixed enumeration of the native countable alphabet for density |
| **#32 Infinitely Many Hallucinations** | Precision, strict and fractional novelty, batched recall, and appendix sharpness | `GenLimit.Paper32_InfinitelyManyHallucinations` | [#32 map](PaperMaps/Paper32_InfinitelyManyHallucinations.md) | Algorithm 7 proves 4.9. Counterexamples to the recall of Algorithms 2 and 6 in 4.5 and 4.8, and to the raw-batch reading of 3.3. An independent generator attains the 4.8 guarantee. |
| **#39 Dense Generation** | Earlier-manuscript patient-scope Lemma 3.11 and Theorem 3.14; partial-enumeration Example 3.15, Lemma 3.16, and Theorem 3.17 (arXiv v1 Example 3.17, Lemma 3.18, and Theorem 3.19) | `GenLimit.Paper39_DenseGeneration` | [#39 map](PaperMaps/Paper39_DenseGeneration.md) | Complete for the listed earlier-manuscript theorem paths; public arXiv v1 has a different criticality definition and is not yet formalized |

Human correspondence status does not live in this paper registry. The
authoritative completed-audit ledger and pending ChatGPT Pro checks are in
[`AuditRecords/Human/README.md`](AuditRecords/Human/README.md).
The #07/#15/#17/#18/#21/#22/#23 maps record AI-assisted adaptations whose
kernel checks are separate from paper correspondence. Named human review
applies only to the explicitly recorded scopes in the ledger above.

For Paper10, Peng Zhang completed a Level 1 human audit of overview Theorems
3.1--3.3; Theorems 4.1, 4.3, and 4.4 are their detailed presentations.  The
countable 4.4-to-3.3 mismatch and Lean's repaired uncountable witness are
Codex-assisted formalization findings.
Proof-correspondence and Appendix review remain pending; there is no
checksum-verified ChatGPT Pro record.

The [#0A map](PaperMaps/Paper00A_PositiveDataInference.md) records the semantic
versus effective boundary of the identification development used by #08 and
#28. It has a Level 1 human audit of the semantic characterization and no
separate external source audit.

The [#09 map](PaperMaps/Paper09_RepresentativeLanguageGeneration.md) records
the final PMLR source, the eleven-result claim inventory, the precise
Corollary 3.6 specialization, and the distinction between the disputed
printed finite-support claims, their Lean obstruction/counterexample, and
the separately named exact-profile repairs. No named human correspondence
audit is claimed for P09.

See the [cross-paper map](PaperMaps/RELATIONSHIPS.md) for shared foundations,
the explicit #0/#01/#39 separation theorems, the #01-to-#39 criticality
bridge, the #02-to-#04 generation equivalence and Theorem 1 bridge, the
#02-to-#08 Appendix A.2 bridge, the #03-to-#04 and #04-to-#05 breadth bridges, neutral Core
and Angluin reuse in #28, canonical ordered-density reuse in #07/#15/#30/#31,
shared #07/#23 tower infrastructure, neutral #0/#15 finite tell-tales, and the
import-independence rule. The
[Paper10 map](PaperMaps/Paper10_UnionClosednessOfLanguageGeneration.md)
records its deliberate reuse of #02's EUC results and Theorem 4.4
countable-generation consequence, while keeping Theorem 3.2's autonomous
schedules and the alternating diagonal machinery paper-local.

## Build each paper independently

```text
lake build GenLimit.Paper00_LanguageIdentification
lake build GenLimit.Paper00_LanguageIdentification.Abstract
lake build GenLimit.Paper00_LanguageIdentification.Text
lake build GenLimit.Paper00_LanguageIdentification.Informant
lake build GenLimit.Paper01_LanguageGeneration
lake build GenLimit.Paper01_LanguageGeneration.Semantic
lake build GenLimit.Paper01_LanguageGeneration.FiniteQuery
lake build GenLimit.Paper01_LanguageGeneration.FiniteFamily
lake build GenLimit.Paper01_LanguageGeneration.SetInterface
lake build GenLimit.Paper01_LanguageGeneration.Transport
lake build GenLimit.Paper01_LanguageGeneration.Results.Overview
lake build GenLimit.Paper02_LearningTheory
lake build GenLimit.Paper03_HallucinationAndModeCollapse
lake build GenLimit.Paper04_ExploringFacetsOfLanguageGeneration
lake build GenLimit.Paper05_HallucinationsBreadthAndStability
lake build GenLimit.Paper06_NoisyExamples
lake build GenLimit.Paper07_DensityMeasuresForLanguageGeneration
lake build GenLimit.Paper00A_PositiveDataInference
lake build GenLimit.Paper08_HallucinationDetection
lake build GenLimit.Paper09_RepresentativeLanguageGeneration
lake build GenLimit.Paper10_UnionClosednessOfLanguageGeneration
lake build GenLimit.Paper14_ListLanguageIdentification
lake build GenLimit.Paper15_PartialEnumeration
lake build GenLimit.Paper16_ComplexityBarriers
lake build GenLimit.Paper17_InfiniteContamination
lake build GenLimit.Paper18_SafeLanguageGeneration
lake build GenLimit.Paper20_AgnosticLanguageIdentificationAndGeneration
lake build GenLimit.Paper21_GenerationInMetricSpaces
lake build GenLimit.Paper22_LanguageGenerationWithReplay
lake build GenLimit.Paper23_BanachDensityTopologyAndGeometry
lake build GenLimit.Paper26_IdentificationWithComputationalTrace
lake build GenLimit.Paper27_FeedbackQueriesAndMistakes
lake build GenLimit.Paper28_ContrastiveGeneration
lake build GenLimit.Paper29_MistakeBoundedLanguageGeneration
lake build GenLimit.Paper30_TimeSensitiveLanguageGeneration
lake build GenLimit.Paper31_BoundedMemory
lake build GenLimit.Paper32_InfinitelyManyHallucinations
lake build GenLimit.Paper39_DenseGeneration
lake build GenLimit.Paper39_DenseGeneration.Partial
lake build GenLimit.Bridges.Paper04ToPaper05
lake build GenLimit.Bridges
```

The global kernel and access-model audit is recorded in [AUDIT.md](AUDIT.md).
Numbered paper directories under [`AuditRecords/`](AuditRecords/) preserve
checksum-verified ChatGPT Pro statement-faithfulness evidence. Named human
correspondence is recorded in the nested
[human-audit ledger](AuditRecords/Human/README.md).
