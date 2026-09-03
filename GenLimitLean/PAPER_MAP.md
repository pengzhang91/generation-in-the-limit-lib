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
GenLimit.Paper17_InfiniteContamination
GenLimit.Paper23_BanachDensityTopologyAndGeometry
GenLimit.Paper27_FeedbackQueriesAndMistakes
GenLimit.Paper28_ContrastiveGeneration
GenLimit.Paper31_BoundedMemory
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
GenLimit/Paper01_LanguageGeneration/        #01 semantic, observed-set, and finite-query proofs
GenLimit/Paper02_LearningTheory/            #02 ordinary, prompted, prediction-proxy, and EUC results
GenLimit/Paper03_HallucinationAndModeCollapse/  #03 probability-free support-oracle reductions
GenLimit/Paper04_ExploringFacetsOfLanguageGeneration/  #04 non-uniform, membership-query, exhaustive, breadth, and feedback results
GenLimit/Paper05_HallucinationsBreadthAndStability/  #05 exact/approximate breadth, stability, and source-gap results
GenLimit/Paper06_NoisyExamples/             #06 noisy-generation models, characterizations, and appendices
GenLimit/Paper07_DensityMeasuresForLanguageGeneration/  #07 selector, rank forest/fallback, charging, and diagnostics
GenLimit/Paper08_HallucinationDetection/    #08 detection and reduction results
GenLimit/Paper09_RepresentativeLanguageGeneration/  #09 representative generation, group closure, and query impossibility
GenLimit/Paper10_UnionClosednessOfLanguageGeneration/  union-closedness witnesses and deterministic appendix
GenLimit/Paper14_ListLanguageIdentification/        #14 list identification, k-Angluin characterization, and stratification
GenLimit/Paper15_PartialEnumeration/        #15 Algorithm 1, priority run, density, and full-text topology/learners
GenLimit/Paper17_InfiniteContamination/     #17 contamination regimes, priority generation, and density obstructions
GenLimit/Paper23_BanachDensityTopologyAndGeometry/  #23 absolute density, finite ranks, and finite trees
GenLimit/Paper27_FeedbackQueriesAndMistakes/  #27 feedback characterizations and query separation
GenLimit/Paper28_ContrastiveGeneration/     #28 geometry, generation, hierarchy, and corruption
GenLimit/Paper31_BoundedMemory/             #31 memoryless, density, buffer, and incremental results
GenLimit/Paper39_DenseGeneration/           #39 exact- and partial-enumeration patient-scope results
GenLimit/Bridges/                           explicit cross-paper comparisons
```

## Formalized papers

| Paper | Formalized result | Lean umbrella | Detailed map | Kernel status |
|---|---|---|---|---|
| **#0 Language Identification** | Semantic model; all three clauses of Theorem 7.1; finite-language text learning; locking and finite tell-tales; arbitrary-text superfinite nonidentifiability; complete-informant enumeration | `GenLimit.Paper00_LanguageIdentification` | [#0 map](PaperMaps/Paper00_LanguageIdentification.md) | Complete for the listed semantic paths |
| **#0A Inductive Inference from Positive Data** | Semantic identification iff nonuniform finite tell-tales; full effective Theorem 1 and Corollary 1 with uniformly recursive families and computable learners/tell-tale enumerations | `GenLimit.Paper00A_PositiveDataInference` | [#0A map](PaperMaps/Paper00A_PositiveDataInference.md) | Complete for the semantic characterization and effective Theorem 1; Theorem 2 statement only |
| **#01 Language Generation** | Round-indexed Section 4 guarantee; literal finite-set interface for repeated presentations; Theorem 2.1 via both the NeurIPS proceedings and arXiv-v1 finite-query algorithms | `GenLimit.Paper01_LanguageGeneration` | [#01 map](PaperMaps/Paper01_LanguageGeneration.md) | Complete for the listed Theorem 2.1 paths; finite-family and prompted results excluded |
| **#02 Learning Theory** | Ordinary and prompted generation characterizations; closure and sample-complexity bounds; hierarchy separations; finite-cover and EUC results; Theorem 4.1 at the VC/Littlestone combinatorial boundary | `GenLimit.Paper02_LearningTheory` | [#02 map](PaperMaps/Paper02_LearningTheory.md) | Complete for the listed deterministic generation scope; identification, literal PAC/online models, and computational claims excluded |
| **#03 On the Limits of Language Generation** | Probability-free semantic support-oracle cores of online Theorems 3.5, 3.7, and 3.9; finite-tell-tale structural lemmas motivated by Propositions 3.11--3.12 | `GenLimit.Paper03_HallucinationAndModeCollapse` | [#03 map](PaperMaps/Paper03_HallucinationAndModeCollapse.md) | Complete for the listed semantic online cores and standalone structural lemmas; statistical rates, randomized/Turing-machine claims, and Appendices A/B are excluded |
| **#04 Exploring Facets of Language Generation in the Limit** | Overview Theorems 1--5; original detailed Theorems 6--7; Propositions 6.1--6.3 and 7.1; Claim 5.2 and Examples 9--10; recalled Theorem 8 supplied by canonical Angluin Theorem 1 | `GenLimit.Paper04_ExploringFacetsOfLanguageGeneration` | [#04 map](PaperMaps/Paper04_ExploringFacetsOfLanguageGeneration.md) | Complete for the listed original scope; Theorem 7 uses a kernel-checked completion-driven adaptive diagonal, while Theorem 8 is not duplicated |
| **#05 Hallucinations, Breadth, and Stability** | Semantic Theorem 3.3; constructive half of Theorem 3.8; approximate-breadth clause of Theorem 3.15; literal stability countertheorems and an explicitly corrected whole-target statement | `GenLimit.Paper05_HallucinationsBreadthAndStability` | [#05 map](PaperMaps/Paper05_HallucinationsBreadthAndStability.md) | Mixed: Theorem 3.3 and stable approximate breadth are complete semantically; Theorem 3.8 necessity is missing; literal stable exact/infinite-coverage claims are inconsistent under the printed definitions |
| **#06 Noisy Examples** | Every paper-owned numbered definition and valid qualitative result, including Theorems 3.1, 3.3, 3.9, 3.10 and Appendices C/D | `GenLimit.Paper06_NoisyExamples` | [#06 map](PaperMaps/Paper06_NoisyExamples.md) | Complete at the kernel-checked semantic level; numerical `NC_n`, asymptotic sample complexity, and efficiency excluded |
| **#07 Density Measures for Language Generation** | Strict-critical selector and Corollary 2.2; feasible sequences; finite topology and the dynamic finite-rank forest through Corollary 6.10; Claim 6.11 persistence diagnostic/frozen-frame repair; rational levels, run thinning, reservation history, and conditional `1/8` / corrected capacity-two `1/10` Theorem 6.12 endgames | `GenLimit.Paper07_DensityMeasuresForLanguageGeneration` | [#07 map](PaperMaps/Paper07_DensityMeasuresForLanguageGeneration.md) | Listed finite-rank and conditional accounting paths kernel-checked; the dynamic Claim 6.11/6.12 bridge, headline generation, truth-index existence, and minimax results remain |
| **#08 Hallucination Detection** | All numbered definitions and valid results: detection/identification equivalence, finite-tell-tale characterization, complete labeled negative-example detection, and Appendix results; the Example 1 impossibility inference is corrected | `GenLimit.Paper08_HallucinationDetection` | [#08 map](PaperMaps/Paper08_HallucinationDetection.md) | Complete at the semantic oracle level; effectiveness, complexity, and probabilistic claims excluded |
| **#09 Representative Language Generation** | Group-closure and nondecreasing-cover characterizations; finite-class/partition consequences and separation; finite-support necessity and criticality; finite-query impossibility; counterexample to the printed finite-support theorem and separately named exact-profile repairs | `GenLimit.Paper09_RepresentativeLanguageGeneration` | [#09 map](PaperMaps/Paper09_RepresentativeLanguageGeneration.md) | Partial for the declared published-result inventory: eight results full, Corollary 3.6 partial, and printed Lemma 4.8/Theorem 4.4 disputed and uncovered; their repairs do not count as source-claim coverage |
| **Paper10 Union-Closedness of Language Generation** | Theorems 3.1, 3.2, 3.3, 4.1, 4.3, and 4.4, including Theorem 3.2's autonomous no-adversary-input schedules; deterministic Proposition A.1; generic conditional prefix-realizability core from Appendix A.2 | `GenLimit.Paper10_UnionClosednessOfLanguageGeneration` | [Paper10 map](PaperMaps/Paper10_UnionClosednessOfLanguageGeneration.md) | Kernel-checked; randomized Proposition A.2 and the concrete Appendix A.2 construction/Remark A.3 are not formalized |
| **#14 A Characterization of List Language Identification in the Limit** | Deterministic Theorems 1 and 2; Algorithm 1 and Claim 5.1; detailed upper/lower Theorems 6 and 7 | `GenLimit.Paper14_ListLanguageIdentification` | [#14 map](PaperMaps/Paper14_ListLanguageIdentification.md) | Complete for the deterministic semantic characterization and stratification; statistical Theorem 3 and Sections 8--10 remain open |
| **#15 Partial Enumeration** | Theorem 2.1/Overview 1.5; Lemma 2.3; concrete Algorithm 1 and Lemma 2.5; Theorems 2.2/2.4/Overview 1.8; concrete warm-up priority run and Lemma 3.2; conditional latest-return charge and corrected `α/3` endgame; source-shaped pod `α/2` limit; full-text Theorem 4.9 and repaired exact-text Corollaries 4.10–4.11 | `GenLimit.Paper15_PartialEnumeration` | [#15 map](PaperMaps/Paper15_PartialEnumeration.md) | Kernel-checked for the listed scope; unconditional Lemma 3.4 is blocked by skipped resets, the dynamic pod bridge has a cumulative-pod gap, the printed arbitrary-partial-text Corollary 4.10 is false, and the partial topology is ambiguous |
| **#17 Infinite Contamination** | Examples 3.3–3.4; Lemma 4.1 / Corollary 4.2; explicit-family Theorems 5.1 and 5.4; Theorem 6.4 obstruction and exact half-density instance; Theorem 6.5 necessity; Proposition 7.4 / Lemma 7.5 | `GenLimit.Paper17_InfiniteContamination` | [#17 map](PaperMaps/Paper17_InfiniteContamination.md) | Partial: Theorem 6.1, Theorem 6.5 sufficiency, Theorems 6.11 and 6.14–6.18, and Algorithm 9 / Theorem 7.8 remain open |
| **#23 Banach Density, Topology, and Geometry** | Absolute one-dimensional density Claims 3.3/3.5; perfect-tower Claim 3.6; finite ranks; repaired Claim 4.11; finite-tree LCA Claims 4.18/4.20; Claim 4.4 and Appendix Claim 7.1 | `GenLimit.Paper23_BanachDensityTopologyAndGeometry` | [#23 map](PaperMaps/Paper23_BanachDensityTopologyAndGeometry.md) | Listed finite/topological path kernel-checked; structural-tree/pod state machine, generation, ordinal ranks, and higher dimensions remain |
| **#27 Language Generation with Feedback: Queries and Mistakes** | Semantic/classical Theorems 3.1–3.4 and Corollaries 3.6–3.8; Theorem 3.9 set-to-element conversion and self-locking-conditional reverse; Theorem 3.10 / Appendix A.9, A.12, and A.13; Appendix A.8 gap counterexample | `GenLimit.Paper27_FeedbackQueriesAndMistakes` | [#27 map](PaperMaps/Paper27_FeedbackQueriesAndMistakes.md) | Seven earlier results and three Theorem 3.10 components full; Theorem 3.9 remains partial, and its unrestricted reverse plus dependent A.10/A.11 route are deliberately deferred; machine-level complexity remains open |
| **#28 Contrastive Generation** | Theorem 4.7; uniform and non-uniform closure characterizations in Theorems 5.4--5.5; core criteria and hierarchy witnesses; Theorems 6.5--6.6 and 6.8; exact Proposition 6.3 defect infimum | `GenLimit.Paper28_ContrastiveGeneration` | [#28 map](PaperMaps/Paper28_ContrastiveGeneration.md) | Complete for the listed deterministic semantic results; full clean diamond, unordered-edge transport, general robustness, corrupted generation, probabilistic, and effective claims excluded |
| **#31 Bounded Memory** | Memoryless generation and output separations; memoryless and sliding-window density values; adaptive-buffer lower bound; finite-family incremental identification; and Appendix index/element results | `GenLimit.Paper31_BoundedMemory` | [#31 map](PaperMaps/Paper31_BoundedMemory.md) | Complete for the listed deterministic semantic results in their Lean interfaces; generic-universe transport, the fixed-global-order game, globally infinite outputs, raw-index learner transport, countable extensions, other density aggregates, and effective claims excluded |
| **#39 Dense Generation** | Earlier-manuscript patient-scope Lemma 3.11 and Theorem 3.14; partial-enumeration Example 3.15, Lemma 3.16, and Theorem 3.17 (arXiv v1 Example 3.17, Lemma 3.18, and Theorem 3.19) | `GenLimit.Paper39_DenseGeneration` | [#39 map](PaperMaps/Paper39_DenseGeneration.md) | Complete for the listed earlier-manuscript theorem paths; public arXiv v1 has a different criticality definition and is not yet formalized |

Human correspondence status does not live in this paper registry. The
authoritative completed-audit ledger and pending ChatGPT Pro checks are in
[`AuditRecords/Human/README.md`](AuditRecords/Human/README.md).
The #07/#15/#17/#23 maps record an AI-assisted adaptation whose kernel checks are
separate from paper correspondence; no completed human audit or immutable
ChatGPT Pro audit record is claimed for this sequence.

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
and Angluin reuse in #28, canonical ordered-density reuse in #07/#15/#31,
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
lake build GenLimit.Paper01_LanguageGeneration.FiniteQuery.ArxivV1
lake build GenLimit.Paper01_LanguageGeneration.SetInterface
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
lake build GenLimit.Paper17_InfiniteContamination
lake build GenLimit.Paper23_BanachDensityTopologyAndGeometry
lake build GenLimit.Paper27_FeedbackQueriesAndMistakes
lake build GenLimit.Paper28_ContrastiveGeneration
lake build GenLimit.Paper31_BoundedMemory
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
