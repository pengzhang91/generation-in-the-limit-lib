# Paper-to-Lean registry

This file is the repository-level index.  Each paper has its own detailed
map, while cross-paper reuse is recorded separately rather than hidden inside
one paper's development.

## Repository layers

```text
GenLimit.Core
├── GenLimit.Paper00_LanguageIdentification
├── GenLimit.Paper00A_PositiveDataInference
├── GenLimit.Paper01_LanguageGeneration
├── GenLimit.Paper02_LearningTheory
├── GenLimit.Paper06_NoisyExamples
├── GenLimit.Paper08_HallucinationDetection
├── GenLimit.Paper11_UnionClosednessOfLanguageGeneration
├── GenLimit.Paper28_ContrastiveGeneration
├── GenLimit.Paper31_BoundedMemory
└── GenLimit.Paper39_DenseGeneration

GenLimit.Bridges  (explicit cross-paper results)
```

- `GenLimit.Core` contains paper-independent definitions and semantic lemmas.
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
GenLimit/Paper00_LanguageIdentification/    #0 abstract, text, and informant identification
GenLimit/Paper00A_PositiveDataInference/    #0A semantic/effective positive-data inference
GenLimit/Paper01_LanguageGeneration/        #01 semantic, observed-set, and finite-query proofs
GenLimit/Paper02_LearningTheory/            #02 ordinary, prompted, prediction-proxy, and EUC results
GenLimit/Paper06_NoisyExamples/             #06 noisy-generation models, characterizations, and appendices
GenLimit/Paper08_HallucinationDetection/    #08 detection and reduction results
GenLimit/Paper11_UnionClosednessOfLanguageGeneration/  union-closedness witnesses and deterministic appendix
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
| **#06 Noisy Examples** | Every paper-owned numbered definition and valid qualitative result, including Theorems 3.1, 3.3, 3.9, 3.10 and Appendices C/D | `GenLimit.Paper06_NoisyExamples` | [#06 map](PaperMaps/Paper06_NoisyExamples.md) | Complete at the kernel-checked semantic level; numerical `NC_n`, asymptotic sample complexity, and efficiency excluded |
| **#08 Hallucination Detection** | All numbered definitions and valid results: detection/identification equivalence, finite-tell-tale characterization, complete labeled negative-example detection, and Appendix results; the Example 1 impossibility inference is corrected | `GenLimit.Paper08_HallucinationDetection` | [#08 map](PaperMaps/Paper08_HallucinationDetection.md) | Complete at the semantic oracle level; effectiveness, complexity, and probabilistic claims excluded |
| **Paper11 Union-Closedness of Language Generation** | Theorems 3.1, 3.2, 3.3, 4.1, 4.3, and 4.4; deterministic Proposition A.1; generic conditional prefix-realizability core from Appendix A.2 | `GenLimit.Paper11_UnionClosednessOfLanguageGeneration` | [Paper11 map](PaperMaps/Paper11_UnionClosednessOfLanguageGeneration.md) | Kernel-checked; human audit pending; randomized Proposition A.2 and the concrete Appendix A.2 construction/Remark A.3 are not formalized |
| **#28 Contrastive Generation** | Theorem 4.7; uniform and non-uniform closure characterizations in Theorems 5.4--5.5; core criteria and hierarchy witnesses; Theorems 6.5--6.6 and 6.8; exact Proposition 6.3 defect infimum | `GenLimit.Paper28_ContrastiveGeneration` | [#28 map](PaperMaps/Paper28_ContrastiveGeneration.md) | Complete for the listed deterministic semantic results; full clean diamond, unordered-edge transport, general robustness, corrupted generation, probabilistic, and effective claims excluded |
| **#31 Bounded Memory** | Memoryless generation and output separations; memoryless and sliding-window density values; adaptive-buffer lower bound; finite-family incremental identification; and Appendix index/element results | `GenLimit.Paper31_BoundedMemory` | [#31 map](PaperMaps/Paper31_BoundedMemory.md) | Complete for the listed deterministic semantic results in their Lean interfaces; generic-universe transport, the fixed-global-order game, globally infinite outputs, raw-index learner transport, countable extensions, other density aggregates, and effective claims excluded |
| **#39 Dense Generation** | Earlier-manuscript patient-scope Lemma 3.11 and Theorem 3.14; partial-enumeration Example 3.15, Lemma 3.16, and Theorem 3.17 (arXiv v1 Example 3.17, Lemma 3.18, and Theorem 3.19) | `GenLimit.Paper39_DenseGeneration` | [#39 map](PaperMaps/Paper39_DenseGeneration.md) | Complete for the listed earlier-manuscript theorem paths; public arXiv v1 has a different criticality definition and is not yet formalized |

Human correspondence status does not live in this paper registry. The
authoritative completed-audit ledger and pending ChatGPT Pro checks are in
[`AuditRecords/Human/README.md`](AuditRecords/Human/README.md).

For Paper11, source alignment was checked locally with AI assistance; there is
no checksum-verified ChatGPT Pro record, and the human audit remains pending.

The [#0A map](PaperMaps/Paper00A_PositiveDataInference.md) records the semantic
versus effective boundary of the identification development used by #08 and
#28. It has a Level 1 human audit of the semantic characterization and no
separate external source audit.

See the [cross-paper map](PaperMaps/RELATIONSHIPS.md) for shared foundations,
the explicit #0/#01/#39 separation theorems, the #01-to-#39 criticality
bridge, the #02-to-#08 Appendix A.2 bridge, neutral Core and Angluin reuse in
#28, neutral ordered-density extraction for #31, and the import-independence
rule. The [Paper11 map](PaperMaps/Paper11_UnionClosednessOfLanguageGeneration.md)
records its deliberate reuse of #02's EUC and countable-generation results,
while keeping the alternating diagonal machinery paper-local.

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
lake build GenLimit.Paper06_NoisyExamples
lake build GenLimit.Paper00A_PositiveDataInference
lake build GenLimit.Paper08_HallucinationDetection
lake build GenLimit.Paper11_UnionClosednessOfLanguageGeneration
lake build GenLimit.Paper28_ContrastiveGeneration
lake build GenLimit.Paper31_BoundedMemory
lake build GenLimit.Paper39_DenseGeneration
lake build GenLimit.Paper39_DenseGeneration.Partial
lake build GenLimit.Bridges
```

The global kernel and access-model audit is recorded in [AUDIT.md](AUDIT.md).
Numbered paper directories under [`AuditRecords/`](AuditRecords/) preserve
checksum-verified ChatGPT Pro statement-faithfulness evidence. Named human
correspondence is recorded in the nested
[human-audit ledger](AuditRecords/Human/README.md).
