# Paper-to-Lean registry

This file is the repository-level index.  Each paper has its own detailed
map, while cross-paper reuse is recorded separately rather than hidden inside
one paper's development.

## Repository layers

```text
GenLimit.Core
├── GenLimit.Gold
├── GenLimit.KM
├── GenLimit.LiRamanTewari
├── GenLimit.NoisyExamples
├── GenLimit.Angluin
├── GenLimit.HallucinationDetection
├── GenLimit.ContrastiveGeneration
├── GenLimit.BoundedMemory
└── GenLimit.DenseGeneration

GenLimit.Bridges  (explicit cross-paper results)
```

- `GenLimit.Core` contains paper-independent definitions and semantic lemmas.
- `GenLimit.Gold`, `GenLimit.KM`, `GenLimit.LiRamanTewari`,
  `GenLimit.NoisyExamples`, `GenLimit.Angluin`,
  `GenLimit.HallucinationDetection`, `GenLimit.ContrastiveGeneration`,
  `GenLimit.BoundedMemory`, and `GenLimit.DenseGeneration` are
  independently buildable paths. `GenLimit.Angluin` is a paper-specific
  dependency sibling rather than a separate paper entry in this focused
  public registry.
- `GenLimit.Bridges` contains declarations whose statements mention both
  identification and generation vocabulary from multiple developments.
- `GenLimit` imports all layers for users who want the whole library.

The filesystem follows the same ownership rule:

```text
GenLimit/Core/           shared definitions, ordered text, identification, and stability
GenLimit/Gold/           Gold abstract, text, and informant identification
GenLimit/KM/             semantic and observed-set KM proofs, plus shared criticality
GenLimit/KM/FiniteQuery/ Proceedings and arXiv-v1 algorithms for Theorem 2.1
GenLimit/LiRamanTewari/  ordinary, prompted, prediction-proxy, and EUC results
GenLimit/NoisyExamples/  noisy-generation models, characterizations, and appendices
GenLimit/Angluin/        semantic/effective identification and tell-tale interfaces
GenLimit/HallucinationDetection/ native Paper 08 detection and reduction results
GenLimit/ContrastiveGeneration/ Paper 28 geometry, generation, hierarchy, and corruption
GenLimit/BoundedMemory/  Paper 31 memoryless, density, buffer, and incremental results
GenLimit/DenseGeneration/Abstract/  certificate, charging, and density mathematics
GenLimit/DenseGeneration/Patient/   concrete patient-scope machine and its proof
GenLimit/DenseGeneration/Partial/   Section 3.3 partial-enumeration extension
GenLimit/Bridges/        optional cross-paper comparisons
```

## Formalized papers

| Paper | Formalized result | Lean umbrella | Detailed map | Kernel status | Human correspondence status |
|---|---|---|---|---|---|
| E. Mark Gold, *Language Identification in the Limit* | Semantic model; all three clauses of Theorem 7.1; finite-language text learning; locking and finite tell-tales; arbitrary-text superfinite nonidentifiability; complete-informant enumeration | `GenLimit.Gold` | [Gold map](PaperMaps/Gold.md) | Complete for the listed semantic paths | Shared Core prerequisites and Gold Text audited at Level 2; Abstract, text enumeration, informant, and bridge paths not yet human-audited |
| Kleinberg--Mullainathan, *Language Generation in the Limit* | Round-indexed Section 4 guarantee; literal finite-set interface for repeated presentations; Theorem 2.1 via both the NeurIPS proceedings and arXiv-v1 finite-query algorithms | `GenLimit.KM` | [KM map](PaperMaps/KM.md) | Complete for the listed Theorem 2.1 paths; finite-family and prompted results excluded | Semantic path audited by Peng Zhang at human Level 3; other paths have a ChatGPT Pro statement-faithfulness check and await human audit |
| Li--Raman--Tewari, *Generation through the Lens of Learning Theory* | Ordinary and prompted generation characterizations; closure and sample-complexity bounds; hierarchy separations; finite-cover and EUC results; Theorem 4.1 at the VC/Littlestone combinatorial boundary | `GenLimit.LiRamanTewari` | [Li--Raman--Tewari map](PaperMaps/LiRamanTewari.md) | Complete for the listed deterministic generation scope; identification, literal PAC/online models, and computational claims excluded | ChatGPT Pro statement-faithfulness check complete; human correspondence audit pending |
| Ananth Raman and Vinod Raman, *Generation from Noisy Examples* | Every paper-owned numbered definition and valid qualitative result, including Theorems 3.1, 3.3, 3.9, 3.10 and Appendices C/D | `GenLimit.NoisyExamples` | [Noisy-examples map](PaperMaps/NoisyExamples.md) | Complete at the kernel-checked semantic level; numerical `NC_n`, asymptotic sample complexity, and efficiency excluded | ChatGPT Pro statement-faithfulness check complete; human correspondence audit pending |
| Karbasi--Montasser--Sous--Velegkas, *`(Im)possibility of Automated Hallucination Detection in Large Language Models`* | All numbered definitions and valid results: detection/identification equivalence, finite-tell-tale characterization, complete labeled negative-example detection, and Appendix results; the Example 1 impossibility inference is corrected | `GenLimit.HallucinationDetection` | [Hallucination-detection map](PaperMaps/HallucinationDetection.md) | Complete at the semantic oracle level; effectiveness, complexity, and probabilistic claims excluded | ChatGPT Pro statement-faithfulness check complete; human correspondence audit pending |
| Li--Han--Jiang--Gao, *Contrastive Identification and Generation in the Limit* | Theorem 4.7; uniform and non-uniform closure characterizations in Theorems 5.4--5.5; core criteria and hierarchy witnesses; Theorems 6.5--6.6 and 6.8; exact Proposition 6.3 defect infimum | `GenLimit.ContrastiveGeneration` | [Contrastive-generation map](PaperMaps/ContrastiveGeneration.md) | Complete for the listed deterministic semantic results; full clean diamond, unordered-edge transport, general robustness, corrupted generation, probabilistic, and effective claims excluded | ChatGPT Pro checked the pre-repair baseline; named-witness interface repair applied separately; human audit pending |
| Kleinberg--Mehrotra--Saberi--Velegkas, *On Language Generation in the Limit with Bounded Memory* | Memoryless generation and output separations; memoryless and sliding-window density values; adaptive-buffer lower bound; finite-family incremental identification; and Appendix index/element results | `GenLimit.BoundedMemory` | [Bounded-memory map](PaperMaps/BoundedMemory.md) | Complete for the listed deterministic semantic results in their Lean interfaces; generic-universe transport, the fixed-global-order game, globally infinite outputs, raw-index learner transport, countable extensions, other density aggregates, and effective claims excluded | ChatGPT Pro checked the pre-repair baseline; Appendix Lemma A.3 interface repair applied separately; human audit pending |
| #39 — Ziyi Cai, Shuangping Li, Yiheng Shen, Kangning Wang, and Peng Zhang, *Dense Language Generation Made Simple: Deterministic, Randomized, and Multi-Order Algorithms* | Earlier-manuscript patient-scope Lemma 3.11 and Theorem 3.14; partial-enumeration Example 3.15, Lemma 3.16, and Theorem 3.17 (arXiv v1 Example 3.17, Lemma 3.18, and Theorem 3.19) | `GenLimit.DenseGeneration` | [DenseGeneration map](PaperMaps/DenseGeneration.md) | Complete for the listed earlier-manuscript theorem paths; public arXiv v1 has a different criticality definition and is not yet formalized | Exact presentation and the manuscript Lemma 3.16--Theorem 3.17 path audited at Level 2 against the earlier supplied manuscript; manuscript Example 3.15 and Level 3 proof correspondence not yet human-audited; no human audit applies to public v1 |

The [Angluin dependency map](PaperMaps/Angluin.md) records the semantic versus
effective boundary of the sibling identification development used by Paper
08 and Paper 28. It has no separate external source audit or assigned
human-audit level.

See the [cross-paper map](PaperMaps/RELATIONSHIPS.md) for shared foundations,
the explicit Gold/KM/Dense separation theorems, the KM-to-Dense-Generation
criticality bridge, the LRT-to-Paper-08 Appendix A.2 bridge, and the
neutral Core and Angluin reuse in Paper 28, the neutral ordered-density
extraction for Paper 31, and the import-independence rule.

## Build each paper independently

```text
lake build GenLimit.Gold
lake build GenLimit.Gold.Abstract
lake build GenLimit.Gold.Text
lake build GenLimit.Gold.Informant
lake build GenLimit.KM
lake build GenLimit.KM.Semantic
lake build GenLimit.KM.FiniteQuery
lake build GenLimit.KM.FiniteQuery.ArxivV1
lake build GenLimit.KM.SetInterface
lake build GenLimit.LiRamanTewari
lake build GenLimit.NoisyExamples
lake build GenLimit.Angluin
lake build GenLimit.HallucinationDetection
lake build GenLimit.ContrastiveGeneration
lake build GenLimit.BoundedMemory
lake build GenLimit.DenseGeneration
lake build GenLimit.DenseGeneration.Partial
lake build GenLimit.Bridges
```

The global kernel and access-model audit is recorded in [AUDIT.md](AUDIT.md).
Checksum-verified ChatGPT Pro statement-faithfulness evidence is kept paper by paper under
[`AuditRecords/`](AuditRecords/); named human correspondence remains separate
in [HUMAN_AUDIT.md](HUMAN_AUDIT.md).
