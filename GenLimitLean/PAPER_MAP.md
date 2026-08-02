# Paper-to-Lean registry

This file is the repository-level index.  Each paper has its own detailed
map, while cross-paper reuse is recorded separately rather than hidden inside
one paper's development.

## Repository layers

```text
                            GenLimit.Core
                       /         |          \
             GenLimit.Gold   GenLimit.KM   GenLimit.DenseGeneration
                       \         |          /
                            GenLimit.Bridges
```

- `GenLimit.Core` contains paper-independent definitions and semantic lemmas.
- `GenLimit.Gold`, `GenLimit.KM`, and `GenLimit.DenseGeneration` are
  independently buildable paper paths.
- `GenLimit.Bridges` contains declarations whose statements mention both
  identification and generation vocabulary from multiple developments.
- `GenLimit` imports all layers for users who want the whole library.

The filesystem follows the same ownership rule:

```text
GenLimit/Core/           shared definitions, ordered text, identification, and stability
GenLimit/Gold/           Gold abstract, text, and informant identification
GenLimit/KM/             semantic KM proof and shared criticality
GenLimit/KM/FiniteQuery/ finite-query Proceedings algorithm and Theorem 2.1
GenLimit/DenseGeneration/Abstract/  certificate, charging, and density mathematics
GenLimit/DenseGeneration/Patient/   concrete patient-scope machine and its proof
GenLimit/DenseGeneration/Partial/   Section 3.3 partial-enumeration extension
GenLimit/Bridges/        optional cross-paper comparisons
```

## Formalized papers

| Paper | Formalized result | Lean umbrella | Detailed map | Kernel status | Human correspondence status |
|---|---|---|---|---|---|
| E. Mark Gold, *Language Identification in the Limit* | Semantic model; all three clauses of Theorem 7.1; finite-language text learning; locking and finite tell-tales; arbitrary-text superfinite nonidentifiability; complete-informant enumeration | `GenLimit.Gold` | [Gold map](PaperMaps/Gold.md) | Complete for the listed semantic paths | Shared Core prerequisites and Gold Text audited at Level 2; Abstract, text enumeration, informant, and bridge paths not yet human-audited |
| Kleinberg--Mullainathan, *Language Generation in the Limit* | Round-indexed Section 4 semantic guarantee (4.6), and Theorem 2.1 via the finite-query Proceedings algorithm | `GenLimit.KM` | [KM map](PaperMaps/KM.md) | Complete | Semantic path audited at Level 3; finite-query path not human-audited |
| Ziyi Cai, Shuangping Li, Yiheng Shen, Kangning Wang, and Peng Zhang, *Dense Language Generation Made Simple: Deterministic, Randomized, and Multi-Order Algorithms* | Patient-scope Lemma 3.11 and Theorem 3.14; partial-enumeration Example 3.15, Lemma 3.16, and Theorem 3.17 | `GenLimit.DenseGeneration` | [DenseGeneration map](PaperMaps/DenseGeneration.md) | Complete for the listed theorem paths | Exact presentation and the Lemma 3.16--Theorem 3.17 path audited at Level 2; Example 3.15 and Level 3 proof correspondence not yet human-audited |

See the [cross-paper map](PaperMaps/RELATIONSHIPS.md) for shared foundations,
the explicit Gold/KM/Dense separation theorems, the KM-to-Dense-Generation
criticality bridge, and the import-independence rule.

## Build each paper independently

```text
lake build GenLimit.Gold
lake build GenLimit.Gold.Abstract
lake build GenLimit.Gold.Text
lake build GenLimit.Gold.Informant
lake build GenLimit.KM
lake build GenLimit.KM.Semantic
lake build GenLimit.KM.FiniteQuery
lake build GenLimit.DenseGeneration
lake build GenLimit.DenseGeneration.Partial
lake build GenLimit.Bridges
```

The global kernel and access-model audit is recorded in [AUDIT.md](AUDIT.md).
