# Shared foundations and cross-paper relationships

This map records mathematical reuse while keeping the Gold, KM, and
DenseGeneration paper developments independently buildable.

## Shared foundations

| Shared declaration | Module | Gold use | KM use | DenseGeneration use |
|---|---|---|---|---|
| `Language`, `LanguageFamily` | `GenLimit.Core.Basic` | Targets, classes, and naming denotations | Target family | Target family |
| `Presents`, `sample`, `Consistent` | `GenLimit.Core.Basic` | Exact positive texts and unordered content of ordered prefixes | KM observations and consistency | DenseGeneration observations and consistency |
| `textPrefix`, `textPrefix_toFinset` | `GenLimit.Core.Text` | Ordered finite text histories and their unordered sample view | — | — |
| `Learner`, `StabilizesTo`, `IdentifiesInLimit` | `GenLimit.Core.Identification` | Shared logical form of abstract and concrete identification in the limit | — | — |
| `consistent_of_target_subset` | `GenLimit.Core.Basic` | Least-compatible text enumeration | Target and containing candidates remain consistent | Focus/target consistency |
| `finite_scope_eventually_consistent_iff_target_subset` | `GenLimit.Core.TargetStability` | Stabilization of bounded enumeration | Eventual KM criticality | DenseGeneration Lemma 3.4 and scope progress |
| `OracleFamily` | `GenLimit.Core.OracleFamily` | Explicit generation bridges for indexed infinite families | Semantic KM uses the languages and infinitude; finite-query KM additionally uses the Boolean query | Common family object; semantic machine uses languages and infinitude |
| `FreshGeneratesInLimit`, `NovelGeneratesInLimit` | `GenLimit.Core.OnlineGeneration` | Trace-level comparison target for identification | KM freshness conclusion | DenseGeneration validity, freshness, and self-novelty conclusion |

## Explicit bridge

| Relationship | Lean declaration | Module |
|---|---|---|
| Gold identification implies fresh generation on an infinite indexed family | `Gold.identifier_implies_fresh_generation` | `GenLimit.Bridges.GoldToKM` |
| KM generation without Gold text identification on the co-singleton family | `GoldKMSeparation.generation_without_identification` | `GenLimit.Bridges.GoldToKM` |
| PatientScope novelty and density without Gold text identification on the same family | `GoldDenseSeparation.dense_generation_without_identification` | `GenLimit.Bridges.GoldToDenseGeneration` |
| KM criticality implies recursive criticality | `critical_recursiveCritical` | `GenLimit.Bridges.KMToDenseGeneration` |

These are comparison theorems, not implementation dependencies. The three
paper umbrellas build without importing the bridge layer.

## Ownership rule for future papers

A declaration belongs in the shared core only when its statement uses only
paper-independent vocabulary.  A declaration mentioning one paper's
criticality, selector, state, or algorithm remains with that paper.  A
declaration mentioning vocabulary from multiple papers belongs in a bridge.

Small proof duplication is preferable to introducing a false conceptual
dependency. In particular, KM's `least_consistent_critical` and
DenseGeneration's `recursiveCritical_of_consistent_of_minimal` remain
separate paper-facing facts.

## Import invariant

```text
GenLimit.Gold            = Core + Gold abstract, text, and informant identification
GenLimit.KM.Semantic     = Core + KM criticality + semantic proof
GenLimit.KM.FiniteQuery  = Core + KM criticality + finite-query refinement
GenLimit.KM              = both KM paths
GenLimit.DenseGeneration = Core + DenseGeneration
GenLimit.Bridges         = Core + Gold + KM + DenseGeneration comparisons
GenLimit                 = all of the above
```
