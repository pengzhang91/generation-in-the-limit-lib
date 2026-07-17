# Shared foundations and cross-paper relationships

This map records mathematical reuse without making either paper development a
dependency of the other.

## Shared foundations

| Shared declaration | Module | KM use | DenseGeneration use |
|---|---|---|---|
| `Language`, `LanguageFamily` | `GenLimit.Core.Basic` | Target family | Target family |
| `Presents`, `sample`, `Consistent` | `GenLimit.Core.Basic` | KM observations and consistency | DenseGeneration observations and consistency |
| `consistent_of_target_subset` | `GenLimit.Core.Basic` | Target and containing candidates remain consistent | Focus/target consistency |
| `finite_scope_eventually_consistent_iff_target_subset` | `GenLimit.Core.TargetStability` | Eventual KM criticality | DenseGeneration Lemma 3.4 and scope progress |
| `OracleFamily` | `GenLimit.Core.OracleFamily` | Semantic KM uses the languages and infinitude; finite-query KM additionally uses the Boolean query | Common family object; semantic machine uses languages and infinitude |

## Explicit bridge

| Relationship | Lean declaration | Module |
|---|---|---|
| KM criticality implies recursive criticality | `critical_recursiveCritical` | `GenLimit.Bridges.KMToDenseGeneration` |

The bridge is a comparison theorem, not an implementation dependency.  Both
`GenLimit.KM` and `GenLimit.DenseGeneration` build without importing it.

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
GenLimit.KM.Semantic     = Core + KM criticality + semantic proof
GenLimit.KM.FiniteQuery  = Core + KM criticality + finite-query refinement
GenLimit.KM              = both KM paths
GenLimit.DenseGeneration = Core + DenseGeneration
GenLimit.Bridges         = Core + KM + DenseGeneration comparisons
GenLimit                 = all of the above
```
