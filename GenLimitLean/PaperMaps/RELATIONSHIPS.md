# Shared foundations and cross-paper relationships

This map records mathematical reuse while keeping the Gold, KM,
Li--Raman--Tewari, Raman--Raman, Angluin, native Paper 08, and DenseGeneration
developments independently buildable.

## Shared foundations

| Shared declaration | Module | Paper uses |
|---|---|---|
| `Language`, `LanguageFamily` | `GenLimit.Core.Basic` | Gold targets and names; KM and DenseGeneration target families |
| `Presents`, `sample`, `Consistent` | `GenLimit.Core.Basic` | Gold exact texts; KM and DenseGeneration observations and consistency |
| `textPrefix`, `textPrefix_toFinset` | `GenLimit.Core.Text` | Gold ordered histories and their unordered sample view |
| `Learner`, `StabilizesTo`, `IdentifiesInLimit` | `GenLimit.Core.Identification` | Shared logical form of Gold's abstract and concrete identification |
| `consistent_of_target_subset` | `GenLimit.Core.Basic` | Gold least-compatible enumeration; KM candidate consistency; DenseGeneration focus consistency |
| `finite_scope_eventually_consistent_iff_target_subset` | `GenLimit.Core.TargetStability` | Gold stabilization; eventual KM criticality; DenseGeneration Lemma 3.4 and scope progress |
| `OracleFamily` | `GenLimit.Core.OracleFamily` | Gold generation bridges; KM semantic and finite-query paths; DenseGeneration's common family object |
| `FreshGeneratesInLimit`, `NovelGeneratesInLimit` | `GenLimit.Core.OnlineGeneration` | Gold comparison target; KM freshness; DenseGeneration validity, freshness, and self-novelty |
| `Language`, `LanguageClass`, `Stream`, `Generator` | `GenLimit.Core.GenericGeneration` | Generic countable-universe generation vocabulary used by Li--Raman--Tewari and Raman--Raman |
| `UUS`, limit/uniform/nonuniform generation predicates | `GenLimit.Core.ClassGeneration` | Paper-independent quantifier patterns shared by Li--Raman--Tewari and Raman--Raman |
| `versionSpace`, `commonCore`, `closure` | `GenLimit.Core.VersionSpace` | Positive-data version-space and closure vocabulary used by Li--Raman--Tewari and the noiseless side of Raman--Raman |
| Closure-witness and closure-dimension predicates | `GenLimit.Core.ClosureDimension` | Paper-independent combinatorial closure notions reused in Raman--Raman's separation example |
| `IsFiniteCover`, `IsNondecreasingCover` | `GenLimit.Core.ClassCovers` | Finite and increasing class-cover interfaces used by both generation developments |

## Explicit bridge

| Relationship | Lean declaration | Module |
|---|---|---|
| Gold identification implies fresh generation on an infinite indexed family | `Gold.identifier_implies_fresh_generation` | `GenLimit.Bridges.GoldToKM` |
| KM generation without Gold text identification on the co-singleton family | `GoldKMSeparation.generation_without_identification` | `GenLimit.Bridges.GoldToKM` |
| PatientScope novelty and density without Gold text identification on the same family | `GoldDenseSeparation.dense_generation_without_identification` | `GenLimit.Bridges.GoldToDenseGeneration` |
| KM criticality implies recursive criticality | `critical_recursiveCritical` | `GenLimit.Bridges.KMToDenseGeneration` |
| Every countable Paper 08 family is generatable in the Appendix Definition 5 sense, via LRT Corollary 3.6 on its infinite members | `HallucinationDetection.theorem_A_2` | `GenLimit.Bridges.LiRamanTewariToHallucinationDetection` |

These are comparison theorems, not hidden implementation dependencies. The
native paper umbrellas build without importing the bridge layer. Paper 08's
identification and tell-tale statements explicitly reuse its Angluin sibling;
the only substantive LRT dependency is the Appendix A.2 bridge.

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
GenLimit.LiRamanTewari   = generic Core + LRT ordinary, prompted, prediction-proxy, and EUC results
GenLimit.NoisyExamples   = generic Core + Raman--Raman noisy-generation results
GenLimit.Angluin         = generic Core + Angluin semantic/effective identification interfaces
GenLimit.HallucinationDetection = generic Core + Angluin + native Paper 08 results (excluding theorem A.2)
GenLimit.DenseGeneration = Core + DenseGeneration
GenLimit.Bridges         = Core + explicit Gold/KM/Dense and LRT/Paper-08 comparisons
GenLimit                 = all of the above
```

The generic semantic necessity theorem
`GenLimit.Angluin.conditionTwo_of_semanticallyIdentifiable` belongs to the
Angluin sibling because its statement uses only Angluin vocabulary. Paper 08
retains `GenLimit.HallucinationDetection.conditionTwo_of_identifiable` as a
thin source-facing wrapper. Conversely,
`GenLimit.HallucinationDetection.theorem_A_2` is physically declared in the
LRT-to-Paper-08 bridge even though it keeps the paper namespace.
