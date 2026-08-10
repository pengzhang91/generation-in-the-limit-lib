# Shared foundations and cross-paper relationships

This map records mathematical reuse while keeping #0 Language Identification,
#01 Language Generation, #02 Learning Theory, #06 Noisy Examples, the
unnumbered Angluin support theory, #08 Hallucination Detection, #28 Contrastive
Generation, #31 Bounded Memory, and #39 Dense Generation independently
buildable.

## Shared foundations

| Shared declaration | Module | Paper uses |
|---|---|---|
| `Language`, `LanguageFamily` | `GenLimit.Core.Basic` | #0 targets and names; #01 and #39 target families |
| `Presents`, `sample`, `Consistent` | `GenLimit.Core.Basic` | #0 exact texts; #01 and #39 observations and consistency |
| `textPrefix`, `textPrefix_toFinset` | `GenLimit.Core.Text` | #0 ordered histories and their unordered sample view |
| `Learner`, `StabilizesTo`, `IdentifiesInLimit` | `GenLimit.Core.Identification` | Shared logical form of #0 abstract and concrete identification |
| `consistent_of_target_subset` | `GenLimit.Core.Basic` | #0 least-compatible enumeration; #01 candidate consistency; #39 focus consistency |
| `finite_scope_eventually_consistent_iff_target_subset` | `GenLimit.Core.TargetStability` | #0 stabilization; eventual #01 criticality; #39 Lemma 3.4 and scope progress |
| `OracleFamily` | `GenLimit.Core.OracleFamily` | #0 generation bridges; #01 semantic and finite-query paths; #39 common family object |
| `FreshGeneratesInLimit`, `NovelGeneratesInLimit` | `GenLimit.Core.OnlineGeneration` | #0 comparison target; #01 freshness; #39 validity, freshness, and self-novelty |
| `Language`, `LanguageClass`, `LanguageFamily`, `Stream`, `Generator`, `Presents` | `GenLimit.Core.GenericGeneration` | Generic countable-universe generation vocabulary used by #02, #06, #28, and #31 |
| `OrderedLanguage`, prefix ratios, lower density, upper density | `GenLimit.Core.OrderedDensity` | Paper-independent Kleinberg--Wei ordered-density interface used by #31; declarations retain namespace `GenLimit.KleinbergWei` |
| `UUS`, limit/uniform/nonuniform generation predicates | `GenLimit.Core.ClassGeneration` | Paper-independent quantifier patterns shared by #02, #06, and #28 |
| `versionSpace`, `commonCore`, `closure` | `GenLimit.Core.VersionSpace` | Positive-data version-space and closure vocabulary used by #02 and the noiseless side of #06 |
| Closure-witness and closure-dimension predicates | `GenLimit.Core.ClosureDimension` | Paper-independent combinatorial closure notions reused in #06's separation example |
| `IsFiniteCover`, `IsNondecreasingCover` | `GenLimit.Core.ClassCovers` | Finite and increasing class-cover interfaces reused by #02, #06, and #28 |
| `stabilizingIndexIdentifier_implies_generatableInLimit` | `GenLimit.Core.IdentificationGeneration` | Paper-independent semantic identification-to-fresh-generation implication extracted for #28's clean hierarchy |
| `conditionTwo_of_semanticallyIdentifiable` | `GenLimit.Angluin.SemanticNecessity` | Generic finite-tell-tale necessity used through a #08 wrapper and directly by #28 |

## Explicit bridge

| Relationship | Lean declaration | Module |
|---|---|---|
| #0 identification implies fresh generation on an infinite indexed family | `Gold.identifier_implies_fresh_generation` | `GenLimit.Bridges.Paper00ToPaper01` |
| #01 generation without #0 text identification on the co-singleton family | `GoldKMSeparation.generation_without_identification` | `GenLimit.Bridges.Paper00ToPaper01` |
| PatientScope novelty and density without #0 text identification on the same family | `GoldDenseSeparation.dense_generation_without_identification` | `GenLimit.Bridges.Paper00ToPaper39` |
| #01 criticality implies #39 recursive criticality | `critical_recursiveCritical` | `GenLimit.Bridges.Paper01ToPaper39` |
| Every countable #08 family is generatable in the Appendix Definition 5 sense, via #02 Corollary 3.6 on its infinite members | `HallucinationDetection.theorem_A_2` | `GenLimit.Bridges.Paper02ToPaper08` |

These are comparison theorems, not hidden implementation dependencies. The
native paper umbrellas build without importing the bridge layer. #08's
identification and tell-tale statements explicitly reuse its Angluin sibling;
the only substantive #02 dependency is the Appendix A.2 bridge.
#28 also imports the Angluin support theory, but only its generic semantic
necessity theorem. It imports neither #02 nor #08, and it
requires no cross-paper bridge.
#31 imports neutral `GenLimit.Core.GenericGeneration` and
`GenLimit.Core.OrderedDensity` foundations but no #02, #06, #08, or #28
module and no bridge. Moving the ordered-density source to Core changes
ownership and import paths, not its `GenLimit.KleinbergWei` namespace.

## Ownership rule for future papers

A declaration belongs in the shared core only when its statement uses only
paper-independent vocabulary.  A declaration mentioning one paper's
criticality, selector, state, or algorithm remains with that paper.  A
declaration mentioning vocabulary from multiple papers belongs in a bridge.

Small proof duplication is preferable to introducing a false conceptual
dependency. In particular, #01's `least_consistent_critical` and #39's
`recursiveCritical_of_consistent_of_minimal` remain
separate paper-facing facts.

## Import invariant

```text
GenLimit.Paper00_LanguageIdentification = Core + #0 abstract, text, and informant identification
GenLimit.Paper01_LanguageGeneration     = Core + #01 semantic and finite-query paths
GenLimit.Paper02_LearningTheory         = generic Core + #02 ordinary, prompted, prediction-proxy, and EUC results
GenLimit.Paper06_NoisyExamples          = generic Core + #06 noisy-generation results
GenLimit.Angluin                        = generic Core + unnumbered semantic/effective support
GenLimit.Paper08_HallucinationDetection = generic Core + Angluin + native #08 results (excluding theorem A.2)
GenLimit.Paper28_ContrastiveGeneration  = generic Core + Angluin semantic necessity + native #28 results
GenLimit.Paper31_BoundedMemory          = Core + native #31 bounded-memory results
GenLimit.Paper39_DenseGeneration        = Core + #39 dense-generation results
GenLimit.Bridges                        = Core + explicit #0/#01/#39 and #02/#08 comparisons
GenLimit                 = all of the above
```

The generic semantic necessity theorem
`GenLimit.Angluin.conditionTwo_of_semanticallyIdentifiable` belongs to the
Angluin support theory because its statement uses only Angluin vocabulary. #08
retains `GenLimit.HallucinationDetection.conditionTwo_of_identifiable` as a
thin source-facing wrapper, while #28 invokes the canonical Angluin
theorem directly. The generic theorem
`GenLimit.Generic.stabilizingIndexIdentifier_implies_generatableInLimit`
belongs to Core because it mentions none of the numbered paper vocabularies;
`ContrastiveGeneration.textIdentification_implies_generation` is the
source-facing specialization. Conversely,
`GenLimit.HallucinationDetection.theorem_A_2` is physically declared in the
#02-to-#08 bridge even though it keeps the paper namespace.
