# Shared foundations and cross-paper relationships

This map records mathematical reuse while keeping #0 Language Identification,
#0A Inductive Inference from Positive Data, #01 Language Generation, #02
Learning Theory, #03 Hallucination and Mode Collapse, #04 Exploring Facets,
#05 Hallucinations, Breadth, and Stability, #06 Noisy Examples,
#08 Hallucination Detection, #28 Contrastive Generation,
#31 Bounded Memory, and #39 Dense Generation independently buildable.

## Shared foundations

| Shared declaration | Module | Paper uses |
|---|---|---|
| `Language`, `LanguageFamily` | `GenLimit.Core.Basic` | #0 targets and names; #01 and #39 target families |
| `Presents`, `sample`, `Consistent` | `GenLimit.Core.Basic` | #0 exact texts; #01 and #39 observations and consistency |
| `Critical`, `critical_subset_of_le`, `target_eventually_critical` | `GenLimit.Paper01_LanguageGeneration.Critical` | #01 semantic generation; #39 arXiv-v1 Definition 3.2, Remark 3.3, and Lemma 3.4 |
| `textPrefix`, `textPrefix_toFinset` | `GenLimit.Core.Text` | #0 ordered histories and their unordered sample view |
| `Learner`, `StabilizesTo`, `IdentifiesInLimit` | `GenLimit.Core.Identification` | Shared logical form of #0, #0A, and #03 semantic identification |
| `consistent_of_target_subset` | `GenLimit.Core.Basic` | #0 least-compatible enumeration; #01 candidate consistency; #39 focus consistency |
| `finite_scope_eventually_consistent_iff_target_subset` | `GenLimit.Core.TargetStability` | #0 stabilization; eventual #01 criticality; #39 Lemma 3.4 and scope progress |
| `OracleFamily` | `GenLimit.Core.OracleFamily` | #0 generation bridges; #01 semantic and finite-query paths; #39 common family object |
| `FreshGeneratesInLimit`, `NovelGeneratesInLimit` | `GenLimit.Core.OnlineGeneration` | #0 comparison target; #01 freshness; #39 validity, freshness, and self-novelty |
| `Language`, `LanguageClass`, `LanguageFamily`, `Stream`, `Generator`, `Presents` | `GenLimit.Core.GenericGeneration` | Generic countable-universe generation vocabulary used by #02, #03, #04, #05, #06, #28, and #31 |
| `OrderedLanguage`, prefix ratios, lower density, upper density | `GenLimit.Core.OrderedDensity` | Paper-independent Kleinberg--Wei ordered-density interface used by #31; declarations retain namespace `GenLimit.KleinbergWei` |
| `UUS`, limit/uniform/nonuniform generation predicates | `GenLimit.Core.ClassGeneration` | Paper-independent quantifier patterns shared by #02, #04 bridges, #06, and #28 |
| `versionSpace`, `commonCore`, `closure` | `GenLimit.Core.VersionSpace` | Positive-data version-space and closure vocabulary used by #02 and the noiseless side of #06 |
| Closure-witness and closure-dimension predicates | `GenLimit.Core.ClosureDimension` | Paper-independent combinatorial closure notions reused in #06's separation example |
| `IsFiniteCover`, `IsNondecreasingCover` | `GenLimit.Core.ClassCovers` | Finite and increasing class-cover interfaces reused by #02, #06, and #28 |
| `stabilizingIndexIdentifier_implies_generatableInLimit` | `GenLimit.Core.IdentificationGeneration` | Paper-independent semantic identification-to-fresh-generation implication extracted for #28's clean hierarchy |
| Exact presentations, finite-prefix completion, and infinite-set enumeration/progress | `GenLimit.Support.Presentations`, `GenLimit.Support.EnumerationProgress` | Neutral infrastructure used by #04 source/Core equivalences and exhaustive proofs, without enlarging Core |
| Finite candidate race | `GenLimit.Support.FiniteCandidateRace` | Proof infrastructure shared by #02 finite-cover arguments and #06 Theorem 3.10 without enlarging the Core umbrella |
| `conditionTwo_of_semanticallyIdentifiable` | `GenLimit.Paper00A_PositiveDataInference.Semantic.Necessity` | #0A finite-tell-tale necessity, proved by countable pullback to #0 and used directly by #08 and #28 |

## Semantic identification equivalence chain

Let `alpha` be a nonempty countable example type, let `H` be a nonempty
countable extensional language class, and let `E : ClassEnumeration H` be an
indexed enumeration of that class.  The following is one kernel-checked
semantic equivalence chain:

```text
P02 ExtensionallyIdentifiable H
  <-> #0A Angluin SemanticallyInferrable E.family
  <-> #0A Angluin ConditionTwo E.family
  <-> P02 ExtensionalTellTaleCondition H
  <-> #08 HallucinationDetectable E.family
  <-> #08 ConsecutivelyIdentifiable E.family
```

The #0A identification/tell-tale edge is
`Angluin.semanticallyInferrable_iff_conditionTwo`.  The transport to P02's
language-valued, extensional interface is proved by
`Angluin.semanticallyInferrable_iff_extensionallyIdentifiable` and
`Angluin.conditionTwo_iff_extensionalTellTaleCondition`; their composition is
the corrected, countable P02 Theorem 2.3,
`Angluin.theorem_2_3_countable`.  On the #08 side, Theorem 2.1
(`HallucinationDetection.theorem_2_1`) identifies hallucination detectability
with the same stable-index semantic identification predicate, while
`HallucinationDetection.definition_3_equivalence` identifies the paper's
literal consecutive-guess formulation with that predicate.  Corollary 2.2
and Appendix Theorem A.1 also package the two direct equivalences with
`ConditionTwo`.

P02 uses an extensional set of languages, whereas #0A and #08 use an indexed
family; `E` is therefore a genuine representation bridge, not a definitional
equality.  The empty P02 class is handled separately by
`theorem_2_3_countable`.  These are semantic results: the chain does not
identify #08's oracle detector with the computable learner or uniformly
enumerable tell-tales in #0A's effective Theorem 1.

## Explicit bridge

| Relationship | Lean declaration | Module |
|---|---|---|
| #0 identification implies fresh generation on an infinite indexed family | `Gold.identifier_implies_fresh_generation` | `GenLimit.Bridges.Paper00ToPaper01` |
| #01 generation without #0 text identification on the co-singleton family | `GoldKMSeparation.generation_without_identification` | `GenLimit.Bridges.Paper00ToPaper01` |
| PatientScope novelty and density without #0 text identification on the same family | `GoldDenseSeparation.dense_generation_without_identification` | `GenLimit.Bridges.Paper00ToPaper39` |
| #01 criticality implies #39 recursive criticality | `critical_recursiveCritical` | `GenLimit.Bridges.Paper01ToPaper39` |
| #04 exact-presentation non-uniform and uniform generation agree with the shared #02/Core predicates on nonempty countable indexed languages | `Bridge.Paper02ToPaper04.nonuniformlyGeneratable_iff`, `uniformlyGeneratable_iff` | `GenLimit.Bridges.Paper02ToPaper04` |
| #04 Theorem 1 follows from #02 Corollary 3.6 | `Bridge.Paper02ToPaper04.theorem_1_from_paper02_corollary_3_6` | `GenLimit.Bridges.Paper02ToPaper04` |
| #04 exact breadth implies the #03 Theorem 3.5 identification premise | `Bridge.Paper03ToPaper04.paper04_breadth_implies_paper03_identifiable` | `GenLimit.Bridges.Paper03ToPaper04` |
| With the #03 family-membership oracle, #04 exact breadth implies existence of a #03 fresh-breadth support generator | `Bridge.Paper03ToPaper04.paper04_breadth_implies_paper03_fresh_breadth` | `GenLimit.Bridges.Paper03ToPaper04` |
| #04 exact breadth implies literal #05 exact breadth after removing the observed sample | `Bridge.Paper04ToPaper05.paper04_breadth_implies_paper05_literalExact` | `GenLimit.Bridges.Paper04ToPaper05` |
| #05's weak Angluin condition is the range form of the #04 weak Angluin condition | `Bridge.Paper04ToPaper05.paper05_weakAngluin_iff_paper04_range` | `GenLimit.Bridges.Paper04ToPaper05` |
| #04 exhaustive generatability is equivalent to #05's weak Angluin condition | `Bridge.Paper04ToPaper05.paper04_exhaustive_iff_paper05_weakAngluin` | `GenLimit.Bridges.Paper04ToPaper05` |
| #03 exact fresh breadth implies #08 hallucination detectability, without a family-membership oracle | `Bridge.Paper03ToPaper08.freshBreadth_implies_hallucinationDetectable` | `GenLimit.Bridges.Paper03ToPaper08` |
| With the #03 family-membership oracle, #08 hallucination detectability is equivalent to existence of a #03 fresh-breadth support generator | `Bridge.Paper03ToPaper08.hallucinationDetectable_iff_freshBreadthInLimit` | `GenLimit.Bridges.Paper03ToPaper08` |
| Every countable #08 family is generatable in the Appendix Definition 5 sense, via #02 Corollary 3.6 on its infinite members | `HallucinationDetection.theorem_A_2` | `GenLimit.Bridges.Paper02ToPaper08` |

These are comparison theorems, not hidden implementation dependencies. The
native paper umbrellas build without importing the bridge layer. #08's
identification and tell-tale statements explicitly reuse #0A;
the only substantive #02 dependency is the Appendix A.2 bridge.
#03 directly reuses #0 informant identification, #0A semantic Angluin
identification, and #01's KM semantic engine, but it does not import #04;
their different breadth objects meet only in `Paper03ToPaper04`.  The derived
#03/#08 relationship is similarly isolated in `Paper03ToPaper08`: neither
native paper umbrella imports the other.
#05 directly reuses #0A's semantic Angluin construction, #04's critical-focus
infrastructure for Theorem 3.8 sufficiency, and #03's stable-approximate
necessity reduction. Its support-valued predicates remain P05-local. Pure
#04/#05 comparisons are isolated in `Paper04ToPaper05`.
#28 also imports #0A, but only its semantic necessity and characterization
theorems. #0A's semantic necessity proof reuses #0's positive-text finite-
tell-tale theorem. #28 imports neither #02 nor #08, and it
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

Paper-facing wrappers may remain separate, but a genuinely shared proof may
be reused when the dependency is explicit. In particular, #0A transports
#0's finite-tell-tale necessity theorem, while #01's
`least_consistent_critical` and #39's
`recursiveCritical_of_consistent_of_minimal` remain separate paper-facing
facts.

In #06, `NoisyExamples.commonIntersection_eq_commonCore_empty` identifies the
paper's class-wide intersection with `Generic.commonCore H ∅`.  The
paper-facing name is retained because it occurs in the source statement of
Theorem 3.1.

## Import invariant

```text
GenLimit.Paper00_LanguageIdentification = Core + #0 abstract, text, and informant identification
GenLimit.Paper00A_PositiveDataInference = generic Core + #0A semantic/effective positive-data inference (+ #0 semantic necessity)
GenLimit.Paper01_LanguageGeneration     = Core + #01 semantic and finite-query paths
GenLimit.Paper02_LearningTheory         = generic Core + neutral Support + #02 ordinary, prompted, prediction-proxy, and EUC results
GenLimit.Paper03_HallucinationAndModeCollapse = generic Core + #0/#0A identification reuse + #01 KM semantic reuse + native #03 support reductions
GenLimit.Paper04_ExploringFacetsOfLanguageGeneration = generic Core + neutral Support + #0A Angluin reuse + native completed #04 results
GenLimit.Paper05_HallucinationsBreadthAndStability = generic Core + neutral Support + #0A/#03/#04 semantic reuse + native #05 support results and source-gap theorems
GenLimit.Paper06_NoisyExamples          = generic Core + neutral Support + #06 noisy-generation results
GenLimit.Paper08_HallucinationDetection = generic Core + #0A + native #08 results (excluding theorem A.2)
GenLimit.Paper28_ContrastiveGeneration  = generic Core + #0A semantic necessity + native #28 results
GenLimit.Paper31_BoundedMemory          = Core + native #31 bounded-memory results
GenLimit.Paper39_DenseGeneration        = Core + #01 criticality reuse for arXiv v1 + #39 dense-generation results
GenLimit.Bridges                        = Core + explicit #0/#01/#39, #02/#04, #03/#04, #04/#05, #03/#08, and #02/#08 comparisons
GenLimit                 = all of the above
```

The #0A semantic necessity theorem
`GenLimit.Angluin.conditionTwo_of_semanticallyIdentifiable` belongs to the
#0A development because its statement uses only Angluin vocabulary; its proof
reuses #0 through an explicit countable-domain pullback. #08's Corollary 2.2
and #28 both invoke the canonical Angluin theorem directly. The generic theorem
`GenLimit.Generic.stabilizingIndexIdentifier_implies_generatableInLimit`
belongs to Core because it mentions none of the numbered paper vocabularies;
`ContrastiveGeneration.textIdentification_implies_generation` is the
source-facing specialization. Conversely,
`GenLimit.HallucinationDetection.theorem_A_2` is physically declared in the
#02-to-#08 bridge even though it keeps the paper namespace.
