# GenLimit

`GenLimit` is a Lean 4 library for language identification and generation in
the limit. It formalizes a semantic layer of Gold's classical identification
model, the foundational Kleinberg--Mullainathan theorem,
Li--Raman--Tewari's learning-theoretic generation characterizations,
Raman--Raman's generation-from-noisy-examples results, Paper 08's automated
hallucination-detection equivalence, Li--Han--Jiang--Gao's contrastive
identification and generation theory, and the DenseGeneration patient-scope
result, while keeping shared mathematics,
paper-specific developments, and cross-paper comparisons separate.

The project uses Lean 4.24.0 and Mathlib 4.24.0. All current main theorem
paths compile without `sorry`, `admit`, or project-defined axioms.

## Main results

| Development | Main Lean declaration | Formalized result |
|---|---|---|
| Gold Theorem 7.1 | `GenLimit.Gold.Abstract.gold_theorem_7_1` | Distinguishability is necessary; collapsing uncertainty makes every enumeration learner succeed; countable allowable-sequence fibers make distinguishability sufficient |
| Gold finite-text learning | `GenLimit.Gold.Text.finiteLearner_identifiesFiniteLanguages` | Every finite language is identifiable from every exact positive text |
| Gold sharp text boundary | `GenLimit.Gold.Text.finiteLanguages_maximal_semanticallyIdentifiable` | Finite languages are semantically identifiable, and every proper superclass is not |
| Gold complete informants | `GenLimit.Gold.Informant.informantEnumerationLearner_identifiesFamily` | Every indexed family is semantically identifiable from complete positive/negative data |
| Gold superfinite obstruction | `GenLimit.Gold.Text.superfinite_not_semanticallyIdentifiable` | No semantic learner identifies a class containing all finite languages and an infinite language from arbitrary positive text |
| KM semantic | `GenLimit.KM.Semantic.kleinbergMullainathan_main` | Round-indexed, noncomputable Section 4 guarantee (4.6) |
| KM observed-set interface | `GenLimit.KM.SetInterface.kleinbergMullainathan_set_interface_with_repetitions` | Literal finite-set-only Section 4 guarantee for arbitrary exact presentations, including repetitions |
| KM finite-query | `GenLimit.OracleFamily.kleinbergMullainathan_main` | Stateful endpoint-test algorithm from the NeurIPS proceedings |
| KM arXiv-v1 finite-query | `GenLimit.OracleFamily.ArxivV1.kleinbergMullainathan_main` | Stateful least-fresh whole-prefix algorithm from arXiv v1 |
| LRT uniform characterization | `GenLimit.LiRamanTewari.uniform_generatability_iff_finite_closure_dimension` | Uniform generation iff finite closure dimension |
| LRT nonuniform characterization | `GenLimit.LiRamanTewari.nonuniform_generatability_iff_nondecreasing_finite_closure_cover` | Nonuniform generation iff there is a nondecreasing finite-closure cover |
| LRT countable-class theorem | `GenLimit.LiRamanTewari.theorem_2_4` | Every countable UUS class is generatable in the limit |
| LRT prompted characterization | `GenLimit.LiRamanTewari.prompted_uniform_generatability_iff_finite_prompted_closure_dimension` | Prompted uniform generation iff finite prompted closure dimension |
| LRT Appendix C | `GenLimit.LiRamanTewari.theorem_C4_eventually_unbounded_closure` | Generation from a nondecreasing finite-EUC cover |
| Raman--Raman uniform noise-independent | `GenLimit.NoisyExamples.theorem_3_1` | Uniform noise-independent generation iff the class-wide common intersection is infinite, with the source's implicit ambient-universe assumption exposed |
| Raman--Raman uniform noise-dependent | `GenLimit.NoisyExamples.theorem_3_3` | Uniform noise-dependent generation iff every fixed noise level has finite noisy closure dimension |
| Raman--Raman robustification | `GenLimit.NoisyExamples.theorem_3_9` | Ordinary non-uniform generation implies noisy generation in the limit |
| Raman--Raman appendices | `GenLimit.NoisyExamples.theorem_C_3`, `GenLimit.NoisyExamples.lemma_D_2` | Bounded noisy-closure excess characterization and the finite parity-class separation |
| Hallucination detection | `GenLimit.HallucinationDetection.theorem_2_1` | Positive-only hallucination detection in the limit iff semantic identification in the limit |
| Hallucination tell-tales | `GenLimit.HallucinationDetection.corollary_2_2` | Hallucination detectability iff Angluin's finite tell-tale condition |
| Detection with negative examples | `GenLimit.HallucinationDetection.theorem_2_3` | Every indexed family is detectable from every valid complete labeled enumeration |
| Hallucination Appendix A.2 | `GenLimit.HallucinationDetection.theorem_A_2` | Countable families are generatable in the appendix sense; isolated in the LRT-to-Paper-08 bridge |
| Contrastive identification | `GenLimit.ContrastiveGeneration.theorem_4_7` | Text identification plus pairwise overlap characterizes contrastive identification |
| Contrastive closure dimension | `GenLimit.ContrastiveGeneration.theorem_5_4_quantitative`, `theorem_5_4` | The exact `d + 1` threshold and qualitative finite-dimension characterization |
| Non-uniform contrastive generation | `GenLimit.ContrastiveGeneration.theorem_5_5` | Characterization by an increasing cover with finite contrastive closure dimension |
| Clean hierarchy witnesses | `GenLimit.ContrastiveGeneration.theorem_5_13_5_14_punctured_witness`, `theorem_5_13_5_14_disjoint_witness` | Concrete components of the clean hierarchy and incomparability results |
| Robust contrastive identification | `GenLimit.ContrastiveGeneration.absenceCountIdentifier_finitely_identifies`, `theorem_6_6`, `theorem_6_8` | The named absence-count identifier handles every finite corruption budget; corrupted text and contrastive identification are incomparable |
| Contrastive defect identity | `GenLimit.ContrastiveGeneration.proposition_6_3_defect_eq_forced_wrong_cut_infimum` | Exact extended-natural defect number as an infimum of forced wrong-cut counts |
| DenseGeneration | `GenLimit.PatientMachine.patientScope_lowerDensity_half` | Patient-scope lower density at least `1 / 2` for every exactly presented target |
| DenseGeneration joint conclusion | `GenLimit.PatientMachine.patientScope_generation_and_lowerDensity` | Eventual validity, freshness, output novelty, and the same density bound |
| Gold--KM separation | `GenLimit.GoldKMSeparation.generation_without_identification` | One explicit uniformly decidable family is KM-generatable but not Gold-identifiable from arbitrary positive text |
| Gold--Dense separation | `GenLimit.GoldDenseSeparation.dense_generation_without_identification` | The same family has PatientScope novelty and density at least `1 / 2`, while remaining nonidentifiable from text |
| Partial-enumeration counterexample | `GenLimit.PartialEnumeration.Counterexample.output_not_mem_trueLanguage` | Example 3.15 for an explicit increasing multiples-of-four enumeration |
| Partial enumeration, Lemma 3.16 | `GenLimit.PartialEnumeration.lemma_3_16_generation` | Eventual target validity and novelty when an infinite `E ⊆ K` is presented |
| Partial enumeration, Theorem 3.17 | `GenLimit.PartialEnumeration.theorem_3_17` | Generator density at least one half of the relative lower density of `E` in `K` |

The Gold development models ordered finite histories, explanatory
identification (eventual stabilization to one fixed name), arbitrary exact
positive texts, and complete Boolean-labeled informants. Its abstract layer
formalizes all three clauses of Gold's Theorem 7.1. It also includes the
finite-language learner, bounded least-compatible enumeration, locking
sequences, finite tell-tale necessity, and the semantic arbitrary-text form
of Gold's superfinite nonidentifiability theorem. This is deliberately a
semantic first layer: Turing-machine indices, recursive or
primitive-recursive texts, and effectiveness-specific diagonal theorems are
not yet formalized. Since an exact text has type `ℕ → ℕ`, the empty language
has no text; statements about its texts are therefore vacuous unless a future
model adds a pause symbol.

All four KM paths eventually output target elements that are fresh relative to
the observed adversary sample. The semantic and finite-set proofs compare
whole infinite languages and are noncomputable; the two finite-query
developments realize their tests through the Boolean membership oracle. The
endpoint and whole-prefix stopping rules are retained as separate source
versions.

The Li--Raman--Tewari path uses a generic countable example type. It includes
the ordinary and prompted closure characterizations, quantitative uniform
sample-complexity bounds, hierarchy separations, finite-cover results, and the
valid Appendix C theorems. Its Theorem 4.1 declarations intentionally stop at
the VC/Littlestone combinatorial layer: no probability space, PAC learner,
online algorithm, regret bound, or computational-efficiency theorem is
claimed. Lean also refutes the paper's stronger arbitrary-stream EUC prose
equivalence without weakening Theorems C.2 or C.4.

The Raman--Raman path formalizes occurrence-count noise, noisy presentations,
noisy closure witnesses, uniform and non-uniform characterizations,
robustification, and the Appendix C/D variants. It exposes nonempty or
infinite ambient-universe assumptions needed to repair degenerate printed
statements. The numerical `NC_n`, its asymptotic sample-complexity claim, and
computational efficiency remain outside the formalized boundary. Its shared
generation, closure, and cover vocabulary comes from neutral `GenLimit.Core`
modules; the paper path does not import substantive LRT theorems.

The Paper 08 path formalizes finite adaptive candidate-set query trees,
positive-only hallucination detection, its equivalence with semantic
identification, the finite-tell-tale characterization, and complete labeled
negative-example detection. Lean corrects the source's false inference after
Example 1: the multiples family has singleton tell-tales and is detectable.
Its native modules depend on the sibling `GenLimit.Angluin` development but
not on substantive LRT results. Theorem A.2 is physically isolated in
`GenLimit.Bridges.LiRamanTewariToHallucinationDetection`, the one location
where LRT Corollary 3.6 is used. No effective detector, query/runtime bound,
probabilistic extension, or effective tell-tale discovery theorem is claimed.

The Paper 28 path formalizes pairwise contrastive geometry, semantic
identification, uniform and target-dependent closure characterizations, core
conditions, explicit hierarchy witnesses, finite-occurrence corruption, and
the exact defect infimum. Its native modules use generic Core vocabulary and
the sibling Angluin semantic-necessity theorem, but import neither the LRT nor
Paper 08 development. The ordinary identification-to-fresh-generation lemma
is paper-independent and lives in `GenLimit.Core.IdentificationGeneration`.
The audit-identified Theorem 6.6 interface gap is resolved by
`absenceCountIdentifier_finitely_identifies`, which exposes the named
budget-independent witness without adding assumptions or oracle access.
Nevertheless, its minimizer is chosen classically: no fixed-enumeration
tie-break, computability, runtime, or oracle-free implementation theorem is
claimed. The full clean strict diamond, unordered-edge learner transport,
general infinite-defect robustness principle, corrupted generation, and
probabilistic extensions remain outside the formalized boundary.

The DenseGeneration machine is also semantic and noncomputable because its
recursive criticality uses exact inclusion between infinite languages. Its
theorem proves the `1 / 2` achievability bound for arbitrary, possibly sparse,
targets. It does not claim finite-query execution or formalize the separate
upper bound needed for optimality.

The Section 3.3 path lets the stream present an infinite sublanguage `E ⊆ K`.
It runs the same patient-scope machine on a filtered finite-intersection
closure and proves density at least one half of the relative lower density of
`E` in `K`. The filter semantically discards finite intersections; deciding
that infinitude and reindexing the retained family are noncomputable from the
pointwise membership oracle in general.

## Library structure

```text
GenLimit.Core
├── GenLimit.Gold
├── GenLimit.KM
├── GenLimit.LiRamanTewari
├── GenLimit.NoisyExamples
├── GenLimit.Angluin
├── GenLimit.HallucinationDetection
├── GenLimit.ContrastiveGeneration
└── GenLimit.DenseGeneration

GenLimit.Bridges  (explicit cross-paper results)
```

- `GenLimit.Core` contains paper-independent definitions and stabilization
  lemmas.
- `GenLimit.Gold` contains semantic identification from text and informants.
- `GenLimit.KM` contains the semantic and finite-query KM developments.
- `GenLimit.LiRamanTewari` contains learning-theoretic ordinary and prompted
  generation results.
- `GenLimit.NoisyExamples` contains Raman--Raman's noisy-generation models,
  characterizations, robustification, examples, and appendix results.
- `GenLimit.Angluin` contains semantic identification and tell-tale theory,
  with effective interfaces kept explicitly separate.
- `GenLimit.HallucinationDetection` contains the native Paper 08 detector,
  reduction, negative-example, Example 1, and appendix definitions/results.
- `GenLimit.ContrastiveGeneration` contains Paper 28's geometry,
  identification, closure, hierarchy, corruption, and defect developments.
- `GenLimit.DenseGeneration` contains the abstract counting argument and the
  exact- and partial-enumeration patient-scope developments.
- `GenLimit.Bridges` contains explicit comparison theorems without making one
  paper development depend on the other.

The umbrella module [`GenLimit.lean`](GenLimit.lean) imports all layers.
The paper-specific umbrellas [`GenLimit/Gold.lean`](GenLimit/Gold.lean),
[`GenLimit/KM.lean`](GenLimit/KM.lean),
[`GenLimit/LiRamanTewari.lean`](GenLimit/LiRamanTewari.lean),
[`GenLimit/NoisyExamples.lean`](GenLimit/NoisyExamples.lean),
[`GenLimit/Angluin.lean`](GenLimit/Angluin.lean),
[`GenLimit/HallucinationDetection.lean`](GenLimit/HallucinationDetection.lean),
[`GenLimit/ContrastiveGeneration.lean`](GenLimit/ContrastiveGeneration.lean), and
[`GenLimit/DenseGeneration.lean`](GenLimit/DenseGeneration.lean) can be used
independently.

## Build

From this directory:

```bash
lake exe cache get
lake build
lake env lean Audit.lean
```

Individual developments can also be built separately:

```bash
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
lake build GenLimit.DenseGeneration
lake build GenLimit.DenseGeneration.Partial
lake build GenLimit.Bridges
```

Opening this directory in VS Code with the Lean 4 extension provides
interactive theorem goals and diagnostics.

## Suggested reading order

| Goal | Start with |
|---|---|
| Shared model and exact presentations | [`GenLimit/Core/Basic.lean`](GenLimit/Core/Basic.lean) |
| Ordered text prefixes and generic identification | [`GenLimit/Core/Text.lean`](GenLimit/Core/Text.lean), then [`GenLimit/Core/Identification.lean`](GenLimit/Core/Identification.lean) |
| Generic identification-to-fresh-generation implication | [`GenLimit/Core/IdentificationGeneration.lean`](GenLimit/Core/IdentificationGeneration.lean) |
| Consistency stabilization | [`GenLimit/Core/TargetStability.lean`](GenLimit/Core/TargetStability.lean) |
| Indexed language family and membership oracle | [`GenLimit/Core/OracleFamily.lean`](GenLimit/Core/OracleFamily.lean) |
| Gold's learner and identification model | [`GenLimit/Gold/Text/Model.lean`](GenLimit/Gold/Text/Model.lean) |
| Gold's abstract Theorem 7.1 | [`GenLimit/Gold/Abstract/Model.lean`](GenLimit/Gold/Abstract/Model.lean), then [`GenLimit/Gold/Abstract/Enumeration.lean`](GenLimit/Gold/Abstract/Enumeration.lean) |
| Gold finite-text learnability | [`GenLimit/Gold/Text/Finite.lean`](GenLimit/Gold/Text/Finite.lean) |
| Gold locking and superfinite obstruction | [`GenLimit/Gold/Text/Locking.lean`](GenLimit/Gold/Text/Locking.lean), then [`GenLimit/Gold/Text/Superfinite.lean`](GenLimit/Gold/Text/Superfinite.lean) |
| Gold complete-informant learning | [`GenLimit/Gold/Informant/Model.lean`](GenLimit/Gold/Informant/Model.lean), then [`GenLimit/Gold/Informant/Enumeration.lean`](GenLimit/Gold/Informant/Enumeration.lean) |
| Short semantic KM proof | [`GenLimit/KM/Critical.lean`](GenLimit/KM/Critical.lean), then [`GenLimit/KM/Semantic.lean`](GenLimit/KM/Semantic.lean) |
| Literal observed-set KM proof | [`GenLimit/KM/SetInterface.lean`](GenLimit/KM/SetInterface.lean) |
| Finite-query KM algorithms | [`GenLimit/KM/FiniteQuery.lean`](GenLimit/KM/FiniteQuery.lean), with the arXiv-v1 variant in [`GenLimit/KM/FiniteQuery/ArxivV1.lean`](GenLimit/KM/FiniteQuery/ArxivV1.lean) |
| Li--Raman--Tewari generation theory | [`GenLimit/LiRamanTewari/Definitions.lean`](GenLimit/LiRamanTewari/Definitions.lean), then [`Closure.lean`](GenLimit/LiRamanTewari/Closure.lean), [`NonuniformCharacterization.lean`](GenLimit/LiRamanTewari/NonuniformCharacterization.lean), and the umbrella [`GenLimit/LiRamanTewari.lean`](GenLimit/LiRamanTewari.lean) |
| Raman--Raman noisy generation | [`GenLimit/NoisyExamples/UniformIndependent.lean`](GenLimit/NoisyExamples/UniformIndependent.lean), then [`NoisyClosure.lean`](GenLimit/NoisyExamples/NoisyClosure.lean), [`Nonuniform.lean`](GenLimit/NoisyExamples/Nonuniform.lean), [`NoiselessRobustification.lean`](GenLimit/NoisyExamples/NoiselessRobustification.lean), and the umbrella [`GenLimit/NoisyExamples.lean`](GenLimit/NoisyExamples.lean) |
| Angluin semantic identification and tell-tales | [`GenLimit/Angluin/Definitions.lean`](GenLimit/Angluin/Definitions.lean), then [`SemanticSufficiency.lean`](GenLimit/Angluin/SemanticSufficiency.lean), [`SemanticNecessity.lean`](GenLimit/Angluin/SemanticNecessity.lean), and [`LockingExistence.lean`](GenLimit/Angluin/LockingExistence.lean) |
| Paper 08 hallucination detection | [`GenLimit/HallucinationDetection/Definitions.lean`](GenLimit/HallucinationDetection/Definitions.lean), then [`Reductions.lean`](GenLimit/HallucinationDetection/Reductions.lean), [`AngluinCondition.lean`](GenLimit/HallucinationDetection/AngluinCondition.lean), and [`Appendix.lean`](GenLimit/HallucinationDetection/Appendix.lean) |
| LRT-to-Paper-08 Appendix A.2 bridge | [`GenLimit/Bridges/LiRamanTewariToHallucinationDetection.lean`](GenLimit/Bridges/LiRamanTewariToHallucinationDetection.lean) |
| Paper 28 contrastive identification | [`GenLimit/ContrastiveGeneration/Geometry.lean`](GenLimit/ContrastiveGeneration/Geometry.lean), [`IdentificationGeometry.lean`](GenLimit/ContrastiveGeneration/IdentificationGeometry.lean), then [`IdentifierCharacterization.lean`](GenLimit/ContrastiveGeneration/IdentifierCharacterization.lean) |
| Paper 28 generation and hierarchy | [`GenLimit/ContrastiveGeneration/GenerationCores.lean`](GenLimit/ContrastiveGeneration/GenerationCores.lean), [`ClosureDimension.lean`](GenLimit/ContrastiveGeneration/ClosureDimension.lean), [`NonuniformClosure.lean`](GenLimit/ContrastiveGeneration/NonuniformClosure.lean), then [`Hierarchy.lean`](GenLimit/ContrastiveGeneration/Hierarchy.lean) |
| Paper 28 corruption and defect | [`GenLimit/ContrastiveGeneration/CorruptedPresentations.lean`](GenLimit/ContrastiveGeneration/CorruptedPresentations.lean), [`AbsenceCount.lean`](GenLimit/ContrastiveGeneration/AbsenceCount.lean), [`CorruptedIncomparability.lean`](GenLimit/ContrastiveGeneration/CorruptedIncomparability.lean), then [`DefectInfimum.lean`](GenLimit/ContrastiveGeneration/DefectInfimum.lean) |
| DenseGeneration criticality and machine | [`GenLimit/DenseGeneration/Critical.lean`](GenLimit/DenseGeneration/Critical.lean), then [`GenLimit/DenseGeneration/Patient/Machine.lean`](GenLimit/DenseGeneration/Patient/Machine.lean) |
| DenseGeneration proof chain | `Patient/Validity.lean`, `Patient/Fact312.lean`, `Patient/Charging.lean`, then [`Patient/Main.lean`](GenLimit/DenseGeneration/Patient/Main.lean) |
| Partial enumeration (Section 3.3) | [`Partial/Counterexample.lean`](GenLimit/DenseGeneration/Partial/Counterexample.lean), then [`Core/PartialPresentation.lean`](GenLimit/Core/PartialPresentation.lean), [`Partial/Closure.lean`](GenLimit/DenseGeneration/Partial/Closure.lean), [`Partial/Validity.lean`](GenLimit/DenseGeneration/Partial/Validity.lean), and [`Partial/Main.lean`](GenLimit/DenseGeneration/Partial/Main.lean) |
| Gold/KM/Dense comparison | [`GenLimit/Bridges/GoldToKM.lean`](GenLimit/Bridges/GoldToKM.lean), [`GenLimit/Bridges/GoldToDenseGeneration.lean`](GenLimit/Bridges/GoldToDenseGeneration.lean), and [`GenLimit/Bridges/KMToDenseGeneration.lean`](GenLimit/Bridges/KMToDenseGeneration.lean) |

## Paper maps and audits

- [`PAPER_MAP.md`](PAPER_MAP.md) is the repository-level paper registry.
- [`PaperMaps/Gold.md`](PaperMaps/Gold.md) maps Gold's 1967 paper to Lean
  declarations and records the semantic/effective boundary.
- [`PaperMaps/KM.md`](PaperMaps/KM.md) maps the KM paper to Lean declarations.
- [`PaperMaps/LiRamanTewari.md`](PaperMaps/LiRamanTewari.md) maps the ordinary,
  prompted, prediction-proxy, and EUC developments and their explicit gaps.
- [`PaperMaps/NoisyExamples.md`](PaperMaps/NoisyExamples.md) maps every
  paper-owned Raman--Raman result and its explicit source repairs.
- [`PaperMaps/HallucinationDetection.md`](PaperMaps/HallucinationDetection.md)
  maps Paper 08, including its corrected Example 1 inference and audit limits.
- [`PaperMaps/Angluin.md`](PaperMaps/Angluin.md) records the semantic/effective
  boundary of the Angluin sibling used by Papers 08 and 28.
- [`PaperMaps/ContrastiveGeneration.md`](PaperMaps/ContrastiveGeneration.md)
  maps Paper 28, including its baseline-to-audit-to-repair chronology and
  remaining semantic/effective limits.
- [`PaperMaps/DenseGeneration.md`](PaperMaps/DenseGeneration.md) maps the
  DenseGeneration manuscript to Lean declarations.
- [`PaperMaps/RELATIONSHIPS.md`](PaperMaps/RELATIONSHIPS.md) records shared
  foundations and explicit bridges.
- [`AUDIT.md`](AUDIT.md) records kernel, axiom, and access-model checks.
- [`AuditRecords/`](AuditRecords/) preserves checksum-verified, paper-scoped
  external review evidence without treating it as human audit.
- [`HUMAN_AUDIT.md`](HUMAN_AUDIT.md) records the Level 3 KM semantic audit and
  the Level 2 DenseGeneration audits for exact presentation and the Section
  3.3 Lemma 3.16--Theorem 3.17 path. It also records completion of the shared
  Core prerequisites and Gold Text audit at Level 2. Gold's Abstract, text
  enumeration, informant, and bridge paths, together with DenseGeneration
  Example 3.15, have not yet received a recorded human paper-to-Lean audit.
  The KM observed-set and both finite-query paths are likewise outside the
  human record; their AI-assisted statement comparison is linked from the KM
  paper map. Li--Raman--Tewari is kernel-checked and AI-compared to its pinned
  source but has no assigned human correspondence level. Raman--Raman is also
  kernel-checked and AI-compared to its pinned source, with human
  correspondence pending. Paper 08 is kernel-checked and AI-compared to its
  pinned arXiv-v2 source; it likewise has no assigned human correspondence
  level. Paper 28 is kernel-checked and AI-compared to its pinned arXiv-v1
  source. The named-witness repair resolves the audit's Theorem 6.6 interface
  finding, but no human correspondence level has been assigned. The Angluin
  sibling has no separate external or human audit record.

Bibliographic metadata is collected in [`CITATION.bib`](CITATION.bib).
