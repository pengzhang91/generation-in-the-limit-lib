# GenLimit

`GenLimit` is a Lean 4 library for language identification and generation in
the limit. Its numbered paper paths currently formalize #0 Language
Identification, #0A Inductive Inference from Positive Data, #01 Language
Generation, #02 Learning Theory, #03 Hallucination and Mode Collapse, #04
Exploring Facets, #06 Noisy
Examples, #08 Hallucination Detection, Paper11 Union-Closedness, #28
Contrastive Generation, #31 Bounded Memory, and #39 Dense Generation, while
keeping shared mathematics, paper-specific developments, and cross-paper
comparisons separate.

The project uses Lean 4.24.0 and Mathlib 4.24.0. All completed main theorem
paths, including Paper11, compile without `sorry`, `admit`, or project-defined
axioms.

## Main results

Paper-facing source modules use the `PaperID_ShortTitle` convention. IDs are
normally numeric; `#0A` is the adjacent foundational Angluin entry between
`#0` and `#01`. Existing declaration namespaces such as `GenLimit.Gold`,
`GenLimit.Angluin`, and `GenLimit.KM` remain stable
so this pre-1.0 organizational rename does not unnecessarily break theorem
users. The package version is `0.4.0`; importers should use the numbered module
paths shown below.

| Development | Main Lean declaration | Formalized result |
|---|---|---|
| #0 Language Identification — Theorem 7.1 | `GenLimit.Gold.Abstract.gold_theorem_7_1` | Distinguishability is necessary; collapsing uncertainty makes every enumeration learner succeed; countable allowable-sequence fibers make distinguishability sufficient |
| #0 Language Identification — finite-text learning | `GenLimit.Gold.Text.finiteLearner_identifiesFiniteLanguages` | Every finite language is identifiable from every exact positive text |
| #0 Language Identification — sharp text boundary | `GenLimit.Gold.Text.finiteLanguages_maximal_semanticallyIdentifiable` | Finite languages are semantically identifiable, and every proper superclass is not |
| #0 Language Identification — complete informants | `GenLimit.Gold.Informant.informantEnumerationLearner_identifiesFamily` | Every indexed family is semantically identifiable from complete positive/negative data |
| #0 Language Identification — superfinite obstruction | `GenLimit.Gold.Text.superfinite_not_semanticallyIdentifiable` | No semantic learner identifies a class containing all finite languages and an infinite language from arbitrary positive text |
| #0A Positive-Data Inference — semantic characterization | `GenLimit.Angluin.semanticallyInferrable_iff_conditionTwo` | Semantic positive-data inferrability iff every indexed language has a finite tell-tale |
| #0A Positive-Data Inference — effective Theorem 1 | `GenLimit.Angluin.theoremOne` | Computable positive-data inference iff there is a uniformly computable finite tell-tale enumeration |
| #0A Positive-Data Inference — effective Corollary 1 | `GenLimit.Angluin.corollaryOne` | The effective characterization implies the corresponding finite-tell-tale condition |
| #01 Language Generation — semantic | `GenLimit.KM.Semantic.kleinbergMullainathan_main` | Round-indexed, noncomputable Section 4 guarantee (4.6) |
| #01 Language Generation — observed-set interface | `GenLimit.KM.SetInterface.kleinbergMullainathan_set_interface_with_repetitions` | Literal finite-set-only Section 4 guarantee for arbitrary exact presentations, including repetitions |
| #01 Language Generation — finite-query | `GenLimit.OracleFamily.kleinbergMullainathan_main` | Stateful endpoint-test algorithm from the NeurIPS proceedings |
| #01 Language Generation — arXiv-v1 finite-query | `GenLimit.OracleFamily.ArxivV1.kleinbergMullainathan_main` | Stateful least-fresh whole-prefix algorithm from arXiv v1 |
| #02 Learning Theory — uniform characterization | `GenLimit.LiRamanTewari.uniform_generatability_iff_finite_closure_dimension` | Uniform generation iff finite closure dimension |
| #02 Learning Theory — nonuniform characterization | `GenLimit.LiRamanTewari.nonuniform_generatability_iff_nondecreasing_finite_closure_cover` | Nonuniform generation iff there is a nondecreasing finite-closure cover |
| #02 Learning Theory — countable/finite class theorems | `GenLimit.LiRamanTewari.theorem_2_4`, `GenLimit.LiRamanTewari.theorem_2_5` | Every countable UUS class is limit-generatable; every finite UUS class is uniformly generatable |
| #02 Learning Theory — Gold/Angluin bridges | `GenLimit.GoldP02Separation.theorem_2_2_countable_uus_not_identifiable`, `GenLimit.Angluin.theorem_2_3_countable`, `GenLimit.Paper02IdentificationDiagnostics.printed_theorem_2_3_is_false` | Theorem 2.2, corrected countable Theorem 2.3, and a counterexample to its printed arbitrary-class wording |
| #02 Learning Theory — prompted characterization | `GenLimit.LiRamanTewari.prompted_uniform_generatability_iff_finite_prompted_closure_dimension` | Prompted uniform generation iff finite prompted closure dimension |
| #02 Learning Theory — Appendix C | `GenLimit.LiRamanTewari.theorem_C4_eventually_unbounded_closure` | Generation from a nondecreasing finite-EUC cover |
| #03 Hallucination and Mode Collapse — online breadth | `GenLimit.HallucinationModeCollapse.Results.theorem_3_5_semantic`, `theorem_3_7_semantic`, `theorem_3_9_semantic` | Probability-free semantic support-oracle forms relating breadth, stability, and positive-data identification; Turing computability is not claimed |
| #03 Hallucination and Mode Collapse — tell-tale relationships | `GenLimit.HallucinationModeCollapse.finiteCollection_conditionTwo`, `finiteLanguages_conditionTwo` | Standalone finite-tell-tale lemmas motivated by Propositions 3.11--3.12; the statistical propositions are not claimed |
| #04 Exploring Facets — overview | `GenLimit.CharikarPabbaraju.Results.theorem_1`, `theorem_2`, `theorem_3`, `theorem_4`, `theorem_5` | All five overview theorems, including the membership-query lower bound through detailed Theorem 7 |
| #04 Exploring Facets — detailed | `GenLimit.CharikarPabbaraju.Results.theorem_6`, `theorem_7` | The quantitative non-uniform bound and adaptive membership-query impossibility; the paper's recalled Theorem 8 is the canonical `GenLimit.Angluin.theoremOne` and is not duplicated |
| Paper11 Union-Closedness — overview | `GenLimit.UnionClosedness.theorem_3_1`, `theorem_3_2`, `theorem_3_3` | Existential non-closure witnesses, including Theorem 3.2's autonomous no-adversary-input schedules, plus an uncountable non-uniform class without EUC |
| Paper11 Union-Closedness — detailed witnesses | `GenLimit.UnionClosedness.theorem_4_1`, `theorem_4_3`, `theorem_4_4` | Signed-integer classes realizing the two union separations and the displayed countable cofinite-negative EUC separation |
| Paper11 Union-Closedness — deterministic appendix | `GenLimit.UnionClosedness.proposition_A_1`, `GenLimit.UnionClosedness.PrefixRealizability.appendix_A_2_deterministic_prefix_realizability_core` | Deterministic Proposition A.1 and a conditional prefix-realizability core for Appendix A.2 |
| #06 Noisy Examples — uniform noise-independent | `GenLimit.NoisyExamples.theorem_3_1` | Uniform noise-independent generation iff the class-wide common intersection is infinite, with the source's implicit ambient-universe assumption exposed |
| #06 Noisy Examples — uniform noise-dependent | `GenLimit.NoisyExamples.theorem_3_3` | Uniform noise-dependent generation iff every fixed noise level has finite noisy closure dimension |
| #06 Noisy Examples — robustification | `GenLimit.NoisyExamples.theorem_3_9` | Ordinary non-uniform generation implies noisy generation in the limit |
| #06 Noisy Examples — appendices | `GenLimit.NoisyExamples.theorem_C_3`, `GenLimit.NoisyExamples.lemma_D_2` | Bounded noisy-closure excess characterization and the finite parity-class separation |
| #08 Hallucination Detection — equivalence | `GenLimit.HallucinationDetection.theorem_2_1` | Positive-only hallucination detection in the limit iff semantic identification in the limit |
| #08 Hallucination Detection — tell-tales | `GenLimit.HallucinationDetection.corollary_2_2` | Hallucination detectability iff Angluin's finite tell-tale condition |
| #08 Hallucination Detection — negative examples | `GenLimit.HallucinationDetection.theorem_2_3` | Every indexed family is detectable from every valid complete labeled enumeration |
| #08 Hallucination Detection — Appendix A.2 | `GenLimit.HallucinationDetection.theorem_A_2` | Countable families are generatable in the appendix sense; isolated in the #02-to-#08 bridge |
| #28 Contrastive Generation — identification | `GenLimit.ContrastiveGeneration.theorem_4_7` | Text identification plus pairwise overlap characterizes contrastive identification |
| #28 Contrastive Generation — closure dimension | `GenLimit.ContrastiveGeneration.theorem_5_4_quantitative`, `theorem_5_4` | The exact `d + 1` threshold and qualitative finite-dimension characterization |
| #28 Contrastive Generation — non-uniform generation | `GenLimit.ContrastiveGeneration.theorem_5_5` | Characterization by an increasing cover with finite contrastive closure dimension |
| #28 Contrastive Generation — hierarchy witnesses | `GenLimit.ContrastiveGeneration.theorem_5_13_5_14_punctured_witness`, `theorem_5_13_5_14_disjoint_witness` | Concrete components of the clean hierarchy and incomparability results |
| #28 Contrastive Generation — robust identification | `GenLimit.ContrastiveGeneration.absenceCountIdentifier_finitely_identifies`, `theorem_6_6`, `theorem_6_8` | The named absence-count identifier handles every finite corruption budget; corrupted text and contrastive identification are incomparable |
| #28 Contrastive Generation — defect identity | `GenLimit.ContrastiveGeneration.proposition_6_3_defect_eq_forced_wrong_cut_infimum` | Exact extended-natural defect number as an infimum of forced wrong-cut counts |
| #31 Bounded Memory — set generation | `GenLimit.BoundedMemory.theorem_1_1`, `theorem_3_1`, `theorem_3_2` | Memoryless generation under finitely repeating presentations, the arbitrary-repetition singleton-core characterization, and element/index output separations |
| #31 Bounded Memory — density | `GenLimit.BoundedMemory.theorem_4_1_memoryless_minimax_upper_density`, `theorem_4_2_no_uniform_positive_lower_density`, `theorem_4_10_window_minimax_upper_density` | Exact memoryless and sliding-window upper-density values and the lower-density obstruction for the order-robust `ℕ` specialization |
| #31 Bounded Memory — adaptive buffer | `GenLimit.BoundedMemory.theorem_4_15_adaptive_buffer_lower_bound` | The paper's piecewise adaptive-buffer lower bound, not an overclaimed low-regime equality |
| #31 Bounded Memory — incremental results | `GenLimit.BoundedMemory.proposition_5_1`, `theorem_5_2`, `theorem_A_1`, `incremental_element_generation` | Three-state exact-identification obstruction, finite-family approximate identification, index-generation obstruction, and incremental element generation |
| #31 Bounded Memory — Appendix coding | `GenLimit.BoundedMemory.lemma_A_3`, `incremental_coding_compilation` | The repaired source-facing disjoint-cell wrapper and the semantic full-history coding compiler |
| #39 Dense Generation — density | `GenLimit.PatientMachine.patientScope_lowerDensity_half` | Patient-scope lower density at least `1 / 2` for every exactly presented target |
| #39 Dense Generation — joint conclusion | `GenLimit.PatientMachine.patientScope_generation_and_lowerDensity` | Eventual validity, freshness, output novelty, and the same density bound |
| #0 → #01 bridge — separation | `GenLimit.GoldKMSeparation.generation_without_identification` | One explicit uniformly decidable family is #01-generatable but not #0-identifiable from arbitrary positive text |
| #0 → #39 bridge — separation | `GenLimit.GoldDenseSeparation.dense_generation_without_identification` | The same family has patient-scope novelty and density at least `1 / 2`, while remaining nonidentifiable from text |
| #39 Dense Generation — partial-enumeration counterexample | `GenLimit.PartialEnumeration.Counterexample.output_not_mem_trueLanguage` | Example 3.15 for an explicit increasing multiples-of-four enumeration |
| #39 Dense Generation — Lemma 3.16 | `GenLimit.PartialEnumeration.lemma_3_16_generation` | Eventual target validity and novelty when an infinite `E ⊆ K` is presented |
| #39 Dense Generation — Theorem 3.17 | `GenLimit.PartialEnumeration.theorem_3_17` | Generator density at least one half of the relative lower density of `E` in `K` |

The #0 Language Identification development models ordered finite histories, explanatory
identification (eventual stabilization to one fixed name), arbitrary exact
positive texts, and complete Boolean-labeled informants. Its abstract layer
formalizes all three clauses of Theorem 7.1. It also includes the
finite-language learner, bounded least-compatible enumeration, locking
sequences, finite tell-tale necessity, and the semantic arbitrary-text form
of the paper's superfinite nonidentifiability theorem. This is deliberately a
semantic first layer: Turing-machine indices, recursive or
primitive-recursive texts, and effectiveness-specific diagonal theorems are
not yet formalized. Since an exact text has type `ℕ → ℕ`, the empty language
has no text; statements about its texts are therefore vacuous unless a future
model adds a pause symbol.

All four #01 Language Generation paths eventually output target elements that are fresh relative to
the observed adversary sample. The semantic and finite-set proofs compare
whole infinite languages and are noncomputable; the two finite-query
developments realize their tests through the Boolean membership oracle. The
endpoint and whole-prefix stopping rules are retained as separate source
versions.

The #02 Learning Theory path uses a generic countable example type. It includes
the ordinary and prompted closure characterizations, quantitative uniform
sample-complexity bounds, hierarchy separations, finite-cover results, and the
valid Appendix C theorems. Its Theorem 4.1 declarations intentionally stop at
the VC/Littlestone combinatorial layer: no probability space, PAC learner,
online algorithm, regret bound, or computational-efficiency theorem is
claimed. Lean also refutes the paper's stronger arbitrary-stream EUC prose
equivalence without weakening Theorems C.2 or C.4.

Paper-specific repeated proof machinery stays in a paper-local `Common`
layer; neutral enumeration/progress and finite-race machinery shared with #06
lives in `GenLimit.Support`. The cofinite Appendix A/C witness has one
canonical definition. Explicit bridge
modules connect the original `Nat` API, generic classes, indexed families,
Gold, Angluin, and KM without adding those dependencies to the native #02
umbrella. Angluin's original theorem concerns an indexed, hence countable,
family. Lean proves P02's corrected countable Theorem 2.3 and refutes its
printed arbitrary-class extension with an uncountable UUS selector antichain.

The #03 Hallucination and Mode Collapse path formalizes the probability-free
semantic support-oracle cores of online Theorems 3.5, 3.7, and 3.9.  It reuses
#0A for semantic positive-data identification, #0 for complete informants,
and #01 for the KM generation engine.  Statistical distributions, universal
rates, and Turing-machine computability remain outside the stated scope.  The
#03-to-#04 bridge records the theorem-level relationship between their
different breadth interfaces without coupling the native paper modules.

The #04 Exploring Facets path formalizes overview Theorems 1--5,
detailed Theorems 6--7, Propositions 6.1--6.3 and 7.1, Claim 5.2, and the
two numbered examples. Source-facing generation definitions remain local,
while explicit equivalence theorems relate them to the shared P02/Core
predicates. The paper's recalled Theorem 8 is exactly the canonical
`GenLimit.Angluin.theoremOne` and is not duplicated in the P04 namespace. The
P02-to-P04 bridge records that P04 Theorem 1 also follows from P02 Corollary
3.6. Overview Theorem 2 delegates to the stronger size-two detailed Theorem
7. Its completion-driven diagonal avoids the printed proof's unsupported
infinite-distinct-query inference by using the contradictory universal
guarantee to obtain finite execution on each temporary infinite completion.
The paper-facing generation theorems uniformly expose Section 2's standing
infinite-language assumption through `UUS` (or directly for the concrete
two-language lower bound), while the imported Angluin identification theorem
does not acquire that assumption.
P04 adds neutral presentation helpers to `GenLimit.Support` but makes no
change to Core.

The Paper11 Union-Closedness path formalizes Theorems 3.1, 3.2, 3.3, 4.1,
4.3, and 4.4, together with deterministic Proposition A.1. Its numbered
union lower bounds use the source convention of duplicate-free enumerations;
the Paper11 presentation bridge yields the stronger lower bounds under the
library's arbitrary exact-presentation convention when needed.
Theorem 3.2's "without requiring any elements from the adversary" clauses are
represented by injective autonomous schedules `-1, -2, ...` and `1, 2, ...`;
Paper11-local adapters derive the standard history-based generation claims.
Paper11 reuses #02's EUC results and its countable-generation theorem for
detailed Theorem 4.4, while the Theorem 4.3 schedules, signed-integer witnesses,
and one shared alternating recursion remain local. Randomized Proposition A.2
is not formalized. Appendix A.2 has only a generic conditional
prefix-realizability core: the concrete family and Remark A.3 remain open.

The #06 Noisy Examples path formalizes occurrence-count noise, noisy presentations,
noisy closure witnesses, uniform and non-uniform characterizations,
robustification, and the Appendix C/D variants. It exposes nonempty or
infinite ambient-universe assumptions needed to repair degenerate printed
statements. The numerical `NC_n`, its asymptotic sample-complexity claim, and
computational efficiency remain outside the formalized boundary. Its shared
generation, closure, and cover vocabulary comes from neutral `GenLimit.Core`
modules. Stable #06-specific semantics are collected in the lightweight
paper-local `Definitions` module, while enumeration/progress and finite-race
proof infrastructure shared with #02 lives in `GenLimit.Support`. The paper
path does not import substantive #02 theorems.

The #08 Hallucination Detection path formalizes finite adaptive candidate-set query trees,
positive-only hallucination detection, its equivalence with semantic
identification, the finite-tell-tale characterization, and complete labeled
negative-example detection. Lean corrects the source's false inference after
Example 1: the multiples family has singleton tell-tales and is detectable.
Its native modules depend on the #0A development (whose declarations remain
under `GenLimit.Angluin`) but
not on substantive #02 results. Theorem A.2 is physically isolated in
`GenLimit.Bridges.Paper02ToPaper08`, the one location where #02 Corollary 3.6
is used. No effective detector, query/runtime bound,
probabilistic extension, or effective tell-tale discovery theorem is claimed.

The #28 Contrastive Generation path formalizes pairwise contrastive geometry, semantic
identification, uniform and target-dependent closure characterizations, core
conditions, explicit hierarchy witnesses, finite-occurrence corruption, and
the exact defect infimum. Its native modules use generic Core vocabulary and
the #0A semantic-necessity theorem, but import neither #02 nor
#08. The ordinary identification-to-fresh-generation lemma
is paper-independent and lives in `GenLimit.Core.IdentificationGeneration`.
The audit-identified Theorem 6.6 interface gap is resolved by
`absenceCountIdentifier_finitely_identifies`, which exposes the named
budget-independent witness without adding assumptions or oracle access.
Nevertheless, its minimizer is chosen classically: no fixed-enumeration
tie-break, computability, runtime, or oracle-free implementation theorem is
claimed. The full clean strict diamond, unordered-edge learner transport,
general infinite-defect robustness principle, corrupted generation, and
probabilistic extensions remain outside the formalized boundary.

The #31 Bounded Memory path formalizes memoryless set generation, output-type
separations, ordered-density guarantees for memoryless and sliding-window
models, adaptive chosen buffers, last-guess identification, and the Appendix
index and element constructions. Its native modules import only neutral Core
and Mathlib modules. `GenLimit.Core.OrderedDensity` owns the paper-independent
Kleinberg--Wei density interface, while `GenLimit.Core.GenericGeneration`
supplies generic presentation vocabulary. The repaired `lemma_A_3` only
packages four already-proved coding-cell properties into the source-facing
existential statement.

Several headline results remain specialized to `ℕ`. The density equalities
are for Lean's target-order-robust game rather than literally the paper's one
fixed ambient order; `MemorylessSetGenerator` does not intrinsically require
every off-target output to be infinite; and `theorem_5_2` concludes through an
equal-range relabeling rather than transporting a learner back to the raw
indexing. The incremental element model intentionally stores full history in
an unbounded natural output. No generic transport, bounded-bit memory,
computability, oracle, runtime, rate, or randomness claim follows.

The #39 Dense Generation machine is also semantic and noncomputable because its
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
├── GenLimit.Paper00_LanguageIdentification
├── GenLimit.Paper00A_PositiveDataInference
├── GenLimit.Paper01_LanguageGeneration
├── GenLimit.Paper02_LearningTheory
├── GenLimit.Paper03_HallucinationAndModeCollapse
├── GenLimit.Paper04_ExploringFacetsOfLanguageGeneration
├── GenLimit.Paper06_NoisyExamples
├── GenLimit.Paper08_HallucinationDetection
├── GenLimit.Paper11_UnionClosednessOfLanguageGeneration
├── GenLimit.Paper28_ContrastiveGeneration
├── GenLimit.Paper31_BoundedMemory
└── GenLimit.Paper39_DenseGeneration

GenLimit.Bridges  (explicit cross-paper results)
```

- `GenLimit.Core` contains paper-independent definitions and stabilization
  lemmas.
- `GenLimit.Paper00_LanguageIdentification` contains #0 semantic
  identification from text and informants.
- `GenLimit.Paper01_LanguageGeneration` contains the #01 semantic and
  finite-query developments.
- `GenLimit.Paper02_LearningTheory` contains #02 ordinary and prompted
  generation results.
- `GenLimit.Paper03_HallucinationAndModeCollapse` contains #03's
  probability-free semantic support-oracle reductions and qualitative cores.
- `GenLimit.Paper04_ExploringFacetsOfLanguageGeneration` contains the
  completed #04 non-uniform, membership-query, exhaustive, breadth,
  identification, and feedback results.
- `GenLimit.Paper06_NoisyExamples` contains #06 noisy-generation models,
  characterizations, robustification, examples, and appendix results.
- `GenLimit.Paper00A_PositiveDataInference` contains #0A semantic
  identification and tell-tale theory, with effective interfaces kept
  explicitly separate; declarations remain under `GenLimit.Angluin`.
- `GenLimit.Paper08_HallucinationDetection` contains the native #08 detector,
  reduction, negative-example, Example 1, and appendix definitions/results.
- `GenLimit.Paper11_UnionClosednessOfLanguageGeneration` contains the
  duplicate-free presentation interface, signed-integer union witnesses,
  overview theorems, and deterministic appendix results.
- `GenLimit.Paper28_ContrastiveGeneration` contains #28 geometry,
  identification, closure, hierarchy, corruption, and defect developments.
- `GenLimit.Paper31_BoundedMemory` contains #31 memoryless, density, window,
  buffer, incremental-identification, and appendix developments.
- `GenLimit.Paper39_DenseGeneration` contains the #39 abstract counting argument and the
  exact- and partial-enumeration patient-scope developments.
- `GenLimit.Bridges` contains explicit comparison theorems without making one
  paper development depend on the other.

The umbrella module [`GenLimit.lean`](GenLimit.lean) imports all layers.
The numbered paper umbrellas [`GenLimit/Paper00_LanguageIdentification.lean`](GenLimit/Paper00_LanguageIdentification.lean),
[`GenLimit/Paper01_LanguageGeneration.lean`](GenLimit/Paper01_LanguageGeneration.lean),
[`GenLimit/Paper02_LearningTheory.lean`](GenLimit/Paper02_LearningTheory.lean),
[`GenLimit/Paper03_HallucinationAndModeCollapse.lean`](GenLimit/Paper03_HallucinationAndModeCollapse.lean),
[`GenLimit/Paper04_ExploringFacetsOfLanguageGeneration.lean`](GenLimit/Paper04_ExploringFacetsOfLanguageGeneration.lean),
[`GenLimit/Paper06_NoisyExamples.lean`](GenLimit/Paper06_NoisyExamples.lean),
[`GenLimit/Paper00A_PositiveDataInference.lean`](GenLimit/Paper00A_PositiveDataInference.lean),
[`GenLimit/Paper08_HallucinationDetection.lean`](GenLimit/Paper08_HallucinationDetection.lean),
[`GenLimit/Paper11_UnionClosednessOfLanguageGeneration.lean`](GenLimit/Paper11_UnionClosednessOfLanguageGeneration.lean),
[`GenLimit/Paper28_ContrastiveGeneration.lean`](GenLimit/Paper28_ContrastiveGeneration.lean),
[`GenLimit/Paper31_BoundedMemory.lean`](GenLimit/Paper31_BoundedMemory.lean), and
[`GenLimit/Paper39_DenseGeneration.lean`](GenLimit/Paper39_DenseGeneration.lean) can be used
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
| #0 Language Identification — learner and model | [`GenLimit/Paper00_LanguageIdentification/Text/Model.lean`](GenLimit/Paper00_LanguageIdentification/Text/Model.lean) |
| #0 Language Identification — Theorem 7.1 | [`GenLimit/Paper00_LanguageIdentification/Abstract/Model.lean`](GenLimit/Paper00_LanguageIdentification/Abstract/Model.lean), then [`GenLimit/Paper00_LanguageIdentification/Abstract/Enumeration.lean`](GenLimit/Paper00_LanguageIdentification/Abstract/Enumeration.lean) |
| #0 Language Identification — finite-text learning | [`GenLimit/Paper00_LanguageIdentification/Text/Finite.lean`](GenLimit/Paper00_LanguageIdentification/Text/Finite.lean) |
| #0 Language Identification — locking and superfinite obstruction | [`GenLimit/Paper00_LanguageIdentification/Text/Locking.lean`](GenLimit/Paper00_LanguageIdentification/Text/Locking.lean), then [`GenLimit/Paper00_LanguageIdentification/Text/Superfinite.lean`](GenLimit/Paper00_LanguageIdentification/Text/Superfinite.lean) |
| #0 Language Identification — complete informants | [`GenLimit/Paper00_LanguageIdentification/Informant/Model.lean`](GenLimit/Paper00_LanguageIdentification/Informant/Model.lean), then [`GenLimit/Paper00_LanguageIdentification/Informant/Enumeration.lean`](GenLimit/Paper00_LanguageIdentification/Informant/Enumeration.lean) |
| #01 Language Generation — semantic proof | [`GenLimit/Paper01_LanguageGeneration/Critical.lean`](GenLimit/Paper01_LanguageGeneration/Critical.lean), then [`GenLimit/Paper01_LanguageGeneration/Semantic.lean`](GenLimit/Paper01_LanguageGeneration/Semantic.lean) |
| #01 Language Generation — observed-set proof | [`GenLimit/Paper01_LanguageGeneration/SetInterface.lean`](GenLimit/Paper01_LanguageGeneration/SetInterface.lean) |
| #01 Language Generation — finite-query algorithms | [`GenLimit/Paper01_LanguageGeneration/FiniteQuery.lean`](GenLimit/Paper01_LanguageGeneration/FiniteQuery.lean), with the arXiv-v1 variant in [`GenLimit/Paper01_LanguageGeneration/FiniteQuery/ArxivV1.lean`](GenLimit/Paper01_LanguageGeneration/FiniteQuery/ArxivV1.lean) |
| #02 Learning Theory | [`GenLimit/Paper02_LearningTheory/Definitions.lean`](GenLimit/Paper02_LearningTheory/Definitions.lean), then [`Closure.lean`](GenLimit/Paper02_LearningTheory/Closure.lean), [`NonuniformCharacterization.lean`](GenLimit/Paper02_LearningTheory/NonuniformCharacterization.lean), and the umbrella [`GenLimit/Paper02_LearningTheory.lean`](GenLimit/Paper02_LearningTheory.lean) |
| Gold/Angluin/KM → #02 bridges | [`GenLimit/Bridges/BasicToGeneric.lean`](GenLimit/Bridges/BasicToGeneric.lean), [`IndexedFamilyToClass.lean`](GenLimit/Bridges/IndexedFamilyToClass.lean), [`AngluinToPaper02.lean`](GenLimit/Bridges/AngluinToPaper02.lean), [`GoldToPaper02.lean`](GenLimit/Bridges/GoldToPaper02.lean), [`Paper01ToPaper02.lean`](GenLimit/Bridges/Paper01ToPaper02.lean), and [`Paper02IdentificationDiagnostics.lean`](GenLimit/Bridges/Paper02IdentificationDiagnostics.lean) |
| #03 Hallucination and Mode Collapse | [`GenLimit/Paper03_HallucinationAndModeCollapse/Definitions.lean`](GenLimit/Paper03_HallucinationAndModeCollapse/Definitions.lean), then [`OnlineReductions.lean`](GenLimit/Paper03_HallucinationAndModeCollapse/OnlineReductions.lean), [`PositiveBreadth.lean`](GenLimit/Paper03_HallucinationAndModeCollapse/PositiveBreadth.lean), [`Results/Overview.lean`](GenLimit/Paper03_HallucinationAndModeCollapse/Results/Overview.lean), and the umbrella |
| #03 → #04 breadth relationship | [`GenLimit/Bridges/Paper03ToPaper04.lean`](GenLimit/Bridges/Paper03ToPaper04.lean) |
| #04 Exploring Facets | [`GenLimit/Paper04_ExploringFacetsOfLanguageGeneration/Definitions.lean`](GenLimit/Paper04_ExploringFacetsOfLanguageGeneration/Definitions.lean), then [`Results/Detailed.lean`](GenLimit/Paper04_ExploringFacetsOfLanguageGeneration/Results/Detailed.lean), [`Results/Overview.lean`](GenLimit/Paper04_ExploringFacetsOfLanguageGeneration/Results/Overview.lean), and the default umbrella; audit Theorem 7 through [`MembershipQueryLowerBoundStatement.lean`](GenLimit/Paper04_ExploringFacetsOfLanguageGeneration/MembershipQueryLowerBoundStatement.lean) and [`MembershipQueryGlobalDiagonal.lean`](GenLimit/Paper04_ExploringFacetsOfLanguageGeneration/MembershipQueryGlobalDiagonal.lean) |
| #02 → #04 relationship | [`GenLimit/Bridges/Paper02ToPaper04.lean`](GenLimit/Bridges/Paper02ToPaper04.lean) |
| #06 Noisy Examples | [`GenLimit/Paper06_NoisyExamples/Definitions.lean`](GenLimit/Paper06_NoisyExamples/Definitions.lean), then [`UniformIndependent.lean`](GenLimit/Paper06_NoisyExamples/UniformIndependent.lean), [`NoisyClosure.lean`](GenLimit/Paper06_NoisyExamples/NoisyClosure.lean), [`Nonuniform.lean`](GenLimit/Paper06_NoisyExamples/Nonuniform.lean), [`NoiselessRobustification.lean`](GenLimit/Paper06_NoisyExamples/NoiselessRobustification.lean), and the umbrella [`GenLimit/Paper06_NoisyExamples.lean`](GenLimit/Paper06_NoisyExamples.lean) |
| #0A semantic characterization | [`GenLimit/Paper00A_PositiveDataInference/Semantic/Definitions.lean`](GenLimit/Paper00A_PositiveDataInference/Semantic/Definitions.lean), then [`Necessity.lean`](GenLimit/Paper00A_PositiveDataInference/Semantic/Necessity.lean) and [`Characterization.lean`](GenLimit/Paper00A_PositiveDataInference/Semantic/Characterization.lean) |
| #0A effective Theorem 1 | [`GenLimit/Paper00A_PositiveDataInference/Effective/Definitions.lean`](GenLimit/Paper00A_PositiveDataInference/Effective/Definitions.lean), then [`Sufficiency.lean`](GenLimit/Paper00A_PositiveDataInference/Effective/Sufficiency.lean), [`Stabilization.lean`](GenLimit/Paper00A_PositiveDataInference/Effective/Stabilization.lean), and [`Necessity.lean`](GenLimit/Paper00A_PositiveDataInference/Effective/Necessity.lean) |
| #08 Hallucination Detection | [`GenLimit/Paper08_HallucinationDetection/Definitions.lean`](GenLimit/Paper08_HallucinationDetection/Definitions.lean), then [`Reductions.lean`](GenLimit/Paper08_HallucinationDetection/Reductions.lean), [`AngluinCondition.lean`](GenLimit/Paper08_HallucinationDetection/AngluinCondition.lean), and [`Appendix.lean`](GenLimit/Paper08_HallucinationDetection/Appendix.lean) |
| #02 → #08 Appendix A.2 bridge | [`GenLimit/Bridges/Paper02ToPaper08.lean`](GenLimit/Bridges/Paper02ToPaper08.lean) |
| Paper11 Union-Closedness | [`Definitions.lean`](GenLimit/Paper11_UnionClosednessOfLanguageGeneration/Definitions.lean) and [`WithoutAdversaryInput.lean`](GenLimit/Paper11_UnionClosednessOfLanguageGeneration/WithoutAdversaryInput.lean), then [`Results/Detailed.lean`](GenLimit/Paper11_UnionClosednessOfLanguageGeneration/Results/Detailed.lean), [`Results/Overview.lean`](GenLimit/Paper11_UnionClosednessOfLanguageGeneration/Results/Overview.lean), and the umbrella [`GenLimit/Paper11_UnionClosednessOfLanguageGeneration.lean`](GenLimit/Paper11_UnionClosednessOfLanguageGeneration.lean) |
| #28 Contrastive Generation — identification | [`GenLimit/Paper28_ContrastiveGeneration/Geometry.lean`](GenLimit/Paper28_ContrastiveGeneration/Geometry.lean), [`IdentificationGeometry.lean`](GenLimit/Paper28_ContrastiveGeneration/IdentificationGeometry.lean), then [`IdentifierCharacterization.lean`](GenLimit/Paper28_ContrastiveGeneration/IdentifierCharacterization.lean) |
| #28 Contrastive Generation — generation and hierarchy | [`GenLimit/Paper28_ContrastiveGeneration/GenerationCores.lean`](GenLimit/Paper28_ContrastiveGeneration/GenerationCores.lean), [`ClosureDimension.lean`](GenLimit/Paper28_ContrastiveGeneration/ClosureDimension.lean), [`NonuniformClosure.lean`](GenLimit/Paper28_ContrastiveGeneration/NonuniformClosure.lean), then [`Hierarchy.lean`](GenLimit/Paper28_ContrastiveGeneration/Hierarchy.lean) |
| #28 Contrastive Generation — corruption and defect | [`GenLimit/Paper28_ContrastiveGeneration/CorruptedPresentations.lean`](GenLimit/Paper28_ContrastiveGeneration/CorruptedPresentations.lean), [`AbsenceCount.lean`](GenLimit/Paper28_ContrastiveGeneration/AbsenceCount.lean), [`CorruptedIncomparability.lean`](GenLimit/Paper28_ContrastiveGeneration/CorruptedIncomparability.lean), then [`DefectInfimum.lean`](GenLimit/Paper28_ContrastiveGeneration/DefectInfimum.lean) |
| #31 Bounded Memory — memoryless generation and separations | [`GenLimit/Paper31_BoundedMemory/Definitions.lean`](GenLimit/Paper31_BoundedMemory/Definitions.lean), [`ArbitraryRepetitions.lean`](GenLimit/Paper31_BoundedMemory/ArbitraryRepetitions.lean), [`FinitelyRepeating.lean`](GenLimit/Paper31_BoundedMemory/FinitelyRepeating.lean), then [`OutputSeparations.lean`](GenLimit/Paper31_BoundedMemory/OutputSeparations.lean) |
| #31 Bounded Memory — density, windows, and buffers | [`GenLimit/Core/OrderedDensity.lean`](GenLimit/Core/OrderedDensity.lean), [`GenLimit/Paper31_BoundedMemory/MemorylessDensity.lean`](GenLimit/Paper31_BoundedMemory/MemorylessDensity.lean), [`MinimaxClosure.lean`](GenLimit/Paper31_BoundedMemory/MinimaxClosure.lean), [`WindowHardInstance.lean`](GenLimit/Paper31_BoundedMemory/WindowHardInstance.lean), then [`AdaptiveBuffer.lean`](GenLimit/Paper31_BoundedMemory/AdaptiveBuffer.lean) |
| #31 Bounded Memory — incremental and Appendix results | [`GenLimit/Paper31_BoundedMemory/IncrementalIdentification.lean`](GenLimit/Paper31_BoundedMemory/IncrementalIdentification.lean), [`ExactIdentificationObstruction.lean`](GenLimit/Paper31_BoundedMemory/ExactIdentificationObstruction.lean), [`IncrementalIndexObstruction.lean`](GenLimit/Paper31_BoundedMemory/IncrementalIndexObstruction.lean), then [`IncrementalElementCoding.lean`](GenLimit/Paper31_BoundedMemory/IncrementalElementCoding.lean) |
| #39 Dense Generation — criticality and machine | [`GenLimit/Paper39_DenseGeneration/Critical.lean`](GenLimit/Paper39_DenseGeneration/Critical.lean), then [`GenLimit/Paper39_DenseGeneration/Patient/Machine.lean`](GenLimit/Paper39_DenseGeneration/Patient/Machine.lean) |
| #39 Dense Generation — proof chain | `Patient/Validity.lean`, `Patient/Fact312.lean`, `Patient/Charging.lean`, then [`Patient/Main.lean`](GenLimit/Paper39_DenseGeneration/Patient/Main.lean) |
| #39 Dense Generation — partial enumeration | [`Partial/Counterexample.lean`](GenLimit/Paper39_DenseGeneration/Partial/Counterexample.lean), then [`Core/PartialPresentation.lean`](GenLimit/Core/PartialPresentation.lean), [`Partial/Closure.lean`](GenLimit/Paper39_DenseGeneration/Partial/Closure.lean), [`Partial/Validity.lean`](GenLimit/Paper39_DenseGeneration/Partial/Validity.lean), and [`Partial/Main.lean`](GenLimit/Paper39_DenseGeneration/Partial/Main.lean) |
| #0/#01/#39 comparison | [`GenLimit/Bridges/Paper00ToPaper01.lean`](GenLimit/Bridges/Paper00ToPaper01.lean), [`GenLimit/Bridges/Paper00ToPaper39.lean`](GenLimit/Bridges/Paper00ToPaper39.lean), and [`GenLimit/Bridges/Paper01ToPaper39.lean`](GenLimit/Bridges/Paper01ToPaper39.lean) |

## Paper maps and audit records

- [`PAPER_MAP.md`](PAPER_MAP.md) is the repository-level paper registry.
- [`PaperMaps/Paper00_LanguageIdentification.md`](PaperMaps/Paper00_LanguageIdentification.md) maps #0 Language Identification to Lean
  declarations and records the semantic/effective boundary.
- [`PaperMaps/Paper01_LanguageGeneration.md`](PaperMaps/Paper01_LanguageGeneration.md) maps #01 Language Generation to Lean declarations.
- [`PaperMaps/Paper02_LearningTheory.md`](PaperMaps/Paper02_LearningTheory.md) maps the ordinary,
  prompted, prediction-proxy, and EUC developments and their explicit gaps.
- [`PaperMaps/Paper03_HallucinationAndModeCollapse.md`](PaperMaps/Paper03_HallucinationAndModeCollapse.md)
  maps the probability-free semantic scope, cross-paper reuse, and remaining
  statistical/computability boundaries of #03.
- [`PaperMaps/Paper04_ExploringFacetsOfLanguageGeneration.md`](PaperMaps/Paper04_ExploringFacetsOfLanguageGeneration.md)
  maps the completed #04 results, reuse relationships, semantic boundaries,
  and the repaired Theorem 7 proof.
- [`PaperMaps/Paper06_NoisyExamples.md`](PaperMaps/Paper06_NoisyExamples.md) maps every
  paper-owned #06 result and its explicit source repairs.
- [`PaperMaps/Paper08_HallucinationDetection.md`](PaperMaps/Paper08_HallucinationDetection.md)
  maps #08 Hallucination Detection, including its corrected Example 1 inference and formalization limits.
- [`PaperMaps/Paper00A_PositiveDataInference.md`](PaperMaps/Paper00A_PositiveDataInference.md)
  records the #0A semantic/effective boundary used by #08 and #28.
- [`PaperMaps/Paper11_UnionClosednessOfLanguageGeneration.md`](PaperMaps/Paper11_UnionClosednessOfLanguageGeneration.md)
  maps the Paper11 overview, detailed witnesses, deterministic appendix scope,
  source qualifications, and remaining gaps.
- [`PaperMaps/Paper28_ContrastiveGeneration.md`](PaperMaps/Paper28_ContrastiveGeneration.md)
  maps #28 Contrastive Generation and its remaining semantic/effective limits.
- [`PaperMaps/Paper31_BoundedMemory.md`](PaperMaps/Paper31_BoundedMemory.md) maps #31 Bounded Memory,
  including the remaining
  universe, density-order, output, indexing, and effectivity limits.
- [`PaperMaps/Paper39_DenseGeneration.md`](PaperMaps/Paper39_DenseGeneration.md) maps #39
  Dense Generation to Lean declarations and explains why the current
  earlier-manuscript development does not yet formalize public arXiv v1.
- [`PaperMaps/RELATIONSHIPS.md`](PaperMaps/RELATIONSHIPS.md) records shared
  foundations and explicit bridges.
- [`AUDIT.md`](AUDIT.md) records kernel, axiom, and access-model checks.
- [`AuditRecords/`](AuditRecords/) is the authoritative home for audit records.
  Its numbered paper directories preserve checksum-verified ChatGPT Pro
  statement-faithfulness evidence.
- [`AuditRecords/Human/README.md`](AuditRecords/Human/README.md) records Peng Zhang's completed human
  audits at their exact levels and historical code anchors. It also gives the matching
  uniform table for the ChatGPT Pro checks of the added #01 paths and #02,
  #06, #08, #28, and #31. #06 has a Level 1 human audit of Section 3
  Theorems 3.1, 3.3, 3.9, and 3.10; its remaining scope still awaits human
  correspondence review. The #28 named-witness and #31 Lemma A.3 wrapper repairs are
  separately kernel-checked changes made after the checked baselines. #0A has
  a Level 1 human audit of its semantic characterization and no separate
  ChatGPT Pro statement-audit record.

Paper11 has a Level 1 human audit by Peng Zhang of overview Theorems 3.1--3.3;
Theorems 4.1, 4.3, and 4.4 are noted as their detailed presentations.  The
3.3/4.4 mismatch and repaired first-Theorem-4.1-class witness are
Codex-assisted formalization findings.
Proof-correspondence and Appendix review remain pending, and there is no
checksum-verified ChatGPT Pro audit record.

Bibliographic metadata is collected in [`CITATION.bib`](CITATION.bib).
