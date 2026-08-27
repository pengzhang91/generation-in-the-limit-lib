# Kernel audit

This record describes the current revision, checked on 27 August 2026 with Lean
4.24.0 and Mathlib 4.24.0.

```text
lake build
Build completed successfully (3453 jobs).

lake env lean Audit.lean
All asserted declarations use only
[propext, Classical.choice, Quot.sound].
```

The umbrella module `GenLimit.lean` imports the shared core, all numbered paper
developments, including #0A, and the explicit bridge layer. The paths can also
be built independently:

```text
lake build GenLimit.Paper00_LanguageIdentification
lake build GenLimit.Paper00_LanguageIdentification.Abstract
lake build GenLimit.Paper00_LanguageIdentification.Text
lake build GenLimit.Paper00_LanguageIdentification.Informant
lake build GenLimit.Paper00A_PositiveDataInference
lake build GenLimit.Paper01_LanguageGeneration
lake build GenLimit.Paper01_LanguageGeneration.Semantic
lake build GenLimit.Paper01_LanguageGeneration.FiniteQuery
lake build GenLimit.Paper01_LanguageGeneration.FiniteQuery.ArxivV1
lake build GenLimit.Paper01_LanguageGeneration.SetInterface
lake build GenLimit.Paper02_LearningTheory
lake build GenLimit.Paper03_HallucinationAndModeCollapse
lake build GenLimit.Paper04_ExploringFacetsOfLanguageGeneration
lake build GenLimit.Paper05_HallucinationsBreadthAndStability
lake build GenLimit.Paper06_NoisyExamples
lake build GenLimit.Paper07_DensityMeasuresForLanguageGeneration
lake build GenLimit.Paper08_HallucinationDetection
lake build GenLimit.Paper10_UnionClosednessOfLanguageGeneration
lake build GenLimit.Paper15_PartialEnumeration
lake build GenLimit.Paper23_BanachDensityTopologyAndGeometry
lake build GenLimit.Papers07_15_23_KleinbergWei
lake build GenLimit.Paper28_ContrastiveGeneration
lake build GenLimit.Paper31_BoundedMemory
lake build GenLimit.Paper39_DenseGeneration
lake build GenLimit.Paper39_DenseGeneration.Partial
lake build GenLimit.Bridges
lake build GenLimit.Bridges.Paper00ToPaper01
lake build GenLimit.Bridges.Paper00ToPaper39
lake build GenLimit.Bridges.Paper02ToPaper08
lake build GenLimit.Bridges.AngluinToPaper02
lake build GenLimit.Bridges.GoldToPaper02
lake build GenLimit.Bridges.Paper01ToPaper02
lake build GenLimit.Bridges.Paper02IdentificationDiagnostics
lake build GenLimit.Bridges.Paper03ToPaper04
lake build GenLimit.Bridges.Paper04ToPaper05
```

An import-boundary scan confirms that the modules under `GenLimit/Paper00_LanguageIdentification/`,
`GenLimit/Paper01_LanguageGeneration/`, `GenLimit/Paper02_LearningTheory/`, `GenLimit/Paper06_NoisyExamples/`,
`GenLimit/Paper07_DensityMeasuresForLanguageGeneration/`,
`GenLimit/Paper15_PartialEnumeration/`, `GenLimit/Paper23_BanachDensityTopologyAndGeometry/`,
`GenLimit/Paper28_ContrastiveGeneration/`, `GenLimit/Paper31_BoundedMemory/`, and
`GenLimit/Paper39_DenseGeneration/` do not import the other paper developments. Native
`GenLimit/Paper00A_PositiveDataInference/` imports #0 only for the shared
positive-text finite-tell-tale necessity proof. Native
`GenLimit/Paper08_HallucinationDetection/` modules import #0A but no
substantive #02 theorem. #28 Contrastive Generation imports neutral generic
Core modules and #0A's semantic necessity theorem, but neither #02 nor #08. Its generic
identification-to-fresh-generation implication is owned by
`GenLimit.Core.IdentificationGeneration`.
Paper10 Union-Closedness deliberately imports #02's canonical EUC definition,
countable-class non-uniform generation theorem, and finite-EUC-cover theorem.
Its duplicate-free presentation interface, signed-integer witnesses, and
shared alternating engine remain Paper10-local; it imports no other paper
development.
#03 Hallucination and Mode Collapse deliberately reuses #0's informant
identification, #0A's semantic Angluin characterization, and #01's KM semantic
engine. Its support-valued definitions and reductions remain paper-local, and
the native #03 path imports neither #04 nor the later #08 development.
#31 Bounded Memory imports the neutral `GenLimit.Core.GenericGeneration` and
`GenLimit.Core.OrderedDensity` modules but no #02, #06, #08, or #28 module
and no bridge. The ordered-density declarations retain their
`GenLimit.KleinbergWei` namespace after extraction to Core.
Cross-paper results are isolated in the bridge
layer: `critical_recursiveCritical` is in
`GenLimit.Bridges.Paper01ToPaper39`, while the identification-to-generation
implication and the co-singleton separation are in
`GenLimit.Bridges.Paper00ToPaper01`; the quantitative PatientScope strengthening is
in `GenLimit.Bridges.Paper00ToPaper39`.
The #03/#04 breadth comparison is isolated in
`GenLimit.Bridges.Paper03ToPaper04`; neither native paper path imports it.
Native #05 deliberately reuses #0A's semantic Angluin construction, #04's
critical-focus infrastructure for Theorem 3.8 sufficiency, and #03's
stable-approximate necessity reduction. Its support-valued definitions remain
P05-local, while pure #04/#05 comparisons are isolated in
`GenLimit.Bridges.Paper04ToPaper05`.
The #07 module imports the canonical `GenLimit.Core.OrderedDensity`
vocabulary, neutral finite-sample progress, and shared relative tower
approximants; #07 and #23 share neutral `GenLimit.Support.KleinbergWei` tower
infrastructure, and neither imports the other. #15 reuses
`GenLimit.Core.PartialPresentation`, `GenLimit.Core.OnlineGeneration`,
`GenLimit.Core.OrderedDensity`, and the neutral
`GenLimit.Generic.IsFiniteTellTale` predicate, and imports no paper
development. `GenLimit.Papers07_15_23_KleinbergWei` is a presentation-only
chronological umbrella; the individual paper modules remain independent.
The sole #02-dependent #08 result, Appendix Theorem A.2, is physically
isolated in `GenLimit.Bridges.Paper02ToPaper08`.
The original `Nat` and generic generation interfaces are connected in
`GenLimit.Bridges.BasicToGeneric`; indexed families and extensional classes
are connected in `GenLimit.Bridges.IndexedFamilyToClass`. Definitions
2.6--2.7, Theorem 2.2, corrected countable Theorem 2.3, its arbitrary-class
counterexample, and the Gold/Angluin/KM comparisons are isolated in
`AngluinToPaper02`, `GoldToPaper02`, `Paper01ToPaper02`, and
`Paper02IdentificationDiagnostics`.

A source scan found no `sorry`, `admit`, or declared project axiom in any Lean
module. `Audit.lean` checks that every audited declaration uses only the
allowlisted logical principles below and fails if anything else appears.
Main classical declarations generally use all three; constructive helpers may
use a strict subset:

```text
GenLimit.KM.Semantic.kleinbergMullainathan_main
  [propext, Classical.choice, Quot.sound]

GenLimit.OracleFamily.kleinbergMullainathan_main
  [propext, Classical.choice, Quot.sound]

GenLimit.OracleFamily.ArxivV1.kleinbergMullainathan_main
  [propext, Classical.choice, Quot.sound]

GenLimit.KM.SetInterface.kleinbergMullainathan_set_interface
  [propext, Classical.choice, Quot.sound]

GenLimit.KM.SetInterface.kleinbergMullainathan_set_interface_with_repetitions
  [propext, Classical.choice, Quot.sound]

GenLimit.LiRamanTewari.uniform_generatability_iff_finite_closure_dimension
  [propext, Classical.choice, Quot.sound]

GenLimit.LiRamanTewari.optimal_uniform_generation_sample_complexity_bounds
  subset of [propext, Classical.choice, Quot.sound]

GenLimit.LiRamanTewari.nonuniform_generatability_iff_nondecreasing_finite_closure_cover
  [propext, Classical.choice, Quot.sound]

GenLimit.LiRamanTewari.theorem_2_4
  subset of [propext, Classical.choice, Quot.sound]

GenLimit.LiRamanTewari.theorem_2_5
  subset of [propext, Classical.choice, Quot.sound]

GenLimit.LiRamanTewari.prompted_uniform_generatability_iff_finite_prompted_closure_dimension
  [propext, Classical.choice, Quot.sound]

GenLimit.LiRamanTewari.theorem_C4_eventually_unbounded_closure
  [propext, Classical.choice, Quot.sound]

#02 relationship, Gold/Angluin/KM bridge, and identification-diagnostic declarations
  each use a subset of [propext, Classical.choice, Quot.sound]

#03 Hallucination and Mode Collapse: 12 declaration probes, including
  GenLimit.HallucinationModeCollapse.Results.theorem_3_5_semantic
  GenLimit.HallucinationModeCollapse.Results.theorem_3_7_semantic
  GenLimit.HallucinationModeCollapse.Results.theorem_3_9_semantic
  GenLimit.HallucinationModeCollapse.identifiableInLimit_iff_freshBreadthInLimit
  GenLimit.HallucinationModeCollapse.stable_unambiguousInLimit_implies_identifiableInLimit
  GenLimit.HallucinationModeCollapse.stable_approximateBreadthInLimit_implies_identifiableInLimit
  GenLimit.HallucinationModeCollapse.finiteCollection_conditionTwo
  GenLimit.HallucinationModeCollapse.finiteLanguages_conditionTwo
  GenLimit.Bridge.Paper03ToPaper04.paper04_breadth_implies_paper03_fresh_breadth
  each uses a subset of [propext, Classical.choice, Quot.sound]

#05 Hallucinations, Breadth, and Stability: 15 declaration probes, including
  GenLimit.BreadthCharacterizations.Results.theorem_3_3_semantic
  GenLimit.BreadthCharacterizations.Results.theorem_3_8_sufficiency_semantic
  GenLimit.BreadthCharacterizations.Results.theorem_3_15_approximate_semantic
  GenLimit.BreadthCharacterizations.Results.theorem_3_15_literal_exact_inconsistent
  GenLimit.BreadthCharacterizations.Results.theorem_3_15_corrected_wholeTarget_semantic
  GenLimit.BreadthCharacterizations.Results.proposition_8_10_literal_specification_inconsistent
  GenLimit.BreadthCharacterizations.no_stable_exactBreadth_for_infinite_family
  GenLimit.BreadthCharacterizations.no_stable_infiniteCoverage_for_infinite_family
  GenLimit.Bridge.Paper04ToPaper05.paper04_exhaustive_iff_paper05_weakAngluin
  each uses a subset of [propext, Classical.choice, Quot.sound]

GenLimit.NoisyExamples.theorem_3_1
  [propext, Classical.choice, Quot.sound]

GenLimit.NoisyExamples.theorem_3_3
  [propext, Classical.choice, Quot.sound]

GenLimit.NoisyExamples.theorem_3_9
  [propext, Classical.choice, Quot.sound]

GenLimit.NoisyExamples.theorem_3_10
  [propext, Classical.choice, Quot.sound]

GenLimit.NoisyExamples.theorem_C_3
  [propext, Classical.choice, Quot.sound]

GenLimit.NoisyExamples.lemma_D_2
  [propext, Classical.choice, Quot.sound]

GenLimit.HallucinationDetection.theorem_2_1
  [propext, Classical.choice, Quot.sound]

GenLimit.HallucinationDetection.corollary_2_2
  [propext, Classical.choice, Quot.sound]

GenLimit.HallucinationDetection.theorem_2_3
  [propext, Classical.choice, Quot.sound]

GenLimit.HallucinationDetection.theorem_A_1
  [propext, Classical.choice, Quot.sound]

GenLimit.HallucinationDetection.theorem_A_2
  [propext, Classical.choice, Quot.sound]

GenLimit.Angluin.conditionTwo_of_semanticallyIdentifiable
  [propext, Classical.choice, Quot.sound]

GenLimit.Angluin.ConditionOne.semantic_sufficiency
  [propext, Classical.choice, Quot.sound]

GenLimit.Angluin.corollaryOne
  [propext, Classical.choice, Quot.sound]

Paper10 Union-Closedness: 17 declaration probes, including
  GenLimit.UnionClosedness.uniformlyGeneratable_of_withoutAdversaryInput
  GenLimit.UnionClosedness.nonuniformlyGeneratable_of_withoutAdversaryInput
  GenLimit.UnionClosedness.theorem43FirstClass_uniformlyGeneratableWithoutAdversaryInput
  GenLimit.UnionClosedness.theorem43SecondClass_nonuniformlyGeneratableWithoutAdversaryInput
  GenLimit.UnionClosedness.theorem_3_1
  GenLimit.UnionClosedness.theorem_3_2
  GenLimit.UnionClosedness.theorem_3_2_standard
  GenLimit.UnionClosedness.theorem_3_3_of_theorem_3_1
  GenLimit.UnionClosedness.theorem_3_3
  GenLimit.UnionClosedness.theorem_4_1
  GenLimit.UnionClosedness.theorem_4_3
  GenLimit.UnionClosedness.theorem_4_4
  GenLimit.UnionClosedness.proposition_A_1
  GenLimit.UnionClosedness.PrefixRealizability.appendix_A_2_deterministic_prefix_realizability_core
  each uses a subset of [propext, Classical.choice, Quot.sound]

#28 Contrastive Generation: 47 declaration probes, including
  GenLimit.ContrastiveGeneration.theorem_4_7
  GenLimit.ContrastiveGeneration.theorem_5_4_quantitative
  GenLimit.ContrastiveGeneration.theorem_5_4
  GenLimit.ContrastiveGeneration.theorem_5_5
  GenLimit.ContrastiveGeneration.proposition_5_12
  GenLimit.ContrastiveGeneration.theorem_5_13_5_14_punctured_witness
  GenLimit.ContrastiveGeneration.theorem_5_13_5_14_disjoint_witness
  GenLimit.ContrastiveGeneration.theorem_6_5
  GenLimit.ContrastiveGeneration.absenceCountIdentifier_finitely_identifies
  GenLimit.ContrastiveGeneration.theorem_6_6
  GenLimit.ContrastiveGeneration.theorem_6_8
  GenLimit.ContrastiveGeneration.proposition_6_3_defect_eq_forced_wrong_cut_infimum
  each uses a subset of [propext, Classical.choice, Quot.sound]

#31 Bounded Memory: 79 declaration probes, including
  GenLimit.BoundedMemory.theorem_1_1
  GenLimit.BoundedMemory.theorem_3_1
  GenLimit.BoundedMemory.theorem_3_2
  GenLimit.BoundedMemory.lemma_4_3_lower_density_bound_from_partition
  GenLimit.BoundedMemory.lemma_4_4_zero_lower_density_partition
  GenLimit.BoundedMemory.lemma_4_7_sperner_hard_instance
  GenLimit.BoundedMemory.lemma_4_8_sperner_achievability
  GenLimit.BoundedMemory.theorem_4_1_memoryless_minimax_upper_density
  GenLimit.BoundedMemory.theorem_4_2_no_uniform_positive_lower_density
  GenLimit.BoundedMemory.lemma_4_11_finite_exception
  GenLimit.BoundedMemory.lemma_4_12_single_hard_instance
  GenLimit.BoundedMemory.theorem_4_10_window_minimax_upper_density
  GenLimit.BoundedMemory.theorem_4_15_adaptive_buffer_lower_bound
  GenLimit.BoundedMemory.proposition_5_1
  GenLimit.BoundedMemory.theorem_5_2
  GenLimit.BoundedMemory.proposition_A_2
  GenLimit.BoundedMemory.theorem_A_1
  GenLimit.BoundedMemory.lemma_A_3
  GenLimit.BoundedMemory.incremental_coding_compilation
  GenLimit.BoundedMemory.incremental_element_generation
  each uses a subset of [propext, Classical.choice, Quot.sound]

The audited #31 baseline contributed 78 probes. The separately tracked
`lemma_A_3` interface repair contributes probe 79.
This adaptation leaves the statements of
`orderedUpperDensity_nonneg'`, `orderedUpperDensity_carrier_eq_one`, and
`orderedUpperDensity_le_one` unchanged while shortening their proof bodies to
delegate to the new canonical Core lemmas. The immutable #31 statement audit
did not claim proof-body correspondence.

#07/#15/#23 Kleinberg--Wei sequence: 168 declaration probes, including
  GenLimit.KleinbergWei.TowerTopology.relativeApproximants_converge
  GenLimit.KleinbergWei.DensityMeasures.theorem_2_1
  GenLimit.KleinbergWei.DensityMeasures.corollary_2_2
  GenLimit.KleinbergWei.DensityMeasures.claim_4_7
  GenLimit.KleinbergWei.DensityMeasures.claim_6_1
  GenLimit.KleinbergWei.DensityMeasures.claim_6_6
  GenLimit.KleinbergWei.DensityMeasures.isTruthIndex_unique
  GenLimit.KleinbergWei.DensityMeasures.FiniteRankParent.claim_6_8
  GenLimit.KleinbergWei.DensityMeasures.FiniteRankFallback.corollary_6_10
  GenLimit.KleinbergWei.DensityMeasures.InfiniteRank.theorem_6_12_finite_accounting
  GenLimit.KleinbergWei.DensityMeasures.InfiniteRank.orderedLowerDensity_one_tenth_of_longBadCapacityTwoCharge
  GenLimit.KleinbergWei.PartialEnumeration.theorem_2_1
  GenLimit.KleinbergWei.PartialEnumeration.theorem_1_7
  GenLimit.KleinbergWei.PartialEnumeration.lemma_2_3_generation_equivalence
  GenLimit.KleinbergWei.PartialEnumeration.lemma_2_5_concrete_algorithmOne
  GenLimit.KleinbergWei.PartialEnumeration.theorem_2_2_freshOutput
  GenLimit.KleinbergWei.PartialEnumeration.WarmupChargeCertificate.theorem_3_1_alpha_third
  GenLimit.KleinbergWei.PartialEnumeration.FullTopology.theorem_4_9_topological_core
  GenLimit.KleinbergWei.Banach.claim_3_3
  GenLimit.KleinbergWei.Banach.claim_3_5
  GenLimit.KleinbergWei.Banach.claim_3_6
  GenLimit.KleinbergWei.Banach.claim_4_11
  GenLimit.KleinbergWei.Banach.claim_4_18_change_index_card_bound
  GenLimit.KleinbergWei.Banach.claim_4_20_adjacent_pair_lca
  GenLimit.KleinbergWei.Banach.claim_4_4
  each uses a subset of [propext, Classical.choice, Quot.sound]

GenLimit.PatientMachine.patient_validity
  [propext, Classical.choice, Quot.sound]

GenLimit.PatientMachine.settledChargingCertificate
  [propext, Classical.choice, Quot.sound]

GenLimit.PatientMachine.patientScope_lowerDensity_half
  [propext, Classical.choice, Quot.sound]

GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
  [propext, Classical.choice, Quot.sound]

GenLimit.PartialEnumeration.Counterexample.output_not_mem_trueLanguage
  [propext, Classical.choice, Quot.sound]

GenLimit.PartialEnumeration.lemma_3_16_generation
  [propext, Classical.choice, Quot.sound]

GenLimit.PatientScope.PartialEnumerationCertificate.theorem_3_17
  [propext, Classical.choice, Quot.sound]

GenLimit.PartialEnumeration.theorem_3_17_lowerDensity
  [propext, Classical.choice, Quot.sound]

GenLimit.PartialEnumeration.theorem_3_17
  [propext, Classical.choice, Quot.sound]

GenLimit.Gold.Abstract.gold_theorem_7_1
  [propext, Classical.choice, Quot.sound]

GenLimit.Gold.Text.finiteLanguages_identifiableWith
  [propext, Classical.choice, Quot.sound]

GenLimit.Gold.Text.finiteLanguages_maximal_semanticallyIdentifiable
  [propext, Classical.choice, Quot.sound]

GenLimit.Gold.Text.enumerationLearner_identifiesFamily_of_isInclusionAntichain
  [propext, Classical.choice, Quot.sound]

GenLimit.Gold.Informant.informantEnumerationLearner_identifiesFamily
  [propext, Classical.choice, Quot.sound]

GenLimit.Gold.Text.exists_locking_of_identifiesLanguage
  [propext, Classical.choice, Quot.sound]

GenLimit.Gold.Text.superfinite_not_semanticallyIdentifiable
  [propext, Classical.choice, Quot.sound]

GenLimit.Gold.identifier_implies_fresh_generation
  [propext, Classical.choice, Quot.sound]

GenLimit.GoldKMSeparation.generation_without_identification
  [propext, Classical.choice, Quot.sound]

GenLimit.GoldDenseSeparation.dense_generation_without_identification
  [propext, Classical.choice, Quot.sound]
```

These are Lean/Mathlib's standard classical and quotient axioms. The project
adds no axiom.

## Access-model audit

The shared `OracleFamily` record is declared in
`GenLimit.Core.OracleFamily`. The semantic #01 generator uses its languages
and infinitude proofs; #01 criticality asks for exact inclusion between whole
languages, so this short construction is classical and noncomputable from the
pointwise oracle in general. The finite-set interface is semantic as well: it
uses whole-language inclusion and classical fresh-element choice, while its
candidate scope is determined solely by the number of distinct observations.
Both finite-query #01 machines additionally use the `query` field and realize
their tests as finite Boolean computations. The Proceedings machine tests the
new endpoint; the separate arXiv-v1 machine searches the whole selected prefix
and returns its least fresh eligible element.

The #39 Dense Generation machine receives the same family object for direct
comparison, but its semantic transition also uses only the languages and
their infinitude; recursive criticality asks for exact inclusion between whole
languages.  Its decisions are therefore classical and noncomputable.  The
#39 theorem does not state that this machine can be run using
finitely many membership queries.

For partial enumeration, `closure` keeps exactly the infinite nonempty finite
intersections, ordered by their binary subset codes. Membership in a selected
intersection is a finite conjunction of original queries, but deciding which
intersections are infinite is classical and noncomputable. Thus the filtered
indexing is part of the semantic access-model boundary.

The #02 Learning Theory closure and prompted generators are semantic classical
constructions over a generic countable example type. They choose fresh points
from infinite common cores and do not expose ERM, max--min, finite-query, PAC,
online-regret, or runtime interfaces. Generator values receive only their
finite histories, not the hidden target, target membership, correctness
feedback, or a convergence threshold.

The #06 Noisy Examples generators use the same history-only generic interface.
Noise budgets, targets, and class indices are quantified in correctness
predicates rather than supplied to the generator. Common-core, noisy-closure,
diagonal-cover, and robustification constructions use classical choice and do
not expose membership-oracle or runtime interfaces. Noise in stream hypotheses
counts bad occurrences; finite noisy-closure witnesses count distinct bad
values. Those two notions are deliberately not conflated.

#08 Hallucination Detection's native detector uses a finite inductive `OracleTree` at every
round, so candidate-set membership queries are finite and adaptive by type.
The function constructing the tree, indexed-family membership tests, and
Angluin identifier remain semantic/noncomputable; no runtime or query bound
is asserted. `ConditionTwo` supplies finite tell-tales only existentially.
The effective Angluin predicates retain `Computable` and `Computable₂`
requirements, while the proved sufficiency conclusion is explicitly
semantic. Complete labeled negative-example streams are substantive only
when such a stream exists.

Paper10's generators use the shared history-only semantic interface. Its
source-facing lower bounds quantify over duplicate-free exact presentations,
while a single Paper10 bridge yields lower bounds for the library's stronger
repetitions-permitted interface when needed. Theorem 3.2's no-adversary-input clauses use
Paper10-local injective autonomous schedules: the next scheduled value depends
only on the clock. A generic adapter consults finite history solely to skip
values already shown when deriving the standard Core predicates; it does not
learn the target from that history. The signed-integer schedules are explicit,
but the reused closure, countability, and fresh-choice arguments are classical;
no finite-query, computability, runtime, or randomized interface is claimed.

#28 identifiers and generators are likewise semantic total functions on
finite histories. The paper presents contrastive observations as unordered
two-element sets, while Lean learners consume an oriented `Edge`; crossing,
incidence, and the closure-dimension carrier are orientation-invariant, but no
target-scope theorem transports arbitrary learners across the two interfaces.
The closure, tell-tale, and fresh-point constructions use classical choice.
The repaired theorem
`ContrastiveGeneration.absenceCountIdentifier_finitely_identifies` exposes
the named identifier for every finite corruption budget without supplying the
budget or hidden target to it. Its minimizer still uses classical choice among
finite minimizers rather than the paper's fixed-enumeration tie-break, so the
repair does not establish computability, oracle-free execution, or a runtime
bound.

#31's generators and learners are also semantic functions. The
memoryless, sliding-window, and adaptive-buffer interfaces constrain the
dynamic observations or state available at each round, while arbitrary
family-wide sets, orders, infinitude tests, and codebooks remain static
noncomputable data. `MemorylessSetGenerator` has codomain `Set α`; successful
runs require eventual infinite target-contained output, and the explicit
positive witnesses return infinite sets, but the raw type does not impose
infinitude on every off-target input.

The density declarations quantify over target-specific ordered realizations,
not one ambient order fixed before every family and strategy. The Appendix
incremental element construction intentionally encodes the complete finite
history in the previous unbounded natural output. This matches the paper's
semantic model and is not a bounded-bit-memory implementation. The repaired
`lemma_A_3` only packages existing disjoint coding-cell facts; it adds no
oracle, computability, runtime, bit complexity, convergence rate, or random
resource.

## Theorem scope

The #0 Language Identification layer is semantic. Its abstract identification-situation model
formalizes all three clauses of Theorem 7.1: necessity of distinguishability,
sufficiency of collapsing uncertainty via every enumeration, and sufficiency
of distinguishability when each object's allowable-sequence set is countable.
The theorem does not claim that its learners or enumerations are computable.

The language-specific layer uses arbitrary exact positive texts and complete
correct informants. `finiteLanguages_identifiableWith` formalizes
the accumulated-sample learner; its empty-language case is vacuous because no
function `ℕ → ℕ` has empty range.
`enumerationLearner_identifiesFamily_of_isInclusionAntichain` proves
positive-text identification only under the stated inclusion-antichain
condition. `informantEnumerationLearner_identifiesFamily` identifies every
indexed family from complete informants, resolving duplicate names by the
least equal index.

`exists_locking_of_identifiesLanguage` is the arbitrary-text semantic locking
lemma for nonempty targets. The superfinite theorem derives finite tell-tale
necessity and rules out any class containing all finite languages and at
least one infinite language. It does not formalize the paper's stronger effective
construction of a recursive bad text.

`identifier_implies_fresh_generation` converts exact-name identification of
an infinite oracle family into the #01 trace-level freshness guarantee using a
classical fresh-element selector. The co-singleton separation instead uses
the existing finite-query #01 generator on the uniformly decidable family
`ℕ, ℕ \ {0}, ℕ \ {1}, ...`; that family is #01-generatable from every exact
text but is not #0-identifiable from all arbitrary positive texts.
`dense_generation_without_identification` strengthens the same-family
separation with PatientScope output novelty and target-relative lower density
at least `1 / 2`.

The #0A Inductive Inference from Positive Data development separates arbitrary
semantic learners from the computable indexed-family interface. At the
semantic level, `semanticallyInferrable_iff_conditionTwo` characterizes
positive-data identification by nonuniform finite tell-tales. At the effective
level, `theoremOne` proves `EffectiveInferrable F ↔ ConditionOne F`, and
`corollaryOne` exposes the corresponding finite-tell-tale consequence. The
Theorem 2 proposition is recorded only as a statement. The declaration
namespace remains `GenLimit.Angluin` after the numbered path migration.

All four #01 paths prove the current Lean specification on their stated
interfaces: eventually every output lies in the target and is absent from the
adversary sample observed by that time. The finite-set path remains correct
under repeated observations by using distinct-observation cardinality as its
candidate scope. The two finite-query paths formalize different published
Section 5 algorithms: the NeurIPS proceedings endpoint test and the arXiv-v1
least-fresh whole-prefix search. None requires outputs from different
generator rounds to be distinct.

The current #01 scope does not include finite-family uniform Theorem 2.2,
robust-prompt Theorem 7.1, arXiv-v1's stronger regular-subset-query prompted
results, or the associated context-free and impossibility claims. The universe
is fixed to `ℕ`; no arbitrary-countable-universe transport theorem is claimed.

The #02 Learning Theory declarations cover the ordinary and prompted generation
definitions and characterizations, closure-dimension and optimal sample-
complexity bounds, hierarchy separations, finite-cover results, Lemmas
4.2--4.3, and the valid Appendix C results. Theorem 4.1 is checked only at the
VC/Littlestone combinatorial boundary. Explicit bridges prove Theorem 2.2 and
Theorem 2.3 with Angluin's indexed-family/countability hypothesis restored;
an uncountable UUS selector-antichain diagnostic refutes P02's printed
arbitrary-class Theorem 2.3. The formalization does not claim the literal
PAC/IID or online-regret models or the paper's computational and efficiency
remarks. It also refutes the false arbitrary-stream EUC prose equivalence
while proving Theorems C.2 and C.4 from Definition C.1.

The #05 Hallucinations, Breadth, and Stability declarations cover the
deterministic semantic support layer of arXiv:2412.18530v2. They prove the
Theorem 3.3 exact-breadth/Angluin equivalence, the constructive direction of
Theorem 3.8, and the approximate-breadth clause of Theorem 3.15. They do not
claim Turing computability, support-oracle computability, distributional
realizability, statistical rates, or the missing finite-non-uniqueness lower
bounds. Under the source's standing infinite-language assumption, Lean proves
that literal fresh exact breadth (Definition 3.1) cannot be combined with
raw-support stability (Definition 3.14); the same conflict affects literal
Proposition 8.10 and Corollary 8.11(2). These are recorded as source-gap
countertheorems, alongside a separately named whole-target/sample-restored
repair that is not presented as the printed theorem. See the
[#05 map](PaperMaps/Paper05_HallucinationsBreadthAndStability.md).

The #06 Noisy Examples declarations cover every paper-owned numbered definition and
valid qualitative result, including both main characterizations, finite- and
countable-class consequences, robustification, finite-union generation, and
Appendices C/D. Lean makes the source's implicit nonempty or infinite ambient
universe assumptions explicit and follows displayed Definition D.1 where it
conflicts with nearby prose. It does not define a numerical `NC_n`, prove the
`Theta(NC_n)` sample-complexity statement or `NC_n(H_i) < i`, or claim an
effective algorithm. These boundaries and repairs are itemized in the
[#06 map](PaperMaps/Paper06_NoisyExamples.md).

The #07 Density Measures declarations cover the strict-critical selector and
temporal index-density corollary, feasible-sequence Claims 4.2--4.7, the
Definition 4.5 predicate with conditional uniqueness, finite topology, the
dynamic finite-rank forest through Corollary 6.10, the Claim 6.11 persistence
diagnostic and frozen-frame repair, and the rational-level, run-thinning,
reservation-history, and conditional `1/8` / corrected capacity-two `1/10`
Theorem 6.12 endgames. The dynamic bridge from bad runs to the charge
certificates, headline output-generation theorems, truth-index existence, and
minimax results are not claimed.
See the [#07 map](PaperMaps/Paper07_DensityMeasuresForLanguageGeneration.md).

The native #08 Hallucination Detection declarations cover all numbered definitions and valid
results at the paper's semantic, unrestricted-oracle level. Theorem 2.1
equates eventual subset detection with semantic identification; Corollary 2.2
uses Angluin's finite tell-tale `ConditionTwo`; and Theorem 2.3 assumes a
complete, perfectly labeled enumeration of the domain. Lean corrects the
paper's false inference after Example 1 by proving that `{i}` is a tell-tale
for the language of multiples of `i`. Theorem A.2 keeps the paper namespace
but lives in the explicit #02-to-#08 bridge. No effective detector, query/runtime
bound, probabilistic carry-over theorem, or effective tell-tale discovery
procedure is claimed. See the
[#08 map](PaperMaps/Paper08_HallucinationDetection.md) and
[#0A map](PaperMaps/Paper00A_PositiveDataInference.md).

The Paper10 Union-Closedness declarations cover overview Theorems 3.1--3.3,
detailed Theorems 4.1, 4.3, and 4.4, and deterministic Proposition A.1.
Theorems 4.1 and 4.3 use a single paper-local alternating engine on their
common hard subfamily. Theorem 3.3's relation to Theorem 3.1 is exposed using
#02's finite-EUC-cover result. Theorem 3.2 is strengthened with the source's
explicit autonomous negative- and positive-integer schedules; their freshening
bridges imply the standard uniform/non-uniform claims. Detailed Theorem 4.4
continues to reuse #02's general countable-class theorem. Randomized Proposition
A.2 is not formalized. Appendix A.2 contains a generic deterministic principle
conditional on infinite-limit membership, not the source's concrete family or
Remark A.3. The source's duplicate-free presentation convention and the
one-way bridge to the library's all-presentations lower bound remain explicitly
distinguished.
See the [Paper10 map](PaperMaps/Paper10_UnionClosednessOfLanguageGeneration.md).

The #15 Partial Enumeration declarations prove the finite-scope Theorem
2.1/Overview 1.5, both Lemma 2.3 generation reductions, a concrete raw-index
stuttering realization of Algorithm 1 and Lemma 2.5, Theorems 2.2/2.4 and
Overview 1.8, semantic fresh output, the corrected capacity-two `α / 3`
density endpoint, the conditional capacity-one pod `α / 2` endpoint, and the
full-enumeration separation hierarchy. They do not claim literal equality with
the compressed displayed trace, the dynamic pod construction, the learner
layer, or the ambiguous partial-enumeration topology.
See the [#15 map](PaperMaps/Paper15_PartialEnumeration.md).

The #23 Banach Density declarations cover absolute one-dimensional density
Claims 3.3 and 3.5, perfect-tower Claim 3.6 under a supplied exact
presentation, finite-natural derivatives and point ranks, repaired Claim 4.11,
finite-tree LCA Claims 4.18 and 4.20, and Claim 4.4/Appendix Claim 7.1. The
structural-tree/pod state machine, relative density, generation, transfinite
ranks, and higher-dimensional geometry are excluded. See the
[#23 map](PaperMaps/Paper23_BanachDensityTopologyAndGeometry.md).

The #28 Contrastive Generation declarations cover the deterministic semantic core of Sections
4--6. `theorem_4_7` gives the three-way contrastive-identification
characterization; `theorem_5_4_quantitative` and `theorem_5_4` give the exact
threshold and finite closure-dimension characterization; and `theorem_5_5`
gives the target-dependent increasing-cover characterization. The core
criteria, Proposition 5.12 obstruction, two explicit hierarchy witnesses,
co-singleton text fragility, named finite-corruption identifier, corrupted
incomparability, and exact defect-infimum identity are also kernel checked.

This does not assemble the paper's full clean strict diamond in one theorem:
the general contrastive-generation-to-text-generation inclusion and the
strict text-identification/text-generation separation are absent. The public
statements also do not prove unordered-to-oriented learner transport, the
broader infinite-defect robustness principle, corrupted generation,
probabilistic results, or effective algorithms. The named Theorem 6.6 repair
closes only the witness-interface gap; it does not make the classical
absence-count minimizer computable. See the
[#28 map](PaperMaps/Paper28_ContrastiveGeneration.md).

The #31 Bounded Memory declarations cover the central deterministic semantic results:
memoryless set generation under finitely repeating presentations; the
singleton-core characterization under arbitrary repetitions; element- and
index-output separations; the memoryless and sliding-window upper-density
values in Lean's order-robust specialization; the lower-density obstruction;
the adaptive-buffer lower bound; the three-state exact-identification
obstruction; finite-family approximate identification; and the Appendix index
and element constructions. The repaired `lemma_A_3` exposes the paper-facing
existential coding-cell statement without changing its assumptions.

This scope does not transport the `ℕ`-specific headline results to arbitrary
countable universes or restate the density theorems in the paper's one fixed
ambient-order game. It does not make every raw memoryless set output
intrinsically infinite or transport Theorem 5.2's learner from an equal-range
relabeling back to the input indexing. The countable-family density remark,
other temporal-density aggregates, countable approximate-identification
extension, weak Angluin obstruction, and a full named Sperner theorem remain
unassembled. No machine-level memory, computability, runtime, oracle, rate, or
randomness claim is made. See the
[#31 map](PaperMaps/Paper31_BoundedMemory.md).

## ChatGPT Pro statement-faithfulness evidence

The new #07/#15/#23 adaptation received AI-assisted source comparison during
development, but it has no checksum-recorded ChatGPT Pro artifact and no
completed human correspondence audit. Its kernel checks, source-facing maps,
and correspondence-review status are reported separately.

The added #01 paths and the #02, #06, #08, #28, and #31 developments were
checked with ChatGPT Pro at the maintainer's direction. Stage 1 reconstructed
their mathematical interfaces from Lean declaration signatures and
statement-relevant definition bodies while withholding the papers and
excluding comments and proof bodies as mathematical evidence. Stage 2 compared
those reconstructions with the pinned author sources, checking objects and
types, quantifier order, hypotheses and conclusions,
representation and indexing, access and output interfaces, theorem coverage,
witness-link assembly, weakening or strengthening, edge cases, and omissions.

The #01 check used the pinned NeurIPS proceedings and arXiv-v1 sources; #02
used arXiv v5; #06 and #08 used arXiv v2; and #28 and #31 used arXiv v1. All
six checks used
Lean snapshot
`dfcd13534f9d51642a9f88904268e95454c88f7f`. Immutable evidence, source
hashes, findings, and exact boundaries are recorded under
[`AuditRecords/`](AuditRecords/), in the numbered #01, #02, #06, #08, #28,
and #31 directories. ChatGPT Pro did not audit theorem
proof-body correctness, establish proof-step correspondence, rerun Lean,
certify the papers' mathematics, or perform a human audit. These records are
review input, not kernel results or human correspondence audits.

#28 deliberately records the audit/improvement loop in order:

1. the immutable review inspected source snapshot
   `dfcd13534f9d51642a9f88904268e95454c88f7f`;
2. the code-only and source-comparison artifacts entered private history at
   `1bb4da0b7004933ffa3eb36f9df899eb65039421` and
   `b66fc33932637dd3a705710758dc2f1140428a20`;
3. the audited baseline was ported publicly at
   `8d9e40c4b512c6037ce0522f16b97c7c9d860e5e`;
4. its checksum-pinned audit record followed at
   `9d7734a43dd3567c2ece588dbdb0d12059cb72ff`; and
5. only afterward was the private repair from
   `fecfee275526952122e16dec275d99a352c2f428` applied as a separately tracked
   public follow-up at `6a1904dd5bc33a47b310adc753d0a35ad9df80cf`.
   It adds `absenceCountIdentifier_finitely_identifies`, factors
   `theorem_6_6` through that named witness, and adds the corresponding axiom
   probe.

The immutable evidence still describes the pre-repair baseline. The
machine-readable record pins both source trees, stable patch ID
`0a2effe9ba91105e4bf664f78bfdde649dee467e`, and source diff SHA-256
`aec4001cfcfd0e2c5cc7e1503f0730bbfe951fbeb079e68995987b9b3234cf04`.

#31 preserves the same audit/improvement ordering:

1. the immutable review inspected source snapshot
   `dfcd13534f9d51642a9f88904268e95454c88f7f`;
2. both the code-only reconstruction and source comparison entered private
   history at `b66fc33932637dd3a705710758dc2f1140428a20`;
3. the neutral ordered-density foundation was extracted publicly at
   `a0ed62b1fa18107b8a1e815e61fce5db56f6cb94`;
4. the 78-probe audited baseline was ported publicly at
   `11b20d4feaa129447a5a34c12dc0954321cc0677`;
5. its checksum-pinned audit record followed at
   `71265c18e05f7650660dec4d117a5b03b645e7f0`; and
6. only afterward was the 18-line Appendix Lemma A.3 wrapper applied at
   `9dc23fcb03eb0be08a1504d80d618508e0d45ea8`, together with probe 79.

The immutable evidence still describes the unbundled pre-repair baseline.
The record pins the private source repair by stable patch ID
`3afa77c3e89b5c7b772aa19c85e6860d7f1d9a12` and diff SHA-256
`66b1f75638cfe76d5763b7a0478af1116b1646a6325b243392b2bdfedb161a95`,
and separately records the adapted public patch. The repair resolves only the
missing theorem-entry-point interface.

`patientScope_lowerDensity_half` proves the operational achievability bound
`1/2 ≤ lower density` for every exact presentation of every indexed target.
`patientScope_generation_and_lowerDensity` adds eventual target validity and
novelty. The separate adversarial upper bound used to call `1/2` optimal is
not included in this version.

`lemma_3_16_generation` assumes `Presents stream E`, `E.Infinite`, and
`E ⊆ O.language z`; it proves eventual target validity, freshness from the
stream, and output novelty for patient-scope on the finite-intersection
closure. `theorem_3_17_lowerDensity` proves the lower bound
`(1/2) * relativeLowerDensity E K ≤ generator lower density`. It does not
claim a full `1/2` bound unless the relative lower density of `E` in `K` is
one.

The formalization of Example 3.15 fixes the otherwise unspecified order of
the partial enumeration to `4, 8, 12, ...`. For that exact stream, the direct
untransformed machine outputs `1, 3, 5, ...` and never outputs an element of
the true positive-even language.

## Human audit records

Completed human reviews, their exact levels, historical code anchors, and the
pending ChatGPT Pro review queue are recorded only in the authoritative
[human-audit ledger](AuditRecords/Human/README.md). They are separate from the
kernel and access-model checks in this file.
