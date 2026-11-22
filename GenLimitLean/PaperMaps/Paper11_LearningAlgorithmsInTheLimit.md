# #11 Learning Algorithms in the Limit map

Lean module: `GenLimit.Paper11_LearningAlgorithmsInTheLimit`.
Declaration namespaces: `GenLimit.LearningAlgorithmsLimit` and the
paper-facing `GenLimit.LearningAlgorithmsLimit.Results`.

## Pinned source

- Hristo Papazov and Nicolas Flammarion, *Learning Algorithms in the Limit*;
- COLT 2025 proceedings version, PMLR 291, pp. 4486--4510
  ([proceedings page](https://proceedings.mlr.press/v291/papazov25a.html));
- local PDF: `papers/P11_LearningAlgorithmsInTheLimit.pdf`;
- local PDF SHA-256:
  `0fd7a1a1ce5d337de01e70e7b4380b405124017dea5f0ea1a20fb0e9814dcd0c`;
- machine-readable claim inventory:
  [`registry/papers/P11.json`](../../registry/papers/P11.json).

The final PMLR version is the formalization target. Source statements were
checked against rendered result pages 9--14 and appendix proof pages 20--25.
No named human correspondence audit currently covers P11.

## Scope and status

The claim inventory covers the nine main P11 results developed in Lean:
Lemma 9; Theorems 12, 14, 16, 17, and 21; and Corollaries 13, 15, and 18.
Theorems 12 and 14 now instantiate a finite-table simulator under the paper's quantitative extended Church–Turing thesis. The learner enumerates all program/parameter tuples. Corollaries 13 and 15 specialize to finite-table Turing machines. `PartialDomains.lemma_9_counterexample` refutes Lemma 9 for teacher-relative domains, including two computable teachers with infinite domains and nonempty characteristic sets. The common-domain repair has a positive proof.

- Theorem 16 reduces completed single-tape policy trajectories to two rational learning runs on the prescribed alphabet. One run recovers the action and the other recovers the terminal-step marker. Replaying the product gives the same final tape. The enumerated finite-table learner solves the rational problem.
- Theorem 17 proves both conclusions on the stated class of finite single-tape machines. A recursion-theorem fixed point gives a linear-time total teacher whose unary output exceeds the proposed mass budget. A computable selector on the whole class would yield an effective bound by simulating all of its legal examples. The appendix's additional assertion about selectors required to work only on linear-time teachers is outside this proof.
- Corollary 18 rules out every polynomial in the number of states for each of the three observation modes. Its mass inequality uses the length of the output in each training example.
- For Theorem 21, `MSM.LabelledDiagram.reaches_types` proves that a finite deterministic diagram with observable source types admits a sequence of actual maximum-score mergers that reaches one state per type while preserving all type-labelled edges. This handles ties at score one. `Results.theorem_21` compiles a terminal rooted quotient to a single-tape program. Every valid history yields a legal MSM output. A characteristic set of at most `2 * (states T).card * Fintype.card σ` inputs fixes that representation on every subsequent history and every presentation of the restricted source.

Theorem 10 is Gold's cited background impossibility result. Definitions 7,
8, 11, 19, and 20 and appendix Theorems 22--23 do not receive separate cards
in this main-result inventory.

## Public entry point

`GenLimit.Paper11_LearningAlgorithmsInTheLimit.Results.Overview` is the
compact paper-facing surface. Its declarations live in
`GenLimit.LearningAlgorithmsLimit.Results` and are thin wrappers around the
detailed proof-owning modules. The P11 umbrella imports this overview.

## Main-result correspondence

| Paper item | Lean declaration | Status |
|---|---|---|
| Definition 7 | `LearnsByCriterion`, `LearnsInLimit`, `SolvesLearningProblem` | Complete semantic interface |
| Definition 8 and Lemma 9 | `PartialDomains.lemma_9_counterexample`, `lemma_9_distinguishability` | Teacher-relative statement refuted. The common-domain version is proved. |
| Theorem 12 | `Results.theorem_12` | The quantitative simulation thesis supplies the finite simulator. Definition 11 supplies its search bound. |
| Theorem 12 minimum-state proof sentence | `theorem_12_minIndex_claim_not_justified` | Concrete diagnostic showing budget-first search need not select the minimum representation index |
| Corollary 13 | `Results.corollary_13` | One learner covers all finite programs satisfying a parameterized time bound. |
| Theorem 14 | `Results.theorem_14` | Quantitative simulation and the rough clock yield a single learner for all restricted legal inputs. |
| Corollary 15 | `corollary_15_turingTBO` | Full concrete finite-table single-tape TM specialization |
| Theorem 16 | `Results.theorem_16`, `Rational.enumeration_solves`, `Policy.execution_of_run` | Full reduction on actual halting computations and rational functions returning the final transition label. |
| Theorem 17 | `Results.theorem_17` | Both printed conclusions on the fixed paper tape alphabet and unrestricted word source. The mass conclusion already holds for linear-time total teachers. |
| Corollary 18 | `Results.corollary_18` | No polynomial-mass characteristic samples in IO, time-bound, or policy-trajectory mode. |
| Theorem 21 | `Results.theorem_21`, `theorem_21_tagged_two_step`, `taggedMachine_runFrom`, `theorem_21_transition_cover_core`, `theorem_21_msm_merge_order_core`, `MSM.LabelledDiagram.reaches_types` | Full statement with an explicit allowed tie convention |

## Module organization

```text
Definitions.lean              Definition 7 semantic framework
Enumeration.lean              executable uniform enumeration learner
TuringMachines.lean           concrete bounded single-tape evaluator
QuantitativeSimulation.lean   quantitative thesis, simulator and complexity bounds
PartialDomains.lean           teacher-relative counterexample to Lemma 9
TimeBounds.lean               Theorems 12 and 14, Corollaries 13 and 15
FiniteTransducers.lean        finite Mealy tables and enumeration
PolicyTrajectories.lean       geometric trace replay and halt-aware product
RationalReduction.lean        Theorem 16 causal learning reduction
MassDiagonal.lean             computability obstruction for unary-output recursive codes
UniversalTape.lean            binary single-tape realization of partial recursion
ConstantTape.lean             constant-output native machines with a uniform linear clock
RepresentationBudget.lean     effective syntax bound independent of the teacher's running time
NativeDiagonal.lean           diagonal lower bound on characteristic sample mass
EffectiveTables.lean          primitive recursive finite-table execution
SelectorBound.lean            effective output bound from any legal sample selector
TeachingImpossibility.lean    both machine obstructions and all three observation modes
Transducers.lean              abstract transition correspondence
CharacteristicSets.lean       Lemma 9 and Theorem 17 lower-bound cores
ObservationForgetting.lean    Corollary 18 information-order argument
TaggedSimulation.lean         Theorem 21 construction and sample cover
MSMMergeOrder.lean            conditional MSM convergence theorem
DeterminizingMerge.lean       merger consistency and cross-type score bound
TypedMergeRun.lean            maximum-score run reaching one state per observed type
TaggedTape.lean               doubled single-tape trajectories and finite event bound
ObservedTree.lean             finite prefix tree and observed transition endpoints
TerminalQuotient.lean         rooted maximum-score mergers to a terminal graph
CanonicalMerge.lean           normalization and a fixed terminal representation
MergeReplay.lean              terminal quotient compiled to a tape table
MSMLearning.lean              characteristic sample and stabilization for every ordering
MSMTheorem.lean               Theorem 21 for every total single-tape-computable function
Results/Overview.lean         compact paper-facing theorem wrappers
```

## Verification and audit boundary

The repository-level `Audit.lean` checks the principal P11 declarations
against the project axiom allowlist. The generated `RegistryAudit.lean`
checks every claim-linked declaration's existence, defining module, and
logical dependencies. These are kernel audits, not proof-correspondence
audits. The formalization makes no hidden `q`-ECTT or Halting-Problem axiom,
and the executable learners receive only finite observation histories.
