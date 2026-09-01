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
Lean fully covers Lemma 9 and the concrete Turing-machine specialization of
Corollary 15. The remaining seven claims have explicit partial coverage:

- Theorems 12 and 14 expose the enumeration argument after a suitable
  bounded representative exists; the physical `q`-ECTT bridge is not
  postulated.
- Corollary 13 records the abstract identity-encoding specialization, but
  does not instantiate named complexity classes.
- Theorem 16 proves the transition-diagram identity and the rational
  learning-by-enumeration core, but not a complete geometric TM/PTO model.
- Theorem 17 proves the late-splitting and finite-mass obstruction, but not
  the final Halting Problem reduction.
- Corollary 18 proves the information-forgetting implication, while its
  machine-level non-IPTD conclusion remains dependent on the missing part of
  Theorem 17.
- Theorem 21 proves the tagged two-step simulation and finite transition
  cover. Its MSM convergence theorem is conditional on score separation and
  soundness invariants not established by the printed proof.

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
| Definition 8 and Lemma 9 | `IsCharacteristicSet`, `lemma_9_distinguishability` | Full for total observation domains; partial observations can be encoded in `Option` |
| Theorem 12 | `theorem_12_timeRestrictedIOO_core` | Uniform semantic enumeration core; `q`-ECTT and named complexity classes omitted |
| Theorem 12 minimum-state proof sentence | `theorem_12_minIndex_claim_not_justified` | Concrete diagnostic showing budget-first search need not select the minimum representation index |
| Corollary 13 | `corollary_13_parametrizedTMClass_core` | Abstract specialization only |
| Theorem 14 | `theorem_14_universalTBO_core` | Conditional core after representative existence |
| Corollary 15 | `corollary_15_turingTBO` | Full concrete finite-table single-tape TM specialization |
| Theorem 16 | `theorem_16_recursiveToRational_behavior`, `theorem_16_rationalEnumeration_core` | Transition identity and enumeration core |
| Theorem 17 | `theorem_17_lateSplit_characteristic_obstruction`, `theorem_17_mass_lower_bound_core` | Semantic and finite-mass core; Halting reduction omitted |
| Corollary 18 | `corollary_18_forgetting_preserves_indistinguishability`, `corollary_18_characteristic_bound_lifts_to_richer_observations` | Observation-information order; final non-IPTD conclusion omitted |
| Theorem 21 | `theorem_21_tagged_two_step`, `taggedMachine_runFrom`, `theorem_21_transition_cover_core`, `theorem_21_msm_merge_order_core` | Construction and sample-cover core; MSM convergence conditional |

## Module organization

```text
Definitions.lean              Definition 7 semantic framework
Enumeration.lean              executable uniform enumeration learner
TuringMachines.lean           concrete bounded single-tape evaluator
TimeBounds.lean               Theorems 12 and 14, Corollaries 13 and 15
Transducers.lean              Theorem 16 transition and enumeration cores
CharacteristicSets.lean       Lemma 9 and Theorem 17 lower-bound cores
ObservationForgetting.lean    Corollary 18 information-order argument
TaggedSimulation.lean         Theorem 21 construction and sample cover
MSMMergeOrder.lean            conditional MSM convergence theorem
Results/Overview.lean         compact paper-facing theorem wrappers
```

## Verification and audit boundary

The repository-level `Audit.lean` checks the principal P11 declarations
against the project axiom allowlist. The generated `RegistryAudit.lean`
checks every claim-linked declaration's existence, defining module, and
logical dependencies. These are kernel audits, not proof-correspondence
audits. The formalization makes no hidden `q`-ECTT or Halting-Problem axiom,
and the executable learners receive only finite observation histories.
