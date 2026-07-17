# DenseGeneration patient-scope paper map

Lean umbrella: `GenLimit.DenseGeneration`

Main declaration: `GenLimit.PatientMachine.patientScope_lowerDensity_half`

Manuscript: *Dense Language Generation Made Simple: Deterministic,
Randomized, and Multi-Order Algorithms*, by Ziyi Cai, Shuangping Li,
Yiheng Shen, Kangning Wang, and Peng Zhang.

Source version: the unpublished manuscript supplied for this formalization,
with Definitions 3.1--3.6, Lemma 3.11, Fact 3.12, Lemma 3.13, and Theorem
3.14 numbered as below. A public version identifier has not yet been recorded.

## Relation to prior work

Kleinberg and Wei had already achieved lower density `1 / 2`, including under
partial enumeration, in *Language Generation and Identification From Partial
Enumeration* (STOC 2026). DenseGeneration gives a simpler
patient-scope construction; the Kleinberg--Wei algorithm is not formalized
here.

Human audit status: the black-box input/output specification is complete;
algorithm and proof correspondence have not yet been audited. See the
[human audit record](../HUMAN_AUDIT.md).

The DenseGeneration development depends on `GenLimit.Core` and imports neither
the `GenLimit.KM.Semantic` path nor the `GenLimit.KM.FiniteQuery` path.  Its
recursive criticality is defined independently, and Lemma 3.4 is proved
directly from shared consistency stabilization.

## Dependency path

```text
Core ──> GenLimit.DenseGeneration.Critical / GenLimit.DenseGeneration.Dynamics
  |                  |
  |  GenLimit.DenseGeneration.Patient.Machine ──> invariants / validity / history
  |                                           |
  └─> GenLimit.DenseGeneration.Abstract counting  Fact 3.12 / departures
                       \                   /
                        charging certificates
                                 |
                       target-density endgame
                                 |
               GenLimit.DenseGeneration.Patient.Main
```

## Indexing and density conventions

The manuscript uses positive integers and one-based language indices.  Lean
uses `ℕ`, strict prefixes `Finset.range n`, and zero-based language indices.
The lower-density denominator is the number of target elements in the ambient
prefix, so the target need not be `Set.univ`.

## Paper correspondence

| Paper item | Lean declaration | Module | Ownership |
|---|---|---|---|
| Consistency, Definition 3.1 | `Consistent` | `GenLimit.Core.Basic` | Core |
| Recursive criticality, Definition 3.2 | `RecursiveCritical` | `GenLimit.DenseGeneration.Critical` | DenseGeneration |
| Descending chain, Remark 3.3 | `recursiveCritical_subset_of_le` | `GenLimit.DenseGeneration.Critical` | DenseGeneration |
| Target eventually critical, Lemma 3.4 | `target_eventually_recursiveCritical` | `GenLimit.DenseGeneration.Critical` | DenseGeneration, using Core stability |
| Scoped focus, Definitions 3.5--3.6 | `IsFocus` | `GenLimit.DenseGeneration.Critical` | DenseGeneration |
| Focus contained in target | `focus_subset_target` | `GenLimit.DenseGeneration.Critical` | DenseGeneration |
| Patient-scope algorithm | `PatientMachine.run`, `PatientMachine.output` | `GenLimit.DenseGeneration.Patient.Machine` | DenseGeneration |
| Run invariants | `run_focus_isFocus`, `run_tau_eq_focus_test`, `run_used_eq_outputsBefore` | `GenLimit.DenseGeneration.Patient.MachineInvariant` | DenseGeneration |
| Scope progress | `target_eventually_in_scope` | `GenLimit.DenseGeneration.Patient.Validity` | DenseGeneration |
| Lemma 3.11 | `patient_validity` | `GenLimit.DenseGeneration.Patient.Validity` | DenseGeneration |
| First-announcer partition | `range_subset_first_announcements`, `ownership_disjoint` | `GenLimit.DenseGeneration.Abstract.Announcements`, `GenLimit.DenseGeneration.Abstract.GameTrace` | General/DenseGeneration |
| Trace validity | `eventual_validity_and_novelty` | `GenLimit.DenseGeneration.Abstract.GameTrace` | DenseGeneration |
| Fact 3.12 local comparison | `previous_output_lt_of_not_lateSwitch` | `GenLimit.DenseGeneration.Patient.Fact312` | DenseGeneration |
| Fact 3.12 injection | `predecessorPartner_injective_machine` | `GenLimit.DenseGeneration.Patient.Fact312` | DenseGeneration |
| Prior patient departure | `exists_upwardDeparture_of_critical_lt_focus` | `GenLimit.DenseGeneration.Patient.Departure` | DenseGeneration |
| Canonical label injection | `certifiedLanding_label_injective` | `GenLimit.DenseGeneration.Patient.Departure` | DenseGeneration |
| Exponential charging bound | `charging_pow_le_prefix` | `GenLimit.DenseGeneration.Abstract.Charging` | General/DenseGeneration |
| Concrete Lemma 3.13 data | `settledChargingCertificate` | `GenLimit.DenseGeneration.Patient.Charging` | DenseGeneration |
| Target-relative Lemma 3.13 | `prefixCount_le_log2_targetCount` | `GenLimit.DenseGeneration.Abstract.TargetSwitchCharging` | General/DenseGeneration |
| Prefix inequality in Theorem 3.14 | `attackerCount_le_log2` | `GenLimit.DenseGeneration.Abstract.PatientScope` | DenseGeneration |
| `log₂(n)/n → 0` | `tendsto_natLog2_div` | `GenLimit.DenseGeneration.Abstract.Density` | General/DenseGeneration |
| Sparse-target lower-density endgame | `lowerDensity_half_of_target_counting` | `GenLimit.DenseGeneration.Abstract.TargetDensity` | General/DenseGeneration |
| Abstract arbitrary-target assembly | `theorem_3_14_target` | `GenLimit.DenseGeneration.Abstract.TargetMain` | DenseGeneration |
| Operational Theorem 3.14 | `patientScope_lowerDensity_half` | `GenLimit.DenseGeneration.Patient.Main` | DenseGeneration |

The operational declaration is uniform in the family, target index, and exact
target presentation.  The generator itself receives no target index.

## Access-model boundary

The machine follows Definition 3.2 semantically: criticality uses exact
inclusion between infinite languages, and its transitions use classical
choice.  It therefore does not claim a finite-membership-query implementation.
