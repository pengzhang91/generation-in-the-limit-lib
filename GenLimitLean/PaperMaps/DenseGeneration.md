# DenseGeneration patient-scope paper map

Lean umbrella: `GenLimit.DenseGeneration`

Main declarations:

- `GenLimit.PatientMachine.patientScope_lowerDensity_half` (Theorem 3.14),
- `GenLimit.PartialEnumeration.lemma_3_16_generation` (Lemma 3.16), and
- `GenLimit.PartialEnumeration.theorem_3_17` (Theorem 3.17; the intrinsic
  parameter-free form is `theorem_3_17_lowerDensity`).

Manuscript: *Dense Language Generation Made Simple: Deterministic,
Randomized, and Multi-Order Algorithms*, by Ziyi Cai, Shuangping Li,
Yiheng Shen, Kangning Wang, and Peng Zhang.

Source version: the unpublished manuscript supplied for this formalization,
with Definitions 3.1--3.6, Lemma 3.11, Fact 3.12, Lemma 3.13, Theorem 3.14,
Example 3.15, Lemma 3.16, and Theorem 3.17 numbered as below. A public version
identifier has not yet been recorded.

The current Lean development covers the deterministic patient-scope and
partial-enumeration results listed above. The manuscript's randomized and
multi-order developments are not included in this repository version.

## Relation to prior work

Kleinberg and Wei first established the optimal lower-density guarantee under
partial enumeration in *Language Generation and Identification From Partial
Enumeration* (STOC 2026): if the enumerated subset has relative lower density
`α` in the target, density `α / 2` is achievable and optimal. DenseGeneration
gives a simpler patient-scope construction for the achievability guarantee;
the Kleinberg--Wei algorithm and the optimality upper bound are not formalized
here.

Human audit status: the exact-presentation patient-scope result has a Level 2
end-to-end audit covering its main theorem statement, recursive criticality,
focus, and complete state-machine construction. The finite-intersection
transformation and the Lemma 3.16--Theorem 3.17 path also have a Level 2
audit. Intermediate proof correspondence and Example 3.15 have not yet been
audited. See the [human audit record](../HUMAN_AUDIT.md).

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

The partial-enumeration branch is organized separately while reusing the same
machine and charging infrastructure:

```text
Core.PartialPresentation ──> Partial.Closure ──> Partial.Critical / Validity
                                                    |
                         Partial.Trace / Patient.StableTargetCharging
                                                    |
Abstract.PartialEnumeration / PartialDensity ──> Partial.Certificate
                                                    |
                                               Partial.Main
```

## Indexing and density conventions

The manuscript uses positive integers and one-based language indices.  Lean
uses `ℕ`, strict prefixes `Finset.range n`, and zero-based language indices.
The lower-density denominator is the number of target elements in the ambient
prefix, so the target need not be `Set.univ`. Exact and partial enumeration
use the same `relativeLowerDensity` metric; their paper-facing wrappers select
different generators but do not redefine the metric.

### Patient-scope counter correspondence

This correspondence was checked directly against the Dense Generation manuscript.

| Paper object | Lean encoding | Correspondence |
|---|---|---|
| Positive integer `x` | A value `x₀ : ℕ` | `x = x₀ + 1`; consequently the paper prefix `[n] = {1, ..., n}` corresponds exactly to `Finset.range n = {0, ..., n - 1}`. |
| Language `L_j`, `j ≥ 1` | `O.language i` | `j = i + 1`. |
| Initial time `t = 0` | `run O stream 0` | Both are the state before either party has announced a value. |
| Paper round `t ≥ 1` | Lean round argument `r = t - 1` | The adversary's paper-round-`t` announcement is `stream r`, the generator's announcement is `output O stream r`, and the resulting state is `run O stream t`. |
| Observations through paper round `t` | `sample stream t` | Within Lean round `r`, decisions and output availability use `sample stream (r + 1)`, after receiving `stream r`. |
| Scope size `s`, containing `{L₁, ..., L_s}` | `scope = s`, containing indices in `Finset.range s` | The numerical scope size is unchanged; paper membership `j ≤ s` becomes Lean membership `i < s` under `j = i + 1`. |
| Paper focus index `j` | `State.focus = i` | `j = i + 1`; in particular the initial paper focus `L₁` is Lean focus `0`. |
| Focus-change count `τ` | `State.tau` | Both start at `1`.  On an exact-presentation run, Lean leaves `tau` unchanged exactly when the focus is unchanged and otherwise increments it by one. |
| “The focus has not changed during the previous `2^τ` time steps” | `State.age` and the test `2 ^ old.tau ≤ old.age` | The paper has no separate `age` variable.  Lean initializes it to `0`, increments it after a completed round with the same focus, and resets it to `1` after a round that changes focus.  The wait test is made before the next output. |
| Backtrack to paper language `L_j` and set scope size to `j` | Choose Lean index `i = j - 1` and set `scope := i + 1` | The landing focus is included as the last index of the truncated scope. |

Thus a paper output in round `1` is Lean `output O stream 0`, whereas the
post-round-`1` state is Lean `run O stream 1`.  Repeated scope expansion while
the focus remains unchanged also agrees with the paper's per-time-step test:
after the first successful wait, the same test is performed again at the next
time step.  The `age` field is not reset merely because the scope expands.

Audit status for this table: **PASS** for the counter/index translation in the
machine state and one-step timing.  This entry does not by itself certify the
rest of the algorithm or its proof correspondence.

In Section 3.3, `E` is the set actually enumerated and `K` is the true target,
with `E ⊆ K`. The transformed `closure` filters the nonempty finite
intersections that are infinite while preserving their raw binary-code order.
Its Lean indices are zero-based positions in that filtered order, not the raw
binary codes themselves.

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
| Shared stable-target charging | `PatientMachine.StableTargetRun.chargingCertificate` | `GenLimit.DenseGeneration.Patient.StableTargetCharging` | DenseGeneration |
| Prefix inequality in Theorem 3.14 | `attackerCount_le_log2` | `GenLimit.DenseGeneration.Abstract.PatientScope` | DenseGeneration |
| `log₂(n)/n → 0` | `tendsto_natLog2_div` | `GenLimit.DenseGeneration.Abstract.Density` | General/DenseGeneration |
| Target-relative lower-density metric | `relativeLowerDensity` | `GenLimit.DenseGeneration.Abstract.TargetDensity` | General/DenseGeneration |
| Sparse-target lower-density endgame | `lowerDensity_half_of_target_counting` | `GenLimit.DenseGeneration.Abstract.TargetDensity` | General/DenseGeneration |
| Abstract arbitrary-target assembly | `theorem_3_14_target` | `GenLimit.DenseGeneration.Abstract.TargetMain` | DenseGeneration |
| Operational Theorem 3.14 | `patientScope_lowerDensity_half` | `GenLimit.DenseGeneration.Patient.Main` | DenseGeneration |
| Example 3.15 (explicit increasing multiples-of-four order) | `Counterexample.presents_enumeratedLanguage`, `Counterexample.output_eq_odd`, `Counterexample.output_not_mem_trueLanguage` | `GenLimit.DenseGeneration.Partial.Counterexample` | DenseGeneration |
| Partial-presentation consistency | `candidate_eventually_consistent_iff_presented_subset` | `GenLimit.Core.PartialPresentation` | Core |
| Finite-intersection family | `closure`, `closureCode` | `GenLimit.DenseGeneration.Partial.Closure` | DenseGeneration |
| Transformed run stays on-model | `closure_onModel` | `GenLimit.DenseGeneration.Partial.Critical` | DenseGeneration |
| Stable critical target subset | `exists_eventually_critical_subset_target` | `GenLimit.DenseGeneration.Partial.Critical` | DenseGeneration |
| Lemma 3.16 | `lemma_3_16_generation` | `GenLimit.DenseGeneration.Partial.Validity` | DenseGeneration |
| Partial-enumeration prefix inequality | `enumeratedCount_le_two_mul_defender` | `GenLimit.DenseGeneration.Abstract.PartialEnumeration` | General/DenseGeneration |
| Abstract Theorem 3.17 | `PartialEnumerationCertificate.theorem_3_17` | `GenLimit.DenseGeneration.Abstract.PartialDensity` | DenseGeneration |
| Operational certificate assembly | `stableTargetRun_nonempty`, `StableTargetRun.partialCertificate` | `GenLimit.DenseGeneration.Partial.Certificate` | DenseGeneration |
| Operational Theorem 3.17 | `theorem_3_17`, `theorem_3_17_lowerDensity` | `GenLimit.DenseGeneration.Partial.Main` | DenseGeneration |

The exact-presentation declaration is uniform in the family, target index,
and target presentation. The Section 3.3 declarations are uniform in the
family, target index, and partial presentation `E ⊆ K`; the generator itself
receives neither `E` nor the target index, only the family and observed stream.

The target-relative switch-loss bound uses a deliberate simplification of the
manuscript proof. Rather than proving that all charged blocks are pairwise
disjoint, Lean uses distinct positive `tau` labels: among `m` losses one label
is at least `m`, so its single charge already contains at least `2^m` target
elements. This gives the same logarithmic bound.

## Access-model boundary

The machine follows Definition 3.2 semantically: criticality uses exact
inclusion between infinite languages, and its transitions use classical
choice.  It therefore does not claim a finite-membership-query implementation.
The Section 3.3 filter must additionally decide whether each finite
intersection is infinite. Although membership in an already selected
intersection is a finite conjunction of original oracle queries, this
filtering and reindexing step is itself classical and noncomputable.
