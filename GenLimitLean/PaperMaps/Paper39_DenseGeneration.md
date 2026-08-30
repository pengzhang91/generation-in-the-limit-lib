# #39 Dense Generation map

Lean module: `GenLimit.Paper39_DenseGeneration`.
Primary declarations retain their existing generic namespaces, including
`GenLimit.PatientMachine`, `GenLimit.PatientScope`, and
`GenLimit.PartialEnumeration`.

Reading-list identifier: **#39**, appended after the repository's established
36-paper working inventory and the two intervening website additions.

Public arXiv-v1 declarations:

- `GenLimit.Critical` (Definition 3.2, reused from #01),
- `GenLimit.Paper39ArxivV1.IsFocus` (Definitions 3.5--3.6), and
- `GenLimit.Paper39ArxivV1.FocusRefreshExample.focus_changes_while_old_focus_survives`
  (the fixed-scope focus-refresh obstruction).

Main declarations preserved from the earlier-manuscript development:

- `GenLimit.PatientMachine.patientScope_lowerDensity_half` (Theorem 3.14),
- `GenLimit.PartialEnumeration.lemma_3_16_generation` (Lemma 3.16), and
- `GenLimit.PartialEnumeration.theorem_3_17` (Theorem 3.17; the intrinsic
  parameter-free form is `theorem_3_17_lowerDensity`).

Manuscript: *Dense Language Generation Made Simple: Deterministic,
Randomized, and Multi-Order Algorithms*, by Ziyi Cai, Shuangping Li,
Yiheng Shen, Kangning Wang, and Peng Zhang. The public version is
[arXiv:2608.01320v1](https://arxiv.org/abs/2608.01320v1).

Source version used for the recorded paper-to-Lean audit: the earlier
manuscript supplied for this formalization, with Definitions 3.1--3.6, Lemma
3.11, Fact 3.12, Lemma 3.13, Theorem 3.14, Example 3.15, Lemma 3.16, and
Theorem 3.17 numbered as below.

The public-v1 criticality and focus definitions now have a deliberately small
Lean layer. Definition 3.2 is not duplicated: it is exactly the existing #01
[`Critical`](../GenLimit/Paper01_LanguageGeneration/Critical.lean#L16), whose
descending-chain and eventual-target results are reused directly. The
kernel-checked three-language example shows that, with this definition, a
higher critical language can appear inside an unchanged scope while the old
focus remains consistent. Consequently the earlier-manuscript fixed-scope
stability invariant cannot be ported by replacing `RecursiveCritical` with
`Critical`.

The current Lean development therefore does **not** claim the public-v1
patient-scope density theorems. Its complete machine and charging chain still
use [`RecursiveCritical`](../GenLimit/Paper39_DenseGeneration/Critical.lean#L19),
which compares only with earlier recursively critical languages. Public v1
also renumbers manuscript Example 3.15, Lemma 3.16, and Theorem 3.17 as
Example 3.17, Lemma 3.18, and Theorem 3.19; those names are not applied to the
recursive-critical results.

Within the earlier manuscript, the current Lean development covers the
deterministic patient-scope and partial-enumeration results listed above. Its
randomized and multi-order developments are not included in this repository
version.

## Relation to prior work

Kleinberg and Wei first established the optimal lower-density guarantee under
partial enumeration in *Language Generation and Identification From Partial
Enumeration* (STOC 2026): if the enumerated subset has relative lower density
`α` in the target, density `α / 2` is achievable and optimal. #39 Dense Generation
gives a simpler patient-scope construction for the achievability guarantee;
the Kleinberg--Wei algorithm and the optimality upper bound are not formalized
here.

Audit record: Peng Zhang's completed human reviews, pending scope, historical
paths, and exact source hashes are recorded only in the
[authoritative human-audit ledger](../AuditRecords/Human/README.md).

The arXiv-v1 layer imports only #01's semantic criticality module, reusing
`Critical`, `critical_subset_of_le`, and `target_eventually_critical`. It does
not import the #01 selection or finite-query machines. The preserved
earlier-manuscript engine keeps its independent recursive definition and proof
chain.

## Dependency path

```text
Core ──> #01 Critical ──> Paper39 ArxivV1 focus/diagnostic
  |
  └──> GenLimit.Paper39_DenseGeneration.Critical / GenLimit.Paper39_DenseGeneration.Dynamics
  |                  |
  |  GenLimit.Paper39_DenseGeneration.Patient.Machine ──> invariants / validity / history
  |                                           |
  └─> GenLimit.Paper39_DenseGeneration.Abstract counting  Fact 3.12 / departures
                       \                   /
                        charging certificates
                                 |
                       target-density endgame
                                 |
               GenLimit.Paper39_DenseGeneration.Patient.Main
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

This counter correspondence applies to the preserved earlier-manuscript
machine. The public-v1 diagnostic uses the same zero-based convention but does
not claim a complete operational correspondence.

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

The counter/index translation was included in the human review. Its
authoritative outcome and boundary are recorded in the
[human-audit ledger](../AuditRecords/Human/README.md); this correspondence
table does not itself assign an audit level.

In Section 3.3, `E` is the set actually enumerated and `K` is the true target,
with `E ⊆ K`. The transformed `closure` filters the nonempty finite
intersections that are infinite while preserving their raw binary-code order.
Its Lean indices are zero-based positions in that filtered order, not the raw
binary codes themselves.

## Paper correspondence

| Paper item | Lean declaration | Module | Ownership |
|---|---|---|---|
| Consistency, arXiv-v1 Definition 3.1 | `Consistent` | `GenLimit.Core.Basic` | Core |
| Criticality, arXiv-v1 Definition 3.2 | `Critical` | `GenLimit.Paper01_LanguageGeneration.Critical` | #01, reused by #39 |
| Descending chain, arXiv-v1 Remark 3.3 | `critical_subset_of_le` | `GenLimit.Paper01_LanguageGeneration.Critical` | #01, reused by #39 |
| Target eventually critical, arXiv-v1 Lemma 3.4 | `target_eventually_critical` | `GenLimit.Paper01_LanguageGeneration.Critical` | #01, reused by #39 |
| Scoped focus, arXiv-v1 Definitions 3.5--3.6 | `Paper39ArxivV1.IsFocus` | `GenLimit.Paper39_DenseGeneration.ArxivV1` | #39 |
| ArXiv-v1 focus contained in a critical target | `Paper39ArxivV1.focus_subset_of_critical` | `GenLimit.Paper39_DenseGeneration.ArxivV1` | #39, reusing #01 |
| Fixed-scope focus-refresh obstruction | `Paper39ArxivV1.FocusRefreshExample.focus_changes_while_old_focus_survives`, `criticality_not_fixed_below_surviving_focus` | `GenLimit.Paper39_DenseGeneration.ArxivV1` | #39 diagnostic |
| Earlier-manuscript recursive criticality | `RecursiveCritical` | `GenLimit.Paper39_DenseGeneration.Critical` | #39 legacy/corrected variant |
| Earlier-manuscript descending chain | `recursiveCritical_subset_of_le` | `GenLimit.Paper39_DenseGeneration.Critical` | #39 legacy/corrected variant |
| Earlier-manuscript eventual target | `target_eventually_recursiveCritical` | `GenLimit.Paper39_DenseGeneration.Critical` | #39 legacy/corrected variant |
| Earlier-manuscript scoped focus | `IsFocus` | `GenLimit.Paper39_DenseGeneration.Critical` | #39 legacy/corrected variant |
| Earlier-manuscript focus contained in target | `focus_subset_target` | `GenLimit.Paper39_DenseGeneration.Critical` | #39 legacy/corrected variant |
| Earlier-manuscript patient-scope algorithm | `PatientMachine.run`, `PatientMachine.output` | `GenLimit.Paper39_DenseGeneration.Patient.Machine` | #39 legacy/corrected variant |
| Earlier-manuscript run invariants | `run_focus_isFocus`, `run_tau_eq_focus_test`, `run_used_eq_outputsBefore` | `GenLimit.Paper39_DenseGeneration.Patient.MachineInvariant` | #39 legacy/corrected variant |
| Earlier-manuscript scope progress | `target_eventually_in_scope` | `GenLimit.Paper39_DenseGeneration.Patient.Validity` | #39 legacy/corrected variant |
| Earlier-manuscript Lemma 3.11 | `patient_validity` | `GenLimit.Paper39_DenseGeneration.Patient.Validity` | #39 legacy/corrected variant |
| First-announcer partition | `range_subset_first_announcements`, `ownership_disjoint` | `GenLimit.Paper39_DenseGeneration.Abstract.Announcements`, `GenLimit.Paper39_DenseGeneration.Abstract.GameTrace` | General/#39 |
| Trace validity | `eventual_validity_and_novelty` | `GenLimit.Paper39_DenseGeneration.Abstract.GameTrace` | #39 |
| Fact 3.12 local comparison | `previous_output_lt_of_not_lateSwitch` | `GenLimit.Paper39_DenseGeneration.Patient.Fact312` | #39 |
| Fact 3.12 injection | `predecessorPartner_injective_machine` | `GenLimit.Paper39_DenseGeneration.Patient.Fact312` | #39 |
| Prior patient departure | `exists_upwardDeparture_of_critical_lt_focus` | `GenLimit.Paper39_DenseGeneration.Patient.Departure` | #39 |
| Canonical label injection | `certifiedLanding_label_injective` | `GenLimit.Paper39_DenseGeneration.Patient.Departure` | #39 |
| Exponential charging bound | `charging_pow_le_prefix` | `GenLimit.Paper39_DenseGeneration.Abstract.Charging` | General/#39 |
| Concrete Lemma 3.13 data | `settledChargingCertificate` | `GenLimit.Paper39_DenseGeneration.Patient.Charging` | #39 |
| Target-relative Lemma 3.13 | `prefixCount_le_log2_targetCount` | `GenLimit.Paper39_DenseGeneration.Abstract.TargetSwitchCharging` | General/#39 |
| Shared stable-target charging | `PatientMachine.StableTargetRun.chargingCertificate` | `GenLimit.Paper39_DenseGeneration.Patient.StableTargetCharging` | #39 |
| Prefix inequality in Theorem 3.14 | `attackerCount_le_log2` | `GenLimit.Paper39_DenseGeneration.Abstract.PatientScope` | #39 |
| `log₂(n)/n → 0` | `tendsto_natLog2_div` | `GenLimit.Paper39_DenseGeneration.Abstract.Density` | General/#39 |
| Target-relative lower-density metric | `relativeLowerDensity` | `GenLimit.Paper39_DenseGeneration.Abstract.TargetDensity` | General/#39 |
| Sparse-target lower-density endgame | `lowerDensity_half_of_target_counting` | `GenLimit.Paper39_DenseGeneration.Abstract.TargetDensity` | General/#39 |
| Abstract arbitrary-target assembly | `theorem_3_14_target` | `GenLimit.Paper39_DenseGeneration.Abstract.TargetMain` | #39 |
| Earlier-manuscript operational Theorem 3.14 | `patientScope_lowerDensity_half` | `GenLimit.Paper39_DenseGeneration.Patient.Main` | #39 legacy/corrected variant |
| Example 3.15 (explicit increasing multiples-of-four order) | `Counterexample.presents_enumeratedLanguage`, `Counterexample.output_eq_odd`, `Counterexample.output_not_mem_trueLanguage` | `GenLimit.Paper39_DenseGeneration.Partial.Counterexample` | #39 |
| Partial-presentation consistency | `candidate_eventually_consistent_iff_presented_subset` | `GenLimit.Core.PartialPresentation` | Core |
| Finite-intersection family | `closure`, `closureCode` | `GenLimit.Paper39_DenseGeneration.Partial.Closure` | #39 |
| Transformed run stays on-model | `closure_onModel` | `GenLimit.Paper39_DenseGeneration.Partial.Critical` | #39 |
| Stable critical target subset | `exists_eventually_critical_subset_target` | `GenLimit.Paper39_DenseGeneration.Partial.Critical` | #39 |
| Lemma 3.16 | `lemma_3_16_generation` | `GenLimit.Paper39_DenseGeneration.Partial.Validity` | #39 |
| Partial-enumeration prefix inequality | `enumeratedCount_le_two_mul_defender` | `GenLimit.Paper39_DenseGeneration.Abstract.PartialEnumeration` | General/#39 |
| Abstract Theorem 3.17 | `PartialEnumerationCertificate.theorem_3_17` | `GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity` | #39 |
| Operational certificate assembly | `stableTargetRun_nonempty`, `StableTargetRun.partialCertificate` | `GenLimit.Paper39_DenseGeneration.Partial.Certificate` | #39 |
| Operational Theorem 3.17 | `theorem_3_17`, `theorem_3_17_lowerDensity` | `GenLimit.Paper39_DenseGeneration.Partial.Main` | #39 |

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

The arXiv-v1 layer follows public Definition 3.2 semantically: direct
criticality uses exact inclusion between infinite languages. The complete
patient machine instead follows the earlier manuscript's recursive
criticality, again using exact whole-language inclusion and classical choice.
Neither layer claims a finite-membership-query implementation.
The Section 3.3 filter must additionally decide whether each finite
intersection is infinite. Although membership in an already selected
intersection is a finite conjunction of original oracle queries, this
filtering and reindexing step is itself classical and noncomputable.
