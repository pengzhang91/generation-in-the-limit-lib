# #39 Dense Generation map

Pinned source: *Dense Language Generation Made Simple: Deterministic,
Randomized, and Multi-Order Algorithms*, Ziyi Cai, Shuangping Li, Yiheng Shen,
Kangning Wang, and Peng Zhang,
[arXiv:2608.01320v2](https://arxiv.org/abs/2608.01320v2).
The source is the supplied `papers/P39_DenseGeneration_v2.pdf` (60 PDF pages),
SHA-256 `8dfc7ada39b62bb79d380331deeb4377035ec35d26b8334c2c6c6a91cb711b08`.
The PDF metadata identifies v2; a revision date is not printed in the supplied
PDF metadata, so none is inferred from the local filename or receipt date.
Source comparison and migration: 5 November 2026. Page references below use
printed page numbers, which are two less than PDF page numbers.

Lean umbrella: `GenLimit.Paper39_DenseGeneration`.
Public entry point: [`Results/Overview.lean`](../GenLimit/Paper39_DenseGeneration/Results/Overview.lean),
namespace `GenLimit.DenseGeneration.Results`.
Canonical declarations retain `GenLimit.PatientMachine`,
`GenLimit.PatientScope`, and `GenLimit.PartialEnumeration`.

**Coverage: partial paper, complete deterministic achievability and
partial-enumeration guarantees.** This is semantic mathematics on indexed
families of infinite subsets of `ℕ`. It includes Lemma 3.12, Fact 3.13,
Lemma 3.14, the achievability clause of Theorem 3.15, and Example B.1,
Lemma B.2, and Theorem B.3. Randomized and multi-order results, the separate
optimality upper bound, and the additional remarks listed below are open.
No executable algorithm or complexity guarantee is claimed.

## Active interface

The development follows arXiv:2608.01320v2 throughout. Canonical theorem
names use Theorem 3.15 and Appendix B's Lemma B.2/Theorem B.3 numbering.
The predecessor-pairing infrastructure lives in `Abstract/Pairing.lean` and
`Patient/Pairing.lean`; `Patient/Fact313.lean` exposes both clauses of Fact 3.13.
The overview states only Theorems 3.15 and B.3 as explicit theorem wrappers.
Supporting results and the full generation/density variants remain in their
canonical proof modules; the paper umbrella imports the complete development.

Definition 3.2 uses recursive criticality. Remark 3.7 distinguishes it from
the KM/all-consistent definition. Example B.1 uses the specified increasing
multiples-of-four enumeration. Peng Zhang reported a Level 1 human audit of
the two Overview statements and their defining interfaces on 7 November 2026,
at checkpoint `3f0aa55`. Theorem 3.15 is reviewed for achievability only.
Construction/proof correspondence and other result statements are outside
this review; historical audit scopes remain `needs-review`. See the
[human-audit ledger](../AuditRecords/Human/README.md#39-dense-generation-arxiv-v2-theorems-315-and-b3-level-1).

## Public claim coverage

The two main theorems are under `GenLimit.DenseGeneration.Results`;
supporting results are listed by their canonical declarations. `Full` refers
to the stated semantic claim. It does not imply an executable implementation
or a human audit beyond the two statements recorded above.

| Paper item | Lean declaration / file | Coverage | Qualification |
|---|---|---|---|
| Definition 2.2 | `PatientScope.relativeLowerDensity`, `Abstract/TargetDensity.lean` | Full | Core ordered lower density in increasing target order; proved equal to the ambient-prefix liminf for target subsets, including sparse targets. |
| Definitions 3.1, 3.2, 3.5, 3.6 | `Consistent`, `RecursiveCritical`, `IsFocus`, `PatientMachine.State.scope` | Full | Indexed family and zero-based language indices; positive scope on runs. |
| Remark 3.3 | `GenLimit.recursiveCritical_subset_of_le`, `GenLimit.lost_recursiveCritical_suffix`, `GenLimit.new_recursiveCritical_above_survivor` | Full | Includes disappearing suffix and newly critical indices above all survivors; proved for any later time. |
| Lemma 3.4 | `GenLimit.target_eventually_recursiveCritical` | Full | Every exactly presented target is eventually critical. |
| Remark 3.7 | `GenLimit.fixed_scope_one_step` | Partial | Full recursive-criticality fixed-scope stability clause; no standalone witness for the KM contrast is added. |
| Definition 3.10 | `PatientMachine.SwitchRound`, `Patient/Pairing.lean` | Full | The arriving value is outside the preceding focus. |
| Patient-scope/backtracking pseudocode, pp. 13--14 | `PatientMachine.run`, `PatientMachine.output` | Full | Semantic/classical machine; total fallback off the paper's on-model inputs. |
| Lemma 3.12 | `GenLimit.PatientMachine.patient_validity`, `GenLimit.PatientMachine.patientScope_generation_and_lowerDensity` | Full | Validity and novelty for the same run; the latter also includes density. |
| Fact 3.13 | `GenLimit.PatientMachine.fact_3_13`, `Patient/Fact313.lean` | Full | Both preceding-focus membership and strict previous-output comparison, at a fresh adversary occurrence in a positive round. Strictness strengthens the printed weak inequality. |
| Lemma 3.14 | `GenLimit.PatientMachine.lemma_3_14` | Full | Operational settled switch losses bounded by `Nat.log2` of target-prefix count; finite initial exceptions excluded. |
| Theorem 3.15: achievability | `GenLimit.DenseGeneration.Results.theorem_3_15`, `GenLimit.PatientMachine.patientScope_generation_and_lowerDensity` | Full | At least `1/2` for arbitrary targets and presentations. |
| Theorem 3.15: optimality / Section 2 upper bound | No declaration | Open | The separate adversarial upper bound is not formalized; the full theorem card is partial. |
| Remark 3.16 | No declaration | Open | The `q`-output machine and `q/(q+1)` bound are not formalized. |
| Remark 3.17 | No declaration | Open | Infinitely-often accuracy of the focus is not proved. |
| Example B.1 | `GenLimit.PartialEnumeration.Counterexample.example_B_1`, `Partial/ExampleB1.lean` | Full | Exact increasing enumeration, odd outputs, failure of eventual validity, and zero target-relative density. |
| Lemma B.2 | `GenLimit.PartialEnumeration.lemma_B_2_generation` | Full | Infinite enumerated subset need not be a member of the original or transformed family. |
| Theorem B.3 | `GenLimit.DenseGeneration.Results.theorem_B_3`, `GenLimit.PartialEnumeration.theorem_B_3_lowerDensity`, `GenLimit.PartialEnumeration.theorem_B_3_with_generation` | Full | Bound `α/2` and an intrinsic parameter-free form, using the same transformed run. |
| Theorems 4.2, 4.3, 4.4 | No declaration | Open | Randomized generator, expectations, oblivious adversary, and bounds are not formalized. |
| Theorems 5.2, 5.3, 5.9 | No declaration | Open | Simultaneous multi-order algorithms and bounds are not formalized. |
| Auxiliary Theorems 2.3--2.5; Appendices A, C--E | No declaration | Open | Online matching, low-crossing partitions, and randomized/multi-order proof infrastructure are outside this update. |
| KM recap Fact 3.8, Example 3.9, Fact 3.11 | No v2-specific declaration | Open | The v2 recursive-criticality recap algorithm and its zero-density example are not separately formalized; the P01 machine is a different interface. |

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

The #39 Dense Generation development depends on `GenLimit.Core` and imports neither
the `GenLimit.Paper01_LanguageGeneration.Semantic` module nor the
`GenLimit.Paper01_LanguageGeneration.FiniteQuery` module. Its
recursive criticality is defined independently, and Lemma 3.4 is proved
directly from shared consistency stabilization.

## Dependency path

```text
Core ──> GenLimit.Paper39_DenseGeneration.Critical / GenLimit.Paper39_DenseGeneration.Dynamics
  |                  |
  |  GenLimit.Paper39_DenseGeneration.Patient.Machine ──> invariants / validity / history
  |                                           |
  └─> GenLimit.Paper39_DenseGeneration.Abstract counting  Fact 3.13 / departures
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

`relativeLowerDensity A K hK` is a thin wrapper around
`KleinbergWei.OrderedLanguage.lowerDensity`, using `OrderedLanguage.increasing`
from `Core/NaturalDensity.lean`. The explicit proof `hK : K.Infinite` supplies
the infinite target required by Core's ordering; each oracle family already
provides it. The abstract certificate density wrappers likewise take a target
infinitude proof; the operational density functions keep their existing
parameters. `relativeLowerDensity_eq_liminf` proves equality with the original
ambient-prefix ratio when `A ⊆ K`, as in every P39 density theorem. Thus the
counting arguments retain their ambient-prefix form while both main theorems
use Core's density definition. This correspondence requires the increasing
target order and does not assert invariance under arbitrary reorderings.

### Patient-scope counter correspondence

This correspondence applies to the v2 pseudocode on printed pp. 13--14.
The historical human review mentioned below used the earlier manuscript.

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

In Appendix B, `E` is the set actually enumerated and `K` is the true target,
with `E ⊆ K`. The transformed `closure` filters the nonempty finite
intersections that are infinite while preserving their raw binary-code order.
Its Lean indices are zero-based positions in that filtered order, not the raw
binary codes themselves.

## Canonical proof inventory

| Paper item | Lean declaration | Module | Ownership |
|---|---|---|---|
| Consistency, Definition 3.1 | `Consistent` | `GenLimit.Core.Basic` | Core |
| Recursive criticality, Definition 3.2 | `RecursiveCritical` | `GenLimit.Paper39_DenseGeneration.Critical` | #39 |
| Descending chain, Remark 3.3 | `recursiveCritical_subset_of_le` | `GenLimit.Paper39_DenseGeneration.Critical` | #39 |
| Target eventually critical, Lemma 3.4 | `target_eventually_recursiveCritical` | `GenLimit.Paper39_DenseGeneration.Critical` | #39, using Core stability |
| Scoped focus, Definitions 3.5--3.6 | `IsFocus` | `GenLimit.Paper39_DenseGeneration.Critical` | #39 |
| Focus contained in target | `focus_subset_target` | `GenLimit.Paper39_DenseGeneration.Critical` | #39 |
| Patient-scope algorithm | `PatientMachine.run`, `PatientMachine.output` | `GenLimit.Paper39_DenseGeneration.Patient.Machine` | #39 |
| Run invariants | `run_focus_isFocus`, `run_tau_eq_focus_test`, `run_used_eq_outputsBefore` | `GenLimit.Paper39_DenseGeneration.Patient.MachineInvariant` | #39 |
| Scope progress | `target_eventually_in_scope` | `GenLimit.Paper39_DenseGeneration.Patient.Validity` | #39 |
| Lemma 3.12 | `patient_validity` | `GenLimit.Paper39_DenseGeneration.Patient.Validity` | #39 |
| First-announcer partition | `range_subset_first_announcements`, `ownership_disjoint` | `GenLimit.Support.TurnTaking.Announcements`, `GenLimit.Paper39_DenseGeneration.Abstract.GameTrace` | Support/#39 |
| Trace validity | `eventual_validity_and_novelty` | `GenLimit.Paper39_DenseGeneration.Abstract.GameTrace` | #39 |
| Fact 3.13 local comparison | `previous_output_lt_of_not_lateSwitch` | `GenLimit.Paper39_DenseGeneration.Patient.Pairing` | #39 |
| Fact 3.13 injection | `predecessorPartner_injective_machine` | `GenLimit.Paper39_DenseGeneration.Patient.Pairing` | #39 |
| Prior patient departure | `exists_upwardDeparture_of_critical_lt_focus` | `GenLimit.Paper39_DenseGeneration.Patient.Departure` | #39 |
| Canonical label injection | `certifiedLanding_label_injective` | `GenLimit.Paper39_DenseGeneration.Patient.Departure` | #39 |
| Exponential charging bound | `charging_pow_le_prefix` | `GenLimit.Paper39_DenseGeneration.Abstract.Charging` | General/#39 |
| Concrete Lemma 3.14 data | `settledChargingCertificate` | `GenLimit.Paper39_DenseGeneration.Patient.Charging` | #39 |
| Target-relative Lemma 3.14 | `prefixCount_le_log2_targetCount` | `GenLimit.Paper39_DenseGeneration.Abstract.TargetSwitchCharging` | General/#39 |
| Shared stable-target charging | `PatientMachine.StableTargetRun.chargingCertificate` | `GenLimit.Paper39_DenseGeneration.Patient.StableTargetCharging` | #39 |
| Prefix inequality in Theorem 3.15 | `attackerCount_le_log2` | `GenLimit.Paper39_DenseGeneration.Abstract.PatientScope` | #39 |
| `log₂(n)/n → 0` | `tendsto_natLog2_div` | `GenLimit.Support.Asymptotics.NatLog` | Support |
| Increasing target order and ambient-prefix equality | `OrderedLanguage.increasing`, `OrderedLanguage.increasing_lowerDensity_eq_liminf` | `GenLimit.Core.NaturalDensity` | Core |
| Target-relative lower-density wrapper | `relativeLowerDensity`, `relativeLowerDensity_eq_liminf` | `GenLimit.Paper39_DenseGeneration.Abstract.TargetDensity` | #39, using Core |
| Sparse-target lower-density endgame | `lowerDensity_half_of_target_counting` | `GenLimit.Paper39_DenseGeneration.Abstract.TargetDensity` | General/#39 |
| Abstract arbitrary-target assembly | `theorem_3_15_target` | `GenLimit.Paper39_DenseGeneration.Abstract.TargetMain` | #39 |
| Operational Theorem 3.15 | `patientScope_lowerDensity_half` | `GenLimit.Paper39_DenseGeneration.Patient.Main` | #39 |
| Example B.1 (explicit increasing multiples-of-four order) | `Counterexample.presents_enumeratedLanguage`, `Counterexample.output_eq_odd`, `Counterexample.output_not_mem_trueLanguage` | `GenLimit.Paper39_DenseGeneration.Partial.Counterexample` | #39 |
| Partial-presentation consistency | `candidate_eventually_consistent_iff_presented_subset` | `GenLimit.Core.PartialPresentation` | Core |
| Finite-intersection family | `closure`, `closureCode` | `GenLimit.Paper39_DenseGeneration.Partial.Closure` | #39 |
| Transformed run stays on-model | `closure_onModel` | `GenLimit.Paper39_DenseGeneration.Partial.Critical` | #39 |
| Stable critical target subset | `exists_eventually_critical_subset_target` | `GenLimit.Paper39_DenseGeneration.Partial.Critical` | #39 |
| Lemma B.2 | `lemma_B_2_generation` | `GenLimit.Paper39_DenseGeneration.Partial.Validity` | #39 |
| Partial-enumeration prefix inequality | `enumeratedCount_le_two_mul_defender` | `GenLimit.Paper39_DenseGeneration.Abstract.PartialEnumeration` | General/#39 |
| Abstract Theorem B.3 | `PartialEnumerationCertificate.theorem_B_3` | `GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity` | #39 |
| Operational certificate assembly | `stableTargetRun_nonempty`, `StableTargetRun.partialCertificate` | `GenLimit.Paper39_DenseGeneration.Partial.Certificate` | #39 |
| Operational Theorem B.3 | `theorem_B_3`, `theorem_B_3_lowerDensity` | `GenLimit.Paper39_DenseGeneration.Partial.Main` | #39 |

The exact-presentation declaration is uniform in the family, target index,
and target presentation. The Appendix B declarations are uniform in the
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
The Appendix B filter must additionally decide whether each finite
intersection is infinite. Although membership in an already selected
intersection is a finite conjunction of original oracle queries, this
filtering and reindexing step is itself classical and noncomputable.


## Integration and verification boundary

The existing umbrella remains imported by `GenLimit.lean`; the current
facade, both READMEs, `CITATION.bib`, and `registry/papers/P39.json` are pinned
to v2. Earlier-manuscript and v1 registry claims remain separately addressable.
The v2 inventory is custom: 21 selected claims, with the weaker randomized
and multi-order recap theorems and other auxiliary results explicitly excluded
from standalone cards. Exclusion from that inventory does not imply coverage.

Shared mathematics remains in Core and Support. `Core.NaturalDensity` adds
the increasing target ordering and its proved ambient-prefix correspondence,
so P39 reuses the ordered-density definition shared by the Kleinberg--Wei
developments. This definition-level correspondence is recorded in the local
cross-paper equivalence register; it does not equate the papers' main theorems.
The P01-to-P39 criticality implication and P00-to-P39 generation/identification
separation are preserved. Executability and complexity checklist items are
inapplicable to the declared semantic scope, not silently satisfied.

The maintained proof uses the same classical axiom allowance as the rest of
the library (`propext`, `Classical.choice`, `Quot.sound`), with no paper-local
axioms or proof holes. Historical audit fingerprints retain their original
baselines. The separate Level 1 review of Theorems 3.15 and B.3 is recorded
above and does not renew those historical scopes.


Verification before the Core-density refactor (7 November 2026):

- Targeted builds passed for `Patient.Charging`, `Results.Overview`, and the
  P39 umbrella. These builds produced no warnings.
- The final repository-wide incremental `lake build` passed (3,872 jobs).
- Registry validation passed for 30 papers, 430 claims, and 580 linked
  declarations. The generated Lean registry audit passed with the supporting
  results linked directly to their canonical proof modules.
- The overview contains exactly two explicit theorem statements and no
  `alias` commands. Supporting results remain available through the umbrella;
  the ambient-prefix form of Lemma 3.14 now lives in `Patient.Charging`.
- The declaration index was regenerated with 11,228 declarations. Fourteen
  duplicate overview declarations were removed and Lemma 3.14 was relocated.
  Every retained declaration type, including both main theorem statements,
  and the relocated lemma's type match the pre-edit export exactly.
- The active P39 source scan found no unfinished proofs or paper-local axioms,
  and the source and documentation have no stale references to the removed
  overview declarations.
- Warnings are separate from failures: the full build replayed seven existing
  linter warnings in P17/P31, with none in P39. The preceding edition-cleanup
  verification passed the curated axiom audit and fingerprint checker, with
  the same six existing `needs-review` notices and pre-existing definition-value
  differences. Those checks were not repeated for this overview change;
  historical fingerprint baselines and audit-only anchor names are unchanged.

Verification of the Core-density refactor (7 November 2026):

- Targeted builds passed for `Core.NaturalDensity`, the P39 density modules,
  the P39 umbrella, and both P39 bridges, with no warnings.
- The final repository-wide incremental `lake build` passed (3,873 jobs).
  It replayed the same seven existing P17/P31 linter warnings; Core and P39
  produced no new warnings or failures.
- Registry validation passed for 30 papers, 430 claims, and 580 linked Lean
  declarations. The declaration index was regenerated and validated with
  11,234 declarations, including the new Core definitions and bridge theorems.
- The generated Lean registry audit and all 722 curated logical-dependency
  checks passed.
- The new Core module and P39 sources contain no proof holes or paper-local
  axioms, and the whitespace check passed.
- This refactor adds definition reuse without adding paper claims. The source
  edition, citation, README coverage, and curated claim metadata are unchanged;
  existing human-audit snapshots remain historical baselines.
