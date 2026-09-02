# Paper 13: Pareto-optimal Non-uniform Language Generation

This map records the correspondence between Moses Charikar and Chirag
Pabbaraju, *Pareto-optimal Non-uniform Language Generation*, and the Lean
development under `GenLimit.Paper13_ParetoOptimalNonuniformGeneration`.

## Source edition and scope

- Formalization source: arXiv:2510.02795v1, submitted 3 October 2025.
- Lean umbrella: `GenLimit.Paper13_ParetoOptimalNonuniformGeneration`.
- Main-results entry point:
  [`Results/Overview.lean`](../GenLimit/Paper13_ParetoOptimalNonuniformGeneration/Results/Overview.lean).
- Status: **partial**.  The deterministic standard-generation path through
  Theorems 1, 4, and 5 is formalized.  The totalized noisy path supplies
  concrete Theorems 6 and 8.  The representative construction of Theorem 7
  is absent, so Theorem 9 currently has only its conditional scheduler
  endgame.
- The source presents its collection as the indexed sequence
  `(L₁, L₂, ...)`, explicitly allowing duplicate languages.  Lean uses
  `F : ℕ → Set α`, which faithfully preserves that indexed-family interface.
- The source allows repeated observations but measures time by the number of
  distinct observed strings.  The current main algorithm theorems work at a
  distinct-history boundary, representing a sample of size `t` by an
  injective map `Fin t → α`.  A wrapper from arbitrary repeated histories to
  that interface is not included.
- The development is classical semantic mathematics.  It does not claim an
  extracted implementation, decidable language access, or a running-time
  bound.
- There is an important edition distinction.  The published ALT 2026 version
  ([PMLR 313](https://proceedings.mlr.press/v313/charikar26a.html)) adds a
  computational-cost discussion after Procedure 1 that is absent from arXiv
  v1.  It assumes two kinds of access: an oracle deciding whether the
  intersection of a given finite family of languages is finite, and a
  membership oracle deciding `x ∈ Lᵢ`.  When processing `Lᵢ`, the paper reports
  roughly `2^i` calls to the first oracle, followed by a forward pass using
  polynomially many calls to the two oracles.
- Those oracle costs are separate from the theorems' generation time, which is
  measured by the number of distinct observed strings.  The current Lean
  development proves the semantic generation-time and Pareto conclusions, but
  does not define either oracle interface, construct a finite-query oracle
  program, or verify the published query-complexity bounds.  Thus the existing
  `Full at the distinct-history semantic boundary` labels do not claim full
  computational coverage of the later PMLR edition.

## Main-result correspondence

| Paper item | Lean declaration / file | Coverage | Qualification |
|---|---|---|---|
| Definition 3 and Pareto comparison | `ParetoOptimal`, `EarlierTradeoff`, and `PrefixParetoOptimal` in [`Order.lean`](../GenLimit/Paper13_ParetoOptimalNonuniformGeneration/Order.lean) and [`GlobalInvariant.lean`](../GenLimit/Paper13_ParetoOptimalNonuniformGeneration/GlobalInvariant.lean) | Full semantic interface | Time vectors are natural-number thresholds indexed by the source's ordered family. |
| Procedure 1 | `canonicalProcedureStage`, `canonicalComplexity`, and the insertion-order invariants in [`GlobalInvariant.lean`](../GenLimit/Paper13_ParetoOptimalNonuniformGeneration/GlobalInvariant.lean) and [`ArbitraryScheduler.lean`](../GenLimit/Paper13_ParetoOptimalNonuniformGeneration/ArbitraryScheduler.lean) | Full with an explicit source qualification | Lean totalizes the zero-score branch and retains the exact max-score fact used downstream without asserting that an empty witness contains the target. |
| Claim 3.1 | `ProcedureStage.earlierPrefixTradeoff`, `ProcedureStage.prefixParetoOptimal`, and `canonicalProcedureStage_prefixParetoOptimal` in [`GlobalInvariant.lean`](../GenLimit/Paper13_ParetoOptimalNonuniformGeneration/GlobalInvariant.lean) | Full | The finite-stage adversary construction proves the paper's earlier-coordinate tradeoff and hence prefix Pareto optimality. |
| Claim 3.2 | `procedureStep_maxScoreBound`, `OrderMaxScoreBounds`, and `target_selected_in_greedyListScan` in [`GlobalInvariant.lean`](../GenLimit/Paper13_ParetoOptimalNonuniformGeneration/GlobalInvariant.lean) | Full for the property used by the algorithm | `literal_claim_3_2_empty_witness_obstruction` and `literal_claim_3_2_counterexample` show that the printed witness formulation fails in the no-candidate zero-score branch.  The corrected max-value invariant suffices for Theorems 1 and 4. |
| Overview Theorem 1 | `Results.theorem_1` in [`Results/Overview.lean`](../GenLimit/Paper13_ParetoOptimalNonuniformGeneration/Results/Overview.lean), delegating to `overview_theorem_1_semantic` in [`GlobalInvariant.lean`](../GenLimit/Paper13_ParetoOptimalNonuniformGeneration/GlobalInvariant.lean) | Full at the distinct-history semantic boundary | For every requested finite prefix, one globally valid generator realizes a time vector matching the canonical vector on that prefix and Pareto-optimal there. |
| Theorem 4 | `Results.theorem_4` in [`Results/Overview.lean`](../GenLimit/Paper13_ParetoOptimalNonuniformGeneration/Results/Overview.lean), delegating to `theorem_4_arbitrary_scheduler` in [`ArbitraryScheduler.lean`](../GenLimit/Paper13_ParetoOptimalNonuniformGeneration/ArbitraryScheduler.lean) | Full at the distinct-history semantic boundary | The scheduler is an explicit monotone unbounded `ℕ → ℕ`; its generalized inverse gives the source's `g(i)`, and the realized vector is the displayed maximum. |
| Theorem 5 | `Results.theorem_5` in [`Results/Overview.lean`](../GenLimit/Paper13_ParetoOptimalNonuniformGeneration/Results/Overview.lean), delegating to `theorem_5_exact_pareto` in [`ExactPareto.lean`](../GenLimit/Paper13_ParetoOptimalNonuniformGeneration/ExactPareto.lean) | Full at the same semantic boundary | `FiniteSublevels (canonicalComplexity F)` is the source condition that every bounded canonical-complexity sublevel contains only finitely many indices.  The constructed scheduler realizes the complete Pareto-optimal vector. |
| Proposition 3.3 | `proposition_3_3_full` and `proposition_3_3_integer_full` in [`CoSingletonFrontier.lean`](../GenLimit/Paper13_ParetoOptimalNonuniformGeneration/CoSingletonFrontier.lean) | Full | Lean characterizes the entire realizable frontier of the co-singleton family and transports the result to the paper's integer universe. |
| Proposition 3.4 | `proposition_3_4_no_pareto_frontier` and `proposition_3_4_uniform_generation` in [`ThresholdFrontier.lean`](../GenLimit/Paper13_ParetoOptimalNonuniformGeneration/ThresholdFrontier.lean) | Full after repairing one proof step | `printed_proposition_3_4_diagonal_step_false` refutes the printed claim that every point below the threshold lies outside the language; `corrected_proposition_3_4_diagonal_step` supplies the needed outside-core version. |
| Procedure 2 and Claims B.1--B.3 | `canonicalNoisyProcedureStage`, `canonicalNoisyWitnessCertificate`, `corrected_procedure_2_claim_B_2`, and the persistence/target-selection theorems in [`NoisyWitness.lean`](../GenLimit/Paper13_ParetoOptimalNonuniformGeneration/NoisyWitness.lean) and [`NoisyProcedure.lean`](../GenLimit/Paper13_ParetoOptimalNonuniformGeneration/NoisyProcedure.lean) | Full for the corrected deterministic semantic interface | `procedure_2_first_step_has_no_candidate` proves that the printed first Step-A optimization can have no feasible witness.  Lean uses a documented empty-sample/zero-score fallback and proves all downstream argmax bounds. |
| Theorem 6 | `Results.theorem_6` in [`Results/Overview.lean`](../GenLimit/Paper13_ParetoOptimalNonuniformGeneration/Results/Overview.lean), delegating to `theorem_6_corrected_totalized` in [`NoisyProcedure.lean`](../GenLimit/Paper13_ParetoOptimalNonuniformGeneration/NoisyProcedure.lean) | Full for the corrected injective-history noisy interface | Noise levels and language indices are encoded by the source's diagonal coordinates.  The generator realizes the displayed maximum of scheduler-entry time and corrected noisy canonical complexity. |
| Theorem 7 | No concrete declaration | None | The representative distribution, finite partition, group-scarcity semantics, Procedure 3, and the proof of the displayed representative time vector remain to be formalized. |
| Theorem 8 | `Results.theorem_8` in [`Results/Overview.lean`](../GenLimit/Paper13_ParetoOptimalNonuniformGeneration/Results/Overview.lean), delegating to `theorem_8_corrected_deterministic_endgame` in [`NoisyProcedure.lean`](../GenLimit/Paper13_ParetoOptimalNonuniformGeneration/NoisyProcedure.lean) | Full for the corrected deterministic noisy interface | The concrete Procedure-2 certificate and finite-sublevel scheduler yield the canonical noisy Pareto vector. |
| Theorem 9 | `Results.theorem_9_representative_endgame` in [`Results/Overview.lean`](../GenLimit/Paper13_ParetoOptimalNonuniformGeneration/Results/Overview.lean), delegating to `theorem_9_representative_exactPareto_endgame` in [`VariantExactPareto.lean`](../GenLimit/Paper13_ParetoOptimalNonuniformGeneration/VariantExactPareto.lean) | Partial / conditional | Lean proves the common finite-sublevel scheduler implication from a `VariantSchedulerCertificate`.  No representative certificate exists yet because Theorem 7 and Claim C.2 are not formalized. |

## Source diagnostics and repairs

Two proof defects are kept visible rather than silently absorbed:

1. In Procedure 1, the source assigns an empty witness and score zero when no
   finite-intersection candidate exists.  The literal Claim 3.2 witness
   statement can then demand that this empty witness contain the target.
   Lean proves a counterexample and replaces only that proof obligation with
   the exact max-score bound used by the generator.
2. In Procedure 2, the first diagonal coordinate has no feasible Step-A
   candidate because its sole language is infinite.  Lean totalizes the step
   with an empty sample/witness and zero complexity, then proves that the
   corrected stage maintains Claims B.2 and B.3 and supports Theorems 6 and 8.

The Proposition 3.4 proof also contains a false pointwise threshold inference.
Lean records a small counterexample and proves the corrected outside-core
statement needed by the full Pareto-impossibility argument.

## Shared infrastructure and reuse

- [`Core/GenericGeneration.lean`](../GenLimit/Core/GenericGeneration.lean)
  supplies the common finite-history generator and sample lemmas; P13's
  `HistoryGenerator` is a compatibility abbreviation.
- [`Paper06_NoisyExamples/UniformIndependent.lean`](../GenLimit/Paper06_NoisyExamples/UniformIndependent.lean)
  retains compatibility wrappers for generic sequence-sample lemmas now owned
  by Core, and P13 reuses P06's finite negative-part operation for noisy
  exceptions.
- [`Support/Fresh.lean`](../GenLimit/Support/Fresh.lean) supplies the common
  choice of a fresh point from an infinite set.
- Standard and noisy greedy scans share the P13-local predicate-parametric
  kernel `greedyListStepBy` / `greedyListScanBy`; their public procedure names
  remain compatibility abbreviations.
- Theorems 5, 8, and 9 use one finite-sublevel scheduler argument through
  `VariantExactPareto.lean`; the standard Theorem-5 API remains stable.

## Remaining roadmap

The next substantive step is the representative branch:

1. define the finite partition, empirical group profile, output distribution,
   group-scarcity predicate, and representative success semantics;
2. formalize Procedure 3 and Claim C.2;
3. prove the concrete scheduler-driven Theorem 7 time vector;
4. instantiate the existing Theorem-9 endgame with that concrete certificate;
5. optionally add a repeated-history adapter for the standard and noisy
   theorem surfaces.

All current P13 declarations are kernel-checked and contain no `sorry`,
`admit`, or paper-local axioms.  No human statement-correspondence audit has
yet been recorded.
