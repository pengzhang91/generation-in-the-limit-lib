# Paper 21: On Generation in Metric Spaces

Jiaxun Li, Vinod Raman, and Ambuj Tewari, *On Generation in Metric Spaces*,
[arXiv:2602.07710v1](https://arxiv.org/abs/2602.07710v1), submitted
2026-02-07.  The formalization is pinned to the v1 PDF with SHA-256
`5e5b068e4eeadedbec5c87913cf294f4f40f75ae87c12cb2c5a815ae94a90355`.

- Lean umbrella: `GenLimit.Paper21_GenerationInMetricSpaces`.
- Main-results facade:
  [`Results/Overview.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/Results/Overview.lean).
- Scope: deterministic semantic mathematics.  The development does not claim
  an extracted algorithm, computability result, runtime bound, or independent
  human source-correspondence audit.
- Overall status: partial for the full source surface.  The valid headline
  scale, finite/countable-class, union-separation, transfer, and discrete
  results are kernel-checked.  Several printed ambient-center implications
  require correction or are false, and Examples 4.8, 4.9, and 4.11 are not
  yet fully covered.

## Claim-to-Lean map

| Paper item | Lean declaration / file | Coverage | Qualification |
|---|---|---|---|
| Definitions 2.2--2.7 and 3.1 | Metric covering, presentation, correctness, uniform/non-uniform/limit generation, and scale-closure definitions in [`Definitions.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/Definitions.lean) | Full semantic interface | Closed-neighbourhood membership is represented by its order characterization `forall eta > r, exists center at distance < eta`, avoiding an extended-real infimum while preserving the intended closed-infimum semantics. |
| Lemma 2.1 | `lemma_2_1_uus_mono` in [`ScaleMonotonicity.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/ScaleMonotonicity.lean) | Full | The proof uses only monotonicity of finite covers. |
| Theorem 3.1 | `GenLimit.MetricSpaces.Results.theorem_3_1_sufficiency`, `theorem_3_1_necessity_of_internalization`, and `theorem_3_1_printed_necessity_is_false` in [`Results/Overview.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/Results/Overview.lean), backed by [`UniformSufficiency.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/UniformSufficiency.lean) and [`UniformNecessityDiagnostic.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/UniformNecessityDiagnostic.lean) | Partial / source repair | The sufficiency direction is full.  Under the literal ambient-center definition, the printed necessity direction is false; Lean proves it with the missing same-radius internalization premise and gives a genuine-metric finite-class counterexample to the unqualified implication. |
| Corollary 3.2 | `GenLimit.MetricSpaces.Results.corollary_3_2` in [`Results/Overview.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/Results/Overview.lean), proved in [`FiniteClassCorollaries.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/FiniteClassCorollaries.lean) | Full / source repair | The conclusion is proved with all printed hypotheses.  The proof replaces an invalid exact-maximum argument by a finite upper bound over the finitely many version-space cores. |
| Theorem 3.3 | `GenLimit.MetricSpaces.Results.theorem_3_3_semantic`, `theorem_3_3_sufficiency`, `theorem_3_3_necessity_of_internalization`, and `theorem_3_3_printed_necessity_is_false` in [`Results/Overview.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/Results/Overview.lean), backed by [`NonuniformCharacterization.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/NonuniformCharacterization.lean) and [`NonuniformNecessityDiagnostic.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/NonuniformNecessityDiagnostic.lean) | Partial / source repair | The exact equivalence with a nondecreasing cover by uniformly generatable subclasses and the printed finite-scale-closure `(ii) -> (i)` direction are full.  The unqualified reverse scale-closure implication is false; Lean proves an internalization-qualified repair and an explicit separable counterexample. |
| Corollary 3.4 | `GenLimit.MetricSpaces.Results.corollary_3_4` in [`Results/Overview.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/Results/Overview.lean), proved in [`FiniteClassCorollaries.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/FiniteClassCorollaries.lean) | Full / source repair | Finite prefixes of an ambient enumeration are intersected with the target class, so the construction also handles empty and finite countable classes. |
| Theorem 3.5 | `GenLimit.MetricSpaces.Results.theorem_3_5_printed_statement_is_false` in [`Results/Overview.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/Results/Overview.lean), proved in [`FiniteUnionDiagnostic.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/FiniteUnionDiagnostic.lean) | Refuted | A two-member separable weighted-star class satisfies the printed finite-union hypotheses but is not generatable in the limit.  The source proof conflates infinite-range closed-neighbourhood membership with membership at a finite prefix and can admit off-target nearby points. |
| Theorem 3.6 | `GenLimit.MetricSpaces.Results.theorem_3_6` in [`Results/Overview.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/Results/Overview.lean), proved in [`Theorem36.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/Theorem36.lean) | Full | Failure of a finite radius-`r` cover yields a countable separated packing; the P10 union-separation witnesses are transported into it.  The transport is semantic and need not be computable. |
| Theorem 4.1 | `GenLimit.MetricSpaces.Results.theorem_4_1` in [`Results/Overview.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/Results/Overview.lean), proved in [`DoublingUUS.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/DoublingUUS.lean) | Full | Iterated doubling covers prove UUS invariance across all positive radii. |
| Theorem 4.2 | `GenLimit.MetricSpaces.Results.theorem_4_2` in [`Results/Overview.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/Results/Overview.lean), proved in [`DoublingGeneration.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/DoublingGeneration.lean) | Full / source repair | Lean repairs a mistyped scale pair and supplies both the missing covering-number comparison and internalization argument available in doubling metrics. |
| Corollary 4.3 | `GenLimit.MetricSpaces.Results.corollary_4_3` in [`Results/Overview.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/Results/Overview.lean), proved in [`FiniteDimensionalCorollary.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/FiniteDimensionalCorollary.lean) | Full / source repair | Compactness proves the doubling property for finite-dimensional real normed spaces, and coordinatewise minima bridge two arbitrary positive scale pairs. |
| Theorem 4.4 | `GenLimit.MetricSpaces.Results.theorem_4_4_proof_inference_is_false` and `theorem_4_4_bilipschitz_repair` in [`Results/Overview.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/Results/Overview.lean), backed by [`EquivalentMetricDiagnostic.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/EquivalentMetricDiagnostic.lean) and [`BiLipschitzRepair.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/BiLipschitzRepair.lean) | Source repair; original open | Topological equivalence does not preserve finite-cover status at the same numerical radius, so the printed proof inference is false.  Mutual global Lipschitz bounds give a complete replacement theorem.  Lean does not claim that the original headline theorem itself is false. |
| Example 4.5 | `GenLimit.MetricSpaces.Results.example_4_5` in [`Results/Overview.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/Results/Overview.lean), proved in [`RealLineThreshold.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/RealLineThreshold.lean) and [`RealLineThresholdNegative.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/RealLineThresholdNegative.lean) | Full / source repair | Both threshold regimes and UUS are proved.  The negative direction replaces the defective general infinite-row lemma by a concrete diagonal that verifies target membership at every phase. |
| Theorem 4.6 | `GenLimit.MetricSpaces.Results.theorem_4_6` in [`Results/Overview.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/Results/Overview.lean), proved in [`ScaleMonotonicity.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/ScaleMonotonicity.lean) | Full | The same generator is preserved while both novelty requirements are weakened. |
| Theorem 4.7 | `GenLimit.MetricSpaces.Results.theorem_4_7_uniform` and `theorem_4_7_nonuniform` in [`Results/Overview.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/Results/Overview.lean), proved in [`ScaleMonotonicity.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/ScaleMonotonicity.lean) | Full | Both uniform and non-uniform scale-monotonicity clauses are exposed. |
| Example 4.8 | `GenLimit.MetricSpaces.Results.example_4_8_positive` in [`Results/Overview.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/Results/Overview.lean), backed by [`HilbertAxisReservoir.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/HilbertAxisReservoir.lean) and [`Example48Positive.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/Example48Positive.lean) | Partial / source repair | UUS and the positive-generation regime use a corrected causal marker/reservoir generator.  The two negative regimes remain open because the printed infinite-row lemma does not ensure that revealed row points belong to the target. |
| Example 4.9 | No Lean declaration | Open | The four scale regimes and their Hilbert-space constructions are not formalized. |
| Theorem 4.10 | `GenLimit.MetricSpaces.Results.theorem_4_10` in [`Results/Overview.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/Results/Overview.lean), proved in [`LipschitzTransfer.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/LipschitzTransfer.lean) | Full | One-sided metric domination transfers both UUS and generation in the limit with the exact rescaled radii. |
| Example 4.11 | No Lean declaration | Open | The equivalent-metric separation example is not formalized. |
| Proposition D.1 | `GenLimit.MetricSpaces.Results.proposition_D_1_limit`, `proposition_D_1_uniform`, and `proposition_D_1_nonuniform` in [`Results/Overview.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/Results/Overview.lean), proved in [`DiscreteReduction.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/DiscreteReduction.lean) | Full | At scales in `[0,1)`, the `{0,1}` discrete metric recovers the earlier countable-space limit, uniform, and non-uniform semantics exactly. |

## Reuse and dependency boundary

- [`Core/GenericGeneration.lean`](../GenLimit/Core/GenericGeneration.lean)
  supplies languages, streams, histories, and generators.
- [`Support/CountableCovers.lean`](../GenLimit/Support/CountableCovers.lean)
  supplies the finite-prefix cover used by Corollary 3.4.
- [`Paper02_LearningTheory/Definitions.lean`](../GenLimit/Paper02_LearningTheory/Definitions.lean)
  is reused only for Proposition D.1's comparison with the earlier discrete
  semantics.
- [`Paper10_UnionClosednessOfLanguageGeneration`](../GenLimit/Paper10_UnionClosednessOfLanguageGeneration.lean)
  supplies the discrete union-separation witnesses transported in Theorem
  3.6.
- [`Common/WeightedStarMetric.lean`](../GenLimit/Paper21_GenerationInMetricSpaces/Common/WeightedStarMetric.lean)
  is P21-local reusable infrastructure for the three weighted-star source
  diagnostics; it is not foundational Core vocabulary.

## Remaining work

1. Formalize the two negative regimes of Example 4.8 using a repaired
   target-valued adversarial diagonal.
2. Formalize the four scale regimes of Example 4.9.
3. Formalize the equivalent-metric separation in Example 4.11.
4. Revisit the original topological-equivalence statement of Theorem 4.4
   only after finding either a valid proof independent of the refuted
   fixed-radius inference or a counterexample to the full statement.
5. Perform an independent human statement-correspondence audit before
   assigning any human-audited status.
