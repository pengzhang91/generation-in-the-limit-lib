# Paper 17: Language Generation with Infinite Contamination

This map records the current correspondence between Mehrotra, Velegkas, Yu,
and Zhou, *Language Generation with Infinite Contamination*, and the Lean
development under `GenLimit.Paper17_InfiniteContamination`.

## Source edition and scope

- Formalization source: arXiv:2511.07417v1 (10 November 2025).
- Lean umbrella: `GenLimit.Paper17_InfiniteContamination`.
- Main-results entry point:
  [`Results/Overview.lean`](../GenLimit/Paper17_InfiniteContamination/Results/Overview.lean).
- Status: **partial formalization**.  Every listed Lean declaration is
  kernel-checked, but several paper results remain open or are represented by
  an explicitly stated specialization.
- The development is semantic and classical.  It does not claim executable
  computability or running-time bounds.

## Claim-to-Lean correspondence

| Paper item | Lean declaration / file | Coverage | Qualification |
|---|---|---|---|
| Definitions 3 and 6--8 | `FreshElementCorrectAt`, `noiseCount`, `empiricalNoiseRate`, and the contamination predicates in [`Definitions.lean`](../GenLimit/Paper17_InfiniteContamination/Definitions.lean) | Full semantic interface | Streams are repetition-free exactly as required by the source; the zero-length empirical rate is set to zero. |
| Set-generator definitions | `SetGenerator`, `IsInfiniteSetGenerator`, `SetCorrectAt`, `InfiniteSetCorrectAt` in [`Definitions.lean`](../GenLimit/Paper17_InfiniteContamination/Definitions.lean) | Full semantic interface | `IsInfiniteSetGenerator` requires every finite-history output to be infinite, including histories not reached on a given run. |
| Examples 3.3--3.4 | `example_3_3_single_noise_proper_separation`, `example_3_4_single_omission_proper_separation` in [`ProperSeparations.lean`](../GenLimit/Paper17_InfiniteContamination/ProperSeparations.lean) | Full | Uses the isomorphic zero-based-natural version of the source examples. |
| Lemma 4.1 | `lemma_4_1_prefix_priority_stabilization` in [`PriorityStabilization.lean`](../GenLimit/Paper17_InfiniteContamination/PriorityStabilization.lean) | Full | The paper's extended-natural limit is normalized to bounded monotone natural-valued traces at a fixed cutoff. |
| Corollary 4.2 | `corollary_4_2_selected_core_subset_target`, `corollary_4_2_exists_fresh_target_output` in [`PriorityStabilization.lean`](../GenLimit/Paper17_InfiniteContamination/PriorityStabilization.lean) | Full | Uses the corrected containment direction: the selected common intersection is contained in the target. |
| Algorithm 2 / Lemma 4.3 | `finiteContamination_expansionWitness`, `finiteExpansionOracleFamily`, and `lemma_4_3_*_finiteExpansion_transfer` in [`FiniteExpansionTransfer.lean`](../GenLimit/Paper17_InfiniteContamination/FiniteExpansionTransfer.lean) and [`FiniteContaminationSufficiency.lean`](../GenLimit/Paper17_InfiniteContamination/FiniteContaminationSufficiency.lean) | Full for the explicit indexed-family interface | Natural-number codes enumerate every finite add/remove expansion; element, set, and infinite-set correctness transfer back after the finitely many extraneous points have appeared. |
| Algorithm 4 / Theorem 5.1 | `theorem_5_1_algorithmFour` in [`AlgorithmFour.lean`](../GenLimit/Paper17_InfiniteContamination/AlgorithmFour.lean) | Full for the explicit indexed-family interface | Includes the recursive finite-history generator, priority ordering, maximal infinite prefix, geometric thresholds, and literal freshness at every round. |
| Theorem 5.1 source diagnostic | `theorem_5_1_printed_containment_is_reversed` in [`VanishingNoise.lean`](../GenLimit/Paper17_InfiniteContamination/VanishingNoise.lean) | Source repair | The printed proof's final containment is reversed.  The Lean theorem uses the direction required by the argument. |
| Theorem 5.4 | `theorem_5_4_characterization_enumerated` in [`AlgorithmFour.lean`](../GenLimit/Paper17_InfiniteContamination/AlgorithmFour.lean) | Full specialization | Both directions are proved for a collection supplied by an explicit countable enumeration.  No stronger presentation-free countability interface is claimed. |
| Algorithm 5 / Proposition 6.3 / Theorem 6.1 | `algorithmFiveGenerator`, `proposition_6_3_algorithmFive`, and `theorem_6_1_algorithmFive` in [`AlgorithmFive.lean`](../GenLimit/Paper17_InfiniteContamination/AlgorithmFive.lean) | Full for the explicit indexed-family interface | Includes the literal finite-history active-set generator, maximal stable infinite prefix, first-bad-language fall-back transition, finite-noise add-only expansion, and the `limsup` density conclusion.  The generator is independent of the omission parameter. |
| Theorem 6.4 / Example 6.6 | `theorem_6_4_semantic_obstruction`, `theorem_6_4_half_density_instance`, and `theorem_6_4_no_better_than_half` in [`SetDensityObstruction.lean`](../GenLimit/Paper17_InfiniteContamination/SetDensityObstruction.lean) | Partial | The general semantic obstruction and exact `1/2` instance are proved.  The source's explicit construction for arbitrary constant `c` remains open. |
| Lemma 6.8 / Lemma 6.9 / Theorem 6.5 | `lemma_6_8_noiseless_setDensity`, `lemma_6_9_finiteContamination_sufficiency`, and `theorem_6_5_lowerDensity_characterization_enumerated` in [`NoiselessSetDensity.lean`](../GenLimit/Paper17_InfiniteContamination/NoiselessSetDensity.lean), [`FiniteContaminationSufficiency.lean`](../GenLimit/Paper17_InfiniteContamination/FiniteContaminationSufficiency.lean), and [`FiniteContaminationNecessity.lean`](../GenLimit/Paper17_InfiniteContamination/FiniteContaminationNecessity.lean) | Full for the explicit indexed-family interface | The KM critical-language set generator supplies the noiseless density theorem; the coded expansion family proves sufficiency; the existing alternating-prefix adversary proves necessity using frequent containment rather than the source's unproved subsequence limit. |
| Theorems 6.11 and 6.14 | — | Open | Vanishing-noise and constant-noise set-density results are not formalized. |
| Theorems 6.15--6.18 | — | Open | The element-density characterizations are not formalized. |
| Definition 11 / Proposition 7.4 | `BoundedDisplacement`, `proposition_7_4_boundedDisplacement_subset` in [`BoundedDisplacement.lean`](../GenLimit/Paper17_InfiniteContamination/BoundedDisplacement.lean) | Full | The canonical order is represented by `OrderedLanguage`. |
| Lemma 7.5 | `lemma_7_5_change_of_density` in [`BoundedDisplacement.lean`](../GenLimit/Paper17_InfiniteContamination/BoundedDisplacement.lean) | Full | Both lower- and upper-density change-of-order inequalities are proved using explicit scaled prefixes. |
| Algorithm 9 / Theorem 7.8 | — | Open | The later bounded-displacement generation algorithm and its main guarantee are not formalized. |

## Shared infrastructure

- Occurrence-counted and distinct-value finite contamination live in
  [`Core/FiniteContamination.lean`](../GenLimit/Core/FiniteContamination.lean).
  `finiteNoiseEnumeration_iff_core` proves that the P17 repetition-free
  finite-noise presentation agrees with the Core interface.
- Ordered prefix density and its monotonicity/bounds live in
  [`Core/OrderedDensity.lean`](../GenLimit/Core/OrderedDensity.lean).
- Finite deletion and finite symmetric-perturbation invariance for the
  measured set also live in `Core/OrderedDensity.lean`; these are used by
  both Algorithm 5 and Lemma 6.9 while keeping the reference ordering fixed.
- The finite-prefix completion construction used by the P17 alternating
  adversary and P12 feedback code lives in
  [`Support/PrefixCompletion.lean`](../GenLimit/Support/PrefixCompletion.lean).
- P17 has no direct dependency on another numbered paper development.

## Recommended substantive roadmap

1. Generalize the Theorem 6.4 witness from the exact `1/2` example to an
   arbitrary admissible constant `c`.
2. Add Theorems 6.11 and 6.14 for vanishing and constant noise.
3. Add the element-density results, Theorems 6.15--6.18.
4. Reconstruct Algorithm 9 and prove Theorem 7.8 on top of the completed
   bounded-displacement infrastructure.

The order is deliberate: steps 1--3 build the remaining density theory, while
step 4 can reuse the already completed Proposition 7.4 / Lemma 7.5 machinery.
