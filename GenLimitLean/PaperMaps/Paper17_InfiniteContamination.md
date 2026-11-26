# Paper 17: Language Generation with Infinite Contamination

This map records the current correspondence between Mehrotra, Velegkas, Yu,
and Zhou, *Language Generation with Infinite Contamination*, and the Lean
development under `GenLimit.Paper17_InfiniteContamination`.

## Source edition and scope

- Formalization source: arXiv:2511.07417v1 (10 November 2025).
- Audited PDF SHA-256:
  `e1ef3e6d24cc382782446f24cb4377b885034812d3d678cf8d9789a703f5e0a9`.
- Lean umbrella: `GenLimit.Paper17_InfiniteContamination`.
- [Main theorem statements](../GenLimit/Paper17_InfiniteContamination/Results/Overview.lean) cover Sections 4–7 and Appendix B. [Supporting results](../GenLimit/Paper17_InfiniteContamination/Results/Supporting.lean) include the set-to-element conversion (6.15–6.16), the strict-range statement of 6.14, Proposition 7.4, and Lemma 7.5.
- Of 27 registered claim groups, 26 have full coverage under their recorded assumptions. Lean refutes the printed Theorem 7.7 and proves the corrected displacement bound.
- Corollary 4.5 uses a terminating membership-query program. Density results use explicit indexed families and canonical target orders, with the requested positive density stated where needed.

## Human audit

Peng Zhang reported a **Level 1 human audit of the nine then-current Overview
theorems (5.1, 5.4, 6.1, 6.4, 6.5, 6.11, 6.14, 6.18, and 7.8) and all
definitions involved in their statements** on 13 November 2026, against
the non-P38 working tree based on `d294766`. The
[human ledger](../AuditRecords/Human/README.md#17-infinite-contamination-all-overview-theorems-and-their-definitions-level-1) and
[fingerprint manifest](../AuditRecords/Human/Fingerprints/P17_AllOverviewTheoremsLevel1.json)
pin its exact source edition, reviewed file bytes, and statement/definition
scope, including the canonical-order Theorem 6.18 transfer.

The review retains the semantic/indexed-family model, parameter restrictions,
and conditional-transfer scope. Named algorithm definitions are included for
statement meaning, without Level 2 construction or Level 3 proof review.
The audit covers the strict-range version of Theorem 6.14. Its original name
and statement remain available in Supporting. The endpoint proof, the new
numbered results, and the independent diagnostics have kernel checks. The
November 13 human review retains its original scope.

## Claim-to-Lean correspondence

| Paper item | Lean declaration / file | Coverage | Qualification |
|---|---|---|---|
| Definitions 3 and 6--8 | `FreshElementCorrectAt`, `noiseCount`, `empiricalNoiseRate`, and the contamination predicates in [`Definitions.lean`](../GenLimit/Paper17_InfiniteContamination/Definitions.lean) | Full semantic interface | Streams are repetition-free exactly as required by the source; the zero-length empirical rate is set to zero. |
| Set-generator definitions | `SetGenerator`, `IsInfiniteSetGenerator`, `SetCorrectAt`, `InfiniteSetCorrectAt` in [`Definitions.lean`](../GenLimit/Paper17_InfiniteContamination/Definitions.lean) | Full semantic interface | `IsInfiniteSetGenerator` requires every finite-history output to be infinite, including histories not reached on a given run. |
| Examples 3.3--3.4 | `example_3_3_single_noise_proper_separation`, `example_3_4_single_omission_proper_separation` in [`ProperSeparations.lean`](../GenLimit/Paper17_InfiniteContamination/ProperSeparations.lean) | Full | Uses the isomorphic zero-based-natural version of the source examples. |
| Lemma 4.1 | `lemma_4_1_prefix_priority_stabilization` in [`PriorityStabilization.lean`](../GenLimit/Paper17_InfiniteContamination/PriorityStabilization.lean) | Full | The paper's extended-natural limit is normalized to bounded monotone natural-valued traces at a fixed cutoff. |
| Corollary 4.2 | `corollary_4_2_selected_core_subset_target`, `corollary_4_2_exists_fresh_target_output` in [`PriorityStabilization.lean`](../GenLimit/Paper17_InfiniteContamination/PriorityStabilization.lean) | Full | Uses the corrected containment direction: the selected common intersection is contained in the target. |
| Algorithm 2 / Lemma 4.3 | `algorithmTwo_transfer` in [MembershipGeneration.lean](../GenLimit/Paper17_InfiniteContamination/MembershipGeneration.lean) | Full | One computed expansion family covers every finite-contamination stream. The same expansion index transfers element, set and infinite-set generation. |
| Corollary 1.2 / Corollary 4.5 | `finiteContamination_membership_machine` in [MembershipGeneration.lean](../GenLimit/Paper17_InfiniteContamination/MembershipGeneration.lean) | Full | Each finite edit is computed locally with one base membership query. The fixed terminating search emits values above the previous output, and replay from a finite history is computable for a computable oracle. |
| Algorithm 4 / Theorem 5.1 | `theorem_5_1_algorithmFour` in [`AlgorithmFour.lean`](../GenLimit/Paper17_InfiniteContamination/AlgorithmFour.lean) | Full for the explicit indexed-family interface | Includes the recursive finite-history generator, priority ordering, maximal infinite prefix, geometric thresholds, and literal freshness at every round. |
| Theorem 5.1 source diagnostic | `theorem_5_1_printed_containment_is_reversed` in [`VanishingNoise.lean`](../GenLimit/Paper17_InfiniteContamination/VanishingNoise.lean) | Source repair | The printed proof's final containment is reversed.  The Lean theorem uses the direction required by the argument. |
| Theorem 5.4 | `theorem_5_4_characterization_enumerated` in [`AlgorithmFour.lean`](../GenLimit/Paper17_InfiniteContamination/AlgorithmFour.lean) | Full specialization | Both directions are proved for a collection supplied by an explicit countable enumeration.  No stronger presentation-free countability interface is claimed. |
| Algorithm 5 / Proposition 6.3 / Theorem 6.1 | `algorithmFiveGenerator`, `proposition_6_3_algorithmFive`, and `theorem_6_1_algorithmFive` in [`AlgorithmFive.lean`](../GenLimit/Paper17_InfiniteContamination/AlgorithmFive.lean) | Full for the explicit indexed-family interface | Includes the literal finite-history active-set generator, maximal stable infinite prefix, first-bad-language fall-back transition, finite-noise add-only expansion, and the `limsup` density conclusion.  The generator is independent of the omission parameter. |
| Theorem 6.4 / Example 6.6 | `theorem_6_4_arbitrary_constant`, `theorem_6_4_semantic_obstruction`, `theorem_6_4_half_density_instance`, and `theorem_6_4_no_better_than_half` in [`SetDensityObstruction.lean`](../GenLimit/Paper17_InfiniteContamination/SetDensityObstruction.lean) | Full | A lower mechanical word has exact prefix count `⌊(1-c)n⌋`, hence exact lower and upper density `1-c`; its increasing enumeration is simultaneously a full noiseless presentation of the smaller language and a noiseless `c`-omission presentation of `ℕ`.  The semantic obstruction then rules out every density strictly above `1-c`. |
| Lemma 6.8 / Lemma 6.9 / Theorem 6.5 | `lemma_6_8_noiseless_setDensity`, `lemma_6_9_finiteContamination_sufficiency`, and `theorem_6_5_lowerDensity_characterization_enumerated` in [`NoiselessSetDensity.lean`](../GenLimit/Paper17_InfiniteContamination/NoiselessSetDensity.lean), [`FiniteContaminationSufficiency.lean`](../GenLimit/Paper17_InfiniteContamination/FiniteContaminationSufficiency.lean), and [`FiniteContaminationNecessity.lean`](../GenLimit/Paper17_InfiniteContamination/FiniteContaminationNecessity.lean) | Full for the explicit indexed-family interface | The KM critical-language set generator supplies the noiseless density theorem; the coded expansion family proves sufficiency; the existing alternating-prefix adversary proves necessity using frequent containment rather than the source's unproved subsequence limit. |
| Theorem 6.11 | `theorem_6_11_characterization_enumerated` in [`AlgorithmSixSeven.lean`](../GenLimit/Paper17_InfiniteContamination/AlgorithmSixSeven.lean) | Full for the explicit indexed-family interface | Necessity uses one sparse injective presentation shared by any finite family with infinite common core; sufficiency is the literal Algorithm 6 finite-history generator. |
| Theorem 6.14 | `theorem_6_14_including_one` in [AlgorithmSixSeven.lean](../GenLimit/Paper17_InfiniteContamination/AlgorithmSixSeven.lean) | Full for positive requested density | Algorithm 7 handles 0 < c < 1. For c = 1 the identity stream is admissible for every infinite target, so the condition bounds the density of every finite common core. Their positive density gives infinite fresh outputs. |
| Theorem 6.15 / Claim 6.17 | `theorem_6_15_algorithmEight`, `claim_6_17_algorithmEight_rank`, and `claim_6_17_implies_asymptoticDisplacement` in [`AlgorithmEight.lean`](../GenLimit/Paper17_InfiniteContamination/AlgorithmEight.lean) | Full semantic interface | Implements the adaptive past-stage cutoff, least fresh output, finite pigeonhole count, canonical-rank bound, and the `ρ/2` density endpoint. `InheritsAmbientOrder` makes the paper's shared canonical-order assumption explicit. |
| Corollary 6.16 | `corollary_6_16` in [`AlgorithmEight.lean`](../GenLimit/Paper17_InfiniteContamination/AlgorithmEight.lean) | Full | The positive `ρ-ε` case uses Algorithm 8 quantitatively; the nonpositive case is discharged by generation plus density nonnegativity. |
| Theorem 6.18 | `theorem_6_18_finiteContamination_transfer` in [`ElementDensity.lean`](../GenLimit/Paper17_InfiniteContamination/ElementDensity.lean), with `finiteExpansion_canonical_density` in [`CanonicalExpansion.lean`](../GenLimit/Paper17_InfiniteContamination/CanonicalExpansion.lean) | Full semantic reduction with constructed canonical orderings | `canonicalFamilyOrders` implements the paper's common ambient-order convention. Both density equalities are proved from finite symmetric difference of the reference languages; the source-facing theorem has no `hmeasure` premise. |
| Theorem 6.19 / Corollary 6.20 | `noiseless_numerical_density` in [NumericalDensity.lean](../GenLimit/Paper17_InfiniteContamination/NumericalDensity.lean) | Full | One generator achieves lower density at least 1/8 and upper density at least 1/2 simultaneously. The noiseless proof uses the P39 generator through the P07 finite-history interface. Theorem 6.18 transfers the bounds under finite noise and omissions. |
| Theorem 6.21 | `theorem_6_21` in [Results/Overview.lean](../GenLimit/Paper17_InfiniteContamination/Results/Overview.lean) | Full | On one injective common stream without omissions, eventual validity on a sparse target forces upper element density zero on the larger target. |
| Definition 11 / Proposition 7.4 | `BoundedDisplacement`, `proposition_7_4_boundedDisplacement_subset` in [`BoundedDisplacement.lean`](../GenLimit/Paper17_InfiniteContamination/BoundedDisplacement.lean) | Full | The canonical order is represented by `OrderedLanguage`. |
| Lemma 7.5 | `lemma_7_5_change_of_density` in [`BoundedDisplacement.lean`](../GenLimit/Paper17_InfiniteContamination/BoundedDisplacement.lean) | Full | Both lower- and upper-density change-of-order inequalities are proved using explicit scaled prefixes. |
| Theorem 7.6 | `no_bounded_identifier` in [BoundedIdentification.lean](../GenLimit/Paper17_InfiniteContamination/BoundedIdentification.lean) | Full | One countable family of one-point deletions and the naturals defeats every identifier on exact presentations for every real M > 1. |
| Example 7.2 / Theorem 7.7 | `theorem_7_7_printed_impossible`, `theorem_7_7_corrected` in [Results/Overview.lean](../GenLimit/Paper17_InfiniteContamination/Results/Overview.lean) | Printed claim refuted, corrected result proved | At a large odd prefix of length 2B+1, the printed constraints allow at most B true observations and at most B errors. The corrected family has a common hard stream with displacement one, which also satisfies Example 7.2’s factor 1+1/k. |
| Algorithm 9 / Theorem 7.8 | `theorem_7_8_algorithmNine` in [`AlgorithmNine.lean`](../GenLimit/Paper17_InfiniteContamination/AlgorithmNine.lean) | Full for the explicit indexed-family interface | Includes the noise/displacement priority diagnostic, dense-prefix stopping rule, finite-history generator, global infinitude, eventual validity, and `(1-ε)/M` lower density. The implementation removes the finite observed sample from the selected intersection, repairing the pseudocode's omission relative to Definition 4 without changing density. |
| Theorem 7.9 | `theorem_7_9` in [Results/Overview.lean](../GenLimit/Paper17_InfiniteContamination/Results/Overview.lean) | Full for all real M ≥ 1 | Two languages share an omission-free vanishing-noise stream. Correctness on the smaller target bounds upper set density on the larger by 1/M. Floor increments allow noninteger M. |
| Theorem 7.10 | `boundedDisplacement_elementDensity` in [AlgorithmNine.lean](../GenLimit/Paper17_InfiniteContamination/AlgorithmNine.lean) | Full | Algorithm 9 and the set-to-element transformation give lower density (1−ε)/(2M) with a generator chosen before the target and stream. |
| Theorem 7.11 | `theorem_7_11` in [Results/Overview.lean](../GenLimit/Paper17_InfiniteContamination/Results/Overview.lean) | Full for all real M ≥ 1 | The same two-target stream bounds upper element density by 1/M. The final paragraph of the source uses the word “set” in its element-output argument. |
| Algorithm 10 / Theorem B.2 | `algorithmTen_generates` in [ActivePrefixes.lean](../GenLimit/Paper17_InfiniteContamination/ActivePrefixes.lean) | Full | With summable geometric thresholds, the longest active prefix with infinite intersection eventually yields fresh target words under vanishing noise and arbitrary omissions. |
| Theorems B.3--B.4 | `finiteClass_threshold`, `finiteClass_limsup` in [FiniteClassThreshold.lean](../GenLimit/Paper17_InfiniteContamination/FiniteClassThreshold.lean) | Full, including equality | Below 1/k one generator tolerates any limiting rate strictly below 1/k. At or above 1/k a family of k distinct targets has one hard stream. The first k words are common, so every prefix respects the pointwise 1/k bound at equality. |

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
- Algorithm 5's single-candidate and finite-scope consistency stabilization
  reuse [`Support/Stabilization.lean`](../GenLimit/Support/Stabilization.lean).
  The P17 declaration names remain thin source-facing wrappers around those
  generic results.
- Corollary 4.5 uses the certified finite membership tables developed for P03 with a lower bound on each new output. Theorem 6.19 uses the P07 finite-history interface for P39’s density construction.

Theorem 6.18 constructs increasing orderings of both the original and expanded
languages. [`Core/CanonicalDensity.lean`](../GenLimit/Core/CanonicalDensity.lean)
proves that finite changes of the reference language preserve lower and upper
density when both orderings inherit the ambient natural-number order. Its
finite-prefix bound applies to every measured set. This discharges the
previous `hmeasure` premise; the more general arbitrary-order transfer remains
available as `finiteContamination_transfer_of_density_compatibility`.

## Source qualifications

At the printed constants in Theorem 7.7 the adversary class is empty. The
refutation and corrected obstruction have separate declarations and registry
links. The numerical statements of 6.14 and B.3 are retained under the
assumptions above, with separate proofs for the endpoints missed by the
printed arguments.

The source comparison for these additions is AI-assisted. Human review is
recorded against the historical scope above.
