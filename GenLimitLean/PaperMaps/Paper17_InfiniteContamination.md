# Paper 17: Language Generation with Infinite Contamination

This map records the current correspondence between Mehrotra, Velegkas, Yu,
and Zhou, *Language Generation with Infinite Contamination*, and the Lean
development under `GenLimit.Paper17_InfiniteContamination`.

## Source edition and scope

- Formalization source: arXiv:2511.07417v1 (10 November 2025).
- Audited PDF SHA-256:
  `e1ef3e6d24cc382782446f24cb4377b885034812d3d678cf8d9789a703f5e0a9`.
- Lean umbrella: `GenLimit.Paper17_InfiniteContamination`.
- Main-results entry point:
  [`Results/Overview.lean`](../GenLimit/Paper17_InfiniteContamination/Results/Overview.lean).
- Status: **substantially complete through Theorem 7.8**. Every listed Lean
  declaration is kernel-checked. Theorem 6.14's `c = 1` endpoint is excluded
  because the printed sufficiency argument does not justify it; explicit
  indexed-family and ordering assumptions are recorded below.
- The selected theorem-card inventory is complete through Section 7 and the
  two independent Appendix B generation variants. Results beyond Theorem 7.8
  are included even when their Lean coverage is partial or zero.
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
| Corollary 1.2 / Corollary 4.5 | — | Not formalized | The source claims a computable membership-query implementation. The P17 development is semantic and contains no machine-level oracle program for this corollary. |
| Algorithm 4 / Theorem 5.1 | `theorem_5_1_algorithmFour` in [`AlgorithmFour.lean`](../GenLimit/Paper17_InfiniteContamination/AlgorithmFour.lean) | Full for the explicit indexed-family interface | Includes the recursive finite-history generator, priority ordering, maximal infinite prefix, geometric thresholds, and literal freshness at every round. |
| Theorem 5.1 source diagnostic | `theorem_5_1_printed_containment_is_reversed` in [`VanishingNoise.lean`](../GenLimit/Paper17_InfiniteContamination/VanishingNoise.lean) | Source repair | The printed proof's final containment is reversed.  The Lean theorem uses the direction required by the argument. |
| Theorem 5.4 | `theorem_5_4_characterization_enumerated` in [`AlgorithmFour.lean`](../GenLimit/Paper17_InfiniteContamination/AlgorithmFour.lean) | Full specialization | Both directions are proved for a collection supplied by an explicit countable enumeration.  No stronger presentation-free countability interface is claimed. |
| Algorithm 5 / Proposition 6.3 / Theorem 6.1 | `algorithmFiveGenerator`, `proposition_6_3_algorithmFive`, and `theorem_6_1_algorithmFive` in [`AlgorithmFive.lean`](../GenLimit/Paper17_InfiniteContamination/AlgorithmFive.lean) | Full for the explicit indexed-family interface | Includes the literal finite-history active-set generator, maximal stable infinite prefix, first-bad-language fall-back transition, finite-noise add-only expansion, and the `limsup` density conclusion.  The generator is independent of the omission parameter. |
| Theorem 6.4 / Example 6.6 | `theorem_6_4_arbitrary_constant`, `theorem_6_4_semantic_obstruction`, `theorem_6_4_half_density_instance`, and `theorem_6_4_no_better_than_half` in [`SetDensityObstruction.lean`](../GenLimit/Paper17_InfiniteContamination/SetDensityObstruction.lean) | Full | A lower mechanical word has exact prefix count `⌊(1-c)n⌋`, hence exact lower and upper density `1-c`; its increasing enumeration is simultaneously a full noiseless presentation of the smaller language and a noiseless `c`-omission presentation of `ℕ`.  The semantic obstruction then rules out every density strictly above `1-c`. |
| Lemma 6.8 / Lemma 6.9 / Theorem 6.5 | `lemma_6_8_noiseless_setDensity`, `lemma_6_9_finiteContamination_sufficiency`, and `theorem_6_5_lowerDensity_characterization_enumerated` in [`NoiselessSetDensity.lean`](../GenLimit/Paper17_InfiniteContamination/NoiselessSetDensity.lean), [`FiniteContaminationSufficiency.lean`](../GenLimit/Paper17_InfiniteContamination/FiniteContaminationSufficiency.lean), and [`FiniteContaminationNecessity.lean`](../GenLimit/Paper17_InfiniteContamination/FiniteContaminationNecessity.lean) | Full for the explicit indexed-family interface | The KM critical-language set generator supplies the noiseless density theorem; the coded expansion family proves sufficiency; the existing alternating-prefix adversary proves necessity using frequent containment rather than the source's unproved subsequence limit. |
| Theorem 6.11 | `theorem_6_11_characterization_enumerated` in [`AlgorithmSixSeven.lean`](../GenLimit/Paper17_InfiniteContamination/AlgorithmSixSeven.lean) | Full for the explicit indexed-family interface | Necessity uses one sparse injective presentation shared by any finite family with infinite common core; sufficiency is the literal Algorithm 6 finite-history generator. |
| Theorem 6.14 | `theorem_6_14_characterization_enumerated` in [`AlgorithmSixSeven.lean`](../GenLimit/Paper17_InfiniteContamination/AlgorithmSixSeven.lean) | Full on `0 < c < 1`; source endpoint gap at `c = 1` | Necessity covers the stated condition. Sufficiency converts constant noise into infinitely many target observations, which is valid only for `c < 1`; at `c = 1` the source premise permits every observation to be noise. |
| Theorem 6.15 / Claim 6.17 | `theorem_6_15_algorithmEight`, `claim_6_17_algorithmEight_rank`, and `claim_6_17_implies_asymptoticDisplacement` in [`AlgorithmEight.lean`](../GenLimit/Paper17_InfiniteContamination/AlgorithmEight.lean) | Full semantic interface | Implements the adaptive past-stage cutoff, least fresh output, finite pigeonhole count, canonical-rank bound, and the `ρ/2` density endpoint. `InheritsAmbientOrder` makes the paper's shared canonical-order assumption explicit. |
| Corollary 6.16 | `corollary_6_16` in [`AlgorithmEight.lean`](../GenLimit/Paper17_InfiniteContamination/AlgorithmEight.lean) | Full | The positive `ρ-ε` case uses Algorithm 8 quantitatively; the nonpositive case is discharged by generation plus density nonnegativity. |
| Theorem 6.18 | `theorem_6_18_finiteContamination_transfer` in [`ElementDensity.lean`](../GenLimit/Paper17_InfiniteContamination/ElementDensity.lean) | Full semantic reduction with explicit ordering compatibility | Transfers lower and upper element-density guarantees through the coded finite expansion. `hmeasure` states the common ambient-order fact that is implicit in the paper but not forced by the repo's generic `OrderedLanguage`. |
| Theorem 6.19 / Corollary 6.20 | `theorem_6_18_finiteContamination_transfer` only | Partial | The P17 transfer is full, but Theorem 6.19 imports the noiseless `1/2` upper- and `1/8` lower-density results from #07. The former is unformalized and the latter retains #07's disputed persistence gap, so the numerical corollary is not end-to-end formalized. |
| Theorem 6.21 | `exists_common_vanishingNoise_presentation`, `floorIncrementLanguage_upperDensity` | Partial ingredients | Lean supplies common vanishing-noise streams and exact sparse-density witnesses, but has no theorem assembling them into the quantified two-target element-density impossibility result. |
| Definition 11 / Proposition 7.4 | `BoundedDisplacement`, `proposition_7_4_boundedDisplacement_subset` in [`BoundedDisplacement.lean`](../GenLimit/Paper17_InfiniteContamination/BoundedDisplacement.lean) | Full | The canonical order is represented by `OrderedLanguage`. |
| Lemma 7.5 | `lemma_7_5_change_of_density` in [`BoundedDisplacement.lean`](../GenLimit/Paper17_InfiniteContamination/BoundedDisplacement.lean) | Full | Both lower- and upper-density change-of-order inequalities are proved using explicit scaled prefixes. |
| Theorem 7.6 | — | Not formalized | The identification learner and the bounded-displacement diagonal lower bound are outside the current Lean interface. |
| Example 7.2 / Theorem 7.7 | — | Not formalized; source gap | The theorem prints a `1/k` displacement factor, but Example 7.2 proves `1+1/k`; a factor below one cannot describe the canonical enumeration. The registry records the supported `1+1/k` reading. |
| Algorithm 9 / Theorem 7.8 | `theorem_7_8_algorithmNine` in [`AlgorithmNine.lean`](../GenLimit/Paper17_InfiniteContamination/AlgorithmNine.lean) | Full for the explicit indexed-family interface | Includes the noise/displacement priority diagnostic, dense-prefix stopping rule, finite-history generator, global infinitude, eventual validity, and `(1-ε)/M` lower density. The implementation removes the finite observed sample from the selected intersection, repairing the pseudocode's omission relative to Definition 4 without changing density. |
| Theorem 7.9 | — | Not formalized | The two-language set-density upper bound is registered. Its proof uses `M · ℕ`, so the card makes the positive-integer scaling implicit in the displayed theorem explicit. |
| Theorem 7.10 | `Results.theorem_7_8`, `Results.theorem_6_15` | Partial only as a source-facing result | Both ingredients are full: Algorithm 9 gives `(1-ε)/M` set density and Theorem 6.15 halves it. There is no Lean theorem composing their exact source quantifiers into the `(1-ε)/(2M)` endpoint. |
| Theorem 7.11 | — | Not formalized; qualified source wording | The theorem concerns element density, while the last proof paragraph says “set-based generator.” The shared-stream argument supports the element reading; the card also records the implicit positive-integer role of `M`. |
| Algorithm 10 / Theorem B.2 | — | Not formalized | This priority-free implementation variant proves the Theorem 5.1 guarantee without Lemma 4.1's stable-prefix mechanism. |
| Theorems B.3--B.4 | — | Not formalized; equality endpoint disputed | Strict-below-`1/k` sufficiency is coherent. For necessity at equality, the proposed stream has fraction `1/k + o(1)`, which does not satisfy the paper's eventual pointwise `c = 1/k` bound at nonmultiples of `k`; the proof supports rates strictly above `1/k`, not the printed equality endpoint. |

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
- P17's Lean modules have no direct dependency on another numbered paper
  development. At the source-result level, Corollary 6.20 explicitly imports
  the noiseless numerical guarantees of #07; the registry records those
  cross-paper dependencies without introducing a Lean import.

## Remaining qualification

The semantic construction roadmap through Theorem 7.8 is substantially
complete, but the source-result inventory intentionally extends beyond that
implementation boundary. Open work includes the machine-level Corollary 4.5,
the end-to-end Corollary 6.20 and Theorem 6.21 conclusions, the Section 7
identification and density lower bounds, Theorem 7.10's thin composition
wrapper, and the Appendix B algorithms.

Three source qualifications remain explicit rather than silently repaired:
Theorem 6.14's `c = 1` endpoint needs a premise guaranteeing infinitely many
true observations; Theorem 7.7 prints the wrong displacement factor; and
Theorem B.3's necessity proof does not establish its equality endpoint.

This map and the registry cards were compared directly against the pinned
PDF using AI-assisted review. That records source locators and discrepancies,
but it is not a human statement-correspondence certification.
