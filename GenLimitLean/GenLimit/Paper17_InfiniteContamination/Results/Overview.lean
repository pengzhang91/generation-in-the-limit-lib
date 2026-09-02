import GenLimit.Paper17_InfiniteContamination.AlgorithmFour
import GenLimit.Paper17_InfiniteContamination.AlgorithmFive
import GenLimit.Paper17_InfiniteContamination.AlgorithmSixSeven
import GenLimit.Paper17_InfiniteContamination.AlgorithmEight
import GenLimit.Paper17_InfiniteContamination.AlgorithmNine
import GenLimit.Paper17_InfiniteContamination.BoundedDisplacement
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationNecessity
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency
import GenLimit.Paper17_InfiniteContamination.FiniteExpansionTransfer
import GenLimit.Paper17_InfiniteContamination.ProperSeparations
import GenLimit.Paper17_InfiniteContamination.SetDensityObstruction

/-!
# Paper 17: main-results overview

This module is an import-only wrapper.  It gives readers one stable entry point
for the paper's main formalized results without redeclaring the canonical
theorems in the proof modules.

## Fully represented results

* Examples 3.3--3.4:
  `example_3_3_single_noise_proper_separation` and
  `example_3_4_single_omission_proper_separation`.
* Lemma 4.1 and Corollary 4.2:
  `lemma_4_1_prefix_priority_stabilization` and the two
  `corollary_4_2_*` declarations.
* Theorem 5.1 for the explicit indexed-family interface:
  `theorem_5_1_algorithmFour`.
* Theorem 5.4 for an explicitly enumerated countable collection:
  `theorem_5_4_characterization_enumerated`.
* Theorem 6.1 for an explicitly indexed countable collection:
  `theorem_6_1_algorithmFive`, including Algorithm 5's literal finite-history
  generator and fall-back proof.
* Theorem 6.4: `theorem_6_4_arbitrary_constant`, including an explicit
  mechanical-word family of every density `1-c`, its canonical injective
  presentation, and the uniform two-target impossibility argument.
* Lemma 6.8, Lemma 6.9, and Theorem 6.5 for an explicitly indexed countable
  collection: `lemma_6_8_noiseless_setDensity`,
  `lemma_6_9_finiteContamination_sufficiency`, and
  `theorem_6_5_lowerDensity_characterization_enumerated`.
* Proposition 7.4 and Lemma 7.5:
  `proposition_7_4_boundedDisplacement_subset` and
  `lemma_7_5_change_of_density`.
* Theorem 6.11: `theorem_6_11_characterization_enumerated`, including the
  shared sparse presentation used for necessity and Algorithm 6 for
  sufficiency.
* Theorem 6.15, Corollary 6.16, and Claim 6.17:
  `theorem_6_15_algorithmEight`, `corollary_6_16`, and
  `claim_6_17_algorithmEight_rank`.
* Theorem 6.18: `theorem_6_18_finiteContamination_transfer` for the paper's
  finite-expansion reduction with ordering compatibility made explicit.
* Algorithm 9 / Theorem 7.8: `theorem_7_8_algorithmNine`, including the
  literal finite-history priority and stopping rules.

## Partial or specialized representations

* Lemma 4.3's element/set transfer is complete, and Algorithm 2's full coded
  finite-expansion family is reconstructed along the Lemma 6.9 path.
* Theorem 6.4 also retains `theorem_6_4_half_density_instance` as the simple
  even-number specialization of its arbitrary-constant construction.
* Theorem 6.14 is represented by
  `theorem_6_14_characterization_enumerated` for `0 < c < 1`. The source
  states `c ∈ (0,1]`, but at `c = 1` its sufficiency proof infers infinitely
  many target observations from a condition that permits all observations
  to be noise. That endpoint is therefore not claimed.
* Algorithm 8 uses `InheritsAmbientOrder` explicitly because the generic
  `OrderedLanguage` structure otherwise allows unrelated per-target orders.
* Algorithm 9 removes the observed finite sample from its selected
  intersection. The pseudocode omits this subtraction even though the
  paper's Definition 4 requires it; finite-deletion density invariance makes
  the repair semantics-preserving.

Within the paper map's current claim inventory through Theorem 7.8, the only
unresolved advertised case is Theorem 6.14's `c = 1` endpoint. See
`PaperMaps/Paper17_InfiniteContamination.md` for the claim matrix and source
qualifications.
-/
