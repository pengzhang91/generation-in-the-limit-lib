import GenLimit.Paper17_InfiniteContamination.AlgorithmFour
import GenLimit.Paper17_InfiniteContamination.BoundedDisplacement
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationNecessity
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
* Proposition 7.4 and Lemma 7.5:
  `proposition_7_4_boundedDisplacement_subset` and
  `lemma_7_5_change_of_density`.

## Partial or specialized representations

* Lemma 4.3 is represented by the finite-expansion transfer theorems; the
  paper's complete Algorithm 2 presentation is not yet reconstructed.
* Theorem 6.4 has a general semantic obstruction and an exact half-density
  instance, but not yet the paper's arbitrary-constant construction.
* Theorem 6.5 currently has the lower-density necessity direction only.
* Lemma 6.9 is represented by the finite-difference inheritance lemmas used
  by the finite-expansion development.

## Open results

Theorem 6.1; the sufficiency direction of Theorem 6.5; Theorems 6.11 and
6.14; the element-density results 6.15--6.18; and Algorithm 9 / Theorem 7.8
remain open.  See `PaperMaps/Paper17_InfiniteContamination.md` for the claim
matrix, source qualifications, and recommended implementation order.
-/
