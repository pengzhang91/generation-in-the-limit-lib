import GenLimit.Paper07_DensityMeasuresForLanguageGeneration
import GenLimit.Paper15_PartialEnumeration
import GenLimit.Paper23_BanachDensityTopologyAndGeometry

/-!
# Kleinberg--Wei sequence

Chronological umbrella for the three Kleinberg--Wei developments:

* #07 establishes the selector, ordered-density, containment-topology, and
  finite/infinite-rank machinery;
* #15 develops partial-enumeration algorithms and density accounting while
  reusing the canonical online-generation and ordered-density interfaces;
* #23 reuses the #07/#23 neutral tower-topology and Cantor--Bendixson support
  for its Banach-density and finite-tree results.

The paper modules remain independently buildable. Shared mathematics lives
once in `GenLimit.Core` or `GenLimit.Support.KleinbergWei`, so this sequence
umbrella imposes chronological presentation without duplicating definitions.
-/
