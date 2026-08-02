import GenLimit.KM.FiniteQuery.Main
import GenLimit.KM.FiniteQuery.ArxivV1

/-!
# Finite-query Kleinberg--Mullainathan development

This umbrella exposes the executable relative-to-oracle Proceedings algorithm:
finite criticality tests, the cutoff-dependent selector, endpoint search, the
stateful counter machine, and KM Theorem 2.1. It also exposes the parallel
first-fresh-eligible algorithm from arXiv:2404.06757v1; the two source versions
share finite criticality and selection but have distinct stopping rules.
-/
