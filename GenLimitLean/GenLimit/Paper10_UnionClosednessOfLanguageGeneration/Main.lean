import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Results.Detailed
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Results.Overview

/-!
# On Union-Closedness of Language Generation: main results

Paper-facing entry point for the formalized main results of
Hanneke--Karbasi--Mehrotra--Velegkas,
*On Union-Closedness of Language Generation* (arXiv:2506.18642v1).

The public numbered results are:

* `theorem_3_1`: two uncountable non-uniform classes whose union fails
  generation in the limit;
* `theorem_3_2`: a countable non-uniform class and an uncountable uniform
  class, both generatable without adversary-provided elements, whose union
  fails generation in the limit;
* `theorem_3_3`: an uncountable non-uniform class without eventually
  unbounded closure;
* `theorem_4_1`, `theorem_4_3`, and `theorem_4_4`: the detailed witnesses.

For union lower bounds, the source-facing numbered statements use injective
presentations.  The Paper10 bridge in `Definitions` derives the stronger
lower bounds in the library's repetitions-permitted presentation model.
Results suffixed `_standard` project Theorem 3.2's autonomous schedules to
the shared history-based generation predicates.

Appendix results are deliberately kept out of this main-results facade; the
paper umbrella imports `Results.Appendix` separately.
-/
