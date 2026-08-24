import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Main
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Results.Appendix

/-!
# On Union-Closedness of Language Generation

Paper-facing umbrella for Hanneke--Karbasi--Mehrotra--Velegkas,
*On Union-Closedness of Language Generation* (arXiv:2506.18642v1).

The public facade exposes overview Theorems 3.1--3.3, detailed Theorems 4.1,
4.3, and 4.4, and deterministic Proposition A.1.  The source-facing union
lower bounds quantify over duplicate-free exact presentations.  The
Paper10-local presentation bridge yields the stronger lower bounds for the
library's repetitions-permitted semantics when needed.

Overview Theorem 3.2 includes the source's explicit "without requiring any
elements from the adversary" strengthening via Paper10-local autonomous
output schedules; `_standard` results expose the corresponding Core
generation consequences.

Randomized Proposition A.2 is outside the present scope.  Appendix A.2 is
represented only by a generic deterministic prefix-realizability principle
conditional on its infinite-limit membership obligation; the source's
concrete family and Remark A.3 are not formalized.
-/
