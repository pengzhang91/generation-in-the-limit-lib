import GenLimit.Paper11_UnionClosednessOfLanguageGeneration.Main
import GenLimit.Paper11_UnionClosednessOfLanguageGeneration.Results.Appendix

/-!
# On Union-Closedness of Language Generation

Paper-facing umbrella for Hanneke--Karbasi--Mehrotra--Velegkas,
*On Union-Closedness of Language Generation* (arXiv:2506.18642v1).

The public facade exposes overview Theorems 3.1--3.3, detailed Theorems 4.1,
4.3, and 4.4, and deterministic Proposition A.1.  The source-facing union
lower bounds quantify over duplicate-free exact presentations; explicitly
named `*_all_presentations` results record the stronger corollaries for the
library's repetitions-permitted semantics.

Randomized Proposition A.2 is outside the present scope.  Appendix A.2 is
represented only by a generic deterministic prefix-realizability principle
conditional on its infinite-limit membership obligation; the source's
concrete family and Remark A.3 are not formalized.
-/
