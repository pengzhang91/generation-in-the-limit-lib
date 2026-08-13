import GenLimit.Paper11_UnionClosednessOfLanguageGeneration.DeterministicDiagonal
import GenLimit.Paper11_UnionClosednessOfLanguageGeneration.PrefixRealizability

/-!
# Appendix results and formalization boundary

High-level entry point for the appendix material of
Hanneke--Karbasi--Mehrotra--Velegkas,
*On Union-Closedness of Language Generation* (arXiv:2506.18642v1).

Formalization status:

* deterministic Proposition A.1 is complete under the source's
  injective-presentation convention (`proposition_A_1`, with compatibility
  alias `proposition_A_1_source_form`); the Paper11 presentation bridge yields
  the stronger library lower bound when needed;
* randomized Proposition A.2 is not formalized;
* the Appendix A.2 prefix-realizability development proves a generic
  deterministic principle conditional on `SchemeLimitInAmbient`; it does
  not instantiate that condition for the source's concrete family and does
  not formalize Remark A.3.

This module intentionally adds no theorem aliases: the names above expose the
actual boundary instead of making the conditional A.2 framework appear to be
a completed paper theorem.
-/
