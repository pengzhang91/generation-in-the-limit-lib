import GenLimit.Paper03_HallucinationAndModeCollapse.Results.Overview
import GenLimit.Paper03_HallucinationAndModeCollapse.FurtherIdentification

/-!
# Hallucination versus mode collapse umbrella

This umbrella exposes online Theorems 3.5, 3.7, and 3.9 with explicit
PMF/MOP and computation interfaces; the randomized statistical exponential lower
bound of Lemma 5.1; the full Theorem 3.1 rate dichotomy with a certified
membership/tell-tale oracle procedure; and certified membership-only exponential identification
upper rates for Propositions 3.11--3.12 via Lemma 8.1. Theorem 3.2 gives the
matching exponential generation upper and randomized lower bounds, with a
certified terminating membership-only oracle search on infinite languages.
Theorem 3.3 adds statistical exact fresh breadth, its no-rate obstruction,
certified full-support samplers, pointwise support-membership procedures, and
ordinary computation certificates under effective oracle assumptions.
Theorem 3.4 derives ordinary computable word-support membership for encoded
token-by-token machines whose local execution halts on every random tape;
the outer process may run forever. Its finite search follows auxiliary state
and checks EOS, using a compactness proof of the uniform local bound.
Theorem 3.6 adds the statistical unambiguous-generation no-rate result,
correcting the printed loss polarity. A proof-only semantic closest-language
classifier transfers Theorem 3.1's one-half lower bound to this loss; no
computability of that classifier is asserted. The public theorem retains
the source's stability and pointwise decidable-MOP hypotheses.
Theorem 3.8 adds the statistical approximate-breadth impossibility result.
It reuses generic support locking and finite IID-prefix mass bounds to
construct a semantic finite tell-tale whenever all valid laws have vanishing
error; no infinite-IID online transfer is assumed.
Proposition 3.10 supplies the certified last-critical subset-oracle identifier,
its finite positive witnesses and exponential IID rate, and ordinary uniform
computation when membership and inclusion are computable. No tell-tale
enumeration oracle is part of that program.
The bounded version-space learner has a certified truth-table realization
and ordinary computation under computable membership. It repairs the printed
construction for Proposition 3.12. Theorem 3.13 adds the full labeled-data
exponential upper and randomized lower bounds: bounded least-consistent
enumeration and finite separators replace the source batching proof. Validity
is proved equivalent to full marginal support and correct deterministic labels. Theorem 3.1's positive
branch uses the stronger exponential Angluin-learner bound, and its no-rate
branch has a direct finite-sample Baire proof. Theorem 3.5 realizes fresh and
repetition-allowing PMF breadth with certified sampling and support membership
in the infinite-language regime. Pointwise MOP needs computable membership;
uniform ordinary sampling additionally needs computable training. Theorems
3.7/3.9 retain source pointwise MOP and semantic/Condition-2 non-ID. The
bounded identifiers have fixed-index convergence and uniform-computation
certificates. Separate ordinary effective results require uniform MOP; no
uniform decider is inferred from pointwise existence. Legacy semantic
wrappers remain available.

`Results.Overview` is the compact paper-facing surface.
`FurtherIdentification` contains supporting Angluin
relationships and does not present them as numbered P03 propositions.
-/
