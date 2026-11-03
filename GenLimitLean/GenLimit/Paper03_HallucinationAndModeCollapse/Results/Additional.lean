import GenLimit.Paper03_HallucinationAndModeCollapse.OracleIdentification

/-!
# Additional results for Paper 03

This module exposes derived results beyond the numbered statements in
`Results.Overview`. These results are proved in the library; their inclusion
here does not attribute the full statements or proofs to the source paper.

Theorem 3.1 states an almost-exponential positive branch, with rates
`exp (-g n)` for admissible nonnegative, divergent, sublinear exponents `g`.
Definition 13 permits distribution-dependent multiplicative and horizontal
scaling; this library's almost-exponential predicate fixes the horizontal
scale to one. The result below gives a particular oracle-based learner with
the stronger bound `D * exp (-c * n)`, where `c, D > 0` may depend on the
target distribution. The learner and its tell-tale oracle are fixed before
either the distribution or the rate exponent is chosen.

The proof combines the Angluin stage learner with the paper's Lemma 8.1.
The additional argument, `angluinLearner_finiteWitness`, proves that this
specific learner is correct once the sample contains a target-dependent
finite witness and its size reaches a target-dependent cutoff. Lemma 8.1 turns that
property into exponential IID error decay. The paper's proof of Theorem 3.1
instead uses Lemma 5.5's black-box almost-exponential conversion; its
Proposition 3.10 obtains exponential identification using a subset oracle.
The result here uses membership and tell-tale enumeration access.

`ConditionTwo` supplies finite tell-tales, chosen classically to define
`emit`. The program reads only finite prefixes of their enumerations and
makes finitely many membership queries on each sample; it never tests whether
an enumeration is complete. Neither oracle is assumed ordinarily computable.
`identificationProgram_computable` separately proves ordinary computability
when membership and tell-tale enumeration are computable. Nontriviality is
needed for Theorem 3.1's lower bound, but is unnecessary for this upper bound.
-/

namespace GenLimit.HallucinationModeCollapse.Results

open GenLimit.Generic

/-- Derived exponential upper bound under membership and tell-tale access.
This is the additional oracle guarantee formerly bundled into
`Results.theorem_3_1`; it is stronger than that paper theorem's stated upper
rate and delegates to the existing certified oracle construction. -/
theorem oracle_exponential_identification
    (C : Generic.LanguageFamily ℕ) (O : GenLimit.MembershipOracle C) :
    GenLimit.Angluin.ConditionTwo C →
      ∃ emit : ℕ → ℕ → Option ℕ,
        (∀ i, GenLimit.Angluin.IsEnumeratedTellTale C i (GenLimit.Angluin.enumeratedSet emit i)) ∧
        ExponentialIdentifies C (deterministicIdentifier
          (identificationProgram.run (identificationOracle O emit))) :=
  HallucinationModeCollapse.oracle_exponentialIdentifies_of_conditionTwo C O

end GenLimit.HallucinationModeCollapse.Results
