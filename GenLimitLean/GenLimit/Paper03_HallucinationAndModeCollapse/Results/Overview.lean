import GenLimit.Paper03_HallucinationAndModeCollapse.PositiveBreadth
import GenLimit.Paper03_HallucinationAndModeCollapse.FiniteIdentificationComputation
import GenLimit.Paper03_HallucinationAndModeCollapse.LabeledIdentification
import GenLimit.Paper03_HallucinationAndModeCollapse.IdentificationLowerBound
import GenLimit.Paper03_HallucinationAndModeCollapse.UniversalRates
import GenLimit.Paper03_HallucinationAndModeCollapse.OracleGeneration
import GenLimit.Paper03_HallucinationAndModeCollapse.StatisticalBreadth
import GenLimit.Paper03_HallucinationAndModeCollapse.RandomizedSupport
import GenLimit.Paper03_HallucinationAndModeCollapse.TokenMembership
import GenLimit.Paper03_HallucinationAndModeCollapse.StatisticalUnambiguous
import GenLimit.Paper03_HallucinationAndModeCollapse.StatisticalApproximateBreadth
import GenLimit.Paper03_HallucinationAndModeCollapse.SubsetIdentificationRates
import GenLimit.Paper03_HallucinationAndModeCollapse.OnlineResults

/-!
# Paper 03 results overview

This module collects the main results of Paper 03:

- Theorems 3.1--3.3: statistical rates for identification, generation, and
  exact breadth, with oracle algorithms and lower bounds.
- Theorem 3.4: decidable finite-word support for token generators whose
  local machines halt on every random tape.
- Theorem 3.5: identification and online breadth for infinite-language
  families, covering both fresh outputs and repetitions.
- Theorems 3.6--3.9: statistical and online impossibility results for
  unambiguous generation and approximate breadth on non-identifiable
  families, under stability and pointwise decidable support membership.
- Proposition 3.10: exponential identification using membership and subset
  queries.
- Propositions 3.11--3.12: exponential identification using membership alone
  for finite collections and countable collections of finite languages.
- Theorem 3.13: optimal exponential rates for labeled identification.

Each wrapper delegates to its proof module. The statements and theorem
comments below specify the oracle, computability, and nontriviality assumptions.
`Results.Additional` exposes the stronger oracle-based exponential
identification guarantee separately from the numbered paper results.
Supporting semantic results are available directly in `FiniteIdentification`,
`PositiveBreadth`, and `OnlineReductions`.
-/

namespace GenLimit.HallucinationModeCollapse.Results

open GenLimit.Generic

/-- Theorem 3.1: exactly one rate alternative holds, Angluin's condition
characterizes the positive branch, and the exponential lower bound holds for
every randomized learner.

The paper places the lower bound inside the positive alternative. Here it is
a separate conjunct: Lemma 5.1 proves it for every nontrivial collection, and
the no-rate alternative also implies it because positive limsup error exceeds
`exp (-2 * n)` infinitely often. This rearrangement preserves the dichotomy.

This semantic statement needs no oracle argument. The certified membership/
tell-tale program and its stronger exponential upper bound are exposed as
`Results.oracle_exponential_identification` in `Results.Additional`, rather
than included as an extra conclusion of the numbered theorem. -/
theorem theorem_3_1 (C : Generic.LanguageFamily ℕ) (hC : NontrivialCollection C) :
    ((AlmostExponentialIdentifiable C ∧ ¬NoIdentificationRate C) ∨
      (¬AlmostExponentialIdentifiable C ∧ NoIdentificationRate C)) ∧
      (AlmostExponentialIdentifiable C ↔ GenLimit.Angluin.ConditionTwo C) ∧
      (∀ A : StatisticalIdentifier, ∃ i p, ValidDistribution C i p ∧
        ∃ᶠ n : ℕ in Filter.atTop, Real.exp (-2 * (n : ℝ)) ≤ identificationError C A p i n) :=
  HallucinationModeCollapse.theorem_3_1_mathematical C hC

/-- Theorem 3.2: a membership-only generator achieves exponential fresh-
generation rates for every indexed infinite-language family. The rate is
optimal on generation-nontrivial families, even against randomized generators.
Ordinary uniform computability follows when membership is computable.

The paper's [Remark 1 in Section 3.1.3](https://arxiv.org/html/2411.09642v3#S3.SS1.SSS3)
uses deterministic outputs to simplify the notation. Here `generationError`
is the expected equation (5) loss extended to randomized outputs. The upper
bound uses the deterministic generator `certifiedKM O`, so its error also
equals the support-based error in equation (1).

The lower bound quantifies over all randomized PMF kernels. The paper's
[proof of Lemma 5.10](https://arxiv.org/html/2411.09642v3#S5.SS2.SSS1)
explicitly handles randomized outputs through a conditional output
distribution `p_n`, despite the earlier deterministic notation. As explained
in the documentation of `generationError`, this error is at most the
equation (1) error. Consequently, the lower bound also implies the same bound
for equation (1), with the same target, distribution, constants, and
infinitely many sample sizes. The two errors need not be equal for randomized
generators. -/
theorem theorem_3_2 (O : GenLimit.OracleFamily) :
    ExponentialGenerates O.language (deterministicIdentifier (certifiedKM O)) ∧
      (Computable₂ O.query → Computable (certifiedKM O)) ∧
      (GenerationNontrivial O.language → ∀ G : StatisticalGenerator,
        ∃ i p, ValidDistribution O.language i p ∧
          ∃ c : ℝ, 0 < c ∧ ∃ D : ℝ, 0 < D ∧
            ∃ᶠ n : ℕ in Filter.atTop,
              D * Real.exp (-c * n) ≤ generationError O.language G p i n) :=
  HallucinationModeCollapse.theorem_3_2 O

/-- Theorem 3.3: non-identifiable families have no breadth rate in the
pointwise decidable-MOP class; consistent generation nevertheless has the
optimal exponential rate. Identifiable families have a certified positive
breadth branch under the same oracle interpretation as Theorem 3.1.
`CertifiedBreadthPositiveBranch` also gives ordinary computation certificates
when membership and tell-tale enumeration are computable. -/
theorem theorem_3_3 (O : GenLimit.OracleFamily) (hC : GenerationNontrivial O.language) :
    (¬IdentifiableInLimit O.language → ∀ G : StatisticalGenerator, DecidableMOP G →
      NoBreadthRate O.language G) ∧
    (∃ G : StatisticalGenerator, DecidableMOP G ∧ OracleMOP (generationOracle O) G ∧
      ExponentialGenerates O.language G ∧ (Computable₂ O.query → HasComputableSampler G)) ∧
    (IdentifiableInLimit O.language → CertifiedBreadthPositiveBranch O) ∧
    (∀ G : StatisticalGenerator, ∃ i p, ValidDistribution O.language i p ∧
      ∃ c : ℝ, 0 < c ∧ ∃ D : ℝ, 0 < D ∧
        ∃ᶠ n : ℕ in Filter.atTop, D * Real.exp (-c * n) ≤ generationError O.language G p i n) :=
  HallucinationModeCollapse.theorem_3_3 O hC

/-- Theorem 3.4: every-tape termination of the local randomized machine
implies decidability of complete-word support. Tokens and auxiliary states
are naturally encoded; EOS is checked and omitted from the returned word.
There is no termination assumption on the outer generation process. -/
theorem theorem_3_4 (G : TokenGenerator) (hG : G.machine.AlwaysHalts) :
    ∃ query : List ℕ → Bool, Computable query ∧
      ∀ word, query word = true ↔ 0 < G.wordProbability hG word :=
  TokenGenerator.theorem_3_4 G hG

/-- Theorem 3.5 in the explicit infinite-language oracle model. Both fresh
and repetition-allowing generators are realized by PMFs and certified
sampling/support programs. Ordinary-MOP equivalences explicitly assume
computable family membership; uniform ordinary training has its separate
certificate in the positive-branch predicate. -/
theorem theorem_3_5 (O : GenLimit.OracleFamily) :
    (¬IdentifiableInLimit O.language → ∀ G : StatisticalGenerator, DecidableMOP G →
      ¬FreshBreadthInLimit (statisticalSupportView G) O.language ∧
      ¬RepeatingBreadthInLimit (statisticalSupportView G) O.language) ∧
    (IdentifiableInLimit O.language → CertifiedOnlineBreadthPositiveBranch O) ∧
    (Computable₂ O.query →
      (IdentifiableInLimit O.language ↔ ∃ G : StatisticalGenerator, DecidableMOP G ∧
        FreshBreadthInLimit (statisticalSupportView G) O.language) ∧
      (IdentifiableInLimit O.language ↔ ∃ G : StatisticalGenerator, DecidableMOP G ∧
        RepeatingBreadthInLimit (statisticalSupportView G) O.language)) :=
  HallucinationModeCollapse.theorem_3_5 O

/-- Theorem 3.6: no vanishing statistical unambiguity rate for a stable
generator with pointwise decidable MOP on a non-identifiable collection.
`NoUnambiguousRate` gives one fixed valid distribution with positive limsup
failure; it also excludes distribution-dependent positive rate rescalings.
The loss uses one for failure, correcting the printed reversed indicator.
Non-identifiability is the same semantic/Condition-2 boundary as Theorem 3.1. -/
theorem theorem_3_6 (C : Generic.LanguageFamily ℕ) (hC : ¬IdentifiableInLimit C)
    (G : StatisticalGenerator) (hstable : StatisticalStable G C) (hMOP : DecidableMOP G) :
    NoUnambiguousRate C G :=
  HallucinationModeCollapse.theorem_3_6 C hC G hstable hMOP

/-- Theorem 3.7 for PMF generators with source pointwise MOP. The stronger
support-semantic obstruction covers every such kernel, so no extraction of a
uniform support procedure from pointwise MOP is needed. -/
theorem theorem_3_7 (C : Generic.LanguageFamily ℕ) (hnot : ¬IdentifiableInLimit C)
    (G : StatisticalGenerator) (hstable : StatisticalStable G C) (hMOP : DecidableMOP G) :
    ¬UnambiguousInLimit (statisticalSupportView G) C :=
  HallucinationModeCollapse.theorem_3_7 C hnot G hstable hMOP

/-- Theorem 3.8: stable generators with pointwise decidable MOP cannot have
a vanishing approximate-breadth failure rate on a non-identifiable collection.
The loss is exactly equation (6). The positive-limsup conclusion excludes
positive distribution-dependent horizontal and vertical rate rescalings.
Non-identifiability uses the semantic/Condition-2 boundary of Theorem 3.1. -/
theorem theorem_3_8 (C : Generic.LanguageFamily ℕ) (hC : ¬IdentifiableInLimit C)
    (G : StatisticalGenerator) (hstable : StatisticalStable G C) (hMOP : DecidableMOP G) :
    NoApproximateBreadthRate C G :=
  HallucinationModeCollapse.theorem_3_8 C hC G hstable hMOP

/-- Theorem 3.9 for PMF generators with source pointwise MOP. Stability and
approximate breadth have exactly the existing support semantics. The family
hypothesis uses semantic/Condition-2 non-identifiability. -/
theorem theorem_3_9 (C : Generic.LanguageFamily ℕ) (hnot : ¬IdentifiableInLimit C)
    (G : StatisticalGenerator) (hstable : StatisticalStable G C) (hMOP : DecidableMOP G) :
    ¬ApproximateBreadthInLimit (statisticalSupportView G) C :=
  HallucinationModeCollapse.theorem_3_9 C hnot G hstable hMOP

/-- Proposition 3.10: a fixed certified last-critical program attains an
exponential statistical identification rate under the standing membership
oracle and an additional subset oracle. No tell-tale oracle is used.
The same learner is ordinarily computable when both oracles are computable.
Error is wrong-language probability; duplicate target indices are permitted. -/
theorem proposition_3_10 (C : Generic.LanguageFamily ℕ)
    (O : GenLimit.MembershipOracle C) (S : GenLimit.SubsetOracle C)
    (hC : GenLimit.Angluin.ConditionTwo C) :
    ExponentialIdentifies C (deterministicIdentifier (subsetIdentifier O S)) ∧
      (Computable₂ O.query → Computable₂ S.query → Computable (subsetIdentifier O S)) :=
  HallucinationModeCollapse.proposition_3_10 C O S hC

/-- Proposition 3.11: the certified membership-only version-space learner
has exponential error on finite-range families, including infinite languages.
Computable membership gives ordinary uniform computation of the same learner. -/
theorem proposition_3_11 (C : Generic.LanguageFamily ℕ)
    (O : GenLimit.MembershipOracle C) (hRange : (Set.range C).Finite) :
    ExponentialIdentifies C (deterministicIdentifier (finiteVersionSpaceLearner O)) ∧
      (Computable₂ O.query → Computable (finiteVersionSpaceLearner O)) :=
  HallucinationModeCollapse.proposition_3_11 C O hRange

/-- Proposition 3.12: the same certified learner has exponential error for
countable families of finite languages. It repairs the printed construction. -/
theorem proposition_3_12 (C : Generic.LanguageFamily ℕ)
    (O : GenLimit.MembershipOracle C) (hfinite : ∀ i, (C i).Finite) :
    ExponentialIdentifies C (deterministicIdentifier (finiteVersionSpaceLearner O)) ∧
      (Computable₂ O.query → Computable (finiteVersionSpaceLearner O)) :=
  HallucinationModeCollapse.proposition_3_12 C O hfinite

/-- Theorem 3.13: every countable indexed family has a membership-only
labeled learner with exponential error; on identification-nontrivial families
every randomized learner has a fixed valid law with exponential error
infinitely often. Validity is precisely source Definition 16. -/
theorem theorem_3_13 (C : Generic.LanguageFamily ℕ) (O : GenLimit.MembershipOracle C) :
    ExponentialLabeledIdentifies C (deterministicLabeledIdentifier (labeledEnumerationLearner O)) ∧
      (Computable₂ O.query → Computable (labeledEnumerationLearner O)) ∧
      (NontrivialCollection C → ∀ A : LabeledIdentifier,
        ∃ i p, ValidLabeledDistribution C i p ∧
          ∃ᶠ n : ℕ in Filter.atTop,
            Real.exp (-2 * (n : ℝ)) ≤ labeledIdentificationError C A p i n) :=
  HallucinationModeCollapse.theorem_3_13 C O

end GenLimit.HallucinationModeCollapse.Results
