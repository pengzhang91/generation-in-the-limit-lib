import GenLimit.Paper03_HallucinationAndModeCollapse.PositiveBreadth
import GenLimit.Paper03_HallucinationAndModeCollapse.FiniteIdentificationComputation
import GenLimit.Paper03_HallucinationAndModeCollapse.LabeledIdentification
import GenLimit.Paper03_HallucinationAndModeCollapse.IdentificationLowerBound
import GenLimit.Paper03_HallucinationAndModeCollapse.OracleIdentification
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

This facade exposes full oracle-relative Theorems 3.1--3.3, online
Theorems 3.5, 3.7, and 3.9 with explicit PMF/MOP and computation interfaces,
certified exponential upper rates
for Propositions 3.11--3.12, and optimal labeled identification in Theorem
3.13. Theorem 3.1 has a certified truth-table oracle
procedure and a direct Baire-category no-rate proof. Admissible exponents
are nonnegative, divergent, and sublinear, as required for vanishing rates.
Theorem 3.2 uses membership alone and explicitly assumes infinite languages;
its certified search terminates on every finite sample. Its lower bound applies
to arbitrary randomized generators under generation-specific nontriviality.
Theorem 3.3 adds statistical exact fresh breadth: a no-rate reduction for
non-identifiable families, a certified full-support sampler for the positive
branch, pointwise support-membership certificates, and explicit ordinary
computation specializations. Its tell-tale access is the same as Theorem 3.1.
Theorem 3.4 gives ordinary computable finite-word support membership for
token-by-token generators with every-tape-total local machines. The proof
derives an effective finite exploration bound using Cantor compactness,
tracks compatible auxiliary states, and explicitly checks the final EOS.
Outer generation need not terminate. Machines use computable encoded
small-step transitions; this is not a compiler from a literal TM syntax.
Theorem 3.6 proves statistical unambiguous-generation impossibility with the
source's stability and pointwise-MOP hypotheses. The failure loss corrects
the printed success-indicator polarity. A semantic closest-language reduction
and the existing statistical necessity theorem give a stronger fixed-
distribution one-half limsup bound without stability/MOP, under failure of
semantic Angluin Condition 2. No computability of that proof-only classifier
or randomized online derandomization is asserted.
Theorem 3.8 proves the statistical approximate-breadth no-rate conclusion.
Stability supplies a support-locking prefix. Its positive IID mass forces
the locked support to approximate each compatible target; the finite omission
set then yields an Angluin tell-tale. This alternative finite-sample proof
keeps all quantifiers explicit and needs no infinite-IID online transfer.
Proposition 3.10 adds a certified last-critical identifier using membership
and subset queries, with no tell-tale enumeration access. Its finite-witness
guarantee and Lemma 8.1 give exponential statistical error; computable
membership and subset oracles give ordinary uniform computation.
Propositions 3.11--3.12 certify the bounded membership-only version-space
program and its ordinary computation when membership is computable.
Proposition 3.12 repairs the printed least-consistent construction.
Theorem 3.13 uses bounded least-consistent labeled enumeration, finite IID
coverage, and a fixed-distribution lower bound for every randomized learner.
Validity is equivalent to full marginal support with correct deterministic
labels. The source batching/estimator proof is replaced by finite separators.
Theorem 3.5 realizes both fresh and repetition-allowing breadth with certified
samplers in the infinite-language regime. Its ordinary pointwise MOP assumes
computable membership; uniform sampling also requires computable training.
Theorems 3.7/3.9 retain pointwise MOP and the same semantic/Condition-2
non-identifiability boundary as Theorems 3.6/3.8. Separate effective results
use uniform MOP explicitly; pointwise deciders are not assembled into a
uniform procedure. Legacy semantic wrappers remain available.
Each wrapper delegates to its canonical proof module.
-/

namespace GenLimit.HallucinationModeCollapse.Results

open GenLimit.Generic

/-- Theorem 3.1: exactly one rate alternative holds, Angluin's condition
characterizes the positive branch, and the exponential lower bound holds for
every randomized learner. The last conjunct provides a certified finite-query
realization relative to membership and an existentially chosen valid
tell-tale oracle, with a stronger exponential upper bound. -/
theorem theorem_3_1 (C : Generic.LanguageFamily ℕ) (O : GenLimit.MembershipOracle C)
    (hC : NontrivialCollection C) :
    ((AlmostExponentialIdentifiable C ∧ ¬NoIdentificationRate C) ∨
      (¬AlmostExponentialIdentifiable C ∧ NoIdentificationRate C)) ∧
      (AlmostExponentialIdentifiable C ↔ GenLimit.Angluin.ConditionTwo C) ∧
      (∀ A : StatisticalIdentifier, ∃ i p, ValidDistribution C i p ∧
        ∃ᶠ n : ℕ in Filter.atTop, Real.exp (-2 * (n : ℝ)) ≤ identificationError C A p i n) ∧
      (GenLimit.Angluin.ConditionTwo C →
        ∃ emit : ℕ → ℕ → Option ℕ,
          (∀ i, GenLimit.Angluin.IsEnumeratedTellTale C i (GenLimit.Angluin.enumeratedSet emit i)) ∧
          ExponentialIdentifies C (deterministicIdentifier
            (identificationProgram.run (identificationOracle O emit)))) :=
  HallucinationModeCollapse.theorem_3_1 C O hC

/-- Theorem 3.2: a membership-only generator achieves exponential fresh-
generation rates for every indexed infinite-language family. The rate is
optimal on generation-nontrivial families, even against randomized generators.
Ordinary uniform computability follows when membership is computable. -/
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

/-- The exponential lower-bound component of Theorem 3.1, proved through
Lemma 5.1. Retained as a direct component-level entry point. -/
theorem theorem_3_1_exponential_lower
    (C : Generic.LanguageFamily ℕ) (hC : NontrivialCollection C)
    (A : StatisticalIdentifier) :
    ∃ i p, ValidDistribution C i p ∧
      ∃ᶠ n : ℕ in Filter.atTop,
        Real.exp (-2 * (n : ℝ)) ≤ identificationError C A p i n :=
  HallucinationModeCollapse.lemma_5_1 C hC A

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

/-- Semantic exponential upper rate for a finite collection, including
collections containing infinite languages. -/
theorem proposition_3_11_semantic (C : Generic.LanguageFamily ℕ)
    (O : GenLimit.MembershipOracle C) (hRange : (Set.range C).Finite) :
    ExponentialIdentifies C (deterministicIdentifier (finiteVersionSpaceLearner O)) :=
  HallucinationModeCollapse.proposition_3_11_semantic C O hRange

/-- Semantic exponential upper rate for a countable collection of finite
languages, using the repaired bounded version-space learner. -/
theorem proposition_3_12_semantic (C : Generic.LanguageFamily ℕ)
    (O : GenLimit.MembershipOracle C) (hfinite : ∀ i, (C i).Finite) :
    ExponentialIdentifies C (deterministicIdentifier (finiteVersionSpaceLearner O)) :=
  HallucinationModeCollapse.proposition_3_12_semantic C O hfinite

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

/-- Legacy semantic support-oracle form of Theorem 3.5: under the paper's uniform
family-membership oracle, positive-data identification is equivalent to
fresh breadth in the limit. -/
theorem theorem_3_5_semantic
    {C : Generic.LanguageFamily ℕ}
    (O : GenLimit.MembershipOracle C) :
    IdentifiableInLimit C ↔
      ∃ G : SupportGenerator, FreshBreadthInLimit G C :=
  HallucinationModeCollapse.identifiableInLimit_iff_freshBreadthInLimit O

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

/-- Legacy impossibility form of the semantic online core of Theorem 3.7. -/
theorem theorem_3_7_semantic
    {C : Generic.LanguageFamily ℕ}
    (hnot : ¬IdentifiableInLimit C) :
    ¬∃ G : SupportGenerator,
      Stable G C ∧ UnambiguousInLimit G C :=
  HallucinationModeCollapse.not_exists_stable_unambiguousInLimit_of_not_identifiableInLimit
    hnot

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

/-- Legacy impossibility form of the semantic online core of Theorem 3.9. -/
theorem theorem_3_9_semantic
    {C : Generic.LanguageFamily ℕ}
    (hnot : ¬IdentifiableInLimit C) :
    ¬∃ G : SupportGenerator,
      Stable G C ∧ ApproximateBreadthInLimit G C :=
  HallucinationModeCollapse.not_exists_stable_approximateBreadthInLimit_of_not_identifiableInLimit
    hnot

end GenLimit.HallucinationModeCollapse.Results
