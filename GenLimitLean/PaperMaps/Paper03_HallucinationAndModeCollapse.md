# #03 On the Limits of Language Generation map

Lean module: `GenLimit.Paper03_HallucinationAndModeCollapse`.
Declaration namespace: `GenLimit.HallucinationModeCollapse`.

## Pinned source

- Alkis Kalavasis, Anay Mehrotra, and Grigoris Velegkas, *On the Limits of
  Language Generation: Trade-Offs Between Hallucination and Mode Collapse*.
- Formalization source: [arXiv:2411.09642v3](https://arxiv.org/abs/2411.09642v3).
- Version date: 2025-10-14. Pinned PDF SHA-256:
  `097bda3ceeab7ddb244595b2817c8766f540b508abfe24a2ca8eaa0feecf3439`.
- The source correspondence has not yet received a named human audit or a
  checksum-pinned external statement-faithfulness audit.

## Scope and status

The development includes online Theorems 3.5, 3.7, and 3.9 with explicit
PMF/MOP and computation interfaces, and discrete statistical identification
and fresh-generation layers. Legacy support-valued semantic APIs remain available.
The legacy online support interface exposes an exact Boolean membership
oracle without effectivity. The new PMF constructions and bounded identifiers
have explicit sampling/support/computation certificates under the stated
oracle and ordinary effective hypotheses.

The statistical layer proves Lemma 5.1's exponential lower bound for every
randomized PMF learner, Lemma 8.1's finite-witness implication, and certified
exponential upper bounds for Propositions 3.11--3.12. Both upper bounds use
one bounded membership-query learner, fixed before the distribution is
chosen. Theorem 3.1 is now fully proved in the source's membership/tell-tale
oracle model. Its positive branch has a certified finite-query procedure;
its no-rate branch has a direct Baire-category proof, without assuming an
Angluin-1988 theorem as an axiom. Ordinary computable membership and tell-tale
procedures also give a uniformly computable learner. Theorem 3.2 is fully
proved for the source's infinite-language generation regime: exponential
upper rates with membership alone, and matching lower rates for arbitrary
randomized generators on generation-nontrivial families. Its oracle program
has primitive recursive finite query stages, computable postprocessing,
proved termination, and ordinary computability under computable membership.
Theorem 3.3 is fully proved in the same explicit infinite-language oracle
model. Exact fresh breadth has a statistical support-equality loss. A bounded
finite-label reduction transfers successful breadth to identification; the
existing necessity theorem yields a fixed-distribution limsup obstruction.
A geometric-seed sampler and terminating membership search realize the
identifiable branch. Pointwise MOP, uniform MOP, and ordinary sampler
computability have separate certificates and quantifiers.
Theorem 3.4 derives an ordinary computable word-support predicate from a
computable binary-branching local machine. Termination on every random tape
implies a uniform finite bound by Cantor compactness, and an effective search
finds such a bound. The whole-word decider follows reachable auxiliary states
and checks EOS; outer generation is allowed to continue forever.
Theorem 3.6 proves the statistical unambiguous-generation no-rate conclusion
with the source's stability and pointwise-MOP hypotheses, correcting its
printed loss polarity. An alternative semantic classifier proof gives a
stronger fixed-distribution one-half limsup bound, under failure of semantic
Angluin Condition 2, without stability or MOP.
Theorem 3.8 proves the statistical approximate-breadth no-rate result through
an alternative locking-prefix argument. Stability supplies a fixed support;
positive IID prefix mass forces it to approximate each compatible target,
and its finite omission set produces a tell-tale. The public theorem retains
the source's pointwise-MOP hypothesis.
Proposition 3.10 implements a certified last-critical identifier using the
standing membership oracle and an additional exact subset oracle. A finite
positive witness under Condition 2 gives its exponential IID rate. The
program does not read a tell-tale; computable membership and subset oracles
give ordinary uniform computability of this same learner.
Theorem 3.13 proves optimal exponential labeled identification for every
indexed family under membership access, with a randomized lower bound under
source identification nontriviality.
In the seventeen-card registry scope, all thirteen Section 3 main result
cards are full in the documented models, the three appendix result cards
have no coverage, and the aggregate definition card is partial.
Theorem 3.5 now supplies both fresh and repetition-allowing PMF generators in
the infinite-language regime. Theorems 3.7/3.9 retain pointwise ordinary MOP
and the semantic/Condition-2 boundary. Separate effective results explicitly
require uniform MOP; pointwise deciders are not assembled into a uniform one.
P03 has no named human source-faithfulness audit.

## Paper-to-Lean correspondence

| Paper item | Lean declaration | Module | Status |
|---|---|---|---|
| Definitions 5--6, support membership oracle | `SupportGenerator` | `Definitions` | Complete semantic oracle interface; computability is not certified. |
| Definitions 5--6, statistical MOP computation | `DecidableMOP`, `UniformDecidableMOP`, `OracleMOP`, `HasComputableSampler` | `BreadthModel`, `SupportMembership` | Pointwise ordinary support deciders, the stronger uniform decider interface, certified oracle programs, and a sufficient computable seeded-sampler realization. Arbitrary randomized Turing-machine descriptions are not encoded. |
| Definition 7, stability | `Stable` | `Definitions` | Complete support-stabilization predicate. |
| Definition 8, unambiguous generation | `UnambiguousAt`, `UnambiguousInLimit`, `unambiguousError` | `Definitions`, `UnambiguousModel` | Strict extended-cardinality comparison; statistical failure probability corrects the printed success-indicator polarity. |
| Definition 9, approximate breadth | `ApproximateBreadthAt`, `ApproximateBreadthInLimit`, `approximateBreadthError` | `Definitions`, `ApproximateBreadthModel` | Existing support predicate and exact statistical equation (6) failure event. |
| Definitions 1, 13--14 (statistical fragment) | `ValidDistribution`, `StatisticalIdentifier`, `identificationError`, `ExponentialIdentifies`, `NontrivialCollection` | `StatisticalModel` | Infrastructure: exact-support PMFs, ordered IID lists, randomized learners, extensional language error, and exponential upper rates. General identification rates and computation certificates are supplied by `UniversalRates` and `OracleIdentification`. |
| Equation (5), statistical generation loss | `StatisticalGenerator`, `generationError`, `ExponentialGenerates`, `FiniteWitnessGenerates` | `GenerationModel` | Full single-output loss and exponential-rate interface, retaining the sample in the joint law to test freshness. |
| Theorem 3.1 | `Results.theorem_3_1`; `theorem_3_1_mathematical` | `Results.Overview`, `OracleIdentification`, `UniversalRates` | Full in the explicit membership/tell-tale-oracle model: exclusive alternatives, admissible almost-exponential rates iff Angluin's condition, randomized exponential lower bound, and a certified oracle procedure. The proof obtains a stronger exponential upper rate. |
| Lemma 5.1 | `lemma_5_1`; `Results.theorem_3_1_exponential_lower` | `IdentificationLowerBound`, `Results.Overview` | Full for all randomized PMF learners: a fixed valid distribution has error at least `exp(-2n)` infinitely often. |
| Lemma 5.5, upper-rate conclusion through an alternative construction | `exponential_rate_implies_sublinear_rate`, `angluinLearner_finiteWitness` | `UniversalRates`, `AngluinWitnessRates` | The main theorem's upper-rate conclusion follows from a stronger bound for the explicit Angluin stage learner. The source's generic black-box batching transformation is not duplicated. |
| Lemma 5.8 | `lemma_5_8`, `lemma_5_8_frequently`, `conditionTwo_of_eventual_small_error` | `UniversalRates`, `StatisticalNecessity` | Full, with a direct Baire proof: failure of Angluin's condition gives one valid distribution with error at least one half infinitely often, hence limsup at least one half, for every randomized learner. |
| Theorem 3.2 | `Results.theorem_3_2`; `theorem_3_2` | `Results.Overview`, `OracleGeneration` | Full in the infinite-language membership-oracle model: one certified, terminating generator has error at most `D exp(-c n)` for every valid distribution; every randomized generator has a fixed hard distribution with a matching lower bound infinitely often on generation-nontrivial families. |
| Lemma 5.10; Definition 18 | `lemma_5_10`, `GenerationNontrivial`, `generation_conditional_error` | `GenerationLowerBound`, `GenerationModel` | Full randomized lower bound using a finite subfamily with nonempty finite intersection. This is distinct from identification nontriviality. |
| Lemma 5.11 | `lemma_5_11`, `generation_finiteWitness_error_bound` | `GenerationWitnessRates` | Full finite-witness-to-exponential-rate implication, reusing the IID finite-coverage infrastructure. |
| Lemma 5.13 | `lemma_5_13`, `statisticalKM_exponential` | `KMGenerationRates` | Full finite-witness guarantee and exponential rate for P01's actual stateful finite-membership-query machine. `certifiedKM` additionally gives an explicitly certified stateless search using the same critical-language argument. |
| Theorem 3.3 | `Results.theorem_3_3`; `theorem_3_3` | `Results.Overview`, `StatisticalBreadth` | Full in the explicit infinite-language oracle model: non-identifiable families have no breadth rate in the pointwise decidable-MOP class; consistent generation has the optimal exponential rate; identifiable families have certified almost-exponential breadth with the same tell-tale-oracle qualifications as Theorem 3.1. |
| Lemma 6.4 | `lemma_6_4`, `identificationError_le_breadthError_eventually`, `breadthIdentifier_computable` | `BreadthIdentification` | Full mathematical obstruction, strengthened to limsup breadth error at least one half for all semantic PMF generators. The bounded identifier is ordinarily computable when membership and support queries are uniform computable procedures. |
| Proposition 6.5, infinite-language generation regime | `proposition_6_5`, `exactFreshSampler_support`, `seededFreshSample_computable` | `ExactSampler` | Certified full-support sampler, including deletion of the finite training sample. At empty training input its support is exactly the named language. Geometric-seed upward search replaces the printed rejection sampler. |
| Theorem 3.4; Definition 15 | `Results.theorem_3_4`, `TokenGenerator`, `wordDecider_computable`, `wordDecider_spec` | `Results.Overview`, `TokenGeneration`, `TokenMembership` | Full in the encoded computable small-step machine model: ordinary word-support decidability under every-tape local termination, coherent auxiliary paths, and a final EOS check. No outer termination premise. |
| Lemmas 6.1--6.3 | `lemma_6_1`, `lemma_6_2`, `lemma_6_3`, `randomized_support_has_code` | `RandomizedSupport`; shared `Support.RandomBitMachine` | Local support decider, finite actual-read execution, uniform random-bit bound, and a finite program-code witness. Compactness completes the printed uniform-bound argument. |
| Proposition A.1 | -- | -- | Open: the non-token-by-token construction and halting-problem reduction are not formalized. |
| Theorem 3.5 | `Results.theorem_3_5`; `certifiedOnlineBreadth_of_identifiable`; effective fresh/repeating biconditionals | `Results.Overview`, `OnlineResults`, `OnlineBreadthConstruction`, `OnlineComputation` | Full in the infinite-language oracle model: both PMF output conventions, certified training/sampling, oracle MOP, conditional ordinary pointwise MOP and uniform computation. General legacy support-set theorem retained. |
| Theorem 3.6 | `Results.theorem_3_6`; `unambiguousError_frequently_ge_half`, `unambiguousError_limsup_ge_half` | `Results.Overview`, `StatisticalUnambiguous` | Full intended no-rate conclusion in the semantic/Condition-2 identifiability model, with explicit corrected loss and the source's stability/MOP hypotheses. A stronger semantic lemma gives error at least one half infinitely often under one fixed valid distribution without stability or MOP. |
| Theorem 3.6 rate interpretation | `NoUnambiguousRate.excludes_rate`, `NoUnambiguousRate.excludes_scaled_rate` | `UnambiguousModel` | Excludes every vanishing natural-domain rate and every real-domain rate with positive distribution-dependent horizontal and vertical scales. |
| Source Lemmas 7.3--7.4 and Proposition 7.2 | -- | -- | Not duplicated: the alternative proof of Theorem 3.6 uses a direct finite-sample reduction to the existing statistical necessity theorem. No infinite-IID or randomized-online derandomization claim is inferred. |
| Theorem 3.7 | `Results.theorem_3_7`; `boundedUnambiguousIdentifier_identifies`; `effective_nonidentifiable_no_stable_unambiguous` | `Results.Overview`, `OnlineResults`, `OnlineComputation` | Full in the semantic/Condition-2 model, for PMF kernels with source pointwise MOP and stability. A separate bounded computable reduction and uniform-MOP effective corollary are proved. |
| Theorem 3.8 | `Results.theorem_3_8`; `noApproximateBreadthRate_of_stable_not_identifiable` | `Results.Overview`, `StatisticalApproximateBreadth` | Full no-rate conclusion in the semantic/Condition-2 identifiability model: one fixed valid distribution has positive limsup failure. Stability is used essentially; the source-facing wrapper retains pointwise MOP. |
| Equation (6); Theorem 3.8 rate interpretation | `approximateBreadthError_source`, `NoApproximateBreadthRate.excludes_rate`, `NoApproximateBreadthRate.excludes_scaled_rate` | `ApproximateBreadthModel` | Exact failure event: support inconsistency or infinitely many omissions. Every vanishing natural-domain rate and every vanishing real-domain rate with positive distribution-dependent rescalings is excluded. |
| Source Lemmas 7.5--7.6 | -- | -- | Not duplicated as separate claims. Theorem 3.8 uses the generic finite support-locking theorem, positive finite IID-prefix mass, and a direct tell-tale construction; no infinite-IID online transfer or derandomization is inferred. |
| Theorem 3.9 | `Results.theorem_3_9`; `breadthIdentifier_identifies_of_approximate`; `effective_nonidentifiable_no_stable_approximate` | `Results.Overview`, `OnlineResults`, `OnlineComputation` | Full in the semantic/Condition-2 model, for PMF kernels with source pointwise MOP and stability. Fixed-index convergence and the uniform-MOP effective corollary are separately proved. |
| Proposition 3.10 | `Results.proposition_3_10`, `subsetIdentifier_finiteWitness`, `subsetIdentifier_computable` | `Results.Overview`, `SubsetIdentification`, `SubsetIdentificationRates` | Full in the membership/subset-oracle model: a certified finite-query last-critical identifier has the source finite-witness property and exponential IID error, without tell-tale enumeration access. Ordinary uniform computation follows when both oracles are computable. |
| Lemma 8.1 | `lemma_8_1`, `finiteWitness_error_bound` | `FiniteWitnessRates` | Full probability implication: a target-dependent finite witness and cutoff yield exponential error decay for every valid distribution, including all small sample sizes through the prefactor. No computation premise is needed for this implication. |
| Algorithm 8.2 | `finiteVersionSpaceLearner`, `finiteVersionSpace_finiteWitness` | `FiniteIdentification`, `FiniteIdentificationComputation` | Certified truth-table program: bounded version space, positive consistency, and finite-prefix minimality. Primitive-recursive queries, computable postprocessing, exact learner equality, and ordinary computation under computable membership. |
| Proposition 3.11 | `Results.proposition_3_11`; `finiteCollection_conditionTwo` (separate qualitative ingredient) | `Results.Overview`, `FiniteIdentificationComputation`, `FiniteIdentification`, `FurtherIdentification` | Full in the standing membership-oracle model: certified version-space program and all-sample exponential rate for finite-range families, allowing infinite languages. Ordinary computation when membership is computable. |
| Proposition 3.12 | `Results.proposition_3_12`; `leastConsistent_counterexample`; `finiteLanguages_conditionTwo` (separate qualitative ingredient) | `Results.Overview`, `FiniteIdentificationComputation`, `FiniteIdentification`, `FurtherIdentification` | Full / source proof repair in the standing membership-oracle model: the same certified version-space learner has exponential error for countable families of finite languages, replacing the incorrect printed least-consistent rule. |
| Definition 16; equation (12) | `ValidLabeledDistribution`, `validLabeledDistribution_iff`, `labeledIdentificationError` | `LabeledIdentificationModel` | Full source model: correct deterministic Boolean labels and full domain marginal support, ordered IID samples, extensional language error. |
| Theorem 3.13 | `Results.theorem_3_13`; `theorem_3_13_upper` | `Results.Overview`, `LabeledIdentification`, `LabeledEnumeration`, `LabeledIdentificationRates` | Full in the standing membership-oracle model: explicit bounded labeled learner, all-sample exponential upper rate, ordinary computation under computable membership, and randomized exponential lower bound on identification-nontrivial families. |
| Lemma 8.2 | `lemma_8_2`, `correctlyLabeledLaw_valid`, `labeledIdentificationError_heavyAtom` | `LabeledIdentificationLowerBound` | Full: one fixed valid law has error at least `exp(-2n)` infinitely often for every randomized learner. |
| Proposition 8.3; Lemma 8.4 | -- | -- | Not separately formalized. The direct finite-separator proof establishes Theorem 3.13 without the source infinite-IID consistency transfer or batch-size estimator. |
| Background Theorem 2.1 | -- | -- | The exact paper-facing nested-chain statement is absent. |
| Background Theorem 2.2 | `GenLimit.Angluin.semanticallyInferrable_iff_conditionTwo` | `Paper00A_PositiveDataInference.Semantic.Characterization` | Already formalized in the canonical #0A Angluin development; P03 introduces no duplicate wrapper. |
| Background Theorem 2.3 | `GenLimit.Gold.Informant.informantEnumerationLearner_identifiesFamily` | `Paper00_LanguageIdentification.Informant.Enumeration` | Already formalized in the canonical #0 Gold development; P03 introduces no duplicate wrapper. |
| Background Theorem 2.4 | `GenLimit.KM.Semantic.kleinbergMullainathan_main` | `Paper01_LanguageGeneration.Semantic` | Already formalized in the canonical #01 KM development; P03 introduces no duplicate wrapper. |
| Appendix Theorem B.1 | `subsetIdentificationProgram` (construction used by Proposition 3.10) | `SubsetIdentification`, `SubsetIdentificationRates` | The last-critical rule and finite-witness language-correctness guarantee are implemented. No separate fixed-index online identification endpoint or index-stabilizing postprocessor is claimed, so the appendix theorem card retains no claim-covering endpoint. |
| Corollary B.2 | -- | -- | Open: the support-valued best-of-both-worlds breadth generator and its guarantees are not formalized. |

## Reuse and ownership

- `IdentifiableInLimit` is only a paper-facing abbreviation for
  `GenLimit.Angluin.SemanticallyInferrable`.
- The proof of source Theorem 3.1 invokes Background Theorem 2.2,
  `GenLimit.Angluin.semanticallyInferrable_iff_conditionTwo`.  That background
  result is owned by #0A. P03 additionally proves that its explicit stage
  learner has the finite-witness property and therefore exponential IID error
  decay under the same tell-tale access. This supplies the positive branch
  of the complete Theorem 3.1. The no-rate proof derives finite tell-tales from
  statistical success by Baire category. P03 does not depend
  on the later #08 Hallucination Detection development.  The separate
  `GenLimit.Bridges.Paper03ToPaper08` module records the library-derived
  fresh-breadth/detection implication and oracle-relative equivalence without
  coupling either native umbrella.
- Theorem 3.2 reuses the actual #01 KM finite-query machine, its maximal
  finite-critical selector, and its round-termination theorem. `lemma_5_13`
  strengthens its presentation-dependent convergence to a finite positive
  witness independent of the distribution. `statisticalKM_exponential`
  gives the source machine an exponential IID rate. A stateless search over
  finite cutoffs and candidate indices gives the public computation witness;
  its termination follows from a KM round initialized above the sample.
  Theorem 3.13 reuses #0 Gold's `InformantDatum` and `InformantCompatible`;
  `labeledConsistent_iff` proves exact Boolean-test compatibility. Its rate
  proof uses finite labeled separators directly, rather than invoking
  qualitative convergence as a black-box statistical transfer.
- Theorem 3.3 reuses the actual Theorems 3.1--3.2, including the no-rate
  necessity theorem, the explicit Angluin oracle identifier, `certifiedKM`,
  and the randomized exponential generation lower bound. The finite-label
  argument also reuses `MatchesInitialSegment` and
  `eventually_leastMatching_of_target` from the online development, while
  preserving the statistical loss and probability quantifiers.
- `finiteCollection_conditionTwo` and `finiteLanguages_conditionTwo` are
  complete standalone structural lemmas motivated by Propositions 3.11 and
  3.12; they do not claim either statistical proposition.
- Shared `Support.DiscreteIID` supplies ordered IID samples, sample-support
  characterization, exact all-one-point and missing-point probabilities, a
  finite union bound, and exponential coverage of finite positive-mass sets.
  `Support.FullSupportDistribution` constructs a full-support distribution on
  any nonempty subset of naturals with a specified atom of mass at least one
  half. Neither module depends on P03 or introduces a parallel distribution
  type: both use Mathlib's `PMF`, also used by P09's distribution bridge.
- The same `lemma_8_1` and `finiteVersionSpaceLearner` are actually reused for
  both finite cases. Proposition 3.10 now also reuses `lemma_8_1` with its
  separately certified last-critical subset-oracle identifier. Theorem 3.13
  uses the corresponding labeled finite-witness implication and the same
  generic `finite_missing_exponential` theorem on pairs. Its lower bound
  directly reuses `twoTarget_conditional_error` and the heavy-atom law
  constructor; this is proved reuse, not a whole-paper equivalence.
- `AngluinWitnessRates` also reuses `lemma_8_1` for the canonical P00A stage
  learner. `computable_exponentialIdentifies_of_conditionOne` retains P00A's
  `Computable` learner certificate when membership and tell-tale enumeration
  are uniformly computable. This is proved cross-paper reuse and a rate
  strengthening, not an equivalence of the complete source papers.
- Shared `Support.DiscreteLawContinuity` proves continuity of bounded
  finite-sample randomized experiments on geometrically weighted sequence
  laws, and the dense G-delta property of surjective sequences.
  `Support.OracleTruthTable` supplies a finite-query program with primitive
  recursive query formation and a computable postprocessor. Both modules are
  actual dependencies of the new theorem.
- Shared `Support.DiscreteSampleAtoms` proves a uniform product lower bound
  for an ordered sample atom. Lemma 5.10 reuses it after an infinite pigeonhole
  argument selects one target. Shared `Support.OracleSearchProgram` certifies
  finite query stages followed by unbounded search, with a partial-recursive
  realization for computable oracles and a total computability theorem when
  termination is proved. It is an actual dependency of Theorem 3.2.
- `Support.OracleSearchMinimality` proves that a successful first search
  stage determines the result; `Support.OracleProcedureComputability`
  proves ordinary computability for a truth-table program with a computable
  oracle. Both are actual dependencies of Theorem 3.3's sampler/MOP proofs.
  The full-support geometric seed is reused from `FullSupportDistribution`.
- `SupportGenerator`, stability, unambiguity, and approximate breadth remain
  paper-local.  None was moved into the lightweight Core.
- The explicit #03/#04 comparison lives in
  `GenLimit.Bridges.Paper03ToPaper04`, so the two native paper umbrellas remain
  independent.

## Source qualifications exposed by Lean

- The online discussion around Theorem 3.5 alternates between a fresh-output
  support `K \ S_t` and a proof sentence treating the support as `K`.  Lean
  distinguishes `FreshBreadthInLimit` from `RepeatingBreadthInLimit` and uses
  `completedSupport = support ∪ sample` to validate both reductions.
- The unambiguous-error indicator printed in arXiv v3 assigns `1` to the
  success condition, while the surrounding loss/rate convention requires
  success to have value `0`. `printedUnambiguousError` records that literal
  success probability; `unambiguousError` is failure probability, and
  `unambiguousError_eq_one_sub_printed` proves the complement identity.
  Theorem 3.6 formalizes the intended failure-loss statement. It does not
  validate the literal reversed error objective.
- The Proposition 3.12 proof's least-consistent learner is incorrect for an
  arbitrary enumeration: take `L0 = {0,1}`, `L1 = {0}`, and target `L1`.
  Even after all target points are observed, the least consistent language is
  the wrong strict superset `L0`. `leastConsistent_counterexample` verifies
  this obstruction. The bounded version-space learner repairs the proof:
  finite-prefix tests eventually reject earlier strict supersets. Its
  semantic upper-rate theorem retains the proposition's conclusion and
  permits countably infinitely many distinct finite languages.
- `AdmissibleSublinearExponent` states nonnegativity, standard real-valued
  little-o sublinearity, and divergence to infinity. `rate_valid` verifies
  that `exp(-g(n))` lies in `[0,1]` and tends to zero. Theorem 3.1's printed
  quantifier `g=o(n)` is read together with Definition 13's vanishing-rate
  requirement; bounded exponents do not meet that requirement. Monotonicity
  and computability of the exponent are not added as assumptions.
- `AchievesIdentificationRate` proves the upper bound at horizontal scale
  `c=1`, a stronger conclusion than allowing a distribution-dependent scale.
  This avoids applying the source's natural-domain `R` to arbitrary real
  arguments `c*n`. The exponential lower bound has fixed constants `c=2`,
  `D=1`, directly implying the source's rescaled exponential bound.
- The explicit Angluin stage learner has a target-dependent finite witness
  and cutoff: finitely many earlier candidates are excluded by finite positive
  witnesses or by their stabilized tell-tale contents. Lemma 8.1 therefore
  gives an exponential upper bound under tell-tale access, stronger than the
  almost-exponential bound needed by Theorem 3.1. This is a library-derived
  strengthening in the stated oracle model. It does not establish the same
  bound for an arbitrary supplied black-box identifier.
- Theorem 3.2 states infinitude through `OracleFamily.infinite'`. Section 1
  (page 2) explicitly requires an infinite generation target, and the proof
  of Lemma 5.10 uses `|L| = infinity` for every candidate language. This also
  reconciles the strict fresh-output statistical loss in equation (5) with
  Definition 12's separate exhausted-finite-target exception. The latter
  convention is not substituted into the statistical loss. In particular,
  no matching lower bound is claimed for exhausted finite targets.
- The public generator is a stateless variant of KM's finite-critical search:
  enumerate encoded cutoff/candidate pairs, check maximal criticality using
  a finite membership table, and return an endpoint above the entire sample.
  The P01 stateful machine itself separately receives the finite-witness and
  exponential-rate proofs. The public procedure does not claim identical
  outputs or the same running time as that machine. No complexity bound is
  asserted. The source's post-theorem strengthening to infinitely many
  generated outputs is not part of the numbered Theorem 3.2 statement and
  is not asserted by this single-output facade.
- Definition 6 states pointwise decidability after training. Lean therefore
  distinguishes `DecidableMOP` (`for every sample, some computable support
  decider exists`) from `UniformDecidableMOP` (`one computable decider handles
  every sample`). The proof of source Lemma 6.4 uses a uniform support query
  when describing its identifier. Lean supplies that bounded identifier and
  its computation certificate when a uniform query is given; the stronger
  semantic necessity theorem from Theorem 3.1 proves the negative conclusion
  even without MOP. Thus the pointwise source class requires no hidden
  uniformization assumption in the final theorem. This strengthened
  obstruction is a library-derived result, not an additional source claim.
- Proposition 6.5 is realized by drawing a geometric seed and searching
  upward for an unseen member of the named infinite language. The numerical
  search terminates for every finite seed, and each unseen string `x` is
  returned on seed `x`. This proves the exact support, not just support
  containment. The algorithm uses membership and the finite training list;
  it does not compute arbitrary real-valued atom probabilities.
- `CertifiedBreadthPositiveBranch` uses precisely the tell-tale enumeration
  oracle of Theorem 3.1. Its sampler and per-trained-support truth-table MOP
  procedures are explicit. Computable membership gives ordinary pointwise
  MOP even if the identifier is not uniformly computable. Computable
  membership and tell-tale enumeration give one ordinary computable seeded
  sampler and a uniform support decider. The separate
  `computable_breadth_of_conditionOne` records the fully effective
  specialization. No ordinary training computability is inferred from bare
  semantic identifiability or nonuniform finite tell-tales.
- The positive breadth construction inherits the stronger exponential bound
  of the explicit Angluin learner, hence every admissible almost-exponential
  bound. As for Theorem 3.1, this strengthening is relative to the stated
  tell-tale access. Theorem 3.3 uses fresh support throughout; Remark 2's
  general conversion to repetition-allowing breadth is not needed there.
  The new online Theorem 3.5 separately realizes both conventions.

These are Codex-assisted formalization findings and have not yet been
confirmed by a named human audit.

## Formalization boundaries

- The legacy `SupportGenerator` interface remains semantic. The canonical
  online wrappers now apply it to actual PMF kernels and retain ordinary
  pointwise `DecidableMOP`. Stronger semantic negative bounds cover all
  kernels, so no source hypothesis is replaced by an assumed uniform decider.
- Online computation uses bounded Boolean searches and Mathlib `Computable`
  certificates. Positive sampling uses the existing certified numerical-seed
  sampler. No compiler from arbitrary literal randomized TM syntax is claimed.
  Bare semantic identification does not supply ordinary computable training;
  the membership/tell-tale oracle and ordinary effective branches are separate.
- Statistical distributions are PMFs on the countable domain; validity means
  support equality, not just containment. Samples retain order and repeated
  observations. Identification error is wrong-language probability, not
  wrong-index probability. Randomized learners are semantic PMF kernels,
  not encoded random-tape machines.
- Generation error is the joint probability, over the IID sample and the
  generator's output, of an output outside the target or already observed.
  Theorem 3.2's positive generator is deterministic. Its randomized lower
  bound applies to all PMF kernels, hence in particular to computable ones.
  Its two positive rate constants can depend on the target distribution;
  the generator itself is fixed before that distribution is chosen.
- Breadth error tests the whole support for equality to the target minus
  the training sample; its outer randomness is only the training sample.
  `HasComputableSampler` realizes the constructed PMF using a standard
  geometric natural seed and a total computable map. This seeded-sampler interface is separate from Theorem 3.4's encoded
  random-bit operational model. A literal TM-syntax compiler and a universal
  checker for the totality promise are not provided. No complexity or
  expected-running-time bound is asserted.
- The positive branch has an explicit `TruthTableProgram`. At sample length
  `n`, it queries language indices at most `n`, tell-tale emission stages
  below `n`, and membership of observed points. Its query list is primitive
  recursive and its postprocessor is `Computable`. It works for every valid
  supplied tell-tale enumerator and requires no completion signal,
  rate-dependent schedule, or distribution-dependent advice. As in source
  Definition 11, the oracles themselves need not be ordinary computable
  functions. Ordinary uniform computability is separately certified under
  P00A's `ConditionOne`; it is not inferred from nonuniform `ConditionTwo`.
- `finiteVersionSpaceLearner` is proved equal to one fixed `TruthTableProgram`.
  It queries observed points and domain points below sample length in
  candidate languages through that length. Query formation is primitive
  recursive and postprocessing is computable. Classical finite witnesses and
  cutoffs occur only in the correctness proof. Computable membership implies
  ordinary computation of the same learner, completing Propositions 3.11--3.12.
- Infinite IID streams, the source's generic black-box amplification proof,
  and Borel--Cantelli arguments are not needed by the alternative proof of
  Theorem 3.1. The attributed Angluin-1988 Theorem 5.6 is not assumed or
  duplicated: `StatisticalNecessity` proves the needed stronger finite-sample
  obstruction directly. Theorem 3.6 now reuses that necessity theorem through
  a semantic closest-language classifier. Theorem 3.8 instead uses an
  alternative finite support-locking/tell-tale proof. Theorem 3.13 uses a
  separate direct finite-separator proof for labeled rates; source Proposition
  8.3 and Lemma 8.4 remain unformalized as standalone black-box results.
- The source commonly works with infinite targets.  The semantic reductions
  state only the assumptions used by their proofs; they do not silently add a
  global infinite-language premise.

## Token-by-token support: Theorem 3.4

- `TokenGenerator` implements Definition 15 with natural encodings for tokens
  and auxiliary states, a computable local-machine input/output interface,
  and a fixed initial auxiliary state (the source's empty initial state is a
  special case). `none` is EOS. Lean omits this final marker from the returned
  token list, but the support predicate always requires its generation.
- The shared `RandomBitMachine.Machine` has halt, deterministic, and binary
  coin actions on encoded configurations. Its transition function is total
  computable; execution may be unbounded. `AlwaysHalts` explicitly quantifies
  over **every** infinite Boolean tape. Almost-sure local termination is not
  substituted for this promise. This model covers computable binary-branching
  operational machines; no compiler from the separate P11 TM syntax is proved.
- The interpreter allocates one tape coordinate per small step and ignores it
  on deterministic steps. `readTrace` removes this padding.
  `canOutput_iff_executes` proves that its finite output support is exactly
  the support of actual-read execution, where deterministic steps consume no
  random bits. Independent fair finite words have full support, so
  `positiveFiniteOutput_iff` equates possible output and positive probability.
- The printed Lemma 6.3 proof jumps from arbitrarily long finite runs to a
  nonterminating run. That implication needs finite-branching compactness.
  `uniform_halting_bound` proves it using compactness of Boolean tapes and
  open finite-prefix halting cylinders (the Cantor-space form of König's
  lemma). `executionBound` searches until every finite trace at a depth has
  halted. Its termination is proved; the bound is not supplied as advice.
  `Executes.reads_bounded` also bounds actual random-bit reads. Lemma 6.2 is
  packaged as the stronger finite complete execution, which makes every gap
  between reads finite. This is a proof completion, not a changed conclusion.
- The source's prefix-check prose must retain the possible auxiliary states
  conditioned on the whole prefix. `successors` enumerates precisely those
  states. `decideFrom_spec` proves the invariant through the queried word;
  `eosFrom_spec` checks termination at its end. Checking independent token
  marginals or dropping EOS would not decide complete-word membership.
- `wordExperiment` defines the finite event of producing a particular word
  followed by EOS. It rejects premature EOS and wrong tokens.
  `wordExperiment_support` proves that this event has positive mass exactly
  when one compatible execution path exists. No normalized PMF on all output
  words is assumed: the outer process may never finish.
  `wordSupport_empty_of_no_eos` checks the empty-support boundary explicitly.
- `wordDecider_computable` is an ordinary computability certificate uniform in
  the queried word for a fixed supplied machine. `wordSupport_has_code` and
  `randomized_support_has_code` supply finite partial-recursive program-code
  witnesses. These do not decide validity/totality of arbitrary descriptions.
  No time complexity, expected running time, or universal compiler is claimed.
- `decidableMOP_of_token_support` connects the result to Definition 6: any
  trained PMF family with exactly the encoded finite-word support has pointwise
  `DecidableMOP`. The compatibility premise is explicit because a possibly
  nonterminating outer process need not define a normalized output PMF.

Shared `Support.ComputableLists` and `Support.BinaryWords` supply computable
finite-list exploration. `Support.OracleSearchProgram` is actually reused
with an empty query list to realize ordinary unbounded search for the bound.
The fair-bit laws reuse `Support.DiscreteIID`; there is no paper-specific
replacement for Mathlib's `Computable`, `Nat.Partrec.Code`, or `PMF`.
Theorem 3.4 is not an undecidability result for arbitrary randomized generators;
Proposition A.1 remains open. These source-correspondence choices still need
human faithfulness review.

## Statistical unambiguous generation: Theorem 3.6

- `StatisticalStable` is exactly `Stable (statisticalSupportView G) C`.
  `statisticalStable_iff` proves the finite-list/stream bridge to the same
  raw-support equality used in source Definition 7. `DecidableMOP` retains
  Definition 6's pointwise quantifiers; no uniform support decider is inferred.
- The loss evaluates the support of the whole trained output PMF, rather
  than an individual generated point. The outer probability is over ordered
  IID training samples. Repetitions of training examples are permitted, as
  Section 3.3 specifies. `Set.encard` retains strict comparison of finite and
  infinite symmetric differences; ties, including infinite ties, fail.
- `unambiguousAt_unique` proves that two successful indices must name the
  same language. `closestLanguageIndex` chooses a successful index if one
  exists, and `closestSupportIdentifier` applies it to a trained support.
  The selection is classical and is **not** asserted computable from MOP.
  This is a proof-only classifier, not an implementation of the source's
  finite-query identification construction.
- `identificationError_le_unambiguousError` is a pointwise-event probability
  inequality. Applying `lemma_5_8_frequently`, already proved for every
  semantic randomized identifier, yields one valid target distribution on
  which unambiguous failure is at least one half infinitely often. Hence
  its limsup is at least one half and no vanishing rate is possible.
- This alternative argument needs neither stability nor MOP for its stronger
  semantic lemma. The canonical `Results.theorem_3_6` retains both source
  assumptions. The family assumption is explicitly
  `¬IdentifiableInLimit C`, equivalently failure of semantic Angluin
  `ConditionTwo`, as in the library's Theorem 3.1. It must not be read as
  merely the absence of an ordinary computable identifier when Condition 2
  still holds. No effective classifier or additional oracle is extracted.
- The source proof first makes a randomized online generator and then
  invokes an online impossibility theorem. Lean avoids that route entirely;
  a probability-one claim separately for each presentation is not silently
  turned into one deterministic random tape working for all presentations.
  Proposition 7.2 and Lemmas 7.3--7.4 remain unformalized as separate claims.
  Infinite-IID stream construction, Borel--Cantelli, and derandomization are
  inapplicable to this alternative finite-sample proof.
- `AchievesUnambiguousRate` covers natural-domain vanishing rates directly.
  `AchievesScaledUnambiguousRate` uses a real-domain rate to make the printed
  `R(c*n)` expression precise, with positive horizontal and vertical constants
  chosen after the target distribution. Positive limsup excludes both
  interfaces. No rate monotonicity, computability, or normalization assumption
  is needed. The impossibility also rules out any vanishing resampled rate
  sequence, independently of a convention for rounding a scaled sample size.

Actual reuse is from `Definitions.UnambiguousAt`, `Definitions.Stable`, the
existing support-view interface, `DiscreteIID.probability_mono`, the PMF
identification error interface, the P00A semantic Angluin characterization,
and `StatisticalNecessity.lemma_5_8_frequently`. No new shared probability
framework or machine encoding is required. These qualifications and the
source-error correction still await a named human faithfulness audit.

## Statistical approximate breadth: Theorem 3.8

- `approximateBreadthError` measures failure of the existing
  `ApproximateBreadthAt` predicate. `approximateBreadthError_source` proves
  agreement with equation (6): positive mass outside the target, or infinitely
  many omitted target points. Finite omissions, of any size, are allowed.
  Repeating training examples is allowed, as in source Section 3.3.
- `StatisticalStable` and `DecidableMOP` are reused unchanged. Applying the
  generic `Support.Locking.exists_lockingSequence_of_converges_with_base`
  to the **entire support set** gives one finite target-contained prefix
  after which every target-contained finite continuation has the same
  support. This is a consequence of stability on every exact presentation;
  no computable locking prefix or known stabilization time is assumed.
- Shared `Support.DiscreteSamplePrefix` proves the concatenation law for
  finite ordered IID samples. If every supported continuation after a prefix
  lies in an event, that event has probability at least the prefix atom's
  mass. Full support makes this mass positive, independently of the total
  sample size. `locked_approximate_failure_limsup_pos` applies this to a bad
  locked support, giving a fixed positive lower bound after the prefix.
- For the contrapositive, suppose no valid target distribution has positive
  limsup failure. A locked support `S` must then satisfy approximate breadth
  for its target `K`. Construct a finite set from the locking-prefix contents,
  all of `K \ S`, and one element of `K`. The extra element ensures a
  candidate language containing this set is nonempty and admits a valid PMF.
  Empty and other finite target languages are handled separately by taking
  the entire target as its tell-tale.
- If a candidate `L` lies between that finite set and `K`, it inherits the
  same locked support, since every `L`-contained continuation is `K`-contained.
  Its full-support law also forces `S ⊆ L`. The tell-tale already places
  `K \ S` inside `L`, hence `K ⊆ L`. This proves semantic Angluin Condition 2,
  contradicting the same non-identifiability boundary used elsewhere in P03.
- The stronger semantic no-rate lemma needs stability but not MOP.
  `Results.theorem_3_8` retains both source assumptions. No uniform support
  decider is extracted from pointwise MOP. No assertion under merely
  ordinary effective non-identifiability when Condition 2 holds is inferred.
- This is a direct finite-sample alternative to source Section 7.4.
  Lemmas 7.5--7.6 remain unformalized as separate statements. Infinite-IID
  stream spaces, almost-sure online transfer, and randomized online
  derandomization are inapplicable to this proof. There is no claim that one
  deterministic random tape can be chosen for all presentations.
- `NoApproximateBreadthRate` supplies one fixed valid distribution with
  positive limsup error, independent of any proposed rate. It excludes every
  vanishing natural-domain rate and real-domain `R(c*n)` with positive
  distribution-dependent horizontal and vertical constants. No monotonicity
  or computability of the rate, uniform lower bound such as one half, or time
  complexity guarantee is asserted.

Actual reuse is from the neutral locking theorem already used by P00A,
the P00A semantic Angluin characterization, the existing P03 support/stability
and approximate-breadth predicates, and shared `DiscreteIID` and
`FullSupportDistribution`. No new machine encoding or probability axioms are
needed. The locking prefix, omission set, and tell-tale are classical proof
witnesses; this negative result does not construct an effective identifier.
Source correspondence still awaits a named human faithfulness audit.

## Subset-oracle identification: Proposition 3.10

- `Core.SubsetOracle` is a paper-independent exact Boolean interface for
  indexed-language inclusion. Oracle correctness is semantic; ordinary
  computability is separate. The standing `MembershipOracle` is also explicit.
  The proposition does not infer point membership from inclusion queries.
- `subsetIdentificationProgram` is a fixed `TruthTableProgram`. For a sample
  of length `n`, it queries membership of observed points in candidates below
  `n` and inclusion of each candidate in every earlier candidate. These are
  finite nonadaptive lists with primitive-recursive query formation. Its
  computable postprocessor selects the last sample-consistent candidate
  contained in every earlier sample-consistent candidate.
- This follows the full-inclusion last-critical rule in Appendix B.1. The
  zero-based indices `0,...,n-1` correspond to source indices `1,...,n`.
  When no critical candidate exists, Lean returns default index zero; the
  source's informal fallback is immaterial once the finite witness is seen.
  No output equality with P01's separate membership-only cutoff machine or
  running-time bound is asserted.
- For target index `i`, take its finite tell-tale and one positive point
  outside each earlier language which fails to contain the target. Once
  these points are observed and sample length is at least `i+1`, the target
  is critical. The selected last critical candidate is at or after `i`.
  Any later one is contained in the target and contains its tell-tale,
  forcing equality. `subsetIdentifier_finiteWitness` proves this for every
  target-contained ordered sample, independently of its distribution.
- Tell-tales and the finite witnesses occur only in the proof. Neither a
  tell-tale enumeration oracle, a completion test, distribution-dependent
  advice, nor a rate parameter is passed to the learner. The same program
  works for every valid pair of membership and subset oracles.
- `lemma_8_1` converts the finite witness into `ExponentialIdentifies`:
  one distribution-independent learner has error at most `D * exp(-c*n)`
  for every sample size, with positive constants depending on the valid
  target distribution. This is the source's `exp(-n)` rate class under its
  allowed rescalings, not a universal coefficient-one numerical bound.
- `subsetIdentifier_computable` certifies ordinary computation when **both**
  oracle functions are computable. This is additional to the oracle-relative
  theorem. No computable inclusion oracle, tell-tale enumerator, or ordinary
  learner is inferred from nonuniform `ConditionTwo` alone.
- Statistical loss compares the denoted language, allowing duplicate indices.
  The raw last-critical index may change among equivalent target names. The
  source mentions fixed-index postprocessing for Appendix B.1; that separate
  online endpoint and Appendix B.2's breadth generator remain unformalized.
  Implementing their shared selection rule is not counted as full appendix
  coverage. Source correspondence still awaits a named human audit.

Actual reuse is from the existing `TruthTableProgram`, `tableLookup_map`,
oracle-procedure computation theorem, and Lemma 8.1's finite-IID bounds.
The new shared `ComputableLastSearch` gives certified bounded maximum search.
The new foundational subset-oracle vocabulary is exported by `GenLimit.Core`.
Bridges to P00A's effective inclusion condition or other papers' inclusion
interfaces remain prospective; no such equivalence is asserted here.

## Propositions 3.11--3.12 and Theorem 3.13: computation and labeled rates

`FiniteIdentificationComputation` certifies the existing version-space
learner without changing either finite-case rate proof. The query list is
primitive recursive; `finiteIdentificationPost_computable` certifies its
postprocessor; `finiteIdentificationProgram_eq_learner` proves exact equality
of outputs. No subset queries, tell-tale access, rate advice, or distribution
advice is used. Proposition 3.12 retains the repaired construction described
above; the original least-consistent rule is not validated.

`LabeledIdentificationModel` reuses Gold's `InformantDatum = ℕ × Bool`.
`validLabeledDistribution_iff` proves Definition 16 exactly in marginal form:
the marginal covers the whole domain and every supported label agrees with
the target. `labeledIdentificationError` is equation (12)'s expected
wrong-language indicator; it permits repeated indices for the same language.
The learner is fixed before the law is chosen. Upper constants are positive
and distribution dependent, as permitted by the source rate convention.

At length `n`, `labeledEnumerationLearner` tests the first `n` indices against
every observed label and returns the least consistent index, or zero when
none exists. `labeledConsistent_iff` connects this Boolean check to Gold's
existing `InformantCompatible`. `labeledEnumerationLearner_computable`
certifies ordinary uniform computation under computable membership. The
finite algorithm is membership relative; arbitrary semantic membership
oracles are not asserted ordinarily computable. No literal TM compiler,
running-time bound, estimator, or subset oracle is supplied or needed.

For target index `i`, finitely many correctly labeled points exclude every
extensionally wrong candidate at or below `i`. Once the sample contains
those points and has length at least `i+1`, the least consistent index
therefore denotes the target. The witnesses may be chosen classically;
they are used only in the proof, never by the learner. Generic finite IID
coverage gives error at most `D exp(-c n)` for all sample sizes. This direct
argument replaces the source batching construction; Proposition 8.3 and
Lemma 8.4 are not separately claimed as formalized.

`lemma_8_2` retains source `NontrivialCollection`: two distinct languages
share a positive point `x`. A full-support domain law with mass at least one
half at `x` is mapped through each correct labeling function. Both resulting
laws are valid and put at least half their mass at `(x,true)`. On the sample
consisting only of that atom, the existing two-target argument forces error
at least one half for one target. Infinite pigeonhole fixes one target and
law, giving error at least `exp(-2n)` infinitely often for every randomized
kernel. The construction avoids the apparent `K \ L` ambient-domain typo in
the printed Lemma 8.2 and does not require splitting residual mass between
possibly empty positive/negative subsets. This is a proof-level repair of
the distribution construction, not a change to Definition 16 or the theorem.
Source correspondence and these qualifications await human audit.

## Online completion: Theorems 3.5, 3.7, and 3.9

`OnlineComputation` reuses the existing `breadthIdentifier`; it does not add a
second finite-label algorithm. Its new convergence theorem gives one fixed
least target index along every positive presentation. Eventual completed-
support equality supplies the reduction for both forms of exact breadth and
for stable approximate breadth. The source unambiguous reduction is realized
by `boundedUnambiguousIdentifier`: sample consistency, prefix coverage, and a
bounded least-index search. It also stabilizes syntactically to the least
target index. Both functions are ordinarily computable when family and
support membership are uniformly computable. The classical least equivalent
index and convergence thresholds are proof witnesses, not algorithm inputs.

`OnlineBreadthConstruction` gives actual PMF generators, rather than only
support sets. `identifiedBreadth` has support exactly the conjectured language
minus the sample; `identifiedRepeatingBreadth` has the whole conjectured
language as support. They use the already certified `samplerProgram` and the
same membership/tell-tale identifier as Theorems 3.1/3.3. After that identifier
stabilizes, both breadth guarantees hold on every positive presentation.
Infinite candidate languages guarantee a nonempty fresh law and termination
on every finite training input. This is the same explicit generation regime
as Theorems 3.2/3.3; exhausted finite targets are not assigned an empty PMF.
The older general support-set theorem remains available without this premise.

`CertifiedOnlineBreadthPositiveBranch` includes both online guarantees,
pointwise oracle-MOP certificates, ordinary pointwise MOP under computable
family membership, and ordinary uniform seeded sampling/support deciders
when training is also computable. The positive theorem does not declare
nonuniform ConditionTwo an effective tell-tale procedure. Computable
membership alone is sufficient for each trained support's MOP, because its
fixed hypothesis index and finite sample can be parameters of the decider.
Uniformity across training inputs requires the additional training certificate.

`Results.theorem_3_7` and `Results.theorem_3_9` now quantify over PMF generators
with the source `DecidableMOP` and `StatisticalStable` hypotheses. They follow
from the stronger existing support-semantic obstructions and thus also rule
out every computable randomized generator in that model. Neither proof needs
to extract a decider from pointwise existence, compile a literal TM, or fix
one random tape uniformly across all presentations. The non-identifiability
hypothesis is the same semantic/ConditionTwo boundary as the other canonical
P03 results, not merely failure of ordinary effective inference.

For that separate effective question,
`effective_identification_iff_fresh_breadth` and its repeating counterpart
prove exact biconditionals using P00A `EffectiveInferrable`, computable seeded
sampling, and `UniformDecidableMOP`. The 3.7/3.9 effective corollaries use the
new bounded identifiers and explicitly assume uniform MOP. These stronger
uniform hypotheses must not be silently replaced by source pointwise MOP.
The preceding ordinary/nonuniform distinction and the infinite-language
sampling regime remain material qualifications for human faithfulness audit.

## Suggested reading order

1. `Definitions.lean`
2. `OnlineReductions.lean`
3. `PositiveBreadth.lean`
4. `Results/Overview.lean`
5. `FurtherIdentification.lean`
6. `StatisticalModel.lean`
7. `IdentificationLowerBound.lean`
8. `FiniteWitnessRates.lean`
9. `FiniteIdentification.lean`
10. `UniversalRates.lean`, `AngluinWitnessRates.lean`, `StatisticalNecessity.lean`
11. `OracleIdentification.lean`
12. `GenLimit.Support.DiscreteIID`, `FullSupportDistribution`, `DiscreteLawContinuity`, `OracleTruthTable`
13. `GenerationModel.lean`, `GenerationWitnessRates.lean`, `KMGenerationRates.lean`
14. `GenerationLowerBound.lean`, `OracleGeneration.lean`
15. `GenLimit.Support.DiscreteSampleAtoms`, `OracleSearchProgram`
16. `BreadthModel.lean`, `BreadthIdentification.lean`
17. `ExactSampler.lean`, `SupportMembership.lean`, `BreadthConstruction.lean`
18. `StatisticalBreadth.lean`, then `Results/Overview.lean`
19. `GenLimit.Support.OracleSearchMinimality`, `OracleProcedureComputability`
20. `RandomizedSupport.lean`, `TokenGeneration.lean`, `TokenMembership.lean`
21. `GenLimit.Support.RandomBitMachine.Basic`, `Compactness`, `Effective`, `Semantics`, `Probability`
22. `UnambiguousModel.lean`, `StatisticalUnambiguous.lean`
23. `ApproximateBreadthModel.lean`, `StatisticalApproximateBreadth.lean`
24. `GenLimit.Support.Locking`, `GenLimit.Support.DiscreteSamplePrefix`
25. `SubsetIdentification.lean`, `SubsetIdentificationRates.lean`
26. `GenLimit.Core.SubsetOracle`, `GenLimit.Support.ComputableLastSearch`
27. `FiniteIdentificationComputation.lean`
28. `LabeledIdentificationModel.lean`, `LabeledEnumeration.lean`
29. `LabeledIdentificationRates.lean`, `LabeledIdentificationLowerBound.lean`, `LabeledIdentification.lean`
30. `OnlineComputation.lean`, `OnlineBreadthConstruction.lean`, `OnlineResults.lean`
31. `GenLimit.Bridges.Paper03ToPaper04`

## Verification

```text
lake build GenLimit.Paper03_HallucinationAndModeCollapse
lake build GenLimit.Bridges.Paper03ToPaper04
lake build
```

No `sorry`, `admit`, or project-defined axiom occurs in the P03 modules.
The statistical extension requires the usual Lean kernel and generated
registry axiom checks; these do not establish source faithfulness or a human
audit. Separate complexity bounds and a compiler from literal Turing-machine syntax
are outside the current encoded recursive-function/operational model. Existing umbrella integration and the pinned `KMV25` citation
are retained; no new paper or claim inventory is introduced.
