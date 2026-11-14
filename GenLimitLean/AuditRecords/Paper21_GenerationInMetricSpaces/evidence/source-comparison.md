# P21 — Stage 2 source comparison

All fourteen scoped source claims are represented at the level of their main statements. Eight slot groups contain faithful extensions of the source assumptions; six have equivalent main claim content. There is no established missing source component or substantively different main claim. This does not certify theorem proofs. Two distinctions matter: all-radius UUS for Example 4.5 is assembled from native interfaces, and Example 4.8 has a literal reservoir-index variant despite matching the full existential threshold classification.

## Identity, freezes and scope

Pinned source: Li–Raman–Tewari, *On Generation in Metric Spaces*, arXiv:2602.07710v2. Original supplied PDF SHA-256: `b4e14e33fce18aa5d970a49d4886a647d9de888e8de29fab12ff8cda0afacfbc`. The title page prints October 27, 2026; the arXiv version mark/manifest date is October 24, 2026. Printed page numbers equal one-based PDF page numbers. The source inventory was completed at 2026-11-14T06:59:51.740952+00:00 and frozen at 07:00:31.154890+00:00 before comparison authorization. Stage 1 was frozen at 06:52:00.173731+00:00. All six frozen report hashes were verified before writing this report.

The exact Lean snapshot is the supplied Stage 1 interface package (original-source snapshot metadata hash `e56b617a39899cb9acfd94b61e19680934bf78aa1f40d8d07d8e7f1d10bee1fc`). Original repository source was not accessed or rehashed. All 18 target types and 65 recursive definition values were rechecked directly in kernel-interface JSON, with selected native census types/definitions added for supporting facts. Native names were locators only; meanings below come from types or defining values. No raw Lean comments, theorem proof bodies, owner/PaperMap/registry material, old audit, or Stage 3 context was read.

## Independent source inventory and shared comparison

The [frozen source inventory](source-inventory.md) contains the complete independent fourteen-slot source reading, global assumptions G1–G9, source locators and visual references. The original 33 pages were read and decisive formulas on 31 pages inspected before Stage 1 access. It remains unchanged. This report cross-references it rather than repeating source passages or Stage 1 exact types.

**S1.** Supports replace binary hypotheses: a class is Set (Set X). This is the standard extensional identification h <-> supp(h); no countability restriction is introduced. All learner outputs are single points, with no probabilities, losses/distributions, or randomization.

**S2.** The generator takes a length and its ordered Fin-length prefix; it is a total map, including the empty history. Streams are Nat-indexed; the paper starts at 1. Repetitions/order are retained by the prefix, while samples are finite sets. This is a reindexing of finite-history access, not access to the target or the future.

**S3.** InClosedNeighborhood rho A r y is forall eta>r, exists x in A with rho(x,y)<eta. On nonempty metric sets this matches the paper inf-distance<=r, including nonattained infima; on finite samples it is membership in a union of closed balls. The definition is not an attained <= witness for infinite sets. Formal empty neighborhoods are empty.

**S4.** CoveringNumberAtLeast universally lower-bounds every ambient finite cover size; CoveringNumberEq also supplies a cover of the claimed size. For the positive metric scales in the paper, finite samples self-cover, so these encode N>=d and N=d. Internal-cover centers are explicitly in the common core. No numeric dimension is defined: finite dimension is existence of a natural upper bound on witness sizes, equivalent to C<infinity.

**S5.** The common core on an inconsistent sample is the entire type, whereas source closure is bottom. IsScaleClosureWitness explicitly requires nonempty version space, so this difference cannot create a closure-dimension witness. Empty-history/zero-threshold conventions add at most a zero-size case, not a new positive-metric existence conclusion.

**S6.** Limit generation has one generator before target/stream and an eventual time after them, with coverage required. Uniform has one generator and one threshold before all targets/positive streams. Non-uniform has one generator before target, then a target-dependent threshold before all positive streams. Both threshold notions guarantee every later output from any triggering round; coverage is not required. Novelty excludes observations, not prior generated outputs.

**S7.** UniformlyUnboundedSupportAt requires each member nonempty and, on each covering stream, forall d exists a prefix whose covering lower bound is d. Prefix covering lower bounds are monotone, so this matches divergence to infinity at the source positive metric scales. Without the source UUS assumptions, the broader formal threshold predicates can be vacuous when thresholds are unreachable.

**S8.** Distance is an arbitrary real-valued function unless target hypotheses add laws. Several theorems deliberately require fewer laws than a separable metric and no UUS. These are faithful extensions when restricted to the source setting, not missing assumptions accidentally attributed to the source. Explicit Nonempty binders clarify the paper total-output convention.

**S9.** All scoped conclusions are semantic function existence/properties. Classical.propDecidable, Classical.choose and Classical.choice are not ordinary computability or a finite-ERM implementation. Appendix E supplies separate oracle/conditional-search statements; no slot claims those as an executable implementation. The named Example 4.8 definition is inspected separately below.

## Full comparison matrix

“Equivalent” concerns the mathematical claim in the paper setting; native construction/rule variants remain separately listed. “Faithful generalization” means the exported semantic theorem restricts to the source result while covering a broader domain. It does not mean executable implementation or reachable thresholds outside UUS.

| Slot | Source (printed/PDF pages) | Target(s), in `GenLimit.MetricSpaces.Results` | Correspondence | Decisive qualification |
|---|---|---|---|---|
| C01 | 6, 14, 15, 31, 32, 33 | `theorem_3_1` | faithful-generalization | Finite bound matches C<infinity; weaker geometry/support assumptions. |
| C02 | 6, 15, 16 | `corollary_3_2`, `corollary_3_4` | faithful-generalization | Both finite/uniform and countable/non-uniform components; e_g=e_a retained. |
| C03 | 6, 16 | `theorem_3_3` | faithful-generalization | Increasing cover and every subclass dimension bound retained. |
| C04 | 7, 17 | `theorem_3_5` | equivalent | Both r-UUS components and all source scale boundaries retained. |
| C05 | 7, 8, 28 | `corollary_4_3`, `theorem_4_1`, `theorem_4_2` | faithful-generalization | All three components; UUS dropped for 4.2; real scalar field explicit in 4.3. |
| C06 | 8, 29 | `theorem_4_4` | faithful-generalization | UUS iff plus unconditional generation iff at independent positive pairs. |
| C07 | 9, 29, 30 | `theorem_4_6`, `theorem_4_7` | faithful-generalization | Opposite adversary directions; all three notions and weak equalities. |
| C08 | 11, 30, 31 | `theorem_4_10` | faithful-generalization | Both independent transfers; rho2<=M*rho1, divide by M. |
| C09 | 13, 28, 29 | `proposition_D_1` | faithful-generalization | All three iff statements; native discrete UUS iff also checked. |
| C10 | 8, 18, 19, 20, 21, 22 | `example_4_5` | equivalent | Same fixed class; all-radius UUS by native interface assembly. |
| C11 | 9, 10, 18, 19, 20, 22, 23, 24 | `example_4_8` | equivalent | Full strict AND classification; named classical rule; exponent-zero reservoir variant. |
| C12 | 9, 10, 17, 18, 24, 25, 26 | `example_4_9` | equivalent | One class, all four regimes; empty middle interval allowed. |
| C13 | 11, 17, 18, 26, 27 | `example_4_11` | equivalent | One class/metric pair; both UUS conjuncts; 1/2 map factor squares to 1/4. |
| C14 | 6, 15 | `example_B_3` | equivalent | Exactly two targets; strict reversed scales; no invented limit negation. |

## Target dossiers

### C01 — Uniform generation iff finite scale-closure dimension

The iff is the source uniform-generation characterization on its intended nonempty, separable metric, r-UUS, positive-scale domain. The exported theorem also covers arbitrary nonempty types, diagonal-zero real functions, nonnegative adversary scale and arbitrary generator scale, without UUS or separability.

- **Theorem 3.1 — faithful-generalization:** Same uniform quantifier order and finite internal-cover witness criterion; formal finite-bound predicate is equivalent to C<infinity.
- **Lemma B.2 quantitative context — represented-by-supporting-statements:** The dimension-bound helper uses D+1 to rule out finite internal covers. scaleClosureGenerator selects a novel common-core point if one exists. The exported iff does not expose a numeric minimal dimension or an exact sample-complexity equality.

**Strength and scope.** Drops separability, UUS, symmetry, triangle and separation; permits e_a=0 and e_g outside positive/r-bounded source regime. Nonempty X is explicit in Lean and tacitly needed by the source total-generator convention. Formal conditional generation outside UUS may be vacuous. The source-domain iff is recovered without strengthening a source hypothesis.

**Representation/access.** S1-S8; realizable finite samples and internal centers match. Bottom versus universal core on inconsistent histories is guarded away. There is no numeric dimension-value API.

**Algorithm scope.** Semantic existence. Native scaleClosureGenerator performs a classical existence test and choice of a fresh core point, with a default output. It matches the source choice-based sufficiency scheme, not Appendix E max-min/finite-ERM execution.

**Checked anchors.** `Results.theorem_3_1` (Overview:51). Native support: `scaleClosureGenerator`, `scaleClosureGenerator_spec`, `finite_scaleClosureDimension_implies_uniform`, `commonCore_not_hasFiniteInternalCover_of_dimension_bound`.

### C02 — Finite and countable class consequences

Both grouped corollaries are present: finite H gives uniform generation and countable H gives non-uniform generation, at e_g<=e_a. The formal predicates and target-dependent/common threshold dependencies agree.

- **Corollary 3.2 — faithful-generalization:** Finite H; same U conclusion. Lean only needs a nonempty type, diagonal zero, 0<=e_a and e_g<=e_a.
- **Corollary 3.4 — faithful-generalization:** Countable H, including finite/empty classes; one generator with target-dependent thresholds. Same relaxed assumptions.

**Strength and scope.** No separable-space or r-UUS hypotheses; e_a=0 and negative e_g allowed. The class-cardinality distinction and weak boundary e_g=e_a are retained. An abstract Countable proof is not an effective listing; outside UUS a threshold guarantee can be vacuous.

**Representation/access.** S1-S8. Countability is of the class, not X. The common generator is selected before targets; d_h before streams.

**Algorithm scope.** Semantic existence. No effective finite/countable enumeration, metric oracle or per-round search is supplied by either target.

**Checked anchors.** `Results.corollary_3_2` (Overview:64); `Results.corollary_3_4` (Overview:100).

### C03 — Non-uniform generation via increasing finite-dimension cover

The countable non-decreasing cover iff matches Theorem 3.3, including both directions, exact union with H and separately finite dimensions of the subclasses. It is generalized beyond the paper metric/UUS regime.

- **Theorem 3.3 (i) iff (ii) — faithful-generalization:** Exists one increasing Nat-indexed cover with a separate finite dimension bound at each index; no global bound on the cover is introduced.

**Strength and scope.** Nonempty type, diagonal zero, e_a>=0 suffice; no UUS, separability or sign condition on e_g. Monotonicity of the cover is retained; a merely arbitrary countable family is not substituted. Explicit nonempty-domain binder and semantic/vacuous-threshold qualifications S7-S8 apply.

**Representation/access.** S1-S8. A Nat-indexed sequence is countable; the members themselves need not be countable. Existential dimension bounds may depend on the index.

**Algorithm scope.** Existential cover and generators, with no effective class-membership tests, index extraction or threshold oracle stipulated.

**Checked anchors.** `Results.theorem_3_3` (Overview:84).

### C04 — Finite-union closure fails on the real line

The real-line failure of two-class finite-union closure is fully represented with all positive scales up to r and both component r-UUS hypotheses. The union negation rules out every semantic limit generator.

- **Theorem 3.5 — equivalent:** For every r>0 and 0<e_a,e_g<=r, two real classes each r-UUS and uniformly generatable have a union not limit-generatable at those scales.
- **construction context — faithful-reindexing:** FiniteUnion.anchor is 3r(n+1)+offset; Admissible places each stream point strictly between offset 0 and e_a anchors; targetClass is the anchor range union that stream range. This is the source A/B/S construction with zero-based indices.

**Strength and scope.** All existential witness dependencies and both scale upper boundaries match. The target does not name H1,H2 or extract their generators; native definitions describe the corresponding support families without inspecting a proof witness.

**Representation/access.** S1-S7 with ordinary real dist=absolute difference. UUS for the union follows semantically from memberwise UUS but is not needed as an extra target conjunct.

**Algorithm scope.** No effective adversary or source-proof diagonal execution is certified. Component and union statements quantify semantic generators.

**Checked anchors.** `Results.theorem_3_5` (Overview:115). Native support: `FiniteUnion.anchor`, `FiniteUnion.Admissible`, `FiniteUnion.targetClass`.

### C05 — UUS and generation scale invariance in doubling geometry

All three grouped results are represented: UUS scale invariance, uniform and non-uniform scale invariance, and arbitrary positive-pair finite-dimensional invariance. Some formal components are stronger than printed assumptions.

- **Theorem 4.1 — faithful-generalization:** Doubling plus diagonal zero, symmetry and triangle, with r>0 and r-UUS, yields every positive-radius UUS. No separability or point-separation hypothesis.
- **Theorem 4.2 — faithful-generalization:** Both uniform and non-uniform iff statements at 0<delta_a<e_a and 0<delta_g<e_g; UUS is omitted.
- **Corollary 4.3 — equivalent-in-explicit-real-scope:** FiniteDimensional over Real is explicit. One r>0 with r-UUS suffices; all four comparison scales are independently positive, with no r bound or ordering. This is the paper real finite-dimensional regime using Theorem 4.1.

**Strength and scope.** Theorem 4.2 drops UUS; geometric theorems omit separability and point separation; native all-positive doubling iff is also present. Lean states the finite-dimensional corollary over R. The source does not name the scalar field; its surrounding Rd/Euclidean motivation supports the real interpretation. Complex instances require the usual real-scalar restriction; no arbitrary-valued-field version is asserted. All three source components in the ordinary real normed-space reading are available. No total strength ordering over an unspecified source scalar field is claimed.

**Representation/access.** S3-S8. Natural doubling cardinal bound is equivalent to a finite real bound after rounding. Native isDoublingDistance_dist_finiteDimensional supplies the geometry; the internal-cover distinction is preserved.

**Algorithm scope.** Semantic equivalences, not a computable doubling-cover refinement algorithm. No limit-generation scale invariance is asserted.

**Checked anchors.** `Results.corollary_4_3` (Overview:174); `Results.theorem_4_1` (Overview:131); `Results.theorem_4_2` (Overview:150). Native support: `IsDoublingDistance`, `doubling_generation_scale_invariance_all_positive`, `isDoublingDistance_dist_finiteDimensional`, `theorem_4_1_doubling_uus_scale_invariance`.

### C06 — Bi-Lipschitz metric invariance in doubling spaces

The exported conjunction contains the UUS iff and both generation iff statements. It is stronger than the source conditional generation claim: UUS is not a premise for either generation iff, and the two metrics may use independent positive scale pairs.

- **UUS preservation — faithful-generalization:** At arbitrary positive r1,r2, r1-UUS under rho1 iff r2-UUS under rho2, with doubling rho1, metric-style laws for both and positive mutual domination constants.
- **uniform/non-uniform metric invariance — faithful-generalization:** Both iff statements hold at independently chosen positive parameter pairs without requiring either UUS condition; restricting to source UUS and a common pair gives the printed result.

**Strength and scope.** No separability, point separation or UUS condition on generation; arbitrary positive scale pairs, not merely fixed common scales. Bi-Lipschitz bounds are explicit in both directions with positive constants, matching Definition D.1. Unconditional threshold equivalence is not a claim that thresholds are reached on supports lacking UUS.

**Representation/access.** S3-S8. Mutual bounds rho2<=M12*rho1 and rho1<=M21*rho2 are equivalent to the source c,C bounds. The source all-radius UUS wording is represented by the arbitrary-radii iff.

**Algorithm scope.** Semantic equivalences; no witness-identification or computable metric-conversion algorithm is part of the target.

**Checked anchors.** `Results.theorem_4_4` (Overview:192). Native support: `DistanceDominatedBy`, `MutuallyLipschitzDominated`, `IsDoublingDistance`.

### C07 — Two different scale monotonicity directions

Both grouped monotonicity theorems match their respective opposite adversary-scale directions, with all uniform/non-uniform branches included. Formal versions need only the scale inequalities.

- **Theorem 4.6 — faithful-generalization:** Limit generation transfers when delta_a<=e_a and delta_g<=e_g.
- **Theorem 4.7 — faithful-generalization:** Uniform and non-uniform generation transfer when e_a<=delta_a and delta_g<=e_g. Weak equalities are retained.

**Strength and scope.** Arbitrary real functions/scales and no UUS/metric/separability assumptions. All paper positive/r-bounded boundary cases are included and neither adversary direction is reversed. Native pointwise-generator monotonicity interfaces retain a given generator (and uniform threshold); the existential exported targets alone do not name witness equality.

**Representation/access.** S2-S7. Coverage inclusion explains limit direction; lower-bound cover monotonicity explains threshold direction.

**Algorithm scope.** Logical reuse of an existing semantic generator. Pointwise native statements do not make that generator computable.

**Checked anchors.** `Results.theorem_4_6` (Overview:234); `Results.theorem_4_7` (Overview:246). Native support: `isUniformGeneratorAt_mono`, `isNonuniformGeneratorAt_mono`.

### C08 — One-sided metric domination with rescaled limit generation

Both source transfers have the correct orientation rho2<=M*rho1 and division by M. The formal target states UUS transfer and limit-generation transfer as independent implications, requiring only M>0 and domination.

- **r-UUS transfer — faithful-generalization:** B_rho2(r,H) implies B_rho1(r/M,H), without a positive-r premise.
- **limit transfer — faithful-generalization:** Limit generation under rho2 at (e_a,e_g) implies under rho1 at (e_a/M,e_g/M), without UUS or scale bounds as premises.

**Strength and scope.** Arbitrary distance functions and real scales; no separability, metric laws, r>0, scale positivity/bounds or UUS requirement for the generation implication. No reverse domination or uniform/non-uniform transfer is substituted for the printed two conclusions.

**Representation/access.** S3-S8. Approximate neighborhood definitions preserve the source infimum issue rather than assuming attained distances.

**Algorithm scope.** Semantic transfer. Native isLimitGeneratorAt_transfer_of_dominated explicitly reuses a given generator; no effective search claim.

**Checked anchors.** `Results.theorem_4_10` (Overview:307). Native support: `DistanceDominatedBy`, `isLimitGeneratorAt_transfer_of_dominated`, `metricPresentation_transfer_of_dominated`, `coveringNumberAtLeast_transfer_of_dominated`.

### C09 — Recovery of all three countable generation notions

All three metric/countable-framework equivalences are present and match Appendix A definitions. The separate native UUS iff also recovers the source infinite-support reduction, so it is not missing because the facade omits it.

- **Proposition D.1 limit/uniform/non-uniform — faithful-generalization:** All three iff statements hold for any type with DecidableEq and 0<=e_a,e_g<1; source countable X, r-UUS and positive scales are not required.
- **UUS reduction in the proof — represented-by-native-statement:** discrete_uus_iff states at 0<=r<1: r-UUS iff every member language is infinite.

**Strength and scope.** No countability/UUS premises and scales may be zero. Strict upper radius 1 and the three distinct quantifier structures are retained. DecidableEq is an explicit interface binder to define the discrete distance. In the classical source setting it can be supplied nonconstructively; it does not imply an effective representation of arbitrary source objects.

**Representation/access.** S1-S7. Metric scales encode distinct-count thresholds; Generic equality triggers match Appendix A. The LiRamanTewari generation predicates are direct aliases to Generic, not new access models.

**Algorithm scope.** Semantic equivalences. No effective enumeration or countable-model algorithm follows from a DecidableEq instance.

**Checked anchors.** `Results.proposition_D_1` (Overview:347). Native support: `discreteDistance`, `discrete_uus_iff`, `discrete_isUniformGeneratorAt_iff`, `discrete_isNonuniformGeneratorAt_iff`. Additional checked types/definitions and full anchors are listed in `stage2-claims.json`.

### C10 — Real-line boundary for limit generation

The fixed real-line class has the source simultaneous positive behavior for every 0<e<1 and failure at (1,1). The facade states 1-UUS. The full all-radius UUS source assertion is available by interface assembly on the same fixed class, not a missing mathematical fact.

- **same-class positive/negative limit statements — equivalent:** languageClass is independent of e and uses odd prime pairs plus an arbitrary subset of positive even integers; n+1 in powers/evens matches positive source indices.
- **UUS at every positive radius — represented-by-interface-assembly:** example_4_5_uus gives 1-UUS for that exact class/distance; Theorem 4.1 gives every positive radius once real doubling is instantiated using isDoublingDistance_dist_finiteDimensional and standard real dist=|x-y|.
- **stronger negative proof context — represented-by-native-statement:** example_4_5_not_generatable_one_half states the stronger failure at (1,1/2).

**Strength and scope.** The same class works for all positive e<1; no pointwise choice of a different class is hidden under that quantifier. No single facade states forall r>0 UUS, but existing typed interfaces compose to it; no new theorem compilation was performed. The class is explicitly named, more concrete than the source existence sentence.

**Representation/access.** S1-S7. The source odd-prime-power support is exact after zero-to-positive reindexing. No source correction is needed to explain facade 1-UUS.

**Algorithm scope.** The target asserts semantic existence. Separately inspected native generator chooses an observed odd integer>1 (default 3), then a sufficiently distant power using Classical.choose. This is a mathematical variant of the source prime-power/tower rule, not a least-power/ordinary-computability certification. Its full correctness proof is excluded.

**Checked anchors.** `Results.example_4_5` (Overview:221). Native support: `RealLineThreshold.realDistance`, `RealLineThreshold.languageClass`, `RealLineThreshold.positiveEvenIntegers`, `RealLineThreshold.primePairSupport`. Additional checked types/definitions and full anchors are listed in `stage2-claims.json`.

### C11 — Independent strict thresholds in Hilbert space

The existence/classification claim is fully represented on one explicitly named r-UUS Hilbert class, including equality in either negative boundary. A named semantic positive generator is an additional refinement. The exact supporting reservoir formula has an exponent-index convention difference recorded below.

- **Example 4.8 full iff — equivalent:** For all 0<gamma_a,gamma_g<=r, limit generation iff gamma_a<e_a AND gamma_g<e_g, with fixed H before the pair quantifiers.
- **named positive rule — faithful-semantic-variant:** The named generator scans the prefix through an existential eligible marker k>=2, chooses a positive-exponent tower point that is actually novel, and defaults to zero if none exists. It may select a different marker/tower point than the source retained-first-marker/least-unused-coordinate rule.
- **literal reservoir construction — variant-with-index-convention-question:** example48Optimal uses n:Nat in 2*k^n+1, so exponent zero adds g_3 to every optimal set. The frozen source positive-n reading uses n>=1; its proof generator also explicitly uses n>=1. The formal named candidate uses n+1 and thus positive exponents. This difference does not remove the source existential threshold phenomenon.

**Strength and scope.** All scales, weak r upper bounds, strict two-coordinate AND, and same-class quantifier dependencies match. The target names a class and a generator; the generator depends on e_a,e_g,gamma_g, not r or gamma_a. No literal equality with the source class under positive-n indexing, no single generator independent of gamma_g, and no computability guarantee are inferred.

**Representation/access.** S1-S7 plus Hilbert2=real lp(N,2). Source positive index sets are enforced by explicit k>0 clauses. The coordinate-0 ambient direction is an ordinary Hilbert-space representation; the exponent-zero extra g_3 is separately material to literal construction identity.

**Algorithm scope.** IsExample48CausalCandidate and example48CausalGenerator bodies were inspected. They use Classical.propDecidable and Classical.choose over candidates and exact novelty predicates, not an executable least-index search or a declared oracle. This audits rule shape and stated generator property, not correctness proof steps.

**Checked anchors.** `Results.example_4_8` (Overview:263). Native support: `HilbertAxisReservoir.Hilbert2`, `HilbertAxisReservoir.axisPoint`, `HilbertAxisReservoir.hilbertDistance`, `HilbertAxisReservoir.example48U`. Additional checked types/definitions and full anchors are listed in `stage2-claims.json`.

### C12 — One Hilbert class with four generation regimes

One existential Hilbert class simultaneously has all four source regimes, with every positive boundary retained. The explicit native family definitions also match the four-coordinate construction, rather than merely a weaker collection of separately chosen examples.

- **upper uniform regime — equivalent:** gamma_a in [e_a2,r], gamma_g in (0,e_g): uniform.
- **middle regime — equivalent:** gamma_a in [e_a1,e_a2), gamma_g in (0,e_g): non-uniform and not uniform.
- **lower regime — equivalent:** gamma_a in (0,e_a1), gamma_g in (0,e_g): limit and not non-uniform.
- **large generator regime — equivalent:** gamma_g in [e_g,r], gamma_a in (0,r]: not limit.
- **construction and threshold proof context — represented-by-native-definitions-and-interfaces:** Native indices are k>=2; U/A/B/G occupy 4k,4k+1,4k+2,4k+3; optimal uses k^(n+1); J is finite. Supporting optimal-of-large-sample lemmas contain trigger 2 and |J|+2. Transfer lemma and orthogonal estimate retain the no-UUS/no-coverage intermediate-set logic.

**Strength and scope.** H is chosen before all gamma pairs. If e_a1=e_a2, the middle interval is empty in both. No strictness is lost at generator equality or either adversary threshold. Positive generators and their thresholds may depend on the gamma pair; the exported existential statements do not identify a single common algorithm across every pair.

**Representation/access.** S1-S7. The named Example49 family/target/optimal definitions agree with source supports after n+1 reindexing; finite/infinite index assumptions are explicit.

**Algorithm scope.** Semantic regime package. Source described tower algorithm and explicit threshold bounds are contextual/supporting facts, not an executable procedure certified by the facade. Native trigger lemmas support those numeric constants, while theorem proof bodies and a full construction audit remain excluded.

**Checked anchors.** `Results.example_4_9` (Overview:288). Native support: `HilbertAxisReservoir.Example49.indices`, `HilbertAxisReservoir.Example49.U`, `HilbertAxisReservoir.Example49.A`, `HilbertAxisReservoir.Example49.B`. Additional checked types/definitions and full anchors are listed in `stage2-claims.json`.

### C13 — Bi-Lipschitz metric separation outside doubling spaces

The same class and an actual MetricSpace structure are chosen before every epsilon; all e in (0,r) have the source ordinary-metric uniform/weighted-metric non-uniform separation. Both r-UUS properties are explicit conjuncts, so no support qualification is omitted.

- **all-scale separation — equivalent:** Ordinary (e,e)-uniform generation and failure of weighted (e,e)-non-uniform generation for every 0<e<r, on one H/metric pair.
- **equivalent metric and support context — equivalent-with-explicit-strengthening:** Formal mutual bounds use constants 1 and 2: d-prime<=d<=2*d-prime. Both metrics have r-UUS. The negative is not non-uniform, not an invented not-limit conclusion.
- **weighted construction — faithful-reindexing:** Native even coordinate multiplier is 1/2 before taking ordinary norm, so squared weight is 1/4 as in the paper. Native amplitude 4r*(1/2)^m for m>=0 equals source 2^(3-m_source)r with m_source=m+1. Orbits 2^n(2k+1) and independent infinite positive sets match.

**Strength and scope.** Same witness pair for every epsilon; same open endpoints and negative notion. An actual metric structure and numerical domination constants are exposed, not merely a distance function; both UUS properties are stated. The existential facade does not by itself name its metric/class witness. Native named definitions and supporting properties were checked separately; proof-body witness extraction was not performed.

**Representation/access.** S1-S7; WeightedHilbert.weightedMetric is induced by the coordinate-weight map. The multiplier-versus-squared-weight difference is an equivalent representation, not a factor-of-two metric error.

**Algorithm scope.** Semantic existence/separation. No finite-ERM method, threshold-search implementation, or source diagonal algorithm is certified.

**Checked anchors.** `Results.example_4_11` (Overview:320). Native support: `HilbertAxisReservoir.WeightedHilbert.weight`, `HilbertAxisReservoir.WeightedHilbert.weightedMap`, `HilbertAxisReservoir.WeightedHilbert.weightedDistance`, `HilbertAxisReservoir.WeightedHilbert.weightedMetric`. Additional checked types/definitions and full anchors are listed in `stage2-claims.json`.

### C14 — Two-target obstruction for reversed novelty scales

The two-hypothesis Hilbert obstruction is fully represented at every strictly reversed positive scale pair, with r-UUS and failure of non-uniform generation. Set.ncard H=2 expresses exact two-element cardinality under the trusted standard semantics.

- **Example B.3 — equivalent:** For r>0 and 0<e_a<e_g<=r there exists H with exactly two languages, r-UUS, and not non-uniformly generatable.
- **support construction context — faithful-reindexing:** Native small points use a e_{3(k+1)}; the two remote families use coordinates 3(k+1)+1 and 3(k+1)+2 with amplitude 2r. Boolean indexing selects the two residue classes. This is the paper two-support geometry with positive indices.

**Strength and scope.** Strict reversed input/output scale ordering and the e_g=r boundary match. Non-uniform failure is not strengthened to a false source claim of limit failure. The target leaves H existential. Native source-like family definitions are available, but no hidden choice of alpha/H is extracted from proof values.

**Representation/access.** S1-S7. Set.ncard=2 rules out an infinite class in Mathlib because infinite-set ncard is zero; this is not merely an upper bound.

**Algorithm scope.** Semantic impossibility for all total finite-history generators. No effective adversary or construction implementation is claimed.

**Checked anchors.** `Results.example_B_3` (Overview:387). Native support: `ExampleB3.offset`, `ExampleB3.small`, `ExampleB3.remote`, `ExampleB3.common`. Additional checked types/definitions and full anchors are listed in `stage2-claims.json`.

## Discrepancies, source questions and Stage 1 corrections

- **Faithful assumption extensions:** C01–C03, C05–C09 do not silently import paper UUS/separability into their Lean types. The broader formal conditional predicates are meaningful as defined, with possible unreachable-threshold vacuity. Their source restrictions agree. C06 additionally removes the paper UUS condition for generation equivalences.
- **Interface assembly:** Example 4.5’s facade states only 1-UUS, but the same named class, the general doubling UUS theorem and finite-dimensional real doubling recover UUS at every positive radius. This is an assembly distinction, not partial source coverage. The discrete UUS/infinite-support reduction is likewise present natively.
- **Construction/rule distinction:** In C11, a Nat exponent in `example48Optimal` includes zero and adds a common g_3 relative to the positive-n source reading. Its named generator uses positive powers, arbitrary eligible markers and arbitrary novel tower points, whereas the source describes retaining a marker and choosing a least unused coordinate. The source existential classification is still fully represented; literal support identity and stepwise algorithm identity are not claimed.
- **Equivalent representations:** In C13, a 1/2 coordinate multiplier gives the paper 1/4 squared weight; zero-based layer amplitudes match source layers after shifting by one. Neither is a metric mismatch.
- **Source questions, not corrections:** Clarify the intended start of N in the Example 4.8 optimal set; source proof towers explicitly use n>=1. Section 2 also leaves X nonempty implicit despite a total generator on empty history. The finite-dimensional corollary leaves its scalar field implicit. No source mathematical correction has been established by this statement comparison, and no difference has been labeled a Lean proof error.
- **Stage 1 assessment:** The exact eighteen target reconstructions required no semantic correction. The source-informed additions are native supporting facts and cross-interface assembly, not revisions of the frozen code-only report. Its literal absence-of-assumption observations must not be read as missing-source-assumption verdicts. Its semantic/computability cautions remain applicable.

## Coverage checklist and remaining limits

- Exactly 14 slots and all 18 distinct exported targets are accounted for; C02 has both corollaries, C05 all three geometric results, C07 both monotonicity theorems, and C09 all three equivalences.
- C12 checks all four regimes and all weak/strict boundaries; C11 checks the AND and equality-negative thresholds; C13 checks one witness pair before all epsilon values and both support properties; C14 checks exact cardinality two.
- Source-global assumptions, support representation, common-generator quantifier dependencies, positive scale boundaries, absence of probabilistic models/rates and semantic versus effective access are explicit in S1–S9 and per-slot JSON. The source proof trigger constants D+1, 2 and |J|+2 have supporting interface evidence; the target facade is not claimed to compute numeric dimension or minimal sample complexity.
- The scoped source result is complete in the ordinary real metric interpretation. Literal C11 construction identity, the implicit source scalar convention, and empty-domain convention remain qualified. No uncovered mathematical slot is inferred from these qualifications.
- This is not a full algorithm-construction/proof audit. No correctness claim for theorem proof steps, fresh Lean compilation, executable real-number handling, finite-ERM implementation, hidden witness extraction or human review is made. Backend model/version/effort are not independently observable.

Companion machine-readable files: [fourteen-slot comparison](stage2-claims.json) and [run record](stage2-run.json). The reviewer stops here for coordinator freeze before any Stage 3 explanation.
