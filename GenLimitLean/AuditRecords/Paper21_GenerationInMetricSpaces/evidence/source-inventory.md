# P21 source-only inventory

Source: **On Generation in Metric Spaces**, Li–Raman–Tewari, **arXiv:2602.07710v2**. The original PDF SHA-256 is `b4e14e33fce18aa5d970a49d4886a647d9de888e8de29fab12ff8cda0afacfbc`, verified from supplied bytes. The author title page says October 27, 2026; the arXiv version mark and manifest say October 24, 2026. Printed and one-based PDF page numbers coincide. All citations below refer to this edition. Visual checks use the annotation-free derivative, hashed separately in the run record.

This is the source-first phase only. Exactly fourteen claim slots are inventoried; grouped components remain within their respective slots. No formalization correspondence judgment has been made.

## Standing source context

**G1 — Section 2.1 (printed/PDF pp. 3).** Throughout the paper (X,rho) is a separable metric space and H is a binary hypothesis class, a subset of {0,1}^X. No countability of H or X is imposed unless a particular claim says so.

**G2 — Definitions 2.1-2.2 (printed/PDF pp. 4).** B(x,e) is closed (rho(x,y)<=e). For a set A, B(A,e)={y:inf_{x in A}rho(x,y)<=e}; for infinite A this is an infimum-based neighborhood, not necessarily a union of point-balls. N(e;A,rho) is the least size of a finite e-cover, with centers anywhere in X; it is infinity if no finite cover exists.

**G3 — Definition 2.3; Lemma 2.1 (printed/PDF pp. 4, 28).** r-UUS requires every target support nonempty and, for every positive infinite sequence whose range r-covers that support, N(r;its finite prefixes,rho) tends to infinity. It is a covering-stream condition, not merely that supports have infinitely many points. r>0. It implies delta-UUS for 0<delta<r. Unless the claim obtains UUS at every radius, generation scales satisfy 0<e_a,e_g<=r.

**G4 — Definitions 2.4-2.7 (printed/PDF pp. 4, 5).** A generator is a total map G:X*->X. Success on a finite observed prefix means output in the true support and outside its closed e_g-neighborhood, hence distance strictly greater than e_g from each observation. Only observed examples enter the exclusion set; earlier generator outputs do not. Definitions quantify arbitrary positive streams and impose no pairwise separation or no-repetition requirement on them.

**G5 — Definition 2.5; Remark 2.1 (printed/PDF pp. 5).** Limit generation: exists one G such that for every target h and every positive infinite stream with supp(h) subset B(range(stream),e_a), there is a stream-and-target-dependent finite time after which every output is correct and e_g-novel.

**G6 — Definitions 2.6-2.7 (printed/PDF pp. 5).** Uniform generation: exists G and a common natural threshold d*, independent of target and positive stream, such that if a prefix has e_a-covering number at least d*, all outputs from that round onward succeed. Non-uniform: exists one G; for each h there is a threshold d_h, independent of positive stream, with the same guarantee. These notions quantify all positive streams, without requiring support coverage. The threshold is a covering-number threshold, not a number-of-rounds bound.

**G7 — Section 2.1; Definition 3.1 (printed/PDF pp. 3, 6).** The version space consists of hypotheses containing every observation. The induced closure is the intersection of supports in a nonempty version space, and is bottom for an inconsistent sample. C_{e_a,e_g}(H) is the largest attainable finite-sample e_a-covering number d for a realizable sample whose closure has a finite internal e_g-cover F subset closure. It is infinity for unbounded such d, and zero if there are no witnesses. Internal centers are essential here, unlike N, whose centers may be anywhere in X.

**G8 — Definition 4.1; Theorem 4.1; Definition D.1 (printed/PDF pp. 7, 28, 29).** Doubling means one uniform bound M on the number of radius-s/2 balls covering any radius-s ball, for every center and s>0. In a doubling space r-UUS for one r>0 implies UUS at all positive radii. Equivalent metrics means bi-Lipschitz: c rho_1 <= rho_2 <= C rho_1 for constants 0<c<=C<infinity, rather than merely equal topology.

**G9 — Appendix E (printed/PDF pp. 31, 32, 33).** The generation results are existence/semantic statements about total maps, with no general computability or finite-query promise. An ERM value oracle tests closure membership on a realizable positive sample by labeling a candidate negative. A separate max-min search oracle, with a fixed default point on empty feasible sets, implements the uniform guarantee with one oracle call per round. It is not reduced to finitely many ERM queries. ERM enumeration search needs exact novelty tests and a supplied candidate sequence meeting the novel closure; density in X alone and separability alone do not ensure this. Such conditional search can fail to terminate on other samples. A terminating fallback/decidable threshold requires further assumptions not adopted. A general finite-ERM implementation remains unresolved by this argument.

The generic source existence proofs use arbitrary choices/default outputs. Section 2 does not separately state that X is nonempty; an actual target has nonempty support, and Appendix E explicitly fixes nonempty X for its oracle. No theorem for an empty instance domain is inferred.

## Claim inventory

### C01 — Uniform generation iff finite scale-closure dimension

Claim locator: `claim:lrt26:theorem-3-1`. Edition: `arxiv-2602-07710-v2`.

Source locations: Theorem 3.1; Definition 3.1 (printed/PDF pp. 6; statement and invariant); Lemmas B.1-B.2 (printed/PDF pp. 14, 15; both directions); Appendix E (printed/PDF pp. 31, 32, 33; computability limits).

Assumptions and definitions: G1, G2, G3, G4, G6, G7, G9; support, version space, induced closure, internal cover, scale-closure dimension, uniform generation.

- **equivalence:** For r>0, H satisfying r-UUS, and 0<e_a,e_g<=r: H is (e_a,e_g)-uniformly generatable iff C_{e_a,e_g}(H)<infinity.
- **quantitative proof guarantee:** If C=d<infinity, the sufficient uniform covering-number threshold is d+1; the proof selects a point of the closure outside the union of observed closed e_g-balls.

Proof/context: Necessity appends the finitely many internal cover centers without changing the version space, then chooses a consistent target on which the proposed generator fails after its threshold. Sufficiency uses lack of any finite internal cover, with observed points already in the closure, to obtain a novel closure point on every above-threshold realizable sample.

Guarantee level: Semantic existence; arbitrary choice of novel closure points and arbitrary outputs on other inputs in B.2. G9 gives oracle implementation qualifications, not an unconditional computable/finite-ERM generator.

Scope/ambiguity: The dimension is not ordinary cardinal closure dimension or arbitrary-center covering finiteness. Natural zero/no-witness conventions are explicit. A total generator needs an output on every input; Section 2 does not separately state X nonempty, although any actual target has nonempty support and Appendix E explicitly assumes nonempty X for its oracle.

Visual evidence: [page_3.png](visual-checks/page_3.png), [page_4.png](visual-checks/page_4.png), [page_5.png](visual-checks/page_5.png), [page_6.png](visual-checks/page_6.png), [page_14.png](visual-checks/page_14.png), [page_15.png](visual-checks/page_15.png), [page_31.png](visual-checks/page_31.png), [page_32.png](visual-checks/page_32.png), [page_33.png](visual-checks/page_33.png).

### C02 — Finite and countable class consequences

Claim locator: `claim:lrt26:finite-and-countable-class-corollaries`. Edition: `arxiv-2602-07710-v2`.

Source locations: Corollaries 3.2 and 3.4 (printed/PDF pp. 6; two grouped statements); Proof of Corollary 3.2 (printed/PDF pp. 15; finite intersection argument); Proof of Corollary 3.4 (printed/PDF pp. 16; increasing finite subclasses).

Assumptions and definitions: G1, G2, G3, G4, G6, G7, G9; finite/countable hypothesis class, scale-closure dimension, uniform generation, non-uniform generation.

- **Corollary 3.2:** Every finite H with r-UUS is (e_a,e_g)-uniformly generatable whenever 0<e_g<=e_a<=r.
- **Corollary 3.4:** Every countable H with r-UUS is (e_a,e_g)-non-uniformly generatable under the same 0<e_g<=e_a<=r condition; finite classes are included.

Proof/context: For a finite H, only finitely many nonempty intersections of target supports arise as realizable closures. The proof bounds sample e_a-covering numbers over those intersections with finite e_g-covering number. For countably infinite H, enumerate targets and use the increasing finite initial classes with Theorem 3.3.

Guarantee level: Semantic existence. Countability of the class does not supply an effective enumeration or exact metric/closure operations. Appendix E G9 applies.

Scope/ambiguity: Both components and the weak ordered-scale boundary e_g=e_a belong to this slot. Reversed scales are excluded; Example B.3 supplies an obstruction. These are cardinality assumptions on H, not X.

Visual evidence: [page_5.png](visual-checks/page_5.png), [page_6.png](visual-checks/page_6.png), [page_15.png](visual-checks/page_15.png), [page_16.png](visual-checks/page_16.png).

### C03 — Non-uniform generation via increasing finite-dimension cover

Claim locator: `claim:lrt26:theorem-3-3`. Edition: `arxiv-2602-07710-v2`.

Source locations: Theorem 3.3 (printed/PDF pp. 6; equivalence); Lemmas B.4-B.5 (printed/PDF pp. 16; necessity and sufficiency).

Assumptions and definitions: G1, G2, G3, G4, G6, G7, G9; non-uniform generation, uniform generation, scale-closure dimension, non-decreasing subclasses.

- **equivalence:** With r-UUS and 0<e_a,e_g<=r, H is (e_a,e_g)-non-uniformly generatable iff H is a countable union of a non-decreasing chain H_1 subset H_2 subset ... with C_{e_a,e_g}(H_n)<infinity for every n.
- **proof strengthening:** The chain may equivalently be required to consist of uniformly generatable subclasses at these fixed scales. Necessity can use H_n={h:d_h<=n} for one common non-uniform generator.

Proof/context: Sufficiency chooses a uniform generator G_n and threshold d_{G_n} for each subclass. At sample length t and covering number d_t, use the largest n<=t with d_{G_n}<=d_t, or a default output if none. For h in H_{n*}, max(d_{G_{n*}},n*) is a sufficient target threshold.

Guarantee level: Semantic existence, including selection of subclass generators and thresholds and exact covering-number comparisons in the proof. No automatic finite-ERM implementation; G9 applies.

Scope/ambiguity: The chain must be non-decreasing, not merely an arbitrary countable family of finite-dimension classes. The index set is countable even when H itself is uncountable. Both directions are in scope.

Visual evidence: [page_6.png](visual-checks/page_6.png), [page_16.png](visual-checks/page_16.png).

### C04 — Finite-union closure fails on the real line

Claim locator: `claim:lrt26:theorem-3-5`. Edition: `arxiv-2602-07710-v2`.

Source locations: Theorem 3.5 (printed/PDF pp. 7; existence statement); Appendix B.3: proof of Theorem 3.5 (printed/PDF pp. 17; construction and diagonal stream).

Assumptions and definitions: G1, G2, G3, G4, G5, G6; usual real metric, uniform generation, limit generation, positive covering stream.

- **counterexample:** For every r>0 and every 0<e_a,e_g<=r, there are H_1,H_2 on R with the usual metric, each r-UUS and (e_a,e_g)-uniformly generatable, whose union is not (e_a,e_g)-generatable in the limit.
- **source construction:** A={3rn:n>=1}, B={3rn+e_a:n>=1}; S chooses one s_n in (3rn,3rn+e_a) for each n. H_1 has supports A union S and H_2 supports B union S. Each component has uniform threshold 1 by outputting a fixed-grid point beyond all observations by more than e_g.

Proof/context: For each proposed union generator, choose s_n avoiding its finitely many earlier outputs. This single stream covers both fixed supports A union S and B union S at radius e_a. Their intersection is exactly S, so at every round the output is old or fails one target; one of the two fixed targets has infinitely many failures. The union also has r-UUS.

Guarantee level: Semantic counterexample against every total generator. The diagonal sequence may depend on that generator. Component output rules are explicit mathematical rules, without a source computational representation assumption.

Scope/ambiguity: Existence of two classes is asserted for each parameter choice, not failure for every pair of uniformly generatable classes. No scale ordering e_g<=e_a is required. The witnessing classes have families of supports, rather than two individual hypotheses.

Visual evidence: [page_5.png](visual-checks/page_5.png), [page_7.png](visual-checks/page_7.png), [page_17.png](visual-checks/page_17.png).

### C05 — UUS and generation scale invariance in doubling geometry

Claim locator: `claim:lrt26:doubling-space-scale-invariance`. Edition: `arxiv-2602-07710-v2`.

Source locations: Definition 4.1; Theorems 4.1-4.2 (printed/PDF pp. 7; two theorem statements); Theorem 4.2 continuation; Corollary 4.3 (printed/PDF pp. 8; proof and finite-dimensional corollary); Appendix D.1: proof of Theorem 4.1 (printed/PDF pp. 28; UUS scale proof).

Assumptions and definitions: G1, G2, G3, G4, G6, G7, G8, G9; doubling metric space, UUS at all radii, uniform/non-uniform generation, internal closure covers.

- **Theorem 4.1:** In a doubling metric space, if H satisfies r-UUS for one r>0, then H satisfies r-prime-UUS for every r-prime>0.
- **Theorem 4.2:** In a doubling metric space with H satisfying UUS, for positive pairs satisfying delta_a<e_a and delta_g<e_g, (e_a,e_g)-uniform generation iff (delta_a,delta_g)-uniform generation, and separately the same iff for non-uniform generation.
- **Corollary 4.3:** In every finite-dimensional normed vector space, a UUS class has equivalent uniform-generation status at any two positive scale pairs, and separately equivalent non-uniform-generation status at any two positive pairs. The pairs need not be coordinatewise ordered.

Proof/context: D.1 shows each support nonempty and unbounded, using separability and doubling to contradict UUS for a bounded support. A stream covering an unbounded support has unbounded range and diverging prefix covering numbers at every radius. Theorem 4.2 compares covering numbers by uniform constants and refines finite internal closure covers using smaller balls and replacement centers in the closure. Apply the comparison to each subclass for the non-uniform case. The corollary compares arbitrary pairs through a common strictly smaller positive pair.

Guarantee level: Semantic equivalences and geometric finite-cover comparisons; not a computability or effective doubling-cover algorithm. G9 applies to generator existence.

Scope/ambiguity: All three named results, both uniform and non-uniform versions, and the standalone UUS conclusion are included. Limit-generation scale invariance is not asserted; Example 4.5 is a counterexample on R. Theorem 4.2 is printed with strict coordinate inequalities, whereas the corollary states arbitrary pairs.

Visual evidence: [page_7.png](visual-checks/page_7.png), [page_8.png](visual-checks/page_8.png), [page_28.png](visual-checks/page_28.png).

### C06 — Bi-Lipschitz metric invariance in doubling spaces

Claim locator: `claim:lrt26:theorem-4-4`. Edition: `arxiv-2602-07710-v2`.

Source locations: Theorem 4.4 (printed/PDF pp. 8; statement); Definition D.1; proof of Theorem 4.4 (printed/PDF pp. 29; metric meaning and complete argument).

Assumptions and definitions: G1, G2, G3, G4, G6, G7, G8, G9; doubling, bi-Lipschitz equivalent metrics, UUS, uniform/non-uniform generation.

- **support invariance:** If (X,rho_1) is doubling and rho_2 is bi-Lipschitz equivalent to rho_1, H satisfies UUS under rho_1 iff it satisfies UUS under rho_2.
- **generation invariance:** Under these equivalent UUS conditions, H is uniformly generatable under rho_1 iff under rho_2, and separately non-uniformly generatable under rho_1 iff under rho_2. The proof fixes any common positive (e_a,e_g); scale invariance makes the statement independent of the choice.

Proof/context: Both metrics are doubling and have the same bounded sets; UUS here is exactly nonempty unbounded support for each target. Covering numbers at a fixed scale are comparable by constants independent of the set; finite internal covers are preserved by metric bounds followed by doubling refinement. Thus finite closure dimension is equivalent, also subclass by subclass.

Guarantee level: Semantic invariance. No metric-comparison computability or generator algorithm follows from the statement; G9 applies.

Scope/ambiguity: Equivalent explicitly means bi-Lipschitz, despite informal nearby wording about equivalent metrics. The generation part is conditional on UUS. The displayed statement omits scale arguments because of doubling scale invariance; the proof verifies any fixed positive pair. Limit generation is not a component of this theorem.

Visual evidence: [page_8.png](visual-checks/page_8.png), [page_29.png](visual-checks/page_29.png).

### C07 — Two different scale monotonicity directions

Claim locator: `claim:lrt26:scale-monotonicity`. Edition: `arxiv-2602-07710-v2`.

Source locations: Theorems 4.6-4.7 (printed/PDF pp. 9; grouped statements); Appendix D.4: proofs of Theorems 4.6-4.7 (printed/PDF pp. 29, 30; same-generator transfer arguments).

Assumptions and definitions: G1, G2, G3, G4, G5, G6; limit generation, uniform/non-uniform generation, covering-number monotonicity.

- **Theorem 4.6:** For r-UUS H and 0<e_a,e_g<=r, limit generation at (e_a,e_g) implies limit generation at every positive (delta_a,delta_g) with delta_a<=e_a and delta_g<=e_g.
- **Theorem 4.7 uniform:** Uniform generation at (e_a,e_g) implies uniform generation at (delta_a,delta_g) whenever e_a<=delta_a<=r and 0<delta_g<=e_g.
- **Theorem 4.7 non-uniform:** The same implication and parameter inequalities hold for non-uniform generation.

Proof/context: For limit generation a smaller adversary scale strengthens the coverage requirement; for threshold generation a larger adversary scale decreases sample covering numbers, so crossing the new threshold implies crossing the old one. Smaller generator scale weakens novelty. The proofs reuse the same generator, and uniform/non-uniform thresholds can be retained.

Guarantee level: Logical transfers using a given generator, without new oracle requirements or an independent computation claim.

Scope/ambiguity: Adversary-scale monotonicity points in opposite directions for limit and threshold generation. All weak boundaries are included. Generator-scale monotonicity is downward for every notion.

Visual evidence: [page_5.png](visual-checks/page_5.png), [page_9.png](visual-checks/page_9.png), [page_29.png](visual-checks/page_29.png), [page_30.png](visual-checks/page_30.png).

### C08 — One-sided metric domination with rescaled limit generation

Claim locator: `claim:lrt26:theorem-4-10`. Edition: `arxiv-2602-07710-v2`.

Source locations: Theorem 4.10 (printed/PDF pp. 11; statement); Appendix D.4: proof of Theorem 4.10 (printed/PDF pp. 30, 31; UUS and generator transfer).

Assumptions and definitions: G1, G2, G3, G4, G5; two metrics on one set, one-sided domination, r-UUS, limit generation.

- **support transfer:** For metrics rho_1,rho_2 on X and M>0 with rho_2(x,y)<=M rho_1(x,y) for all x,y, if H is r-UUS under rho_2, then H is (r/M)-UUS under rho_1.
- **generation transfer:** If also 0<e_a,e_g<=r and H is (e_a,e_g)-generatable in the limit under rho_2, then H is (e_a/M,e_g/M)-generatable in the limit under rho_1.

Proof/context: The proof takes infima in rho_2<=M rho_1 to transfer infinite-stream neighborhoods. Every rho_1-cover at radius r/M is a rho_2-cover at radius r, yielding the required covering-number inequality. The same generator works because rho_1 novelty failure would imply rho_2 novelty failure.

Guarantee level: Semantic implication and direct reuse of the same generator. It is not a search-oracle or computability theorem.

Scope/ambiguity: Only the inequality rho_2<=M rho_1 is required; no lower metric bound or doubling assumption. Direction is from rho_2 generation/UUS to rho_1 with all scales divided by M. The theorem does not state uniform/non-uniform transfer. Section 2 has the global separable-space convention; the two-metric statement does not restate metricwise separability.

Visual evidence: [page_11.png](visual-checks/page_11.png), [page_30.png](visual-checks/page_30.png), [page_31.png](visual-checks/page_31.png).

### C09 — Recovery of all three countable generation notions

Claim locator: `claim:lrt26:proposition-d-1`. Edition: `arxiv-2602-07710-v2`.

Source locations: Appendix A, Definitions A.1-A.4 (printed/PDF pp. 13; the earlier framework as restated in this edition); Proposition D.1 (printed/PDF pp. 28; metric/countable equivalences); Proof sketch of Proposition D.1 (printed/PDF pp. 29; reduction of support, coverage, threshold, novelty).

Assumptions and definitions: G1, G2, G3, G4, G5, G6; countable X, discrete 0-1 metric, infinite support, enumeration, distinct observation count.

- **common hypotheses:** X is countable with rho(x,y)=1 if x!=y and 0 otherwise; r<1 and 0<e_a,e_g<=r; H satisfies r-UUS.
- **limit equivalence:** H is (e_a,e_g)-generatable in the limit in the metric definitions iff it is generatable in the limit as restated in Definition A.2.
- **non-uniform equivalence:** H is (e_a,e_g)-non-uniformly generatable iff it is non-uniformly generatable in Definition A.4.
- **uniform equivalence:** H is (e_a,e_g)-uniformly generatable iff it is uniformly generatable in Definition A.3.
- **proof reductions:** At every radius in (0,1), balls are singletons; support coverage means enumeration, prefix covering number equals distinct-observation count, novelty means previously unseen, and r-UUS is equivalent to every support infinite.

Proof/context: Appendix A has arbitrary positive streams for uniform/non-uniform generation and enumeration streams for limit generation. Its threshold premises are equality to a distinct count d, while Section 2 uses covering number at least d; the complete-stream and persistent-output formulations reconcile them by the first crossing of d.

Guarantee level: Semantic equivalence of generator properties, not an effectiveness upgrade. Appendix A is the author restatement of the earlier framework; no external earlier paper was consulted.

Scope/ambiguity: The strict upper bound r<1 matters: at radius 1 the discrete space is covered by a single ball. All three equivalences, plus the UUS reduction in the proof, are included. Countability here is of X, not H.

Visual evidence: [page_13.png](visual-checks/page_13.png), [page_28.png](visual-checks/page_28.png), [page_29.png](visual-checks/page_29.png).

### C10 — Real-line boundary for limit generation

Claim locator: `claim:lrt26:example-4-5`. Edition: `arxiv-2602-07710-v2`.

Source locations: Example 4.5 (printed/PDF pp. 8; statement); Appendix C.2 (printed/PDF pp. 20, 21, 22; construction and both directions); Lemma C.2 (printed/PDF pp. 18, 19, 20; diagonal lower-bound criterion).

Assumptions and definitions: G1, G2, G3, G4, G5; usual real metric, UUS all positive radii, odd prime powers, limit generation.

- **simultaneous behavior:** There is one class H on R with its usual metric satisfying UUS, limit-generatable at (e,1) for every 0<e<1, but not limit-generatable at (1,1).
- **source construction:** For an odd prime p, A_p={p^n:n>=1} union {p^n-1:n>=1}. Supports are A_p union B for arbitrary B subset the positive even integers and some odd prime p.
- **proof strengthening:** The proof establishes failure already at (1,1/2), then derives failure at (1,1) by monotonicity.

Proof/context: All supports are unbounded, giving UUS at every radius. If e<1, integer-valued supports and streams make e-coverage an actual enumeration; an observed odd-prime power identifies p and permits output of an unseen sufficiently distant power of p. At adversary scale 1, rows x_{ij}=p_i^j-1 and prime-factorization separation satisfy Lemma C.2.

Guarantee level: Explicit mathematical positive rule and semantic impossibility for every generator. No input-number representation or computability model is asserted.

Scope/ambiguity: The same class works simultaneously for all 0<e<1. The example concerns limit generation, despite the ambient real line being doubling. The proof has a stronger negative generator scale, but the named statement only requires (1,1).

Visual evidence: [page_8.png](visual-checks/page_8.png), [page_18.png](visual-checks/page_18.png), [page_19.png](visual-checks/page_19.png), [page_20.png](visual-checks/page_20.png), [page_21.png](visual-checks/page_21.png), [page_22.png](visual-checks/page_22.png).

### C11 — Independent strict thresholds in Hilbert space

Claim locator: `claim:lrt26:example-4-8`. Edition: `arxiv-2602-07710-v2`.

Source locations: Example 4.8 and Figure 1a (printed/PDF pp. 9, 10; statement and construction intuition); Appendix C.3 (printed/PDF pp. 22, 23, 24; all positive/negative regimes); Lemma C.2 (printed/PDF pp. 18, 19, 20; negative adversary regime).

Assumptions and definitions: G1, G2, G3, G4, G5; ell_2 ordinary norm metric, standard basis, r-UUS, limit generation, tower construction.

- **all parameter pairs:** For every r>0 and 0<e_a,e_g<=r, there exists a single r-UUS class H on ell_2 such that, for every 0<gamma_a,gamma_g<=r, H is (gamma_a,gamma_g)-generatable in the limit iff gamma_a<e_a AND gamma_g<e_g.
- **source construction:** u_k=4r e_k, a_k=e_a e_k, g_k=e_g e_k. For infinite index sets, U_I={u_k:k in I}, O_I={a_{2k}:k in I} union {g_{2 k^n+1}:k in I,n>=1}, D_I={g_{2k+1}:k in I}. Supports are {0} union U_{I1} union O_{I2} union D_{I3}.

Proof/context: Large u-points force r-UUS. For both strict inequalities, coverage forces observation of a_{2K} with K>=2, identifying an infinite g-tower from which unused coordinates give novel outputs. If gamma_a>=e_a while gamma_g<e_g, rows based on prime powers satisfy Lemma C.2. If gamma_g>=e_g, reveal 0 to block every g-point and diagonally select/forbid remaining prime-indexed u/a pairs while enumerating a final target. Equality at either threshold belongs to the negative regime.

Guarantee level: Concrete mathematical positive rule; semantic lower bounds against all generators. Neither finite-query effectiveness nor a uniform/non-uniform status is stated in this example.

Scope/ambiguity: The logical connector is AND, with strict inequalities; the complement includes either threshold equality. The tower index is 2 k^n+1, confirmed visually, not 2kn+1. Main text uses positive-integer index sets and Appendix C.3 writes N; the proof consistently uses positive indices and n>=1 towers, so no zero-based alteration has been inferred.

Visual evidence: [page_9.png](visual-checks/page_9.png), [page_10.png](visual-checks/page_10.png), [page_18.png](visual-checks/page_18.png), [page_19.png](visual-checks/page_19.png), [page_20.png](visual-checks/page_20.png), [page_22.png](visual-checks/page_22.png), [page_23.png](visual-checks/page_23.png), [page_24.png](visual-checks/page_24.png).

### C12 — One Hilbert class with four generation regimes

Claim locator: `claim:lrt26:example-4-9`. Edition: `arxiv-2602-07710-v2`.

Source locations: Example 4.9; Figure 1b (printed/PDF pp. 9, 10; four-regime statement and construction); Appendix C.4 (printed/PDF pp. 24, 25, 26; four proof cases); Lemma C.1; orthogonal cover estimate (1) (printed/PDF pp. 17, 18; non-uniform threshold transfer and covering lower bound).

Assumptions and definitions: G1, G2, G3, G4, G5, G6, G7; ell_2 ordinary metric, four disjoint coordinate families, r-UUS, all three generation notions, finite/infinite index subsets.

- **common quantifiers:** For every r>0, 0<e_{a1}<=e_{a2}<=r, and 0<e_g<=r, one r-UUS class H on ell_2 has the following status for every 0<gamma_a,gamma_g<=r.
- **uniform regime:** If 0<gamma_g<e_g and e_{a2}<=gamma_a<=r, H is (gamma_a,gamma_g)-uniformly generatable; source proof gives threshold 2.
- **non-uniform only regime:** If 0<gamma_g<e_g and e_{a1}<=gamma_a<e_{a2}, H is non-uniformly but not uniformly generatable. A target with finite second-family index set J has sufficient threshold |J|+2.
- **limit only regime:** If 0<gamma_g<e_g and 0<gamma_a<e_{a1}, H is generatable in the limit but not non-uniformly generatable.
- **no limit regime:** If e_g<=gamma_g<=r, for every 0<gamma_a<=r, H is not generatable in the limit.
- **source construction:** K={2,3,...}; u_k=2r e_{4k}, a_{k,1}=e_{a1}e_{4k+1}, a_{k,2}=e_{a2}e_{4k+2}, g_k=e_g e_{4k+3}. O_I={u_k:k in I} union {g_{k^n}:k in I,n>=1}; D_{I,J}={a_{k,1}:k in I} union {a_{k,2}:k in J}. Supports are {0} union O_{I1} union D_{I2,J}, with I1,I2 infinite and J finite.

Proof/context: For gamma_g<e_g, observing any u- or g-point identifies a tower and gives a permanent novel-output rule. Covering-number thresholds force that observation in the upper regimes; coverage forces u-observation for limit generation. Arbitrarily many second-family points with finite closures rule out uniformity in the middle regime. Lemma C.1 transfers a putative non-uniform guarantee to first-family sets without imposing UUS or coverage on those sets; the orthogonal covering lower bound and a selected/forbidden-index stream contradict it. At gamma_g>=e_g, 0 blocks g-points and a diagonal enumerating stream defeats all generators.

Guarantee level: Semantic regime separation with explicit mathematical positive generator and threshold bounds; no general computational promise. The lower-bound stream for non-uniformity need not cover its intermediate S_I set.

Scope/ambiguity: All four regimes belong to the slot. If e_{a1}=e_{a2}, the middle interval is empty, explicitly noted in the proof. Equal-scale parameters do not merge point families because their coordinate sets differ. Generator boundary gamma_g=e_g is negative; adversary lower boundaries belong to the regimes on their right.

Visual evidence: [page_9.png](visual-checks/page_9.png), [page_10.png](visual-checks/page_10.png), [page_17.png](visual-checks/page_17.png), [page_18.png](visual-checks/page_18.png), [page_24.png](visual-checks/page_24.png), [page_25.png](visual-checks/page_25.png), [page_26.png](visual-checks/page_26.png).

### C13 — Bi-Lipschitz metric separation outside doubling spaces

Claim locator: `claim:lrt26:example-4-11`. Edition: `arxiv-2602-07710-v2`.

Source locations: Example 4.11 (printed/PDF pp. 11; statement); Appendix C.5 (printed/PDF pp. 26, 27; metric, single class, all-scale proof); Lemma C.1; estimate (1) (printed/PDF pp. 17, 18; non-uniform lower-bound tools).

Assumptions and definitions: G1, G2, G3, G4, G6, G8; ell_2 ordinary/weighted norms, bi-Lipschitz equivalence, r-UUS, uniform/non-uniform generation, layers and doubling orbits.

- **simultaneous separation:** For every r>0 there are a single class H on ell_2 and a metric rho-prime bi-Lipschitz equivalent to ordinary rho such that H is r-UUS and (e,e)-uniformly generatable under rho for every 0<e<r, but is not (e,e)-non-uniformly generatable under rho-prime for any 0<e<r. The proof verifies r-UUS under both metrics.
- **source metric and supports:** rho-prime(x,y)=(sum_j delta_j(x_j-y_j)^2)^(1/2), delta_j=1 for odd j and 1/4 for even j; rho/2<=rho-prime<=rho. alpha_m=2^(3-m)r, a_{m,k}=alpha_m e_k; A_{m,I}={a_{m,2^n(2k+1)}:k in I,n>=0}. Supports are {0} union union_{m>=1} A_{m,I_m} for an independent infinite positive-index set I_m in each layer.

Proof/context: First-layer odd-coordinate points give r-UUS in both metrics. Under rho a sample covering number of at least 2 forces an observation of norm>e; its forward doubling orbit yields novel outputs forever, giving uniform threshold 2. Under rho-prime choose the layer with alpha_m/2<=e<alpha_m: odd points remain separated above e, but even descendants lie in the closed e-ball about 0. Two disjoint completions and Lemma C.1 transfer target thresholds to this layer, where selected/forbidden odd indices defeat them despite diverging covering numbers.

Guarantee level: Semantic separation at every stated scale for the same H and same rho-prime. The positive rule is explicit as a mathematical map; no representation/computability model is supplied.

Scope/ambiguity: The negative conclusion is failure of non-uniform generation, not an assertion of failure of generation in the limit. The source defines equivalence as bi-Lipschitz and gives explicit constants. The layer choice includes alpha_m/2=e; closed-ball novelty makes those even points non-novel. The metric may depend on r only through the chosen class construction; the displayed weight sequence itself is fixed.

Visual evidence: [page_11.png](visual-checks/page_11.png), [page_17.png](visual-checks/page_17.png), [page_18.png](visual-checks/page_18.png), [page_26.png](visual-checks/page_26.png), [page_27.png](visual-checks/page_27.png).

### C14 — Two-target obstruction for reversed novelty scales

Claim locator: `claim:lrt26:example-b-3`. Edition: `arxiv-2602-07710-v2`.

Source locations: Example B.3 and its proof (printed/PDF pp. 15; complete statement/construction); Theorem 3.1 (printed/PDF pp. 6; dimension lower bound to impossibility).

Assumptions and definitions: G1, G2, G3, G4, G6, G7; ell_2 ordinary metric, two hypotheses, internal closure cover, scale-closure dimension, finite maximum of target thresholds.

- **existence:** For every r>0 and 0<e_a<e_g<=r, there is a two-hypothesis r-UUS class H on ell_2 that is not (e_a,e_g)-non-uniformly generatable.
- **source construction:** Choose e_a<alpha<e_g; set a_k=alpha e_{3k}, S={0} union {a_k:k>=1}, T_1={2r e_{3k+1}:k>=1}, T_2={2r e_{3k+2}:k>=1}. The two supports are S union T_1 and S union T_2.
- **obstruction:** The closure of each sample a_1,...,a_t is exactly S, which is internally e_g-covered by {0}, while N(e_a;{a_1,...,a_t},rho) diverges. Thus scale-closure dimension is infinite and uniform generation fails; for two targets, any non-uniform generator would become uniform by taking the maximum of its two thresholds.

Proof/context: The separated tails T_1,T_2 provide r-UUS despite their common bounded part S. The obstruction is that a positive stream in S has arbitrarily large e_a-covering number while all points guaranteed by both targets are within generator distance e_g of 0.

Guarantee level: Semantic lower bound on all generators, with explicit two-support construction. It supplies no claim about computability or about generation in the limit.

Scope/ambiguity: Strict reversed ordering e_a<e_g is essential to choose alpha. The claim excludes non-uniform generation, and hence uniform generation, but does not state failure of generation in the limit. The two supports are distinct and the internal center 0 belongs to S.

Visual evidence: [page_6.png](visual-checks/page_6.png), [page_15.png](visual-checks/page_15.png).

## Limits of this inventory

All supplied author text (33 pages, including Appendices A–E) was read. Decisive formulas and their relevant proof context were inspected on rendered pages 1, 3–11, 13–33. Only reference/bibliographic page 12 and introductory page 2 were not rendered; their text was read. No mathematical source content needed for the listed slots was unavailable. Recovery provenance from the manifest was not independently reconstructed. This inventory freezes the source reading before any formalization or Stage 1 access.
