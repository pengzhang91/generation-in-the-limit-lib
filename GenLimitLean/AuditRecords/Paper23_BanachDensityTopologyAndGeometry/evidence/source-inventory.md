# P23 independent source inventory

Stage 2 first phase only. Source: **arXiv:2604.02385v2**, Kleinberg–Wei, *Validity, Sparse Holes, and Breadth in Language Generation: Banach Density, Topology, and Geometry*. The original local PDF has 80 pages and independently matches SHA-256 `c884ae86bdb9510c752b26cd5962ea94fb548885672b3cb0d24a2c2ab31cad3d`. Its arXiv stamp is 17 July 2026; the title-page date is 21 July 2026. Printed pages 1–76 correspond to PDF pages 5–80. No Lean or first-stage material has been read.

The JSON file contains the same 13 slots and more structured location fields. Source wording and proof context are distinguished where they differ; no source-to-Lean assessment is made.

## Source-global assumptions and conventions

**G1.** The candidate class X={L_1,L_2,...} is countable and known to the algorithm through its description; every candidate is infinite. A hidden target K belongs to X. The adversary reveals one target string per time step and must eventually enumerate all of K. The current results use full enumeration; partial enumeration is mentioned as prior work, not the present default.
Source locations: Introduction generation game (printed 1–2; PDF 5,6); Section 5 discrete model (printed 51–52; PDF 55,56).

**G2.** If S_t is the set of adversarial strings through t, generation in the limit means there exists a finite t* such that o_t belongs to K minus S_t for every t>=t*. The introduction only writes freshness against the adversary prefix. The algorithms use the stronger available convention: used by neither adversary nor generator. An adversary can reveal a point already generated, but the finite game explicitly disallows the adversary repeating itself. O is the set of generated target strings (or all generated strings intersected with K inside every density); multiplicity does not contribute.
Source locations: Introduction winning condition (printed 1; PDF 5); Availability and algorithm (printed 37; PDF 41); Game rules (printed 46; PDF 50).

**G3.** The author explicitly calls the results information theoretic, allowing access to the countable class description and disclaiming efficient finite-sample or polynomial-time procedures. No membership-decision algorithm, computable rank/tree, effective presentation of all candidates, or finite running-time bound is supplied as a standing theorem hypothesis. The text says a countable discrete universe admits an effective enumeration; this is an author normalization assertion, not a uniform effectiveness theorem for arbitrary language classes. In higher dimensions the detailed reduction assumes discrete coordinate-value sets; coordinatewise normalization preserves incidences with axis-parallel windows.
Source locations: Information-theoretic qualification (printed 6; PDF 10); Countable normalization (printed 19–20; PDF 23,24); Higher-dimensional discrete coordinate assumptions (printed 51; PDF 55).

**G4.** For A subset of positive naturals, delta_f(A,N)=liminf_(k→infinity) min_(1<=m<=f(k)) |A intersect [m,m+k-1]|/k, with nondecreasing f:N→N union {infinity}. At f=infinity the inner minimum/infimum ranges over all positive starts and gives lower Banach density. Density in K is read in the increasing order of K, equivalently |O intersect K intersect I|/|K intersect I| as |K intersect I|→infinity over coordinate intervals I. Relative intervals [a,b]_K use positions in the ordered target, not coordinate differences. In d dimensions ordinary density ranges over all bounded axis-parallel rectangles R with |R intersect K|→infinity.
Source locations: Definitions 3.1 and 3.2 (printed 17–18; PDF 21,22); Relative intervals (printed 39; PDF 43); Higher-dimensional relative density (printed 52; PDF 56).

**G5.** On X the basis is U_(L,F)={Lprime in X: F subseteq Lprime subseteq L}, for L in X and finite F in the countable universe. The source calls this topology Hausdorff and first countable. Derived sets are computed relative to X: X^(0)=X, X^(i+1)=d(X^(i)); the class rank is the least ordinal with empty derivative, infinity if none. Finite-rank results use a finite r. This is the containment-refined topology; Remark 1 distinguishes the coarser finite-evidence topology without the upper containment condition. The numerical point-rank convention on printed p.35 is internally inconsistent by one; strict rank comparisons and finite class rank are recorded without silently choosing one indexing.
Source locations: Containment-refined topology and derivatives (printed 19–20; PDF 23,24); Point rank setup (printed 35; PDF 39).

**G6.** For a fixed nondecreasing divergent g:[0,infinity)→[0,infinity), filtered density retains rectangles along which |R intersect K|/[g(Vol(R)) log Vol(R)]→infinity. The detailed theorem fixes g (named f there) before choosing its algorithm. Vol is geometric/discrete scale as used by the source, and the proof uses L(R)<=Vol(R)<=L(R)^d. Exact conventions for zero-volume, side-length-one and empty admissible families are not specified. The overview instead describes a sequence as nondegenerate if there exists some divergent function witnessing that ratio; that quantifier is kept separate from the fixed-function detailed theorem.
Source locations: Definition 5.3 (printed 57; PDF 61); Theorem 5.5 and Corollaries 5.6–5.7 (printed 57–58; PDF 61,62); Proof convention (printed 68–70; PDF 72,73,74).

**G7.** Default generation is speed one, one generator response to each adversary string. Speed C means up to C output strings per input, with C a fixed finite speed parameter (the overview says C>=1). The negative and positive speed extensions are separate source components, not unbounded or increasing output budgets.
Source locations: Speed C definition and zero-density extension (printed 22; PDF 26); Speed C positive extension (printed 51; PDF 55).

## C01 — Lower Banach density is the minimum of the lower window densities

Claim ID: `claim:kw26banach:claim-3-5`. Edition: `arxiv-2604-02385-v2`.

**Source locations.** Claim 3.5 (printed 19; PDF 23); Definitions 3.1–3.2 and Claim 3.3 (printed 17–18; PDF 21,22).

**Mathematical content.** For every A subseteq N and every admissible nondecreasing f:N→N union {infinity}, delta_B(A,N)<=delta_f(A,N). Equality is attained by the constant infinity window scale, so Banach density is a least member of this family, not merely a lower bound.

**Assumptions.**

- G4; A is arbitrary; no language class, rank or generation assumption.
- The f values allow at least one positive window start.

**Definitions needed.**

- The outer parameter is window length k→infinity; the inner domain is 1<=m<=f(k).
- Constant infinity recovers the all-starts formula (4).

**Effective/oracle/semantic status.** A semantic density-order statement. No effective/oracle or algorithmic guarantee is asserted or needed.

**Multipart scope.**

- Claim 3.5, with the identification f=infinity and monotonicity context.

**Potential source ambiguity.**

- The displayed window definition uses min even at f(k)=infinity, whereas the Banach definition uses inf. For fixed k these integer counts have a minimum; the source does not separately explain the convention.
- The claim does not say every pair of unequal functions yields a strict inequality.

**Visual checks.** [visual-checks/page_22.png](visual-checks/page_22.png), [visual-checks/page_23.png](visual-checks/page_23.png).

## C02 — Topological accumulation and infinite perfect towers

Claim ID: `claim:kw26banach:claim-3-6`. Edition: `arxiv-2604-02385-v2`.

**Source locations.** Definition 3.1 (infinite perfect tower) (printed 19; PDF 23); Claim 3.6, topology and Remark 1 (printed 20; PDF 24).

**Mathematical content.** For a language Lprime in X, Lprime is an accumulation point of the containment-refined topological space (X,T) if and only if it is the terminal language of an infinite perfect tower in X. A tower is a sequence Lambda_j of proper subsets of Lprime, every Lambda_j fixes at least one terminal string, and every terminal string is fixed by some Lambda_j. The accompanying explanation describes each string as eventually present permanently and each tower stage as contributing a permanent appearance.

**Assumptions.**

- G1 and G5; all tower terms and the terminal language belong to X.
- The basis imposes both finite evidence and upper containment.
- The accumulation point is a point of X, not a point in an ambient completion.

**Definitions needed.**

- U_(L,F)={Lprime in X:F subseteq Lprime subseteq L}.
- Proper subset Lambda_j subsetneq terminal for all j.
- Fixing is explained by eventual permanent occurrence and nonredundancy; no separate precise first-fixing definition is provided in this edition.

**Effective/oracle/semantic status.** A semantic equivalence. First countability and Hausdorffness are asserted in context; no computable tower extraction or oracle bound is claimed. The result is attributed to prior paper [21], whose independent content is not an allowed input in this phase.

**Multipart scope.**

- Both implications of Claim 3.6.
- All three tower conditions, including the nonredundancy/fixing condition, not only eventual coverage.

**Potential source ambiguity.**

- Definition number 3.1 is reused for the tower after density Definition 3.1.
- The paper does not explicitly formalize fixes beyond the following explanatory paragraph; mere union coverage is weaker than its stated intent.
- Earlier overview says the topology was used in [21,22], while Remark 1 explains an essential refinement relative to [22]; the concrete basis here governs this inventory.

**Visual checks.** [visual-checks/page_23.png](visual-checks/page_23.png), [visual-checks/page_24.png](visual-checks/page_24.png).

## C03 — A converging accumulation sequence eventually has smaller point rank

Claim ID: `claim:kw26banach:claim-4-11`. Edition: `arxiv-2604-02385-v2`.

**Source locations.** Claim 4.11 and proof (printed 38; PDF 42); Finite class rank and point rank setup (printed 35; PDF 39); Use in validity argument (printed 38–39; PDF 42,43).

**Mathematical content.** Within the finite-Cantor–Bendixson-rank setting of Section 4.2, the source states: if K is the limit point of J_1,J_2,..., then there is n such that CB(J_j)<CB(K) for every j>n. Its proof interprets this as a sequence converging to K: a subsequence of points of rank at least alpha=CB(K) would remain in X^(alpha), making K a point of X^(alpha+1), contrary to its rank.

**Assumptions.**

- G5 and the standing finite class rank r in Section 4.2.
- J_j and K are languages in X; sequence convergence uses the containment-refined topology.
- The proof needs genuine accumulation away from K, not a tail or infinitely repeated occurrences equal to K. This exclusion is implicit in its accumulation argument, not written in the claim.

**Definitions needed.**

- Point rank is determined by which finite derived layer contains/removes a point.
- A sequence merely having K as a cluster point is weaker than all its terms converging to K.

**Effective/oracle/semantic status.** A semantic eventual rank inequality, with no effective convergence modulus, index bound, decidable rank or oracle guarantee.

**Multipart scope.**

- Claim statement and the derived-set contradiction in its proof.
- Standing finite-rank context and later proper-subset use in the validity proof.

**Potential source ambiguity.**

- Literal limit point of a sequence can mean a cluster point, but the proof assumes convergence and says a selected subsequence still converges.
- Allowing J_j=K infinitely often defeats a strict eventual inequality; the printed statement does not explicitly exclude this.
- Printed p.35 assigns rank i to X^(i-1) minus X^(i) but then assigns rank 0 to X minus X^(1); printed p.38 instead uses rank>=alpha iff membership in X^(alpha). These conventions must not be silently merged.

**Visual checks.** [visual-checks/page_39.png](visual-checks/page_39.png), [visual-checks/page_42.png](visual-checks/page_42.png).

## C04 — Prefix least common ancestors rise at most the tree depth

Claim ID: `claim:kw26banach:claim-4-18`. Edition: `arxiv-2604-02385-v2`.

**Source locations.** Claim 4.18 and proof (printed 41–42; PDF 45,46).

**Mathematical content.** In a rooted tree T of depth at most r, take a nonempty finite sequence v_1,...,v_m of vertices, allowing repetitions. Put V_i={v_1,...,v_i} and u_i=LCA(V_i). If x<=_T y means x is an ancestor of y, then u_m<=_T...<=_T u_1. The number of i in {2,...,m} with u_i != u_(i-1) is at most r.

**Assumptions.**

- One rooted tree with unique root paths and well-defined LCAs of nonempty finite vertex sets.
- Finite depth r, measured by number of edges from a root of depth 0.
- m>=1; repeated vertices are explicitly permitted. No finiteness of the entire tree is required by the statement.

**Definitions needed.**

- Ancestor relation includes equality.
- A strict prefix-LCA change decreases its depth by at least one.

**Effective/oracle/semantic status.** Pure finite combinatorics; no language, rank, generation, effective or oracle assumption belongs to the abstract claim.

**Multipart scope.**

- Monotone ancestor chain.
- Cardinality bound |{i:2<=i<=m and u_i!=u_(i-1)}|<=r.

**Potential source ambiguity.**

- The prose says strictly bounded above but the decisive formula and proof give <=r, not <r.
- The surrounding application uses class rank as an upper bound on a structural-tree depth; that application is distinct from the abstract tree claim.

**Visual checks.** [visual-checks/page_45.png](visual-checks/page_45.png), [visual-checks/page_46.png](visual-checks/page_46.png).

## C05 — An adjacent pair attains the LCA of a finite ordered collection

Claim ID: `claim:kw26banach:claim-4-20`. Edition: `arxiv-2604-02385-v2`.

**Source locations.** Claim 4.20 (printed 42; PDF 46); Proof and application (printed 43; PDF 47).

**Mathematical content.** Let Q=LCA(Q_1,...,Q_s) in a rooted tree, with s>=2. In every linear ordering of these vertices, some adjacent pair Q_i,Q_(i+1), 1<=i<s, has LCA(Q_i,Q_(i+1))=Q. If Q occurs among the vertices it supplies an adjacent pair; otherwise some adjacent vertices cross between different child-subtrees of Q.

**Assumptions.**

- A rooted tree and a nonempty finite ordered family with at least two terms.
- No height bound, CB rank, language inclusion or generation hypothesis.

**Definitions needed.**

- The ordering is arbitrary, not a tree traversal order.
- LCA is the deepest common ancestor, and a vertex is its own ancestor.

**Effective/oracle/semantic status.** Semantic existence of an adjacent index, proved by elementary tree structure; no special computational access is asserted.

**Multipart scope.**

- All orderings are covered.
- Includes the case where Q itself is one of the terms and the case where all terms are below Q.

**Potential source ambiguity.**

- The source calls S both a set and a finite sequence; it does not explicitly discuss repetitions. The proof and conclusion continue to make sense with repetitions, but a set-based reading has distinct elements.

**Visual checks.** [visual-checks/page_46.png](visual-checks/page_46.png).

## C06 — Window-scale monotonicity

Claim ID: `claim:kw26banach:claim-3-3`. Edition: `arxiv-2604-02385-v2`.

**Source locations.** Claim 3.3 and Definition 3.2 (printed 18; PDF 22).

**Mathematical content.** For A subseteq N and nondecreasing f,g:N→N union {infinity} satisfying f(k)>=g(k) for every k, delta_f(A,N)<=delta_g(A,N). For each fixed window length the larger scale permits a superset of the window starts, and the inequality persists through liminf.

**Assumptions.**

- G4; both functions are in the stated density domain and ordered pointwise.
- No unboundedness assumption; bounded and infinite-valued scales are allowed.

**Definitions needed.**

- Delta_f uses windows [m,m+k-1] of exactly k positive integers.
- Function comparison is pointwise, not merely asymptotic growth.

**Effective/oracle/semantic status.** Semantic monotonicity only; no algorithmic or oracle content.

**Multipart scope.**

- The full non-strict density inequality for arbitrary A.

**Potential source ambiguity.**

- Nearby prose refers to faster growth and strictly expanding domains, but the formal claim is the weak inequality under pointwise order; it does not prove strict density decrease.

**Visual checks.** [visual-checks/page_22.png](visual-checks/page_22.png).

## C07 — Nice finite window configurations are equivalent to unboundedness

Claim ID: `claim:kw26banach:claim-4-4`. Edition: `arxiv-2604-02385-v2`.

**Source locations.** Nice definition and Claim 4.4 (printed 22; PDF 26); Claim 7.1 and proof (printed 74; PDF 78).

**Mathematical content.** For an increasing natural-valued function f, nice means: for each T>0 there exist m>=2 and naturals k_1<=...<=k_m and T<a_1<...<a_m such that a_(i+1)>=a_i+k_i+1 and a_i<=f(k_i). Claims 4.4 and 7.1 assert that this is equivalent to f having no uniform upper bound. The appendix proves necessity with T equal to a proposed bound and sufficiency with m=2: choose f(k_1)>T, set a_1=f(k_1), a_2=a_1+k_1+1, then choose k_2>k_1 with f(k_2)>=a_2.

**Assumptions.**

- The precise claims use f:N→N and call f increasing.
- The preceding definition allows N union {infinity}; Theorem 4.1 uses nondecreasing functions with limsup infinity.
- Only existence of some m>=2 for each T is required, not configurations of every prescribed length.

**Definitions needed.**

- All four nice conditions and the quantifier order for T,m,k_i,a_i.
- Unboundedness means for every proposed finite upper bound there exists a larger function value.

**Effective/oracle/semantic status.** A finite existential construction from semantic unboundedness. No computable f, effective witness selector or oracle running-time bound is assumed.

**Multipart scope.**

- Main-text Claim 4.4.
- Appendix Claim 7.1 and its two directions.

**Potential source ambiguity.**

- Increasing is not explicitly distinguished from nondecreasing; surrounding text uses both.
- The appendix writes a_1=f(k_1), which requires finite f(k_1), and both numbered claims restrict to N-valued f. Application to the infinity-valued domain of Theorem 4.1 is not separately handled there.
- Intervals later written [a_i,a_i+k_i] have k_i+1 points; the density definition uses [m,m+k-1]. This is an endpoint convention to keep separate from nice itself.

**Visual checks.** [visual-checks/page_26.png](visual-checks/page_26.png), [visual-checks/page_78.png](visual-checks/page_78.png).

## C08 — Unbounded window scales admit a countable hard class with zero output density

Claim ID: `claim:kw26banach:theorem-4-1`. Edition: `arxiv-2604-02385-v2`.

**Source locations.** Overview Theorem 2.2 (printed 8; PDF 12); Theorem 4.1 and Corollaries 4.2–4.3 (printed 22; PDF 26); Construction and proof (printed 22–28; PDF 26,27,28,29,30,31,32).

**Mathematical content.** For every nondecreasing f:N→N union {infinity} with limsup f(n)=infinity, there exists a countable class C of infinite languages for which every algorithm that generates in the limit on C has an adversarial target/enumeration yielding delta_f(O,K)=0. Corollary 4.2 and Overview 2.2 specialize this to lower Banach density. Corollary 4.3 says the Banach zero-density obstruction persists for generators of any fixed finite speed C. The exhibited family has infinite CB rank and contains N as the final target for the continuing mega-step construction.

**Assumptions.**

- G1–G5 and G7; the generator must succeed at generation in the limit on all class members, enabling simulated-target contradictions.
- Quantifier order: f first, then a fixed countable class, then each generator, then an adversarial enumeration/target. The class does not adapt separately to each generator.
- The speed extension concerns a fixed finite bound C per input.

**Definitions needed.**

- Delta_f and ordinary Banach density as in G4.
- Nice configurations and a separated sequence of groups of intervals.
- The class consists of finite-prefix additions and bounded shifts/extensions of a fixed sparse marker set P, plus N; its integer tuple parameters make it countable.
- Perfect towers at finite extension parameters justify ending failed rounds and preserve class membership; sparse refill steps ensure eventual enumeration of all target strings.

**Effective/oracle/semantic status.** Information-theoretic adversarial impossibility against any successful generator, including ones using the entire class description. The proof supplies semantic/adaptive adversary strategies and countable languages; it does not state computable presentations or effective stopping-time bounds. It is not the assertion that every run of every generator has density zero.

**Multipart scope.**

- Overview Theorem 2.2: countable Banach-density-zero class.
- Theorem 4.1: every nondecreasing unbounded f-window scale has such a class.
- Corollary 4.2: Banach specialization.
- Corollary 4.3: fixed-speed-C Banach impossibility.
- Proof context: countability, infinite rank, increasing missed intervals, and full enumeration of N.

**Potential source ambiguity.**

- The overview and theorem abbreviate adversarial quantifiers; the proof and model supply a bad enumeration, not all enumerations.
- The main theorem includes infinity-valued f, but the invoked nice lemma is printed for natural-valued f; the proof also uses f inverse and f(k)<N_(s+1), requiring an interpretation for infinite values.
- Repeated endpoint notation uses [a,a+k] while calling its length k; this is immaterial to a zero limiting density but not an exact finite-window identity.
- Corollary 4.3 reuses C as both class name and speed symbol; no unbounded-speed statement follows.

**Visual checks.** [visual-checks/page_12.png](visual-checks/page_12.png), [visual-checks/page_26.png](visual-checks/page_26.png).

## C09 — Finite rank gives the optimal half-density guarantee in one dimension

Claim ID: `claim:kw26banach:theorem-4-5`. Edition: `arxiv-2604-02385-v2`.

**Source locations.** Overview Theorem 2.3 (printed 9; PDF 13); Theorem 4.5 and Corollaries 4.6–4.7 (printed 29; PDF 33); Algorithm, validity and density proof (printed 30–51; PDF 34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55).

**Mathematical content.** For every countable class X of infinite languages having finite rank in the containment-refined CB topology, there is a generator that succeeds in the limit for every target and every enumeration and whose output has lower Banach density at least 1/2 in the true language. The overview calls 1/2 optimal. Corollary 4.6 transfers the same half guarantee to lower f-window densities for unbounded f. Corollary 4.7 asserts that for every bijection rho:N→N, there is such a generator under the reordered universe; the generator may be chosen for that ordering.

**Assumptions.**

- G1–G5; the finite rank belongs to X itself, not its completion.
- No bound on lengths of inclusion chains or coordinate sparsity of K is assumed.
- The fixed language collection and chosen ordering are available to the algorithm; guarantees quantify over all targets in it and all full adversary enumerations.

**Definitions needed.**

- Finite CB rank and containment-refined topology.
- A_acc guesses the true language infinitely often (Theorem 4.8, attributed to [21]); strict-critical chains organize its guesses.
- A static structural tree points toward earlier-index higher-rank candidate supersets; pullbacks and locally growing pods support eventual validity.
- Density is relative to target order; the finite interval game bounds leakage by O_r(log ell), yielding 1/2-o(1) uniformly on sufficiently long intervals.

**Effective/oracle/semantic status.** Existence of an information-theoretic generator with eventual validity and a limiting density bound. No finite-sample convergence rate, computable CB-tree construction or decidable containment/rank oracle implementation is established. The coloring-free one-dimensional construction uses semantic class structure. The source separately states the speed-C C/(C+1) extension at Corollary 4.26, printed p.51/PDF55.

**Multipart scope.**

- Overview Theorem 2.3 and its optimality language.
- Theorem 4.5: eventual validity plus Banach density >=1/2.
- Corollary 4.6: unbounded f-window density >=1/2.
- Corollary 4.7: a generator exists for each reordered universe.
- Relevant proof context includes Claim 4.11, structural-tree depth, pods, and the finite game; Corollary 4.26 is a related extension rather than one of this slot’s enumerated claims.

**Potential source ambiguity.**

- The source does not claim every infinite-rank class fails; it explicitly leaves positive infinite-rank classes open.
- Corollary 4.6 writes any unbounded f:N→N+ without repeating nondecreasing; Definition 3.2 supplies that admissibility condition.
- The ordering corollary does not assert that one fixed output set has half Banach density under every permutation.
- Point-rank indexing and the convergence/exclusion ambiguity of Claim 4.11 remain as recorded in C03.
- The tree definition says a sequence including L has a higher-rank limit, while surrounding discussion treats parent languages as supersets of L; mere inclusion as an arbitrary early sequence term alone does not impose that containment. This source convention is not repaired here.

**Visual checks.** [visual-checks/page_13.png](visual-checks/page_13.png), [visual-checks/page_33.png](visual-checks/page_33.png), [visual-checks/page_39.png](visual-checks/page_39.png), [visual-checks/page_42.png](visual-checks/page_42.png), [visual-checks/page_45.png](visual-checks/page_45.png), [visual-checks/page_46.png](visual-checks/page_46.png).

## C10 — Ordinary rectangular density can be forced to zero for a known singleton target

Claim ID: `claim:kw26banach:theorem-5-1`. Edition: `arxiv-2604-02385-v2`.

**Source locations.** Overview Theorem 2.4 (printed 10; PDF 14); Theorem 5.1 (printed 53; PDF 57); Copy-strategy proof and singleton interpretation (printed 53–55; PDF 57,58,59).

**Mathematical content.** For each d>=2 there is an infinite K subseteq Z^d such that even for the known singleton class {K}, every generator can be opposed by a full enumeration of K yielding ordinary lower Banach density zero over axis-parallel rectangles. Overview 2.4 displays liminf as |R intersect K|→infinity. The detailed Theorem 5.1 instead displays liminf as |R intersect O intersect K|→infinity with the same ratio |R intersect O intersect K|/|R intersect K|=0. Both printed limit conditions are preserved as distinct source components.

**Assumptions.**

- G1–G3 and speed one from G7, with d>=2.
- Rectangles have arbitrary locations and side-length ratios; this is ordinary density with no volume filter.
- The target K is fixed independently of the generator; the enumeration can depend on its actions.
- Successful generators obey eventual validity/freshness; the proof’s copy strategy invokes prohibition of outputs previously revealed by the adversary.

**Definitions needed.**

- Ordinary density denominator counts target points in R.
- Theorem 5.2 (as stated here) supplies finite d-dimensional point sets whose every two-coloring has arbitrarily large monochromatic rectangular intersections.
- K is a union of separated paired translated copies at increasing monochromatic sizes; response-copying forces a large missed rectangle in one copy and slow refills preserve full enumeration.

**Effective/oracle/semantic status.** An information-theoretic adversarial impossibility even with K known. The external Ramsey theorem is used as stated in this PDF; its original source is not read in this phase. No effective construction complexity is claimed.

**Multipart scope.**

- Overview Theorem 2.4, including its target-count limit condition.
- Detailed Theorem 5.1, including its different output-count limit condition.
- Relevant proof: paired-copy strategy and arbitrarily large all-adversary rectangles.
- The closing interpretation restricts failure to some known languages; it does not say every singleton target has zero benchmark.

**Potential source ambiguity.**

- The different limit conditions are visible in the rendered PDF, not extraction artifacts. Rectangles containing no output witness the overview condition, but alone do not witness the displayed detailed condition requiring output count to tend to infinity.
- The detailed proof repeatedly concludes the output-count display after constructing empty-output rectangles; this inventory does not silently replace its subscript.
- The statement does not promise a bad result for every K or a single enumeration that defeats every generator simultaneously.
- The proof first reasons with full freshness; handling finitely many early invalid/repeated outputs is implicit in the generation-in-the-limit model.

**Visual checks.** [visual-checks/page_14.png](visual-checks/page_14.png), [visual-checks/page_57.png](visual-checks/page_57.png).

## C11 — Finite rank gives nearly half filtered density in higher dimensions

Claim ID: `claim:kw26banach:theorem-5-5`. Edition: `arxiv-2604-02385-v2`.

**Source locations.** Overview Theorem 2.5 and nondegenerate sequences (printed 10–11; PDF 14,15); Definition 5.3 and Theorem 5.5 (printed 57–58; PDF 61,62); Corollaries 5.6–5.7 and formula (19) (printed 58; PDF 62); Filtered algorithm and density proof (printed 65–70; PDF 69,70,71,72,73,74); Appendix Claims 7.2–7.3 (printed 74–76; PDF 78,79,80).

**Mathematical content.** Fix a nondecreasing divergent f:[0,infinity)→[0,infinity), a countable finite-CB-rank class X of infinite subsets of a product U_1×...×U_d of countable string sets, and epsilon>0. Theorem 5.5 asserts a generator with eventual validity and liminf |R intersect K intersect O|/|R intersect K|>=1/2-epsilon over all axis-parallel rectangles satisfying |R intersect K|/[f(Vol(R)) log Vol(R)]→infinity. Corollary 5.6 restricts to cubes B(x,r) of side r, requiring |B(x,r) intersect K|/[f(r^d) log r^d]→infinity. Corollary 5.7 fixes a rectangular shape R and considers all translates and dilations R(x,r), requiring |R(x,r) intersect K|/(log r)^2→infinity; it literally asserts an algorithm that identifies any target in the limit and has density >=1/2-epsilon. Overview 2.5 states nearly half filtered density using its sequence-based definition (2).

**Assumptions.**

- G1–G3 and G5–G6, with fixed positive finite dimension in the higher-dimensional setting.
- The class has finite CB rank in the same containment-refined topology; each coordinate universe is countable, with the discrete coordinate normalization used to speak of rectangles in Z^d.
- Theorem 5.5 fixes f and epsilon before the generator is chosen; all targets and full enumerations are covered for that choice.
- The rectangle restriction is essential: ordinary density is not asserted, even for finite-rank singleton classes.
- Fixed-shape Corollary 5.7 has a log-squared scale condition, not the arbitrary f formula repeated verbatim.

**Definitions needed.**

- Definition 5.3 filtered density for a fixed divergent scale function.
- B(x,r) is a cube centered at x with side r; R(x,r) has a fixed side-length ratio.
- The algorithm partitions Z^d into slowly growing infinity-norm shells, preserves assigned colors, and responds within a shell using opposite-color points where possible.
- Claim 5.11/appendix 7.2 constructs an eventually bounded strictly concave divergent minorant of f. Lemma 5.10 uses its inverse to obtain a shell partition meeting at most f(ell)+2 regions in a side-ell cube.
- Claim 5.13/appendix 7.3 partitions a rectangle intersected with a shell into at most 2d disjoint rectangles. Theorem 5.9 controls discrepancy on each piece; finite CB rank controls the number of pod changes in a shell.

**Effective/oracle/semantic status.** An information-theoretic generator existence statement for each fixed filter/accuracy parameter. The discrepancy ingredient uses a finite probabilistic existence proof and compactness for infinite sets, not an effective global coloring algorithm. No polynomial-time or computable class-presentation guarantee is provided. Corollary 5.7’s literal identification guarantee is recorded separately from generation.

**Multipart scope.**

- Overview Theorem 2.5, with its nondegenerate-sequence definition.
- Theorem 5.5 for all rectangles and a fixed f.
- Corollary 5.6 for cubes with the displayed f(r^d) log r^d denominator.
- Corollary 5.7 for a fixed rectangular shape, translates/dilates, log-squared condition, and literal identification wording.
- Relevant Appendix Claims 7.2 and 7.3, including their links to Claims 5.11 and 5.13.

**Potential source ambiguity.**

- Overview nondegeneracy is existential in a divergent function for each sequence; the detailed theorem fixes f before selecting an algorithm. The source does not explicitly reconcile these quantifiers.
- Corollary 5.7 says identifies rather than generates; it must not silently be weakened during later comparison.
- The source repeatedly calls Corollary 5.6 Theorem 5.6 and the final proof says it completes Theorem 5.6, although the main all-rectangle statement is Theorem 5.5.
- Volume and geometric side conventions are not fully fixed for degenerate rectangles. The proof’s L<=Vol<=L^d assumes positive side lengths at least one.
- Appendix 7.2 only promises g<=f eventually, while Lemma 5.10’s proof uses that inequality for every ell; its eventual-density use may ignore bounded scales but this is not explicitly separated.
- Appendix 7.3’s shell proof uses radii minus one although Lemma 5.10 permits real radii, and says boundary inclusion is ignored. The at-most-2d decomposition is the mathematical claim.
- The detailed proof uses opposite colors and a discrepancy-to-density argument; no stronger ordinary rectangular bound or exact 1/2 bound is asserted.

**Visual checks.** [visual-checks/page_14.png](visual-checks/page_14.png), [visual-checks/page_15.png](visual-checks/page_15.png), [visual-checks/page_61.png](visual-checks/page_61.png), [visual-checks/page_62.png](visual-checks/page_62.png), [visual-checks/page_78.png](visual-checks/page_78.png), [visual-checks/page_80.png](visual-checks/page_80.png).

## C12 — Origin-centered cubes admit the universal asymptotic half guarantee

Claim ID: `claim:kw26banach:theorem-5-8`. Edition: `arxiv-2604-02385-v2`.

**Source locations.** Theorem 5.8 and proof (printed 59; PDF 63).

**Mathematical content.** For every countable class X of infinite languages in Z^d, there is a generator that succeeds in the limit and achieves the optimal half lower asymptotic density in the true K, where the windows are cubes B(0,r) centered at the origin and r→infinity. The displayed prose says always 1/2; the proof transports the one-dimensional half guarantee by enumerating lattice shells in increasing infinity norm and ordering within each shell lexicographically, so every origin-centered cube becomes an initial segment of a fixed enumeration.

**Assumptions.**

- G1–G3 and speed one; fixed finite dimension.
- No finite-CB-rank assumption.
- No nondegeneracy/filtered-volume requirement.
- The windows are nested origin-centered cubes, not translated cubes and not all anchored rectangular aspect ratios.

**Definitions needed.**

- Asymptotic relative density is liminf_(r→infinity) |B(0,r) intersect K intersect O|/|B(0,r) intersect K|.
- Shell S_k={x:||x||_infinity=k}; order shells and use lexicographic order within each finite shell.
- The proof invokes the prior one-dimensional lower asymptotic density algorithm [22], as stated here.

**Effective/oracle/semantic status.** Existence of an information-theoretic eventual generator. The shell enumeration itself is explicit, but no effective implementation of the arbitrary-class generation algorithm, sample rate or oracle bound is supplied. Optimality is the uniform speed-one benchmark, not a claim every run must have exactly half its points generated.

**Multipart scope.**

- Theorem 5.8 with its origin-centered-cube density convention.
- Shell-order reduction to one-dimensional prefix density.
- The text explicitly contrasts this with unfiltered translated-window Banach density.

**Potential source ambiguity.**

- The theorem says density always 1/2; surrounding text and the reduction present a guaranteed lower bound of 1/2 and optimal worst-case constant. Exact equality on every enumeration is not justified by the stated reduction.
- The proof writes rho(x)=(2k-1)^d+N(x) even at shell k=0, with N counting earlier points in the shell, and alternates between N and prefixes starting at 0. A special convention for the origin/initial index is omitted; finite initial indexing does not change the claimed asymptotic guarantee.
- The prose calls B(0,r) anchored at the origin, but the notation and shell proof describe centered cubes.

**Visual checks.** [visual-checks/page_63.png](visual-checks/page_63.png).

## C13 — Multi-level discrepancy and the asymmetric Lovasz local lemma

Claim ID: `claim:kw26banach:theorem-5-9`. Edition: `arxiv-2604-02385-v2`.

**Source locations.** Theorem 5.9 (printed 62; PDF 66); Finite-grid LLL proof and compactness extension (printed 62–65; PDF 66,67,68,69); Theorem 7.4 (printed 76; PDF 80).

**Mathematical content.** Theorem 5.9: for arbitrary possibly infinite P subseteq Z^d, epsilon in (0,1) and alpha>0, put c0=(2*pi^2/(3*epsilon^2))^(alpha/(2*d)). For a rectangle R in R^d with m=|R intersect P|>=1, the source defines a nonnegative integer tier j by (c0/2^j)*L(R)^alpha<=m<(c0/2^(j-1))*L(R)^alpha, where L is the maximum geometric side length. It asserts one global coloring chi:P→{-1,+1} satisfying |sum_(x in R intersect P) chi(x)|<=epsilon*m+beta*sqrt(m*j)+gamma(m)*sqrt(m) for every rectangle, with beta=sqrt(2*(2*d/alpha+1)*ln 2), gamma(m)=sqrt(2*(2*d/alpha+2)*ln m+4*ln 2). The grouped appendix result is Theorem 7.4: for finitely many events A_i with a dependency graph, if x_i in (0,1) and Pr(A_i)<=x_i product_(j in Gamma(i))(1-x_j), then Pr(intersection_i complement A_i)>=product_i(1-x_i)>0.

**Assumptions.**

- P is any lattice point set and may be finite or infinite; dimension is fixed and positive (the application is d>=2).
- epsilon in (0,1), alpha>0, and nonempty finite R intersect P.
- The tier must satisfy the exact displayed lower and strict upper bounds and j>=0.
- For Theorem 7.4, the event family is finite, the graph genuinely encodes joint independence from non-neighbor events, and every weight lies strictly between zero and one.

**Definitions needed.**

- Discrepancy is the absolute signed sum over the points in the rectangle.
- L(R) is maximum geometric side length, not rectangle volume or point count.
- The finite proof restricts P to [-N,N]^d, bounds rectangle capacities by c0^(-2*d/alpha)*2^(2*d*j/alpha)*k^(2*d/alpha), and uses independent unbiased point colors plus weights (1/2)*k^(-p)*2^(-q*j), p=2*d/alpha+2, q=2*d/alpha+1.
- The infinite extension uses compactness of {-1,+1}^P (sequential compactness because P is countable) and finite closed cylinder constraints, not an infinite-event version of Theorem 7.4.

**Effective/oracle/semantic status.** Semantic existence of a global coloring simultaneous for all rectangles. The finite argument proves positive probability, and the infinite argument is compactness-based. It does not give an efficient randomized construction, an effective infinite coloring procedure, or an oracle complexity guarantee. The appendix LLL includes the positive lower bound, not only existence.

**Multipart scope.**

- Theorem 5.9 with exact c0, tier inequality, beta and gamma.
- Finite-grid asymmetric-LLL application and countable compactness extension.
- Theorem 7.4 in full: finite dependency assumptions, weight hypothesis and positive quantitative avoidance bound.

**Potential source ambiguity.**

- The tier formula does not provide a nonnegative j when m>=2*c0*L(R)^alpha, despite asserting that every nonempty rectangle has a unique tier. The displayed statement does not say to cap j at zero or treat dense rectangles separately.
- If zero geometric side lengths are allowed, L(R)=0 is another case without the stated tier. Positive-side conventions are not made explicit.
- The theorem quantifies over real-coordinate rectangles, while the capacity proof counts integer intervals and treats the geometric side-length cutoff as an integer interval-length cutoff; canonical lattice representatives and endpoint conventions are implicit.
- The theorem says constants depend only on d and alpha after c0, but gamma explicitly also varies with m, as its displayed formula records.
- Theorem 7.4’s mutually independent wording should be read as independence from the sigma-algebra generated by non-neighbor events; pairwise independence alone is not the dependency hypothesis used by LLL.

**Visual checks.** [visual-checks/page_66.png](visual-checks/page_66.png), [visual-checks/page_80.png](visual-checks/page_80.png).

## Source limitations and stop condition

- All 80 pages of the exact local edition were available and the full page-marked author text was read. No source pages were unavailable.
- Only author base-page content was used; visual checks used the annotation-removed review derivative, with the original PDF hash independently checked.
- Prior references [21], [22], the original rectangular Ramsey source and the original LLL book were not accessed; results imported from them are inventoried only as this edition states them.
- Source-internal ambiguities are identified in the relevant items; no correction or strengthening is silently substituted.
- No Lean, Stage 1, owner metadata, stage3 context, old audits, PaperMaps, registry assessment or external primary-source material was accessed.

Inventory complete. Comparison has not started. Stop here for coordinator freeze and subsequent authorization.
