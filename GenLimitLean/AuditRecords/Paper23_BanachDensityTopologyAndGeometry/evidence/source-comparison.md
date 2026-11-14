# P23 — Stage 2 source comparison

## Identity, isolation and scope

This is the continuation of the same source-informed Stage 2 reviewer after its independent inventory was frozen. It compares statements and defining interfaces, not theorem proof bodies or full algorithm correctness. Requested configuration: gpt-6.1-sol / xhigh. The actual backend revision and independently attested runtime settings are unobservable. No human-review credit is claimed.

The pinned edition is arXiv:2604.02385v2, by Jon Kleinberg and Fan Wei, with arXiv stamp 17 July 2026 and title-page date 21 July 2026. Its original 80-page PDF independently matches SHA-256 `c884ae86bdb9510c752b26cd5962ea94fb548885672b3cb0d24a2c2ab31cad3d`. PDF pages 1–4 are front matter; printed pages 1–76 are PDF pages 5–80. Visual evidence comes from the annotation-removed derivative; annotation payloads are excluded.

The source inventory freeze is dated 2026-11-14 06:40:46.713525 UTC; the independent Stage 1 freeze is dated 06:49:38.871741 UTC. All six frozen report hashes were rechecked before comparison and remain unchanged. The claimed source snapshot hash `e56b617a39899cb9acfd94b61e19680934bf78aa1f40d8d07d8e7f1d10bee1fc` is supplied export metadata; the raw source tree was not reopened or independently hashed.

All 13 current claim slots and their grouped source components are covered below. Eight registered theorem types occupy seven slots; six main-result slots have no matching full theorem in the supplied native census after search. Native results beyond the facade were inspected so a missing wrapper is not confused with missing mathematics. The neutral external predecessor-class supplement resolves C05 as a faithful statement-level generalization; no registered slot remains unclassified.

## Independent inventory and source-global assumptions

The frozen [source inventory](source-inventory.md) and [structured inventory](source-inventory.json) remain the independent source-first record. The complete 80-page author text, including the appendix, was read before Lean/Stage 1 access; 20 decisive pages were visually inspected. Each dossier below repeats the mathematical claim and exact page locators. Source-global conventions are:

- **G1** The candidate class X={L_1,L_2,...} is countable and known to the algorithm through its description; every candidate is infinite. A hidden target K belongs to X. The adversary reveals one target string per time step and must eventually enumerate all of K. The current results use full enumeration; partial enumeration is mentioned as prior work, not the present default.
- **G2** If S_t is the set of adversarial strings through t, generation in the limit means there exists a finite t* such that o_t belongs to K minus S_t for every t>=t*. The introduction only writes freshness against the adversary prefix. The algorithms use the stronger available convention: used by neither adversary nor generator. An adversary can reveal a point already generated, but the finite game explicitly disallows the adversary repeating itself. O is the set of generated target strings (or all generated strings intersected with K inside every density); multiplicity does not contribute.
- **G3** The author explicitly calls the results information theoretic, allowing access to the countable class description and disclaiming efficient finite-sample or polynomial-time procedures. No membership-decision algorithm, computable rank/tree, effective presentation of all candidates, or finite running-time bound is supplied as a standing theorem hypothesis. The text says a countable discrete universe admits an effective enumeration; this is an author normalization assertion, not a uniform effectiveness theorem for arbitrary language classes. In higher dimensions the detailed reduction assumes discrete coordinate-value sets; coordinatewise normalization preserves incidences with axis-parallel windows.
- **G4** For A subset of positive naturals, delta_f(A,N)=liminf_(k→infinity) min_(1<=m<=f(k)) |A intersect [m,m+k-1]|/k, with nondecreasing f:N→N union {infinity}. At f=infinity the inner minimum/infimum ranges over all positive starts and gives lower Banach density. Density in K is read in the increasing order of K, equivalently |O intersect K intersect I|/|K intersect I| as |K intersect I|→infinity over coordinate intervals I. Relative intervals [a,b]_K use positions in the ordered target, not coordinate differences. In d dimensions ordinary density ranges over all bounded axis-parallel rectangles R with |R intersect K|→infinity.
- **G5** On X the basis is U_(L,F)={Lprime in X: F subseteq Lprime subseteq L}, for L in X and finite F in the countable universe. The source calls this topology Hausdorff and first countable. Derived sets are computed relative to X: X^(0)=X, X^(i+1)=d(X^(i)); the class rank is the least ordinal with empty derivative, infinity if none. Finite-rank results use a finite r. This is the containment-refined topology; Remark 1 distinguishes the coarser finite-evidence topology without the upper containment condition. The numerical point-rank convention on printed p.35 is internally inconsistent by one; strict rank comparisons and finite class rank are recorded without silently choosing one indexing.
- **G6** For a fixed nondecreasing divergent g:[0,infinity)→[0,infinity), filtered density retains rectangles along which |R intersect K|/[g(Vol(R)) log Vol(R)]→infinity. The detailed theorem fixes g (named f there) before choosing its algorithm. Vol is geometric/discrete scale as used by the source, and the proof uses L(R)<=Vol(R)<=L(R)^d. Exact conventions for zero-volume, side-length-one and empty admissible families are not specified. The overview instead describes a sequence as nondegenerate if there exists some divergent function witnessing that ratio; that quantifier is kept separate from the fixed-function detailed theorem.
- **G7** Default generation is speed one, one generator response to each adversary string. Speed C means up to C output strings per input, with C a fixed finite speed parameter (the overview says C>=1). The negative and positive speed extensions are separate source components, not unbounded or increasing output budgets.

The topology basis matches after refinement to neighborhoods centered at the point K: any source basic set U_(L,F) containing K contains U_(K,F). Internal versus ambient derivatives are distinguished below; from the whole Hausdorff space their finite iterates agree mathematically. All relevant density ratios count sets of target points; no distribution, support-loss or single-output-loss formalism occurs.

## Comparison matrix

| Slot | Source components | Correspondence | Native coverage / material qualification |
|---|---|---|---|
| C01 | Claim 3.5 | equivalent | The source least-density assertion is represented by an infimum identity, the separate all-f inequality, and the explicit constant-top equality. Positive-length windows agree exactly after translating inclusive integer notation to half-open notation. |
| C02 | Claim 3.6, both directions; Definition 3.1 tower: properness, per-stage fixing, complete fixing; Named auxiliary construction and same-witness properties | faithful-generalization | The concrete basis and all three perfect-tower clauses match the source explanation. The theorem does not require the class X to be countable or its other languages to be infinite, and accepts a semantic presentation of the terminal. |
| C03 | Claim 4.11 under convergent proper approximation; Convergence formulation; Derived-layer exit underlying the claim | faithful-specialization | The target states the intended eventual rank drop for a genuinely approaching proper-subset sequence in a finite-rank class. It does not formalize the unqualified literal source sentence for arbitrary sequences merely having K as a cluster point or containing K infinitely often. |
| C04 | Claim 4.18 monotone ancestral chain; Claim 4.18 strict-change cardinality <=r | faithful-generalization | Both source conclusion components are represented, using the running meet in a semilattice and a natural strictly increasing depth. The monotone ancestor chain is a separate native theorem, so the cardinality facade is not a missing half of the claim. |
| C05 | Claim 4.20 | faithful-generalization | Exact predecessor/finite-iteration fields hold in rooted-tree ancestor order via the parent map; the adjacent-pair conclusion is preserved. |
| C06 | Claim 3.3 | equivalent | Pointwise f>=g yields delta_f(A)<=delta_g(A) for the same A with exactly the source nondecreasing positive-bound convention. |
| C07 | Claim 4.4; Appendix Claim 7.1 | equivalent | Both grouped numbered claims have exact endpoints for monotone natural-valued f and the complete finite-configuration definition of nice, including m>=2, the nondecreasing k prefix, strictly increasing a prefix, threshold, gap +1 and upper f bound. |
| C08 | Overview Theorem 2.2; Theorem 4.1; Corollary 4.2; Corollary 4.3 | not-covered | No countable hard-class/adversarial generator-density statement is present. Window monotonicity and the nice equivalence are related prerequisites, not a zero-density construction. |
| C09 | Overview Theorem 2.3; Theorem 4.5; Corollary 4.6; Corollary 4.7 | not-covered | Finite-rank, tower and LCA interfaces formalize auxiliary ingredients, but no finite-rank generator with a half-density guarantee is present. |
| C10 | Overview Theorem 2.4; Theorem 5.1 | not-covered | No singleton high-dimensional geometric obstruction is present, under either printed limit condition. |
| C11 | Overview Theorem 2.5; Theorem 5.5; Corollary 5.6; Corollary 5.7; Appendix Claim 7.2 / Claim 5.11; Appendix Claim 7.3 / Claim 5.13 | not-covered | No filtered rectangular density definition or nearly-half generator theorem is present. The finite-rank/topological helpers do not assemble such a result. |
| C12 | Theorem 5.8 | not-covered | No origin-centered-cube generation-density theorem or shell-order reduction is present. |
| C13 | Theorem 5.9; Appendix Theorem 7.4 | not-covered | No size-sensitive discrepancy or finite asymmetric-LLL project endpoint is present in the supplied census. |

## Target and component dossiers

### C01 — Lower Banach density is the minimum of the lower window densities

Claim ID: `claim:kw26banach:claim-3-5`. **equivalent**.

**Source locations.** Claim 3.5 (printed 19; PDF 23); Definitions 3.1–3.2 and Claim 3.3 (printed 17–18; PDF 21,22).

**Full source statement.** For every A subseteq N and every admissible nondecreasing f:N→N union {infinity}, delta_B(A,N)<=delta_f(A,N). Equality is attained by the constant infinity window scale, so Banach density is a least member of this family, not merely a lower bound.

**Standing assumptions and definitions.**

- G4; A is arbitrary; no language class, rank or generation assumption.
- The f values allow at least one positive window start.
- The outer parameter is window length k→infinity; the inner domain is 1<=m<=f(k).
- Constant infinity recovers the all-starts formula (4).

**Lean declarations directly checked.**

- `GenLimit.KleinbergWei.Banach.claim_3_5` — theorem; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.WindowDensity:111`; native census line 93; registered endpoint.
- `GenLimit.KleinbergWei.Banach.lowerBanachDensity_le_windowDensity` — theorem; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.WindowDensity:100`; native census line 111; supporting native interface or definition.
- `GenLimit.KleinbergWei.Banach.lowerWindowDensity_top` — theorem; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.WindowDensity:91`; native census line 113; supporting native interface or definition.
- `GenLimit.KleinbergWei.Banach.Results.claim_3_5` — theorem; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.Results.Overview:24`; native census line 211; supporting native interface or definition.
- `GenLimit.KleinbergWei.Banach.AdmissibleWindowBound` — definition; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.WindowDensity:32`; native census line 82; supporting native interface or definition.
- `GenLimit.KleinbergWei.Banach.windowCount` — definition; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.WindowDensity:22`; native census line 128; supporting native interface or definition.
- `GenLimit.KleinbergWei.Banach.windowRatio` — definition; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.WindowDensity:27`; native census line 132; supporting native interface or definition.
- `GenLimit.KleinbergWei.Banach.windowMinimum` — definition; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.WindowDensity:36`; native census line 129; supporting native interface or definition.
- `GenLimit.KleinbergWei.Banach.banachMinimum` — definition; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.WindowDensity:49`; native census line 89; supporting native interface or definition.
- `GenLimit.KleinbergWei.Banach.lowerWindowDensity` — definition; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.WindowDensity:44`; native census line 112; supporting native interface or definition.
- `GenLimit.KleinbergWei.Banach.lowerBanachDensity` — definition; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.WindowDensity:54`; native census line 110; supporting native interface or definition.

**Exact registered theorem types.**

`GenLimit.KleinbergWei.Banach.claim_3_5`

```lean
∀ (A : GenLimit.Language),
  @Eq.{1} ENNReal (GenLimit.KleinbergWei.Banach.lowerBanachDensity A)
    (⨅ f,
      GenLimit.KleinbergWei.Banach.lowerWindowDensity
        (@Subtype.val.{1} (Nat → WithTop.{0} Nat) (fun f => GenLimit.KleinbergWei.Banach.AdmissibleWindowBound f) f) A)
```

**Reconstruction and quantifier order.** For every A ⊆ Nat, the ENNReal liminf, as the window length k tends to infinity, of the infimum of |A∩[m,m+k)|/k over all natural starts m≥1 equals the infimum of the analogous liminf over all nondecreasing f : Nat → WithTop Nat satisfying f(k)≥1, restricting starts to 1≤m≤f(k). Ratios at k=0 are defined as 0. The outer infimum is over admissible functions, not a single finite bound.

∀ A : Set Nat, lowerBanachDensity A = inf {lowerWindowDensity f A | f : Nat → WithTop Nat, Monotone f ∧ ∀k, 1≤f(k)}. No existential witness function or rate is quantified by the target.

**Comparison.** The source least-density assertion is represented by an infimum identity, the separate all-f inequality, and the explicit constant-top equality. Positive-length windows agree exactly after translating inclusive integer notation to half-open notation.

**Strength and representation.** Equivalent on the source positive-natural domain. The target equality alone uses an infimum rather than an explicit minimizing witness; the native top equality supplies attainment at f=∞. ENNReal is a representation change for these [0,1]-valued limits, not a stronger density guarantee.

**Grouped components.**

- **Claim 3.5 — equivalent.** The same window-density family is ordered above Banach density, with equality at the infinity-valued scale.

**Algorithm/access scope.** Pure semantic equality/order of infima and liminf values. No generator, effective estimator or minimizer algorithm is supplied or required. The same A occurs throughout; the top function is explicit in a separate native theorem.

**Witness identity and assembly.** No unnamed minimizing f is extracted from the target equality. The separate top equality explicitly uses f(k)=∞ for every k.

**Differences and qualifications.**

- The registered target states delta_B(A)=inf_f delta_f(A), while the source calls delta_B the smallest member; native lowerWindowDensity_top and lowerBanachDensity_le_windowDensity supply the two missing parts of the minimum interpretation.
- Lean uses Nat including 0 but permits starts only m>=1. Its k=0 ratio is defined as 0 and is ignored by atTop; there is no endpoint shift for positive k: [m,m+k) contains exactly the source [m,m+k-1].

**Source questions kept separate from Lean differences.**

- The displayed window definition uses min even at f(k)=infinity, whereas the Banach definition uses inf. For fixed k these integer counts have a minimum; the source does not separately explain the convention.
- The claim does not say every pair of unequal functions yields a strict inequality.

**Limits.**

- All infima are over a nonempty eligible-start set under AdmissibleWindowBound; no empty-set density convention is invoked.
- The source’s min/inf notation at f=∞ has the same fixed-k values because possible counts are among finitely many integers 0,...,k.
- Statement/interface correspondence only: no proof correctness, fresh compilation, or human review certification.

**Visual evidence.** [visual-checks/page_22.png](visual-checks/page_22.png), [visual-checks/page_23.png](visual-checks/page_23.png).

### C02 — Topological accumulation and infinite perfect towers

Claim ID: `claim:kw26banach:claim-3-6`. **faithful-generalization**.

**Source locations.** Definition 3.1 (infinite perfect tower) (printed 19; PDF 23); Claim 3.6, topology and Remark 1 (printed 20; PDF 24).

**Full source statement.** For a language Lprime in X, Lprime is an accumulation point of the containment-refined topological space (X,T) if and only if it is the terminal language of an infinite perfect tower in X. A tower is a sequence Lambda_j of proper subsets of Lprime, every Lambda_j fixes at least one terminal string, and every terminal string is fixed by some Lambda_j. The accompanying explanation describes each string as eventually present permanently and each tower stage as contributing a permanent appearance.

**Standing assumptions and definitions.**

- G1 and G5; all tower terms and the terminal language belong to X.
- The basis imposes both finite evidence and upper containment.
- The accumulation point is a point of X, not a point in an ambient completion.
- U_(L,F)={Lprime in X:F subseteq Lprime subseteq L}.
- Proper subset Lambda_j subsetneq terminal for all j.
- Fixing is explained by eventual permanent occurrence and nonredundancy; no separate precise first-fixing definition is provided in this edition.

**Lean declarations directly checked.**

- `GenLimit.KleinbergWei.Banach.claim_3_6` — theorem; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.Topology:57`; native census line 94; registered endpoint.
- `GenLimit.KleinbergWei.TowerTopology.Point` — definition; supplied source anchor `GenLimit.Support.KleinbergWei.TowerTopology:17`; native census line 143; supporting native interface or definition.
- `GenLimit.KleinbergWei.TowerTopology.basicNeighborhood` — definition; supplied source anchor `GenLimit.Support.KleinbergWei.TowerTopology:20`; native census line 160; supporting native interface or definition.
- `GenLimit.KleinbergWei.TowerTopology.KWOpen` — definition; supplied source anchor `GenLimit.Support.KleinbergWei.TowerTopology:31`; native census line 141; supporting native interface or definition.
- `GenLimit.KleinbergWei.TowerTopology.IsLimitPoint` — definition; supplied source anchor `GenLimit.Support.KleinbergWei.TowerTopology:92`; native census line 140; supporting native interface or definition.
- `GenLimit.KleinbergWei.TowerTopology.FixesAt` — definition; supplied source anchor `GenLimit.Support.KleinbergWei.TowerTopology:177`; native census line 138; supporting native interface or definition.
- `GenLimit.KleinbergWei.TowerTopology.PerfectTower` — inductive; supplied source anchor `GenLimit.Support.KleinbergWei.TowerTopology:182`; native census line 142; supporting native interface or definition.
- `GenLimit.KleinbergWei.TowerTopology.PerfectTower.mk` — constructor; supplied source anchor `GenLimit.Support.KleinbergWei.TowerTopology:182`; native census line 270; supporting native interface or definition.
- `GenLimit.KleinbergWei.TowerTopology.BasisLimitPoint` — definition; supplied source anchor `GenLimit.Support.KleinbergWei.TowerTopology:87`; native census line 135; supporting native interface or definition.
- `GenLimit.KleinbergWei.TowerTopology.basisLimitPoint_iff_exists_perfectTower` — theorem; supplied source anchor `GenLimit.Support.KleinbergWei.TowerTopology.PerfectConverse:277`; native census line 163; supporting native interface or definition.
- `GenLimit.KleinbergWei.TowerTopology.isLimitPoint_iff_exists_perfectTower` — theorem; supplied source anchor `GenLimit.Support.KleinbergWei.TowerTopology.PerfectConverse:290`; native census line 186; supporting native interface or definition.
- `GenLimit.KleinbergWei.TowerTopology.adaptiveStageOf` — definition; supplied source anchor `GenLimit.Support.KleinbergWei.TowerTopology.PerfectConverse:27`; native census line 145; supporting native interface or definition.
- `GenLimit.KleinbergWei.TowerTopology.nextFixed` — definition; supplied source anchor `GenLimit.Support.KleinbergWei.TowerTopology.PerfectConverse:66`; native census line 193; supporting native interface or definition.
- `GenLimit.KleinbergWei.TowerTopology.advance` — definition; supplied source anchor `GenLimit.Support.KleinbergWei.TowerTopology.PerfectConverse:87`; native census line 154; supporting native interface or definition.
- `GenLimit.KleinbergWei.TowerTopology.adaptiveStages` — definition; supplied source anchor `GenLimit.Support.KleinbergWei.TowerTopology.PerfectConverse:112`; native census line 147; supporting native interface or definition.
- `GenLimit.KleinbergWei.TowerTopology.adaptiveTower` — definition; supplied source anchor `GenLimit.Support.KleinbergWei.TowerTopology.PerfectConverse:167`; native census line 151; supporting native interface or definition.
- `GenLimit.KleinbergWei.TowerTopology.AdaptiveStage` — inductive; supplied source anchor `GenLimit.Support.KleinbergWei.TowerTopology.PerfectConverse:14`; native census line 133; supporting native interface or definition.
- `GenLimit.KleinbergWei.TowerTopology.AdaptiveStage.mk` — constructor; supplied source anchor `GenLimit.Support.KleinbergWei.TowerTopology.PerfectConverse:14`; native census line 254; supporting native interface or definition.
- `GenLimit.KleinbergWei.TowerTopology.perfectTower_of_basisLimitPoint` — theorem; supplied source anchor `GenLimit.Support.KleinbergWei.TowerTopology.PerfectConverse:245`; native census line 194; supporting native interface or definition.
- `GenLimit.KleinbergWei.TowerTopology.adaptiveTower_proper` — theorem; supplied source anchor `GenLimit.Support.KleinbergWei.TowerTopology.PerfectConverse:211`; native census line 153; supporting native interface or definition.
- `GenLimit.KleinbergWei.TowerTopology.adaptiveTower_eventually_contains` — theorem; supplied source anchor `GenLimit.Support.KleinbergWei.TowerTopology.PerfectConverse:196`; native census line 152; supporting native interface or definition.
- `GenLimit.KleinbergWei.TowerTopology.PerfectTower.toConvergentProperTower` — theorem; supplied source anchor `GenLimit.Support.KleinbergWei.TowerTopology:196`; native census line 275; supporting native interface or definition.
- `GenLimit.Language` — definition; supplied source anchor `GenLimit.Core.Basic:20`; native census line 2; supporting native interface or definition.
- `GenLimit.Presents` — definition; supplied source anchor `GenLimit.Core.Basic:26`; native census line 5; supporting native interface or definition.
- `GenLimit.sample` — definition; supplied source anchor `GenLimit.Core.Basic:30`; native census line 12; supporting native interface or definition.

**Exact registered theorem types.**

`GenLimit.KleinbergWei.Banach.claim_3_6`

```lean
∀ {X : Set.{0} GenLimit.Language} {terminal : GenLimit.KleinbergWei.TowerTopology.Point X} (enumeration : Nat → Nat),
  GenLimit.Presents enumeration
      (@Subtype.val.{1} GenLimit.Language
        (fun L =>
          @Membership.mem.{0, 0} GenLimit.Language (Set.{0} GenLimit.Language)
            (@Set.instMembership.{0} GenLimit.Language) X L)
        terminal) →
    Iff (@GenLimit.KleinbergWei.TowerTopology.IsLimitPoint X terminal)
      (∃ tower, GenLimit.KleinbergWei.Banach.PerfectTower X tower terminal)
```

**Reconstruction and quantifier order.** For arbitrary X ⊆ Set Nat, terminal K : Point X, and total enumeration e : Nat → Nat with range(e)=K.val, K is a limit point for KWOpen iff there exists tower : Nat → Point X such that every tower(n) is a proper subset of K; every stage n has some u∈K that belongs to all tower(m) for m≥n and, if n>0, is absent from tower(n−1); and every u∈K has some such stage n. All three tower conditions, including the per-stage witness, are part of the conclusion.

∀ {X} {K : Point X}, ∀ e : Nat→Nat, Presents e K.val → (IsLimitPoint K ↔ ∃ tower : Nat→Point X, [∀n, tower(n).val⊊K.val] ∧ [∀n ∃u∈K.val, FixesAt tower n u] ∧ [∀u∈K.val ∃n, FixesAt tower n u]). Stage witnesses may depend on tower and n; fixation times may depend on u. The tower may depend on X,K,e and the limit-point premise.

**Comparison.** The concrete basis and all three perfect-tower clauses match the source explanation. The theorem does not require the class X to be countable or its other languages to be infinite, and accepts a semantic presentation of the terminal.

**Strength and representation.** The class-domain hypotheses are weaker than the source’s countable class of infinite languages. Supplying range(e)=K is an extra parameter, but every source terminal is an infinite subset of a countable universe and admits such a semantic presentation; this does not restrict the source case. The equivalence and its witnesses are semantic, with no added effective guarantee.

**Grouped components.**

- **Claim 3.6, both directions — faithful-generalization.** Same accumulation/tower equivalence on all source instances, extended to arbitrary classes with a supplied terminal presentation.
- **Definition 3.1 tower: properness, per-stage fixing, complete fixing — equivalent.** All three clauses are present. FixesAt specifies permanent entry, not mere first occurrence or union coverage.
- **Named auxiliary construction and same-witness properties — faithful-generalization.** The native theorem types explicitly mention the same adaptiveTower expression with the same X,K,hK,e,hP parameters; these properties need not be attributed to an arbitrary existential witness.

**Algorithm/access scope.** The registered target existentially quantifies a tower. Separately, adaptiveTower is a named classical selection construction with full X/K and a BasisLimitPoint proof as input, in addition to e and Presents e K. adaptiveStageOf chooses a proper point and a missing terminal member with Classical.choose; nextFixed inserts the prior missing member and the next enumeration value. This is an auxiliary tower construction, not a learner discovering an unknown K.

**Witness identity and assembly.** The existential facade does not name adaptiveTower. Native perfectTower_of_basisLimitPoint does; native properness and eventual-containment types use that same named value. No proof inspection is needed to identify that shared expression.

**Differences and qualifications.**

- The paper’s fixes is explained informally; Lean defines it as permanent membership from n together with n=0 or absence at n-1. Earlier intermittent occurrence is allowed, consistent with the moment of permanent appearance reading.
- The target has a presentation premise that is not written in Claim 3.6, while dropping class-countability and candidate-infinitude premises. These are opposing syntactic changes and are not an access-model defect.
- No monotone inclusion chain among tower terms is required by either the source definition or Lean.

**Source questions kept separate from Lean differences.**

- Definition number 3.1 is reused for the tower after density Definition 3.1.
- The paper does not explicitly formalize fixes beyond the following explanatory paragraph; mere union coverage is weaker than its stated intent.
- Earlier overview says the topology was used in [21,22], while Remark 1 explains an essential refinement relative to [22]; the concrete basis here governs this inventory.

**Limits.**

- The precise interpretation of fixes remains a source ambiguity rather than a demonstrated Lean mismatch.
- Range-equality presentations can repeat values and are not computable-stream certificates.
- An empty terminal has no Nat-indexed surjective presentation; source terminals are infinite, so this is outside its domain.
- Statement/interface correspondence only: no proof correctness, fresh compilation, or human review certification.

**Visual evidence.** [visual-checks/page_23.png](visual-checks/page_23.png), [visual-checks/page_24.png](visual-checks/page_24.png).

### C03 — A converging accumulation sequence eventually has smaller point rank

Claim ID: `claim:kw26banach:claim-4-11`. **faithful-specialization**.

**Source locations.** Claim 4.11 and proof (printed 38; PDF 42); Finite class rank and point rank setup (printed 35; PDF 39); Use in validity argument (printed 38–39; PDF 42,43).

**Full source statement.** Within the finite-Cantor–Bendixson-rank setting of Section 4.2, the source states: if K is the limit point of J_1,J_2,..., then there is n such that CB(J_j)<CB(K) for every j>n. Its proof interprets this as a sequence converging to K: a subsequence of points of rank at least alpha=CB(K) would remain in X^(alpha), making K a point of X^(alpha+1), contrary to its rank.

**Standing assumptions and definitions.**

- G5 and the standing finite class rank r in Section 4.2.
- J_j and K are languages in X; sequence convergence uses the containment-refined topology.
- The proof needs genuine accumulation away from K, not a tail or infinitely repeated occurrences equal to K. This exclusion is implicit in its accumulation argument, not written in the claim.
- Point rank is determined by which finite derived layer contains/removes a point.
- A sequence merely having K as a cluster point is weaker than all its terms converging to K.

**Lean declarations directly checked.**

- `GenLimit.KleinbergWei.Banach.claim_4_11_of_convergentProperTower` — theorem; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.FiniteRankSequence:191`; native census line 99; registered endpoint.
- `GenLimit.KleinbergWei.TowerTopology.RelativeLimitPoint` — definition; supplied source anchor `GenLimit.Support.KleinbergWei.CantorBendixson:12`; native census line 144; supporting native interface or definition.
- `GenLimit.KleinbergWei.TowerTopology.derivative` — definition; supplied source anchor `GenLimit.Support.KleinbergWei.CantorBendixson:20`; native census line 174; supporting native interface or definition.
- `GenLimit.KleinbergWei.TowerTopology.cbDerivative` — definition; supplied source anchor `GenLimit.Support.KleinbergWei.CantorBendixson:42`; native census line 166; supporting native interface or definition.
- `GenLimit.KleinbergWei.TowerTopology.cbLevel` — definition; supplied source anchor `GenLimit.Support.KleinbergWei.CantorBendixson:65`; native census line 171; supporting native interface or definition.
- `GenLimit.KleinbergWei.TowerTopology.FiniteRankAtMost` — definition; supplied source anchor `GenLimit.Support.KleinbergWei.CantorBendixson:85`; native census line 137; supporting native interface or definition.
- `GenLimit.KleinbergWei.Banach.FiniteRankAtMost` — definition; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.Topology:25`; native census line 84; supporting native interface or definition.
- `GenLimit.KleinbergWei.Banach.HasFiniteCBRank` — definition; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.FiniteRankSequence:30`; native census line 85; supporting native interface or definition.
- `GenLimit.KleinbergWei.Banach.BasisConverges` — definition; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.FiniteRankSequence:38`; native census line 83; supporting native interface or definition.
- `GenLimit.KleinbergWei.Banach.basisConverges_of_convergentProperTower` — theorem; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.FiniteRankSequence:46`; native census line 90; supporting native interface or definition.
- `GenLimit.KleinbergWei.Banach.claim_4_11` — theorem; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.FiniteRankSequence:170`; native census line 97; supporting native interface or definition.
- `GenLimit.KleinbergWei.Banach.claim_4_11_derivative_exit` — theorem; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.FiniteRankSequence:138`; native census line 98; supporting native interface or definition.
- `GenLimit.KleinbergWei.Banach.exists_hasFiniteCBRank_of_finiteRankAtMost` — theorem; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.FiniteRankSequence:77`; native census line 107; supporting native interface or definition.
- `GenLimit.KleinbergWei.Banach.Results.claim_4_11_repaired` — theorem; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.Results.Overview:27`; native census line 213; supporting native interface or definition.
- `GenLimit.KleinbergWei.TowerTopology.ConvergentProperTower` — inductive; supplied source anchor `GenLimit.Support.KleinbergWei.TowerTopology:191`; native census line 136; supporting native interface or definition.
- `GenLimit.KleinbergWei.TowerTopology.ConvergentProperTower.mk` — constructor; supplied source anchor `GenLimit.Support.KleinbergWei.TowerTopology:191`; native census line 264; supporting native interface or definition.
- `GenLimit.KleinbergWei.TowerTopology.basicNeighborhood` — definition; supplied source anchor `GenLimit.Support.KleinbergWei.TowerTopology:20`; native census line 160; supporting native interface or definition.

**Exact registered theorem types.**

`GenLimit.KleinbergWei.Banach.claim_4_11_of_convergentProperTower`

```lean
∀ {X : Set.{0} GenLimit.Language} {sequence : Nat → GenLimit.KleinbergWei.TowerTopology.Point X}
  {terminal : GenLimit.KleinbergWei.TowerTopology.Point X} {R r : Nat},
  GenLimit.KleinbergWei.Banach.FiniteRankAtMost X R →
    GenLimit.KleinbergWei.Banach.HasFiniteCBRank X terminal r →
      GenLimit.KleinbergWei.TowerTopology.ConvergentProperTower X sequence terminal →
        ∃ N,
          ∀ (n : Nat),
            @LE.le.{0} Nat instLENat N n →
              ∃ q, And (@LT.lt.{0} Nat instLTNat q r) (GenLimit.KleinbergWei.Banach.HasFiniteCBRank X (sequence n) q)
```

**Reconstruction and quantifier order.** Let X be any set of languages, sequence : Nat → Point X, terminal K : Point X, and R,r : Nat. If the R-th internal derivative D_R of X is empty, K lies in D_r \ D_(r+1), every sequence term is a proper subset of K, and each u∈K belongs to all sufficiently late sequence terms, then there is N such that for every n≥N there is q<r with sequence(n)∈D_q \ D_(q+1). The derivative starts at all points and repeatedly retains a point of the current set exactly when every finite positive neighborhood below it contains another point of the current set.

∀ {X} {sequence : Nat→Point X} {K : Point X} {R r : Nat}, [D_R=∅] → [K∈D_r ∧ K∉D_(r+1)] → [(∀n,sequence(n).val⊊K.val) ∧ (∀u∈K.val ∃N_u ∀n≥N_u,u∈sequence(n).val)] → ∃N ∀n≥N ∃q : Nat, q<r ∧ sequence(n)∈D_q\D_(q+1). N can depend on all preceding data and hypotheses; q can additionally depend on n.

**Comparison.** The target states the intended eventual rank drop for a genuinely approaching proper-subset sequence in a finite-rank class. It does not formalize the unqualified literal source sentence for arbitrary sequences merely having K as a cluster point or containing K infinitely often.

**Strength and representation.** The Lean target strengthens sequence hypotheses to all terms being proper subsets plus pointwise eventual coverage. Native claim_4_11 separately handles basis convergence with explicit terminal exclusion. These are qualifications of an ambiguous/overbroad source statement, while arbitrary X generalizes its class domain. Both conclude one eventual threshold N and a possibly n-dependent q<r; no monotone rank decrease along time is added.

**Grouped components.**

- **Claim 4.11 under convergent proper approximation — faithful-specialization.** Requires every sequence term to be a proper subset and every terminal element to be eventually permanently present; yields ∃N ∀n>=N ∃q<r exactRank(sequence n,q).
- **Convergence formulation — faithful-specialization.** The broader native version accepts eventual membership in every finite-evidence neighborhood and explicit ∀n,sequence n≠K.
- **Derived-layer exit underlying the claim — faithful-specialization.** Without a global empty-derivative premise, an exact-rank terminal plus genuine basis convergence implies eventual nonmembership in D_r. Global finite rank is used by the fuller endpoint to produce a finite exact q.

**Algorithm/access scope.** Semantic eventual rank comparison only. N and q are existentially quantified and need not be computable; no learner, rank oracle, convergence rate or named witness selector appears.

**Witness identity and assembly.** N may depend on X, sequence, terminal and rank data; q may also depend on n. There is no single eventual q or computable modulus.

**Differences and qualifications.**

- The source says K is the limit point of a sequence; its proof assumes convergence and genuine accumulation. Lean requires explicit convergence data and properness/exclusion. A constant sequence J_n=K makes the unqualified literal strict-drop statement fail; this is a source-qualification issue, not evidence of a Lean bug.
- Lean uses exact zero-based levels D_r minus D_(r+1), consistent with the source proof on printed p.38. The source rank assignment on printed p.35 also gives a conflicting one-based description.
- Lean’s derivative is internal: a retained point must already lie in the previous derivative. Source ambient derived sets agree through finite iterations from the whole Hausdorff space because those iterated sets are closed, but there is no blanket equality of these two operators on arbitrary nonclosed subsets.

**Source questions kept separate from Lean differences.**

- Literal limit point of a sequence can mean a cluster point, but the proof assumes convergence and says a selected subsequence still converges.
- Allowing J_j=K infinitely often defeats a strict eventual inequality; the printed statement does not explicitly exclude this.
- Printed p.35 assigns rank i to X^(i-1) minus X^(i) but then assigns rank 0 to X minus X^(1); printed p.38 instead uses rank>=alpha iff membership in X^(alpha). These conventions must not be silently merged.

**Limits.**

- The source’s literal cluster-point reading is not covered.
- A source terminal of rank zero cannot admit the full proper convergent hypotheses; the Lean conclusion q<0 is correspondingly impossible.
- Only finite natural derivative indices are formalized here; no transfinite-rank comparison is supplied.
- Statement/interface correspondence only: no proof correctness, fresh compilation, or human review certification.

**Visual evidence.** [visual-checks/page_39.png](visual-checks/page_39.png), [visual-checks/page_42.png](visual-checks/page_42.png).

### C04 — Prefix least common ancestors rise at most the tree depth

Claim ID: `claim:kw26banach:claim-4-18`. **faithful-generalization**.

**Source locations.** Claim 4.18 and proof (printed 41–42; PDF 45,46).

**Full source statement.** In a rooted tree T of depth at most r, take a nonempty finite sequence v_1,...,v_m of vertices, allowing repetitions. Put V_i={v_1,...,v_i} and u_i=LCA(V_i). If x<=_T y means x is an ancestor of y, then u_m<=_T...<=_T u_1. The number of i in {2,...,m} with u_i != u_(i-1) is at most r.

**Standing assumptions and definitions.**

- One rooted tree with unique root paths and well-defined LCAs of nonempty finite vertex sets.
- Finite depth r, measured by number of edges from a root of depth 0.
- m>=1; repeated vertices are explicitly permitted. No finiteness of the entire tree is required by the statement.
- Ancestor relation includes equality.
- A strict prefix-LCA change decreases its depth by at least one.

**Lean declarations directly checked.**

- `GenLimit.KleinbergWei.Banach.claim_4_18_change_index_card_bound` — theorem; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.FiniteTreeLCA:179`; native census line 101; registered endpoint.
- `GenLimit.KleinbergWei.Banach.prefixLCA` — definition; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.FiniteTreeLCA:24`; native census line 115; supporting native interface or definition.
- `GenLimit.KleinbergWei.Banach.prefixLCAChangeIndices` — definition; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.FiniteTreeLCA:85`; native census line 121; supporting native interface or definition.
- `GenLimit.KleinbergWei.Banach.prefixLCAChangeCount` — definition; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.FiniteTreeLCA:61`; native census line 116; supporting native interface or definition.
- `GenLimit.KleinbergWei.Banach.claim_4_18_monotone_ancestral_chain` — theorem; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.FiniteTreeLCA:52`; native census line 102; supporting native interface or definition.
- `GenLimit.KleinbergWei.Banach.claim_4_18_change_bound` — theorem; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.FiniteTreeLCA:167`; native census line 100; supporting native interface or definition.
- `GenLimit.KleinbergWei.Banach.prefixLCAChangeCount_eq_card` — theorem; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.FiniteTreeLCA:93`; native census line 118; supporting native interface or definition.
- `GenLimit.KleinbergWei.Banach.Results.claim_4_18` — theorem; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.Results.Overview:29`; native census line 214; supporting native interface or definition.

**Exact registered theorem types.**

`GenLimit.KleinbergWei.Banach.claim_4_18_change_index_card_bound`

```lean
∀ {Vertex : Type u_1} [inst : SemilatticeInf.{u_1} Vertex] [inst_1 : DecidableEq.{u_1 + 1} Vertex]
  (vertices : Nat → Vertex) (depth : Vertex → Nat) (r : Nat),
  @StrictMono.{u_1, 0} Vertex Nat
      (@PartialOrder.toPreorder.{u_1} Vertex (@SemilatticeInf.toPartialOrder.{u_1} Vertex inst)) Nat.instPreorder
      depth →
    @LE.le.{0} Nat instLENat (depth (vertices (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) r →
      ∀ (n : Nat),
        @LE.le.{0} Nat instLENat
          (@Finset.card.{0} Nat
            (@GenLimit.KleinbergWei.Banach.prefixLCAChangeIndices.{u_1} Vertex inst inst_1 vertices n))
          r
```

**Reconstruction and quantifier order.** For any universe-polymorphic type Vertex with SemilatticeInf and DecidableEq, any total vertices : Nat→Vertex, depth : Vertex→Nat, and r : Nat, if depth is strictly increasing on strict order comparisons and depth(vertices(0))≤r, then every prefix index n has at most r indices i∈{1,…,n} at which the running meet C(i)=vertices(0)⊓⋯⊓vertices(i) differs from C(i−1).

∀ {Vertex : Type u} [SemilatticeInf Vertex] [DecidableEq Vertex], ∀ vertices depth r, StrictMono depth → depth(vertices 0)≤r → ∀n : Nat, card {i∈Icc 1 n | C(i)≠C(i−1)}≤r. r bounds the initial depth; no hypothesis bounds every input vertex depth.

**Comparison.** Both source conclusion components are represented, using the running meet in a semilattice and a natural strictly increasing depth. The monotone ancestor chain is a separate native theorem, so the cardinality facade is not a missing half of the claim.

**Strength and representation.** Lean allows arbitrary meet-semilattices with a StrictMono natural depth, bounding only the initial depth by r; the source assumes a rooted tree of globally bounded depth. On rooted-tree ancestor order, meet is LCA and usual depth supplies the hypotheses. The monotonicity statement itself needs only the meet-semilattice. DecidableEq supports finite counting and can be supplied classically, without an effective equality claim.

**Grouped components.**

- **Claim 4.18 monotone ancestral chain — faithful-generalization.** Antitone prefixLCA under the induced semilattice order; no depth assumption is needed.
- **Claim 4.18 strict-change cardinality <=r — faithful-generalization.** The exact requested cardinal bound and the alternate recursive count are both available; source <=r is preserved.

**Algorithm/access scope.** prefixLCA is a finite recursive meet calculation, with C(0)=v_0 and C(n+1)=C(n) meet v_(n+1). Change indices are filtered in {1,...,n}. Computational content is relative to the supplied operations/equality; no complexity or final-change-time bound is asserted.

**Witness identity and assembly.** The chain and count properties are stated separately for the same explicitly defined prefixLCA and the same vertices; there is no existential-witness mismatch.

**Differences and qualifications.**

- Source sequence length m corresponds to Lean prefix index m-1, because C(n) contains n+1 vertices. The source change set {2,...,m} becomes {1,...,m-1}; this is only an indexing translation.
- The global tree depth hypothesis is replaced by StrictMono depth plus depth(v_0)<=r; later input vertices need not have depth<=r.
- The registered endpoint is the change-index cardinality bound. Native claim_4_18_monotone_ancestral_chain supplies Antitone prefixLCA for the same running-meet definition; native count/card equality joins the alternate count form.

**Source questions kept separate from Lean differences.**

- The prose says strictly bounded above but the decisive formula and proof give <=r, not <r.
- The surrounding application uses class rank as an upper bound on a structural-tree depth; that application is distinct from the abstract tree claim.

**Limits.**

- No explicit rooted-graph-to-order adapter is exported in this package. The mathematical identification uses ancestor order and ordinary depth.
- The abstract theorem does not formalize the source algorithm’s static-tree construction or prove that it has the required depth; C09 remains uncovered.
- Statement/interface correspondence only: no proof correctness, fresh compilation, or human review certification.

**Visual evidence.** [visual-checks/page_45.png](visual-checks/page_45.png), [visual-checks/page_46.png](visual-checks/page_46.png).

### C05 — An adjacent pair attains the LCA of a finite ordered collection

Claim ID: `claim:kw26banach:claim-4-20`. **faithful-generalization**.

**Source locations.** Claim 4.20 (printed 42; PDF 46), with proof/application on printed 43/PDF47.

**Full source statement.** Let Q=LCA(Q_1,...,Q_s) in a rooted tree, with s>=2. In every linear ordering of these vertices, some adjacent pair Q_i,Q_(i+1), 1<=i<s, has LCA(Q_i,Q_(i+1))=Q. If Q occurs among the vertices it supplies an adjacent pair; otherwise some adjacent vertices cross between different child-subtrees of Q.

**Standing assumptions and definitions.**

- A rooted tree and a nonempty finite ordered family with at least two terms.
- No height bound, CB rank, language inclusion or generation hypothesis.
- The ordering is arbitrary, not a tree traversal order.
- LCA is the deepest common ancestor, and a vertex is its own ancestor.

**Lean declarations directly checked.**

- `GenLimit.KleinbergWei.Banach.claim_4_20_adjacent_pair_lca` — theorem; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.FiniteTreeLCA:200`; native census line 103; registered endpoint.
- `GenLimit.KleinbergWei.Banach.prefixLCA` — definition; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.FiniteTreeLCA:24`; native census line 115; supporting native interface or definition.
- `GenLimit.KleinbergWei.Banach.Results.claim_4_20` — theorem; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.Results.Overview:31`; native census line 215; supporting native interface or definition.

**Exact registered type.**

```lean
∀ {Vertex : Type u_1} [inst : SemilatticeInf.{u_1} Vertex]
  [inst_1 :
    @PredOrder.{u_1} Vertex (@PartialOrder.toPreorder.{u_1} Vertex (@SemilatticeInf.toPartialOrder.{u_1} Vertex inst))]
  [@IsPredArchimedean.{u_1} Vertex
      (@PartialOrder.toPreorder.{u_1} Vertex (@SemilatticeInf.toPartialOrder.{u_1} Vertex inst)) inst_1]
  (vertices : Nat → Vertex) (Q : Vertex) (n : Nat),
  @Eq.{u_1 + 1} Vertex
      (@GenLimit.KleinbergWei.Banach.prefixLCA.{u_1} Vertex inst vertices
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      Q →
    ∃ i,
      And (@LE.le.{0} Nat instLENat i n)
        (@Eq.{u_1 + 1} Vertex
          (@Min.min.{u_1} Vertex (@SemilatticeInf.toMin.{u_1} Vertex inst) (vertices i)
            (vertices
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          Q)
```

**Reconstruction and quantifier order.** For every type Vertex with SemilatticeInf, PredOrder on its induced order, and IsPredArchimedean for that predecessor structure, every vertices : Nat→Vertex, Q : Vertex and n : Nat satisfy: if C(n+1)=Q, where C is the running meet starting at vertices(0), then some natural i≤n has vertices(i)⊓vertices(i+1)=Q. Thus the meet of n+2 supplied consecutive-prefix entries is achieved by one adjacent pair among them.

∀ {Vertex : Type u} [SemilatticeInf Vertex] [PredOrder Vertex] [IsPredArchimedean Vertex], ∀ vertices : Nat→Vertex, ∀Q : Vertex, ∀n : Nat, C(n+1)=Q → ∃i : Nat, i≤n ∧ (vertices i ⊓ vertices(i+1))=Q. i may depend on all data and the equality premise.

**Neutral external definitions.** The coordinator supplied definition-only source excerpts and an exact 12-record kernel export after the original Stage 1 freeze; no frozen input was modified. Both were read and hashed. The decisive fields are:

```lean
class PredOrder (α : Type*) [Preorder α] where
  pred : α → α
  pred_le : ∀ a, pred a ≤ a
  min_of_le_pred {a} : a ≤ pred a → IsMin a
  le_pred_of_lt {a b} : a < b → a ≤ pred b

class IsPredArchimedean (α : Type*) [Preorder α] [PredOrder α] : Prop where
  exists_pred_iterate_of_le {a b : α} (h : a ≤ b) : ∃ n, pred^[n] b = a

def IsMin (a : α) : Prop := ∀ ⦃b⦄, b ≤ a → a ≤ b
```

`Order.pred` is the `PredOrder.pred` projection; iteration is `Nat.iterate`, not an assumed linear-order operation. The source-excerpt SHA256 is `f92c7498abd8e482c06ec13a17a31f0ecc12b68dcdcbda0566f58c1afeeb6513`; the essential kernel-export SHA256 is `b75bfa212372fa33a9025695cdd29f359066b7fc6205c20e2e72fc66ef14f99c`. Exact class, constructor and field types were read; no field theorem proof values were supplied.

**Comparison.** The adjacent-pair conclusion matches the source in an abstract predecessor-archimedean meet order. Exact external class fields show that rooted-tree ancestor order supplies these hypotheses by taking pred to be parent and fixing the root; no global depth bound is required.

**Strength and representation.** A faithful statement-level generalization. The source rooted tree has LCA as meet, parent as predecessor (root fixed), and every ancestor reached by finitely many parent steps. These satisfy the supplied PredOrder and IsPredArchimedean fields. Lean permits more general orders, including ones with no global root, while retaining the exact adjacent-prefix conclusion. The predecessor axioms cannot be deleted to claim arbitrary meet-semilattices.

**Grouped component.** Claim 4.20 is faithfully generalized under this order representation. The source s=n+2 vertices and its adjacent indices translate exactly.

**Algorithm/access scope.** Logical existence of i<=n for a prefix of n+2 arbitrary vertices. The prefix operation is recursive meet. There is no DecidableEq premise, named search procedure or complexity claim. Every source finite sequence extends to a total Nat sequence by repeating its final vertex; the unused tail is irrelevant.

**Witness identity.** The witness i depends on the sequence, Q and the final prefix-meet equality. No particular adjacent pair is singled out by a named selector.

**Differences and qualifications.**

- The rooted-tree representation is replaced by SemilatticeInf plus PredOrder and IsPredArchimedean. The exact exported fields, rather than their names, establish the mathematical relationship.
- PredOrder provides pred(a)<=a, a<=pred(a) implies a is minimal, and a<b implies a<=pred(b). IsPredArchimedean requires that a<=b implies pred iterated n times on b equals a for some finite n.
- For ancestor order, define pred(nonroot)=parent and pred(root)=root. These fields hold by unique finite root paths; meet is LCA. No explicit graph-to-order adapter theorem is included in the supplied native project census, so this is a statement-level bridge rather than a claim of formal adapter coverage.
- Source s>=2 is represented by s=n+2; the witness i in {0,...,n} identifies exactly one of the source adjacent pairs. Repetitions are harmless and arbitrary orderings remain universally quantified.

**Source questions.**

- The source calls S both a set and a finite sequence; it does not explicitly discuss repetitions. The proof and conclusion continue to make sense with repetitions, but a set-based reading has distinct elements.

**Limits.**

- No explicit rooted-graph-to-order adapter is exported; the mathematical bridge is checked against the exact external field definitions.
- The essential 12-record external kernel supplement was inspected; the full 108-row export and raw Mathlib files were not opened.
- Statement/interface correspondence only: no proof correctness, fresh compilation, or human review certification.

**Visual evidence.** [PDF46 / printed42](visual-checks/page_46.png).

### C06 — Window-scale monotonicity

Claim ID: `claim:kw26banach:claim-3-3`. **equivalent**.

**Source locations.** Claim 3.3 and Definition 3.2 (printed 18; PDF 22).

**Full source statement.** For A subseteq N and nondecreasing f,g:N→N union {infinity} satisfying f(k)>=g(k) for every k, delta_f(A,N)<=delta_g(A,N). For each fixed window length the larger scale permits a superset of the window starts, and the inequality persists through liminf.

**Standing assumptions and definitions.**

- G4; both functions are in the stated density domain and ordered pointwise.
- No unboundedness assumption; bounded and infinite-valued scales are allowed.
- Delta_f uses windows [m,m+k-1] of exactly k positive integers.
- Function comparison is pointwise, not merely asymptotic growth.

**Lean declarations directly checked.**

- `GenLimit.KleinbergWei.Banach.claim_3_3` — theorem; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.WindowDensity:72`; native census line 92; registered endpoint.
- `GenLimit.KleinbergWei.Banach.AdmissibleWindowBound` — definition; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.WindowDensity:32`; native census line 82; supporting native interface or definition.
- `GenLimit.KleinbergWei.Banach.windowCount` — definition; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.WindowDensity:22`; native census line 128; supporting native interface or definition.
- `GenLimit.KleinbergWei.Banach.windowRatio` — definition; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.WindowDensity:27`; native census line 132; supporting native interface or definition.
- `GenLimit.KleinbergWei.Banach.windowMinimum` — definition; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.WindowDensity:36`; native census line 129; supporting native interface or definition.
- `GenLimit.KleinbergWei.Banach.banachMinimum` — definition; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.WindowDensity:49`; native census line 89; supporting native interface or definition.
- `GenLimit.KleinbergWei.Banach.lowerWindowDensity` — definition; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.WindowDensity:44`; native census line 112; supporting native interface or definition.
- `GenLimit.KleinbergWei.Banach.lowerBanachDensity` — definition; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.WindowDensity:54`; native census line 110; supporting native interface or definition.
- `GenLimit.KleinbergWei.Banach.windowMinimum_anti` — theorem; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.WindowDensity:57`; native census line 130; supporting native interface or definition.
- `GenLimit.KleinbergWei.Banach.Results.claim_3_3` — theorem; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.Results.Overview:23`; native census line 210; supporting native interface or definition.

**Exact registered theorem types.**

`GenLimit.KleinbergWei.Banach.claim_3_3`

```lean
∀ {f g : Nat → WithTop.{0} Nat} {A : GenLimit.Language},
  GenLimit.KleinbergWei.Banach.AdmissibleWindowBound f →
    GenLimit.KleinbergWei.Banach.AdmissibleWindowBound g →
      (∀ (k : Nat),
          @LE.le.{0} (WithTop.{0} Nat)
            (@Preorder.toLE.{0} (WithTop.{0} Nat) (@WithTop.preorder.{0} Nat Nat.instPreorder)) (g k) (f k)) →
        @LE.le.{0} ENNReal (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
          (GenLimit.KleinbergWei.Banach.lowerWindowDensity f A) (GenLimit.KleinbergWei.Banach.lowerWindowDensity g A)
```

**Reconstruction and quantifier order.** For any f,g : Nat→WithTop Nat and A ⊆ Nat, if both f and g are nondecreasing and everywhere at least 1, and g(k)≤f(k) for every k, then lowerWindowDensity f A≤lowerWindowDensity g A in ENNReal. These densities are liminf over window lengths k of the infimum of the normalized A-count in [m,m+k) with starts 1≤m≤the given bound at k, and zero-length ratios are 0.

∀ {f g : Nat→WithTop Nat} {A : Set Nat}, AdmissibleWindowBound f → AdmissibleWindowBound g → (∀k : Nat,g(k)≤f(k)) → lowerWindowDensity f A≤lowerWindowDensity g A. The same A is used on both sides; the result is uniform as a theorem over the supplied data but does not quantify a common program.

**Comparison.** Pointwise f>=g yields delta_f(A)<=delta_g(A) for the same A with exactly the source nondecreasing positive-bound convention.

**Strength and representation.** Equivalent after Nat/positive-natural and ENNReal representation conventions. It is a weak inequality, not a strict comparison for unequal scales and not an assertion based merely on asymptotic growth rate.

**Grouped components.**

- **Claim 3.3 — equivalent.** Preserves pointwise domination, both function hypotheses, same A and the non-strict antitone direction.

**Algorithm/access scope.** Semantic monotonicity of the admissible start domain followed by liminf. No generator, sampler, loss function, runtime or oracle procedure is involved.

**Witness identity and assembly.** No witness selection or common program is quantified; the theorem is universal over mathematical f,g,A.

**Differences and qualifications.**

- AdmissibleWindowBound explicitly requires Monotone f and f(k)>=1, making the source positive-N convention explicit. The same condition is required separately for g.
- Lean window [m,m+k) is the source inclusive interval [m,m+k-1] for k>=1. The separately defined zero-length value is asymptotically irrelevant.

**Source questions kept separate from Lean differences.**

- Nearby prose refers to faster growth and strictly expanding domains, but the formal claim is the weak inequality under pointwise order; it does not prove strict density decrease.

**Limits.**

- Pointwise domination at every k is required, as in the printed claim.
- The real-valued source densities are represented in ENNReal, but all admissible positive-window ratios are finite and in [0,1].
- Statement/interface correspondence only: no proof correctness, fresh compilation, or human review certification.

**Visual evidence.** [visual-checks/page_22.png](visual-checks/page_22.png).

### C07 — Nice finite window configurations are equivalent to unboundedness

Claim ID: `claim:kw26banach:claim-4-4`. **equivalent**.

**Source locations.** Nice definition and Claim 4.4 (printed 22; PDF 26); Claim 7.1 and proof (printed 74; PDF 78).

**Full source statement.** For an increasing natural-valued function f, nice means: for each T>0 there exist m>=2 and naturals k_1<=...<=k_m and T<a_1<...<a_m such that a_(i+1)>=a_i+k_i+1 and a_i<=f(k_i). Claims 4.4 and 7.1 assert that this is equivalent to f having no uniform upper bound. The appendix proves necessity with T equal to a proposed bound and sufficiency with m=2: choose f(k_1)>T, set a_1=f(k_1), a_2=a_1+k_1+1, then choose k_2>k_1 with f(k_2)>=a_2.

**Standing assumptions and definitions.**

- The precise claims use f:N→N and call f increasing.
- The preceding definition allows N union {infinity}; Theorem 4.1 uses nondecreasing functions with limsup infinity.
- Only existence of some m>=2 for each T is required, not configurations of every prescribed length.
- All four nice conditions and the quantifier order for T,m,k_i,a_i.
- Unboundedness means for every proposed finite upper bound there exists a larger function value.

**Lean declarations directly checked.**

- `GenLimit.KleinbergWei.Banach.claim_4_4` — theorem; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.Nice:75`; native census line 104; registered endpoint.
- `GenLimit.KleinbergWei.Banach.claim_7_1` — theorem; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.Nice:81`; native census line 105; registered endpoint.
- `GenLimit.KleinbergWei.Banach.Nice` — definition; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.Nice:13`; native census line 86; supporting native interface or definition.
- `GenLimit.KleinbergWei.Banach.UniversallyUnbounded` — definition; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.Nice:23`; native census line 88; supporting native interface or definition.
- `GenLimit.KleinbergWei.Banach.nice_universallyUnbounded` — theorem; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.Nice:26`; native census line 114; supporting native interface or definition.
- `GenLimit.KleinbergWei.Banach.universallyUnbounded_nice` — theorem; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.Nice:33`; native census line 127; supporting native interface or definition.
- `GenLimit.KleinbergWei.Banach.Results.claim_4_4` — theorem; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.Results.Overview:26`; native census line 216; supporting native interface or definition.
- `GenLimit.KleinbergWei.Banach.Results.claim_7_1` — theorem; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.Results.Overview:33`; native census line 217; supporting native interface or definition.

**Exact registered theorem types.**

`GenLimit.KleinbergWei.Banach.claim_4_4`

```lean
∀ {f : Nat → Nat},
  @Monotone.{0, 0} Nat Nat Nat.instPreorder Nat.instPreorder f →
    Iff (GenLimit.KleinbergWei.Banach.Nice f) (GenLimit.KleinbergWei.Banach.UniversallyUnbounded f)
```

`GenLimit.KleinbergWei.Banach.claim_7_1`

```lean
∀ {f : Nat → Nat},
  @Monotone.{0, 0} Nat Nat Nat.instPreorder Nat.instPreorder f →
    Iff (GenLimit.KleinbergWei.Banach.Nice f) (GenLimit.KleinbergWei.Banach.UniversallyUnbounded f)
```

**Reconstruction and quantifier order.** Both exact endpoints assert the same statement: for every monotone f : Nat→Nat, Nice f iff ∀M : Nat,∃n : Nat,M<f(n). Nice means that for every T one can choose m≥2 and total k,a : Nat→Nat such that k is nondecreasing on indices <m, a is strictly increasing on those indices, T<a(0), a(i)+k(i)+1≤a(i+1) whenever i+1<m, and a(i)≤f(k(i)) for every i<m. Every conjunct and the offset +1 are required.

∀ {f : Nat→Nat}, Monotone f → ((∀T : Nat ∃m : Nat ∃k : Nat→Nat ∃a : Nat→Nat, 2≤m ∧ [∀i,j<m, i≤j→k(i)≤k(j)] ∧ [∀i,j<m, i<j→a(i)<a(j)] ∧ T<a(0) ∧ [∀i, i+1<m→a(i)+k(i)+1≤a(i+1)] ∧ [∀i<m,a(i)≤f(k(i))]) ↔ (∀M : Nat ∃n : Nat,M<f(n))). Witnesses m,k,a may depend on f,T; n may depend on f,M. Each endpoint retains the monotonicity premise.

**Comparison.** Both grouped numbered claims have exact endpoints for monotone natural-valued f and the complete finite-configuration definition of nice, including m>=2, the nondecreasing k prefix, strictly increasing a prefix, threshold, gap +1 and upper f bound.

**Strength and representation.** Equivalent on the contextual nondecreasing reading of increasing. If the word increasing is intended strictly, Lean is a faithful generalization to nondecreasing functions. Total-function witnesses restricted to their first m entries are equivalent to finite tuples; T=0 is a harmless cofinal-threshold extension.

**Grouped components.**

- **Claim 4.4 — equivalent.** Full nice iff unbounded equivalence for nondecreasing finite-valued scales.
- **Appendix Claim 7.1 — equivalent.** The second target has the same complete type; it is not silently omitted as a duplicate.

**Algorithm/access scope.** Logical equivalence with semantic finite witnesses after each T. Neither endpoint supplies a named configuration algorithm or computability/rate claim. It is not a formalization of Theorem 4.1’s adversarial construction.

**Witness identity and assembly.** For each threshold T, m,k,a may depend on f,T; the unboundedness n may depend on f,M. There is no single fixed tuple or requirement that every prescribed m be realizable.

**Differences and qualifications.**

- The precise numbered source claims and Lean both restrict to finite natural-valued f; the preceding source nice definition and later application also mention infinity-valued f, which these endpoints do not cover.
- Lean uses zero-based i<m and source one-based tuples; all four source constraints are retained.
- Lean allows k_i=0 under Nat convention, while the surrounding paper often uses positive indices. For the unboundedness equivalence one can choose positive witness indices; no new effective guarantee or unbounded-length configuration is inferred.

**Source questions kept separate from Lean differences.**

- Increasing is not explicitly distinguished from nondecreasing; surrounding text uses both.
- The appendix writes a_1=f(k_1), which requires finite f(k_1), and both numbered claims restrict to N-valued f. Application to the infinity-valued domain of Theorem 4.1 is not separately handled there.
- Intervals later written [a_i,a_i+k_i] have k_i+1 points; the density definition uses [m,m+k-1]. This is an endpoint convention to keep separate from nice itself.

**Limits.**

- Increasing versus strictly increasing is a source terminology ambiguity.
- No infinity-valued extension or proof of the zero-density generation theorem is present in these interfaces.
- Statement/interface correspondence only: no proof correctness, fresh compilation, or human review certification.

**Visual evidence.** [visual-checks/page_26.png](visual-checks/page_26.png), [visual-checks/page_78.png](visual-checks/page_78.png).

### C08 — Unbounded window scales admit a countable hard class with zero output density

Claim ID: `claim:kw26banach:theorem-4-1`. **not-covered**.

**Source locations.** Overview Theorem 2.2 (printed 8; PDF 12); Theorem 4.1 and Corollaries 4.2–4.3 (printed 22; PDF 26); Construction and proof (printed 22–28; PDF 26,27,28,29,30,31,32).

**Full source statement.** For every nondecreasing f:N→N union {infinity} with limsup f(n)=infinity, there exists a countable class C of infinite languages for which every algorithm that generates in the limit on C has an adversarial target/enumeration yielding delta_f(O,K)=0. Corollary 4.2 and Overview 2.2 specialize this to lower Banach density. Corollary 4.3 says the Banach zero-density obstruction persists for generators of any fixed finite speed C. The exhibited family has infinite CB rank and contains N as the final target for the continuing mega-step construction.

**Standing assumptions and definitions.**

- G1–G5 and G7; the generator must succeed at generation in the limit on all class members, enabling simulated-target contradictions.
- Quantifier order: f first, then a fixed countable class, then each generator, then an adversarial enumeration/target. The class does not adapt separately to each generator.
- The speed extension concerns a fixed finite bound C per input.
- Delta_f and ordinary Banach density as in G4.
- Nice configurations and a separated sequence of groups of intervals.
- The class consists of finite-prefix additions and bounded shifts/extensions of a fixed sparse marker set P, plus N; its integer tuple parameters make it countable.
- Perfect towers at finite extension parameters justify ending failed rounds and preserve class membership; sparse refill steps ensure eventual enumeration of all target strings.

**Lean declarations directly checked.**

- `GenLimit.KleinbergWei.Banach.claim_4_4` — theorem; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.Nice:75`; native census line 104; related prerequisite only.
- `GenLimit.KleinbergWei.Banach.claim_7_1` — theorem; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.Nice:81`; native census line 105; related prerequisite only.
- `GenLimit.KleinbergWei.Banach.Nice` — definition; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.Nice:13`; native census line 86; related prerequisite only.
- `GenLimit.KleinbergWei.Banach.UniversallyUnbounded` — definition; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.Nice:23`; native census line 88; related prerequisite only.
- `GenLimit.KleinbergWei.Banach.lowerWindowDensity` — definition; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.WindowDensity:44`; native census line 112; related prerequisite only.
- `GenLimit.KleinbergWei.Banach.lowerBanachDensity` — definition; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.WindowDensity:54`; native census line 110; related prerequisite only.
**Comparison.** No countable hard-class/adversarial generator-density statement is present. Window monotonicity and the nice equivalence are related prerequisites, not a zero-density construction.

**Strength and representation.** No counterpart statement to order by strength in the supplied frozen census. The source mathematical claim is not refuted by missing formalization, and existing prerequisites do not entail an exported generator/geometry result.

**Grouped components.**

- **Overview Theorem 2.2 — not-covered.** Banach-density-zero hard class; no corresponding endpoint in the supplied census.
- **Theorem 4.1 — not-covered.** hard class for every nondecreasing unbounded f; no corresponding endpoint in the supplied census.
- **Corollary 4.2 — not-covered.** Banach specialization; no corresponding endpoint in the supplied census.
- **Corollary 4.3 — not-covered.** fixed finite speed-C extension; no corresponding endpoint in the supplied census.

**Algorithm/access scope.** No mega-step adversary, countable marker-language class, enumeration-refill construction or corresponding generation/density theorem is exported.

**Witness identity and assembly.** No common generator, adversary, coloring or quantitative witness is provided for this source component by any inspected endpoint.

**Differences and qualifications.**

- The slot mapping has no registered endpoint; the complete 325-record native census was also searched by identifiers, theorem types, project dependencies and defining-body tokens before reporting lack of coverage.
- Coverage is bounded to the supplied frozen project census, not an assertion about every repository branch or unexported Mathlib theorem.

**Source questions kept separate from Lean differences.**

- The overview and theorem abbreviate adversarial quantifiers; the proof and model supply a bad enumeration, not all enumerations.
- The main theorem includes infinity-valued f, but the invoked nice lemma is printed for natural-valued f; the proof also uses f inverse and f(k)<N_(s+1), requiring an interpretation for infinite values.
- Repeated endpoint notation uses [a,a+k] while calling its length k; this is immaterial to a zero limiting density but not an exact finite-window identity.
- Corollary 4.3 reuses C as both class name and speed symbol; no unbounded-speed statement follows.

**Limits.**

- Source-internal ambiguities listed below are not diagnosed as Lean errors.
- No theorem proof, full algorithm construction or fresh compilation has been certified.
- Statement/interface correspondence only: no proof correctness, fresh compilation, or human review certification.

**Visual evidence.** [visual-checks/page_12.png](visual-checks/page_12.png), [visual-checks/page_26.png](visual-checks/page_26.png).

### C09 — Finite rank gives the optimal half-density guarantee in one dimension

Claim ID: `claim:kw26banach:theorem-4-5`. **not-covered**.

**Source locations.** Overview Theorem 2.3 (printed 9; PDF 13); Theorem 4.5 and Corollaries 4.6–4.7 (printed 29; PDF 33); Algorithm, validity and density proof (printed 30–51; PDF 34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55).

**Full source statement.** For every countable class X of infinite languages having finite rank in the containment-refined CB topology, there is a generator that succeeds in the limit for every target and every enumeration and whose output has lower Banach density at least 1/2 in the true language. The overview calls 1/2 optimal. Corollary 4.6 transfers the same half guarantee to lower f-window densities for unbounded f. Corollary 4.7 asserts that for every bijection rho:N→N, there is such a generator under the reordered universe; the generator may be chosen for that ordering.

**Standing assumptions and definitions.**

- G1–G5; the finite rank belongs to X itself, not its completion.
- No bound on lengths of inclusion chains or coordinate sparsity of K is assumed.
- The fixed language collection and chosen ordering are available to the algorithm; guarantees quantify over all targets in it and all full adversary enumerations.
- Finite CB rank and containment-refined topology.
- A_acc guesses the true language infinitely often (Theorem 4.8, attributed to [21]); strict-critical chains organize its guesses.
- A static structural tree points toward earlier-index higher-rank candidate supersets; pullbacks and locally growing pods support eventual validity.
- Density is relative to target order; the finite interval game bounds leakage by O_r(log ell), yielding 1/2-o(1) uniformly on sufficiently long intervals.

**Lean declarations directly checked.**

- `GenLimit.KleinbergWei.Banach.FiniteRankAtMost` — definition; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.Topology:25`; native census line 84; related prerequisite only.
- `GenLimit.KleinbergWei.Banach.HasFiniteCBRank` — definition; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.FiniteRankSequence:30`; native census line 85; related prerequisite only.
- `GenLimit.KleinbergWei.Banach.claim_4_11` — theorem; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.FiniteRankSequence:170`; native census line 97; related prerequisite only.
- `GenLimit.KleinbergWei.Banach.claim_4_18_monotone_ancestral_chain` — theorem; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.FiniteTreeLCA:52`; native census line 102; related prerequisite only.
- `GenLimit.KleinbergWei.Banach.claim_4_18_change_index_card_bound` — theorem; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.FiniteTreeLCA:179`; native census line 101; related prerequisite only.
- `GenLimit.KleinbergWei.Banach.claim_4_20_adjacent_pair_lca` — theorem; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.FiniteTreeLCA:200`; native census line 103; related prerequisite only.
- `GenLimit.KleinbergWei.Banach.lowerBanachDensity` — definition; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.WindowDensity:54`; native census line 110; related prerequisite only.
**Comparison.** Finite-rank, tower and LCA interfaces formalize auxiliary ingredients, but no finite-rank generator with a half-density guarantee is present.

**Strength and representation.** No counterpart statement to order by strength in the supplied frozen census. The source mathematical claim is not refuted by missing formalization, and existing prerequisites do not entail an exported generator/geometry result.

**Grouped components.**

- **Overview Theorem 2.3 — not-covered.** optimal half-density generation; no corresponding endpoint in the supplied census.
- **Theorem 4.5 — not-covered.** generation in the limit plus Banach density >=1/2; no corresponding endpoint in the supplied census.
- **Corollary 4.6 — not-covered.** f-window transfer; no corresponding endpoint in the supplied census.
- **Corollary 4.7 — not-covered.** generator for each reordering; no corresponding endpoint in the supplied census.

**Algorithm/access scope.** No A_acc, strict-critical guessing algorithm, CB structural tree, pullback/pod update, finite interval game or final half-density generator endpoint is exported. The contextual speed-C Corollary 4.26 is also not found.

**Witness identity and assembly.** No common generator, adversary, coloring or quantitative witness is provided for this source component by any inspected endpoint.

**Differences and qualifications.**

- The slot mapping has no registered endpoint; the complete 325-record native census was also searched by identifiers, theorem types, project dependencies and defining-body tokens before reporting lack of coverage.
- Coverage is bounded to the supplied frozen project census, not an assertion about every repository branch or unexported Mathlib theorem.

**Source questions kept separate from Lean differences.**

- The source does not claim every infinite-rank class fails; it explicitly leaves positive infinite-rank classes open.
- Corollary 4.6 writes any unbounded f:N→N+ without repeating nondecreasing; Definition 3.2 supplies that admissibility condition.
- The ordering corollary does not assert that one fixed output set has half Banach density under every permutation.
- Point-rank indexing and the convergence/exclusion ambiguity of Claim 4.11 remain as recorded in C03.
- The tree definition says a sequence including L has a higher-rank limit, while surrounding discussion treats parent languages as supersets of L; mere inclusion as an arbitrary early sequence term alone does not impose that containment. This source convention is not repaired here.

**Limits.**

- Source-internal ambiguities listed below are not diagnosed as Lean errors.
- No theorem proof, full algorithm construction or fresh compilation has been certified.
- Statement/interface correspondence only: no proof correctness, fresh compilation, or human review certification.

**Visual evidence.** [visual-checks/page_13.png](visual-checks/page_13.png), [visual-checks/page_33.png](visual-checks/page_33.png), [visual-checks/page_39.png](visual-checks/page_39.png), [visual-checks/page_42.png](visual-checks/page_42.png), [visual-checks/page_45.png](visual-checks/page_45.png), [visual-checks/page_46.png](visual-checks/page_46.png).

### C10 — Ordinary rectangular density can be forced to zero for a known singleton target

Claim ID: `claim:kw26banach:theorem-5-1`. **not-covered**.

**Source locations.** Overview Theorem 2.4 (printed 10; PDF 14); Theorem 5.1 (printed 53; PDF 57); Copy-strategy proof and singleton interpretation (printed 53–55; PDF 57,58,59).

**Full source statement.** For each d>=2 there is an infinite K subseteq Z^d such that even for the known singleton class {K}, every generator can be opposed by a full enumeration of K yielding ordinary lower Banach density zero over axis-parallel rectangles. Overview 2.4 displays liminf as |R intersect K|→infinity. The detailed Theorem 5.1 instead displays liminf as |R intersect O intersect K|→infinity with the same ratio |R intersect O intersect K|/|R intersect K|=0. Both printed limit conditions are preserved as distinct source components.

**Standing assumptions and definitions.**

- G1–G3 and speed one from G7, with d>=2.
- Rectangles have arbitrary locations and side-length ratios; this is ordinary density with no volume filter.
- The target K is fixed independently of the generator; the enumeration can depend on its actions.
- Successful generators obey eventual validity/freshness; the proof’s copy strategy invokes prohibition of outputs previously revealed by the adversary.
- Ordinary density denominator counts target points in R.
- Theorem 5.2 (as stated here) supplies finite d-dimensional point sets whose every two-coloring has arbitrarily large monochromatic rectangular intersections.
- K is a union of separated paired translated copies at increasing monochromatic sizes; response-copying forces a large missed rectangle in one copy and slow refills preserve full enumeration.

**Lean declarations directly checked.**

No source-claim endpoint or source-specific related prerequisite was found. The census search is documented below.
**Comparison.** No singleton high-dimensional geometric obstruction is present, under either printed limit condition.

**Strength and representation.** No counterpart statement to order by strength in the supplied frozen census. The source mathematical claim is not refuted by missing formalization, and existing prerequisites do not entail an exported generator/geometry result.

**Grouped components.**

- **Overview Theorem 2.4 — not-covered.** zero density as |R∩K|→∞; no corresponding endpoint in the supplied census.
- **Theorem 5.1 — not-covered.** printed zero-density formula as |R∩O∩K|→∞; no corresponding endpoint in the supplied census.

**Algorithm/access scope.** No integer-grid rectangle model, paired-copy target construction, rectangular Ramsey interface or copy adversary is exported. The two source limit conditions remain distinct unresolved source formulations.

**Witness identity and assembly.** No common generator, adversary, coloring or quantitative witness is provided for this source component by any inspected endpoint.

**Differences and qualifications.**

- The slot mapping has no registered endpoint; the complete 325-record native census was also searched by identifiers, theorem types, project dependencies and defining-body tokens before reporting lack of coverage.
- Coverage is bounded to the supplied frozen project census, not an assertion about every repository branch or unexported Mathlib theorem.

**Source questions kept separate from Lean differences.**

- The different limit conditions are visible in the rendered PDF, not extraction artifacts. Rectangles containing no output witness the overview condition, but alone do not witness the displayed detailed condition requiring output count to tend to infinity.
- The detailed proof repeatedly concludes the output-count display after constructing empty-output rectangles; this inventory does not silently replace its subscript.
- The statement does not promise a bad result for every K or a single enumeration that defeats every generator simultaneously.
- The proof first reasons with full freshness; handling finitely many early invalid/repeated outputs is implicit in the generation-in-the-limit model.

**Limits.**

- Source-internal ambiguities listed below are not diagnosed as Lean errors.
- No theorem proof, full algorithm construction or fresh compilation has been certified.
- Statement/interface correspondence only: no proof correctness, fresh compilation, or human review certification.

**Visual evidence.** [visual-checks/page_14.png](visual-checks/page_14.png), [visual-checks/page_57.png](visual-checks/page_57.png).

### C11 — Finite rank gives nearly half filtered density in higher dimensions

Claim ID: `claim:kw26banach:theorem-5-5`. **not-covered**.

**Source locations.** Overview Theorem 2.5 and nondegenerate sequences (printed 10–11; PDF 14,15); Definition 5.3 and Theorem 5.5 (printed 57–58; PDF 61,62); Corollaries 5.6–5.7 and formula (19) (printed 58; PDF 62); Filtered algorithm and density proof (printed 65–70; PDF 69,70,71,72,73,74); Appendix Claims 7.2–7.3 (printed 74–76; PDF 78,79,80).

**Full source statement.** Fix a nondecreasing divergent f:[0,infinity)→[0,infinity), a countable finite-CB-rank class X of infinite subsets of a product U_1×...×U_d of countable string sets, and epsilon>0. Theorem 5.5 asserts a generator with eventual validity and liminf |R intersect K intersect O|/|R intersect K|>=1/2-epsilon over all axis-parallel rectangles satisfying |R intersect K|/[f(Vol(R)) log Vol(R)]→infinity. Corollary 5.6 restricts to cubes B(x,r) of side r, requiring |B(x,r) intersect K|/[f(r^d) log r^d]→infinity. Corollary 5.7 fixes a rectangular shape R and considers all translates and dilations R(x,r), requiring |R(x,r) intersect K|/(log r)^2→infinity; it literally asserts an algorithm that identifies any target in the limit and has density >=1/2-epsilon. Overview 2.5 states nearly half filtered density using its sequence-based definition (2).

**Standing assumptions and definitions.**

- G1–G3 and G5–G6, with fixed positive finite dimension in the higher-dimensional setting.
- The class has finite CB rank in the same containment-refined topology; each coordinate universe is countable, with the discrete coordinate normalization used to speak of rectangles in Z^d.
- Theorem 5.5 fixes f and epsilon before the generator is chosen; all targets and full enumerations are covered for that choice.
- The rectangle restriction is essential: ordinary density is not asserted, even for finite-rank singleton classes.
- Fixed-shape Corollary 5.7 has a log-squared scale condition, not the arbitrary f formula repeated verbatim.
- Definition 5.3 filtered density for a fixed divergent scale function.
- B(x,r) is a cube centered at x with side r; R(x,r) has a fixed side-length ratio.
- The algorithm partitions Z^d into slowly growing infinity-norm shells, preserves assigned colors, and responds within a shell using opposite-color points where possible.
- Claim 5.11/appendix 7.2 constructs an eventually bounded strictly concave divergent minorant of f. Lemma 5.10 uses its inverse to obtain a shell partition meeting at most f(ell)+2 regions in a side-ell cube.
- Claim 5.13/appendix 7.3 partitions a rectangle intersected with a shell into at most 2d disjoint rectangles. Theorem 5.9 controls discrepancy on each piece; finite CB rank controls the number of pod changes in a shell.

**Lean declarations directly checked.**

- `GenLimit.KleinbergWei.Banach.FiniteRankAtMost` — definition; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.Topology:25`; native census line 84; related prerequisite only.
- `GenLimit.KleinbergWei.Banach.claim_4_11` — theorem; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.FiniteRankSequence:170`; native census line 97; related prerequisite only.
- `GenLimit.KleinbergWei.Banach.claim_4_18_monotone_ancestral_chain` — theorem; supplied source anchor `GenLimit.Paper23_BanachDensityTopologyAndGeometry.FiniteTreeLCA:52`; native census line 102; related prerequisite only.
**Comparison.** No filtered rectangular density definition or nearly-half generator theorem is present. The finite-rank/topological helpers do not assemble such a result.

**Strength and representation.** No counterpart statement to order by strength in the supplied frozen census. The source mathematical claim is not refuted by missing formalization, and existing prerequisites do not entail an exported generator/geometry result.

**Grouped components.**

- **Overview Theorem 2.5 — not-covered.** nondegenerate-sequence near-half guarantee; no corresponding endpoint in the supplied census.
- **Theorem 5.5 — not-covered.** fixed-filter all-rectangle near-half guarantee; no corresponding endpoint in the supplied census.
- **Corollary 5.6 — not-covered.** cube specialization; no corresponding endpoint in the supplied census.
- **Corollary 5.7 — not-covered.** fixed-shape translates/dilates with log-squared filter and literal identification; no corresponding endpoint in the supplied census.
- **Appendix Claim 7.2 / Claim 5.11 — not-covered.** concave minorant used for shell partition; no corresponding endpoint in the supplied census.
- **Appendix Claim 7.3 / Claim 5.13 — not-covered.** at-most-2d rectangle decomposition of a shell intersection; no corresponding endpoint in the supplied census.

**Algorithm/access scope.** No filtered density, shell partition, coloring assignment, opposite-color response algorithm or density aggregation endpoint is exported. Source quantifier/identification/boundary questions are separate from this absence.

**Witness identity and assembly.** No common generator, adversary, coloring or quantitative witness is provided for this source component by any inspected endpoint.

**Differences and qualifications.**

- The slot mapping has no registered endpoint; the complete 325-record native census was also searched by identifiers, theorem types, project dependencies and defining-body tokens before reporting lack of coverage.
- Coverage is bounded to the supplied frozen project census, not an assertion about every repository branch or unexported Mathlib theorem.

**Source questions kept separate from Lean differences.**

- Overview nondegeneracy is existential in a divergent function for each sequence; the detailed theorem fixes f before selecting an algorithm. The source does not explicitly reconcile these quantifiers.
- Corollary 5.7 says identifies rather than generates; it must not silently be weakened during later comparison.
- The source repeatedly calls Corollary 5.6 Theorem 5.6 and the final proof says it completes Theorem 5.6, although the main all-rectangle statement is Theorem 5.5.
- Volume and geometric side conventions are not fully fixed for degenerate rectangles. The proof’s L<=Vol<=L^d assumes positive side lengths at least one.
- Appendix 7.2 only promises g<=f eventually, while Lemma 5.10’s proof uses that inequality for every ell; its eventual-density use may ignore bounded scales but this is not explicitly separated.
- Appendix 7.3’s shell proof uses radii minus one although Lemma 5.10 permits real radii, and says boundary inclusion is ignored. The at-most-2d decomposition is the mathematical claim.
- The detailed proof uses opposite colors and a discrepancy-to-density argument; no stronger ordinary rectangular bound or exact 1/2 bound is asserted.

**Limits.**

- Source-internal ambiguities listed below are not diagnosed as Lean errors.
- No theorem proof, full algorithm construction or fresh compilation has been certified.
- Statement/interface correspondence only: no proof correctness, fresh compilation, or human review certification.

**Visual evidence.** [visual-checks/page_14.png](visual-checks/page_14.png), [visual-checks/page_15.png](visual-checks/page_15.png), [visual-checks/page_61.png](visual-checks/page_61.png), [visual-checks/page_62.png](visual-checks/page_62.png), [visual-checks/page_78.png](visual-checks/page_78.png), [visual-checks/page_80.png](visual-checks/page_80.png).

### C12 — Origin-centered cubes admit the universal asymptotic half guarantee

Claim ID: `claim:kw26banach:theorem-5-8`. **not-covered**.

**Source locations.** Theorem 5.8 and proof (printed 59; PDF 63).

**Full source statement.** For every countable class X of infinite languages in Z^d, there is a generator that succeeds in the limit and achieves the optimal half lower asymptotic density in the true K, where the windows are cubes B(0,r) centered at the origin and r→infinity. The displayed prose says always 1/2; the proof transports the one-dimensional half guarantee by enumerating lattice shells in increasing infinity norm and ordering within each shell lexicographically, so every origin-centered cube becomes an initial segment of a fixed enumeration.

**Standing assumptions and definitions.**

- G1–G3 and speed one; fixed finite dimension.
- No finite-CB-rank assumption.
- No nondegeneracy/filtered-volume requirement.
- The windows are nested origin-centered cubes, not translated cubes and not all anchored rectangular aspect ratios.
- Asymptotic relative density is liminf_(r→infinity) |B(0,r) intersect K intersect O|/|B(0,r) intersect K|.
- Shell S_k={x:||x||_infinity=k}; order shells and use lexicographic order within each finite shell.
- The proof invokes the prior one-dimensional lower asymptotic density algorithm [22], as stated here.

**Lean declarations directly checked.**

- `GenLimit.Generic.Generator` — definition; supplied source anchor `GenLimit.Core.GenericGeneration:41`; native census line 18; related prerequisite only.
- `GenLimit.Generic.output` — definition; supplied source anchor `GenLimit.Core.GenericGeneration:87`; native census line 37; related prerequisite only.
- `GenLimit.Generic.CorrectAt` — definition; supplied source anchor `GenLimit.Core.GenericGeneration:367`; native census line 16; related prerequisite only.
**Comparison.** No origin-centered-cube generation-density theorem or shell-order reduction is present.

**Strength and representation.** No counterpart statement to order by strength in the supplied frozen census. The source mathematical claim is not refuted by missing formalization, and existing prerequisites do not entail an exported generator/geometry result.

**Grouped components.**

- **Theorem 5.8 — not-covered.** universal asymptotic half guarantee for centered cubes; no corresponding endpoint in the supplied census.

**Algorithm/access scope.** Generic finite-history operators and a per-time correctness predicate exist, but no theorem promises a generator with eventual correctness or asymptotic half density on these windows. No lattice-shell bijection is exported.

**Witness identity and assembly.** No common generator, adversary, coloring or quantitative witness is provided for this source component by any inspected endpoint.

**Differences and qualifications.**

- The slot mapping has no registered endpoint; the complete 325-record native census was also searched by identifiers, theorem types, project dependencies and defining-body tokens before reporting lack of coverage.
- Coverage is bounded to the supplied frozen project census, not an assertion about every repository branch or unexported Mathlib theorem.

**Source questions kept separate from Lean differences.**

- The theorem says density always 1/2; surrounding text and the reduction present a guaranteed lower bound of 1/2 and optimal worst-case constant. Exact equality on every enumeration is not justified by the stated reduction.
- The proof writes rho(x)=(2k-1)^d+N(x) even at shell k=0, with N counting earlier points in the shell, and alternates between N and prefixes starting at 0. A special convention for the origin/initial index is omitted; finite initial indexing does not change the claimed asymptotic guarantee.
- The prose calls B(0,r) anchored at the origin, but the notation and shell proof describe centered cubes.

**Limits.**

- Source-internal ambiguities listed below are not diagnosed as Lean errors.
- No theorem proof, full algorithm construction or fresh compilation has been certified.
- Statement/interface correspondence only: no proof correctness, fresh compilation, or human review certification.

**Visual evidence.** [visual-checks/page_63.png](visual-checks/page_63.png).

### C13 — Multi-level discrepancy and the asymmetric Lovasz local lemma

Claim ID: `claim:kw26banach:theorem-5-9`. **not-covered**.

**Source locations.** Theorem 5.9 (printed 62; PDF 66); Finite-grid LLL proof and compactness extension (printed 62–65; PDF 66,67,68,69); Theorem 7.4 (printed 76; PDF 80).

**Full source statement.** Theorem 5.9: for arbitrary possibly infinite P subseteq Z^d, epsilon in (0,1) and alpha>0, put c0=(2*pi^2/(3*epsilon^2))^(alpha/(2*d)). For a rectangle R in R^d with m=|R intersect P|>=1, the source defines a nonnegative integer tier j by (c0/2^j)*L(R)^alpha<=m<(c0/2^(j-1))*L(R)^alpha, where L is the maximum geometric side length. It asserts one global coloring chi:P→{-1,+1} satisfying |sum_(x in R intersect P) chi(x)|<=epsilon*m+beta*sqrt(m*j)+gamma(m)*sqrt(m) for every rectangle, with beta=sqrt(2*(2*d/alpha+1)*ln 2), gamma(m)=sqrt(2*(2*d/alpha+2)*ln m+4*ln 2). The grouped appendix result is Theorem 7.4: for finitely many events A_i with a dependency graph, if x_i in (0,1) and Pr(A_i)<=x_i product_(j in Gamma(i))(1-x_j), then Pr(intersection_i complement A_i)>=product_i(1-x_i)>0.

**Standing assumptions and definitions.**

- P is any lattice point set and may be finite or infinite; dimension is fixed and positive (the application is d>=2).
- epsilon in (0,1), alpha>0, and nonempty finite R intersect P.
- The tier must satisfy the exact displayed lower and strict upper bounds and j>=0.
- For Theorem 7.4, the event family is finite, the graph genuinely encodes joint independence from non-neighbor events, and every weight lies strictly between zero and one.
- Discrepancy is the absolute signed sum over the points in the rectangle.
- L(R) is maximum geometric side length, not rectangle volume or point count.
- The finite proof restricts P to [-N,N]^d, bounds rectangle capacities by c0^(-2*d/alpha)*2^(2*d*j/alpha)*k^(2*d/alpha), and uses independent unbiased point colors plus weights (1/2)*k^(-p)*2^(-q*j), p=2*d/alpha+2, q=2*d/alpha+1.
- The infinite extension uses compactness of {-1,+1}^P (sequential compactness because P is countable) and finite closed cylinder constraints, not an infinite-event version of Theorem 7.4.

**Lean declarations directly checked.**

No source-claim endpoint or source-specific related prerequisite was found. The census search is documented below.
**Comparison.** No size-sensitive discrepancy or finite asymmetric-LLL project endpoint is present in the supplied census.

**Strength and representation.** No counterpart statement to order by strength in the supplied frozen census. The source mathematical claim is not refuted by missing formalization, and existing prerequisites do not entail an exported generator/geometry result.

**Grouped components.**

- **Theorem 5.9 — not-covered.** one global coloring with the exact multi-level bound; no corresponding endpoint in the supplied census.
- **Appendix Theorem 7.4 — not-covered.** finite asymmetric LLL with positive quantitative avoidance probability; no corresponding endpoint in the supplied census.

**Algorithm/access scope.** No finite-grid coloring construction, probability-event dependency interface, size-sensitive discrepancy constants/tier definition or compactness extension is exported. A standard-library LLL outside this project census is not ruled out and would not by itself formalize Theorem 5.9.

**Witness identity and assembly.** No common generator, adversary, coloring or quantitative witness is provided for this source component by any inspected endpoint.

**Differences and qualifications.**

- The slot mapping has no registered endpoint; the complete 325-record native census was also searched by identifiers, theorem types, project dependencies and defining-body tokens before reporting lack of coverage.
- Coverage is bounded to the supplied frozen project census, not an assertion about every repository branch or unexported Mathlib theorem.

**Source questions kept separate from Lean differences.**

- The tier formula does not provide a nonnegative j when m>=2*c0*L(R)^alpha, despite asserting that every nonempty rectangle has a unique tier. The displayed statement does not say to cap j at zero or treat dense rectangles separately.
- If zero geometric side lengths are allowed, L(R)=0 is another case without the stated tier. Positive-side conventions are not made explicit.
- The theorem quantifies over real-coordinate rectangles, while the capacity proof counts integer intervals and treats the geometric side-length cutoff as an integer interval-length cutoff; canonical lattice representatives and endpoint conventions are implicit.
- The theorem says constants depend only on d and alpha after c0, but gamma explicitly also varies with m, as its displayed formula records.
- Theorem 7.4’s mutually independent wording should be read as independence from the sigma-algebra generated by non-neighbor events; pairwise independence alone is not the dependency hypothesis used by LLL.

**Limits.**

- Source-internal ambiguities listed below are not diagnosed as Lean errors.
- No theorem proof, full algorithm construction or fresh compilation has been certified.
- Statement/interface correspondence only: no proof correctness, fresh compilation, or human review certification.

**Visual evidence.** [visual-checks/page_66.png](visual-checks/page_66.png), [visual-checks/page_80.png](visual-checks/page_80.png).

## Native census search and coverage boundary

The complete 325-record census was parsed: 98 definitions, 215 theorem interfaces, four inductives, four constructors and four recursors. All theorem values are suppressed. All 40 recursive bundle records agree with their native copies in name, kind, module, source line, type and definition value. All ten files in Stage 1 SHA256SUMS match. These are export-integrity checks, not Lean proof verification.

Search used every record’s identifier/type/dependencies, and definition values where present. Matches for ENNReal, Filter.liminf and the density definitions reduce to the one-dimensional window definitions, Claims 3.3/3.5 and their elementary inequalities/top equalities; the relevant native lines are 89, 92, 93, 110–113, 129–132, 210–211, 218 and 243. No type or definition body matches integer/real lattice geometry, rectangular/filtered density, discrepancy/coloring, or probability-event structures. The only direct Generic.Generator/CorrectAt/output matches in type/value searches are the generic per-time correctness definition and output definition (lines 16 and 37). No inspected theorem combines a generator’s eventual validity with a zero, half or nearly-half density conclusion.

The generic definitions provide finite-history operators `(t : Nat) → (Fin t → Input) → Output`, sets and presentations; MembershipOracle provides a query function with a semantic membership specification. They do not supply the source’s generation-density algorithms, and none of the registered targets consumes that oracle. No computability claim is inferred from these arbitrary functions.

Consequently C08–C13 are **not-covered in this supplied frozen project census**. C08 has the nice/window prerequisites; C09 has rank/tower/LCA prerequisites; C11 has topological prerequisites. These are partial background formalization, not the corresponding theorem or named algorithm. C13’s imported mathematical LLL could exist in Mathlib outside the exported project roots; that possibility neither establishes the grouped project statement nor supplies its discrepancy construction. No global repository or other-branch absence claim is made.

## Discrepancies, suspected source issues and Stage 1 refinements

The covered density helpers match their mathematical source meanings after standard integer-window and extended-nonnegative-real representations. The C02 tower equivalence and C04 tree bookkeeping are abstracted to wider mathematical domains. C03 makes a genuine-approach/exclusion hypothesis explicit; its failure to reproduce an unqualified constant/cluster-point reading is a source qualification, not a demonstrated Lean error. C05’s exact structural assumptions are now expanded from the neutral kernel/source supplement and support the rooted-tree bridge; no bare-semilattice generalization is claimed.

Source issues retained for Stage 3 include: the inconsistent point-rank indexing; convergence versus cluster-point language and terminal repetitions in Claim 4.11; the two different limit conditions in Theorem 2.4/5.1; overview versus fixed-filter quantifier order; literal identification in Corollary 5.7; volume/side-boundary and empty-admissible-family conventions; exact-half wording and shell-origin indexing in Theorem 5.8; and the uncovered dense-tier range in Theorem 5.9. For the last issue, when alpha<d and P fills large lattice rectangles, m can exceed 2*c0*L^alpha, for which the stated nonnegative tier does not exist. No source correction has been applied silently.

No definite mathematical misreconstruction of the eight Stage 1 targets was found. The following additions refine Stage 1’s scope:

- C01: native `lowerWindowDensity_top` supplies an explicit attaining scale alongside the infimum facade; the facade alone need not be rewritten as a witness-bearing theorem.
- C02: the exact `perfectTower_of_basisLimitPoint`, properness and eventual-containment types identify the same named `adaptiveTower`. This does not identify the facade’s arbitrary existential witness with it or confer computability.
- C03: the native basis-convergence theorem and derivative-exit theorem distinguish the actual source qualification from the proper-tower facade. The exit theorem alone does not require a globally finite class rank.
- C04: native `claim_4_18_monotone_ancestral_chain` covers the source’s chain component separately from the registered cardinality endpoint; both concern the same `prefixLCA`.
- C05: the source and kernel external-definition supplements expand the previously disclosed Stage 1 boundary; this is added evidence, not a correction to its exact-type reconstruction.
- C08–C13: Stage 1 correctly limited its no-target finding to the slot map. Stage 2 now reports no corresponding complete theorem after native-census search; it does not merely repeat the absent-facade flag.

## Coverage checklist and unresolved questions

- Exactly 13 slot rows; every overview, detailed theorem, enumerated corollary and relevant appendix component is itemized. The speed-C extensions and source-global model are retained.
- All eight registered theorem types and recursively necessary defining values were rechecked directly. Supporting native types are cited with exact module/line and census-line anchors.
- Same-witness properties, abstract interface assembly and semantic/classical versus effective access are separated. No learner program is inferred from a set/function or unnamed existential.
- Questions for Stage 3: resolve source rank/exclusion conventions; whether Corollary 5.7’s identification wording and overview-filter quantifiers are intended literally; Theorem 5.1’s limit subscript; Theorem 5.9’s dense-tier case; and geometric boundary conventions. None makes uncovered Lean results into incorrect Lean results.
- C05’s external-definition boundary is resolved using the authorized neutral 12-record kernel supplement and source excerpts. No explicit native graph-to-order adapter is claimed. All 13 comparison rows are complete.
- No proof-body audit, raw Lean comments, owner notes, stage3 context, PaperMaps, old audits, Git writes, or source modifications were used. No agents were spawned.
- No targeted Lean check or repository-wide Lake build was run: this is an interface audit without Lean edits. No build failures or warnings were observed because builds were not attempted.

Stage 2 comparison is complete and stops here for coordinator verification/freeze. No owner/developer explanation or Stage 3 adjudication was opened.
