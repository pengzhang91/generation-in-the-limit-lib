# P30 independent source inventory — source-first freeze candidate

Source: Ganju, McVoy, Dughmi, and Teng, *A Theory of Time-Sensitive Language Generation: Sparse Hallucination Beats Mode Collapse*, arXiv:2605.11302v2. The local original PDF actually hashes to `c66e7e8848a3931c0f03023769ef70a78785b2eaec15e0f1724e625f8392416a`. Its annotation-free viewing derivative has a different verified hash recorded in the run file. Printed and PDF page numbers coincide. The edition marker is 19 May 2026; the title-page manuscript date is 21 May 2026. Only this edition was used; all 28 pages of supplied author text were read.

## Shared mathematical and computational context

Section 1.1 (pp.2–3) gives fixed known bijective orders on the countably infinite universe U and language collection L. The universe order restricts to each target language’s rank order. The adversary fixes K∈L and a total enumeration E of K; observations may repeat. At round t, A sees e₁:ₜ and outputs one universe string not previously observed or output. Internal randomness is allowed. The language ranks kⱼ are not observation positions.

Write H_A(t)=E[|A(E)ₜ∖K|/t], with expectation over the generator’s randomness. Vanishing hallucination means, for each L, sup_K sup_E limₜ H_A(t)=0: the limit is inside the suprema. Eventual consistency means there exists a finite T, allowed to depend on L,K,E, after which every output lies in K. The definition does not separately specify a random stopping-time interpretation.

Element-wise timely density is μᵢ(S,K,D)=i⁻¹∑ⱼ₌₁ⁱ1{kⱼ∈S_D(j)}. Global μ_low takes inf_L inf_K inf_E liminfᵢ; μ_up uses limsup. Prefix density instead counts |S_D(i)∩Kᵢ|/i, allowing a string to count after its individual deadline. The generalized inverse is D⁻¹(t)=min{n:D(n)≥t}. The deadline ∞ denotes the no-deadline metric. Half-density optimality is attributed to adversary-first turn-taking (p.3 footnote 1).

The results concern interaction rounds, not computational work. The source provides abstract access to L,U and pseudocode involving earliest-unused searches and, for GCG, language-inclusion comparisons. It gives no named oracle interface, decidability assumptions, or bound on the work needed for a round. The all-prefix/fresh-output setup implicitly uses infinite languages; p.2 does not separately state this for every language.

## C01 — claim:gmdt26:theorem-1

**Locations:** Theorem 1, p.4; Definition 1 and discussion, pp.4–5; Appendix B Definition 5 and Examples 1–2, pp.13–14; Appendix C Lemma 4/proof and Theorem 5, pp.14–16.

There exists one countable family L such that **for every** D:ℕ→ℕ and **every** eventually consistent A, inf_K∈L inf_E∈E(K) liminfᵢ μᵢ(A(E),K,D)=0. Consequently global μ_low(A,D)=0. The family precedes D and A in the quantifier order.

The witness is a measure-zero chain L¹⊆L²⊆⋯⊆L∞, with union L∞ and each fixed Lʲ having zero lower density in L∞. Appendix B constructs dyadic-block and exponential-marker examples. The shared barrier (Lemma 1/4) says that, for monotone D, sup_K sup_E H_A(t)=o(D⁻¹(t)/t) forces zero lower density almost surely for randomized A. Appendix C constructs a seed-independent enumeration of L∞ in stages indistinguishable from Lʲ through tⱼ. It arranges chain density ≤2⁻⁽ʲ⁺¹⁾ and expected outside-Lʲ contribution divided by iⱼ ≤2⁻⁽²ʲ⁺¹⁾, where iⱼ=D⁻¹(tⱼ); Markov yields failure ≤2⁻ʲ, and Borel–Cantelli yields zero prefix density along a subsequence, hence zero element-wise lower density.

**Source qualifications:** Theorem 1/5 has arbitrary D and no probability qualifier; its lemma assumes monotonicity and explicitly says almost surely. The one-line bridge from eventual consistency to the lemma does not explain the lemma’s uniform supremum rate. The inverse also needs a nonempty defining set. On p.15, the displayed output-prefix inequality uses D(iⱼ) as though it were ≤tⱼ, whereas the p.3 inverse definition gives D(iⱼ)≥tⱼ; this apparent source mismatch is preserved. These are source issues, not changes to the advertised claim.

**Visuals:** pages 2–5, 14–16 in `visual-checks/`.

## C02 — claim:gmdt26:theorem-2

**Locations:** Theorem 2 and Lemma 1, p.4; shared chain context, p.5; Appendix C, pp.14–16, especially Theorem 6 on p.16.

There exists one countable L such that for every D satisfying **D(i)=O(i)**, every A with vanishing hallucination rate has the same fixed-family worst-case timely liminf zero. Consequently global μ_low(A,D)=0. The printed condition is an upper asymptotic bound, not only the identity deadline or Θ(i). The theorem does not restrict A to be deterministic and does not print an almost-sure qualifier; the supporting randomized lemma does.

The proof is the C01 barrier specialized to linearly bounded deadlines, including its stage construction and summable failure probabilities. The printed vanishing-rate definition is pointwise in K,E, while the lemma states a supremum-before-little-o assumption. The one-line application does not explain this difference. O(i) alone also does not add monotonicity or unboundedness required by the inverse context. The p.15 inverse-time mismatch belongs to this shared proof too.

**Visuals:** pages 3–5, 14–16.

## C03 — claim:gmdt26:theorem-3

**Locations:** Definition 2, p.5; Theorem 3, Definition 3 and Lemmas 2–3, pp.6–7; Algorithm 1 and discussion, pp.8–9; Appendix D data models and reductions, pp.16–23; Appendix D.3 Theorems 8–11 and proof of Theorem 3, pp.23–24.

For every feasible (D,H), there exists a **randomized** generator A with global element-wise μ_low(A,D)=1/2 and, for each countable L, sup_K sup_E H_A(t)≤H(t) at all sufficiently large t. Feasibility requires D nondecreasing, discrete convex and superlinear, H nonnegative, nonincreasing and vanishing, and H(t)=ω(D⁻¹(t)/t). Footnote 2 says discrete convexity is unnecessary for the argument but assumed for exposition. Thus the budget is strictly above the inverse-deadline barrier in asymptotic scale, while still tending to zero.

Theorem 3 does not print “almost surely”; its supporting Lemma 3/9 and Theorem 9 do. The rate is **expected** hallucination, not a pathwise probability-one rate. The density equality is a global worst-case optimum; it is not an assertion that every run has exactly half density.

The full construction has two components. Lemma 2/5 selects a prefix profile (D_pfx,H_pfx), with r(i)=max{j≤i:D(j)<D_pfx(i)}=o(i) and H_pfx≤H eventually, so μᵢ(element)≥μᵢ(prefix)−r(i)/i. Lemma 3/9 converts an eventually consistent deterministic black box B of no-deadline density ρ into A_B with prefix density ≥ρ almost surely, using only black-box calls to B.

Algorithm 1 takes D,H,B and observations. In epoch m, rounds D(m−1)+1 through D(m), it speculates with probability δ_m=min{1,10C(m)/(D(m)−D(m−1))}; speculation uniformly chooses one of the first C(m) languages and emits its earliest unused element. Otherwise it uses B’s t-th proposal. C is nondecreasing and unbounded, C(m)=o(D(m)−D(m−1)), and ∑_{m≤m(t)}C(m)=o(tH(t)). On a fixed instance the expected hallucination count is bounded by N_B(X,K)+10∑C(m). After target inclusion, expected target speculations by D(i) are ≥5i eventually, and the chance of fewer than i is ≤exp(−ci). Freedman’s inequality gives a black-box credit-loss probability ≤exp(−c_εi), using increments bounded by 1, variance total ≤i and deviation εi/2. Borel–Cantelli yields the prefix guarantee.

Appendix D explicitly includes grouped extensions: arbitrary admissible observation models; partial enumeration of an infinite subset of K of lower density ≥α, yielding timely density ≥α/2 (Theorems 8–9); and finite symmetric-difference contamination, yielding ≥1/2 (Theorems 10–11). Theorem 3 is derived by α=1. These black-box baseline facts are imported from [18] and [20], not independently checked here. Section 3.2 additionally describes deadline density 1 for the union of generator and adversary outputs and target-index-dependent onset through C.

**Source qualifications:** The p.20 hallucination proof fixes X,K and then chooses a time depending on finite N_B(X,K); the stated sup_K sup_E bound is uniform, and no uniform bound on this finite term is supplied. Lemma 7 proves D_pfx monotone and superlinear but does not separately prove discrete convexity before calling its profile feasible. Algorithm 1 has no explicit replacement for a B proposal already speculated. General-model p.16 excludes prior outputs but omits the main model’s exclusion of observed strings, although NextUnused still refers to both players. Concentration is proved after fixing X; no simultaneous full-measure seed event across all observations is specified. Initial D(0), flat increments, and empty maxima conventions are not fully stated.

**Visuals:** pages 3, 5–8, 16–24.

## C04 — claim:gmdt26:theorem-4

**Locations:** Definition 4 and Theorem 4, p.10; Appendix E imported Accurate and Algorithm 2, p.25; Theorem 12 and full proof, pp.26–28.

With **D(i)=i**, an eventually consistent generator achieves global μ_up=1/2. Appendix Theorem 12 specifies that GCG is **deterministic**. For each K and total enumeration E the proof gives limsupᵢ μᵢ(GCG(E),K,id)≥1/2. The high-density subsequence can depend on the instance. This is not a liminf guarantee.

Accurate, imported from [17], outputs language guesses equal to K infinitely often and contained in K at every sufficiently large time. GCG appends a guess to list G when it strictly contains its immediately preceding guess. It generates the earliest on-time element unused by either player from the current guess during stage 0 and from g_m in later stages. Thresholds α_m=1/2−2⁻ᵐ determine advancement when a next candidate exists. The proof treats G empty, G growing indefinitely, and G finite nonempty. In a permanent fixed-language stage beginning at T, the greedy bound is μᵢ≥⌊(i−2T)/2⌋/i; in infinitely many target stages the thresholds approach 1/2. Eventual consistency is a separate assertion of Theorem 12 with no quantitative stabilization time.

**Source qualifications:** The stage-advance test is printed at m=0 with undefined g₀, while the prose says move to stage 1 once G is nonempty. Numeric third arguments in μ_t(…,g_m,t) are used as shorthand for the identity deadline. Only two Accurate properties are supplied locally, while the finite-list proof reasons about strict-superset transitions from immediate predecessors without stating an extra nesting/transition property. The final paragraph closes the upper-density cases without a separate concluding eventual-consistency proof. Strict language inclusion and earliest-on-time search remain abstract operations.

**Visuals:** pages 3, 10, 25–28.

## Review boundary

Exactly four indexed slots are inventoried in the JSON. All relevant grouped appendix material was included as context under those slots. No source-to-formalization comparison or correspondence classification has been made. Stage 1, implementation/interface material, prior assessments and audit records were not accessed. This inventory and its run record are ready for coordinator freeze; further access requires that authorization.
