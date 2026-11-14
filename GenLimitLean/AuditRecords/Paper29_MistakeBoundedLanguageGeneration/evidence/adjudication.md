# P29 informed adjudication

## Disposition and provenance

The frozen Stage 2 findings stand. C01's positive-prior finite-bound guard and C02's generator-first +1 correction are justified. C03's full displayed bound is present in the native interface. C04 remains a disclosed substantive coverage gap: its endpoint is arithmetic only, and its source proof independently has an unresolved fixed-base/Big-O quantifier problem. No genuine translation mismatch or missing interface assembly was established.

This is the **same continuing source-informed Stage 2 reviewer**, now authorized to read explanations, not a third independent blind audit. The coordinator supplied the focus topics (+1, positive/reachable targets, native C03 display, arithmetic-only C04); they repeat the frozen findings and are not independent evidence. PaperMap and registry assertions were treated as fallible explanations. Their kernel/human-review assurances were not adopted as validation or awarded audit credit.

All informal arguments below are **not Lean-checked**. No theorem proofs, source or registry edits, builds or Git operations were performed. The source remains arXiv:2605.10809v1, original PDF SHA-256 `c79335d8c0fec7e3960c141c034a34144e4928d118f27311c8d661f81ba61365`; printed/PDF page numbers coincide.

## Every registered target

| Slot / target suffix under `GenLimit.MistakeBounded.Results` | Final assessment |
|---|---|
| C01 / `theorem_4_1` | Justified source clarification: exact finite bound for positive, finitely activated target; faithful weighted algorithm with a semantic/classical qualification. |
| C02 / `theorem_5_1` | Justified source correction: same generator has count min{floor(log2 N),d+1} and no errors at zero-based t≥d+1. Literal printed d bounds remain different. |
| C02 / `theorem_5_1_order_diagnostic` | Matches the static disjoint-pair obstruction. Its type does not itself formalize an online adversary. |
| C03 / `theorem_6_1` | Matches source context through a sharper integer form. Supporting native/public displayed-bound endpoint supplies the exact source real RHS. |
| C04 / `theorem_6_4_proof_diagnostic` | Valid numerical proof fragment; substantive formalization gap for the headline tradeoff. Source theorem truth remains unresolved. |

The final four-row JSON retains the frozen correspondence classifications and splits source corrections, model qualifications, native supporting results and gaps by component.

## Existing explanation inventory

| Explanation | Actual SHA-256 | Decisive anchors |
|---|---|---|
| `stage3-context/PaperMap.md` | `3c0e38bf0a98fe7f5758324584296997725856cf9517317f4971658c9ba7c26c` | Lines 20–23: classical boundary; line 34: positive prior; line 36: +1; line 40: C03 exact/displayed bounds; line 42 and lines 81–83: C04 open. |
| `owner/registry.json` | `78e603ec973415885fd71b1f994e0014afcfc412c4806b4233033c3706b50071` | Each scoped claim's `source_assessment`, `formalization`, `lean_links`; `paper.formalization_scope`. |

Both disclose the corrections and C04 gap. Disclosure resolves whether these differences were acknowledged; the mathematical checks below determine whether the explanations are justified. Their broad “full source repair” phrasing is read subject to the actual finite-domain and semantic qualifications, not as certification of every paper component. LfD/noisy results and the separate finite hard-class lemma remain outside these four headline conclusions, as documented.

## C01: positive finite/reachable domain

Source Theorem 4.1 (pp.5,15–16) permits nonnegative priors and writes `d_i+floor(log2(W/w0(i)))`, assigning infinite delay when the schedule never reaches i. The frozen Lean endpoint instead requires positive target prior, a finite first-activation witness a, bounded nonnegative prefix mass B, and `B<2^(b+1)w(k)`, then bounds every prefix by a+b. With i=k+1, r=t+1 and A(t)=f(t+1), activation a equals source delay d_i. Since B≥w(k)>0, the least admissible natural b is exactly floor(log2(B/w(k))); the strict endpoint handles dyadic equality correctly. The generator does not depend on its target or budget.

The zero-prior issue is real under all other source premises. Take X=N, L1=evens, and Li=N∖{2i} for i≥2. These are a fixed countably infinite family of distinct infinite languages. Choose f(t)=t, all priors zero, W=1, adversarial xt=2(t−1), and generate the point 1 at every round. Every score stays zero, so this is an admissible fresh maximizing tie rule; 1 is never an adversarial output and every prediction is wrong. The target is realized, the stream is injective, and every target index is reached. Thus one cannot infer a finite guarantee for all allowed zero-prior ties. Separately, at weight zero the dyadic premise is B<0, impossible when B≥0; the native zero-weight interface states that impossibility.

The smallest finite-bound repair is to require positive target prior and finite entry delay, or explicitly treat unreachable targets as an infinite/vacuous bound. Lean implements the positive finite-entry branch. Positive prior is not asserted necessary for every successful generator, and it does not itself ensure reachability. This qualification is stronger than merely citing the owner explanation.

## C02: generator-first +1 correction

Source Theorem 5.1 (p.6) says count≤min{floor(log2 N),d} and last erroneous round≤d. Its own Example 1 (p.2) instead forces an error at n+1 after n shared points are exhausted. The smallest instance satisfies every source premise: X=N, class {evens,odds}, both infinite, disjoint and with closure dimension 0. Before any observation the first prediction misses one possible target; choose that target and enumerate it injectively. At least one error occurs in paper round 1, contradicting both printed zero bounds. These languages, observations and the adversary require no special oracle or noncomputable representation.

The correction also works in the general source setting. After zero-based t≥d+1 distinct target observations, the intersection of all consistent languages contains t>d points. If finite it would violate the dimension upper bound. It is therefore infinite and has an unseen common point; the weighted algorithm's critical-choice property selects such a point. Errors are confined to zero-based rounds 0,...,d, giving at most d+1 errors, combined with the retained floor(log2 N) mass bound. The checked endpoint puts these two bounds on the same named generator.

Thus the smallest generator-first repair changes both closure clauses to d+1. `LastMistakeBefore(d+1)` means no errors for zero-based t≥d+1, equivalently paper correctness from r≥d+2 and last erroneous paper round≤d+1. A clock shift alone would not repair the original total-count clause. The diagnostic proves only D(pair,0) and pointwise nonmembership in one member; the adversarial argument above is informal. N=0 has no target, N=1 has zero logarithmic count, and the corrected disjoint-pair weighted run allows exactly one worst-case first-round error.

## C03: full native bound and harmless proof inequality repair

The source instance uses prior 1/i² and f(r)=2ʳ, with total π²/6. Under i=k+1 and r=t+1, the checked definitions are exactly p(k)=1/(k+1)² and A(t)=2^(t+1). Every target prior is positive and every target is reached, so C01's finite-domain guards impose no loss on this instance.

The registered endpoint bounds count by the exact activation `max{ceil(log2 i)−1,0}` plus `floor(log2((π²/6)i²))`. The activation is at most log2 i, and the floor term is at most log2(π²/6)+2log2 i, giving the source display for every valid stream and every horizon. Initial indices i=1,2 and powers of two are covered without assuming a false equality with floor(log2 i).

This is also explicit natively: `Results.theorem_6_1_displayed_bound` (`Results.Overview:125`) and `theorem_6_1_displayed_real_bound_concrete_semantic_algorithm` (`PolynomialPrior:532`) state the real bound `3log2(k+1)+log2(π²/6)` for the identical stream. They are supporting evidence outside the five required target links, not an expansion of those targets. The source proof's final floor-dropping equality needs only replacement by ≤; its headline statement is unchanged. There is no missing-rate or interface-assembly issue.

## C04: construction/quantifiers remain separate from arithmetic coverage

The source (pp.11–12) asserts one fixed class, followed by every generator meeting an O(max{i,m_i}) convergence rate, followed by an i−1 mistake lower bound for every i≥2. The frozen endpoint says only `G(n,i)+n^i+1=G(n,i+1)+1` for i>0. It includes no language, generator, stream, O constant or lower bound. Native Modified-Greedy upper bounds are present but concern a different positive result. The owner accurately documents that the headline theorem is unformalized; the diagnostic is neither a proof nor a refutation of it.

The source family itself passes the basic premise checks for fixed n≥2. On a countably infinite pair universe, Li has its full infinite i-th row and finite earlier row-prefixes. The languages are infinite and distinct. For a nonempty earlier subfamily, the intersection with Li is determined by its smallest index, giving maximal finite intersection `m_i=G(n,i)=Σ(1≤j<i)n^j`; the source explicitly sets m_1=0. The tail intersection has size G(n,i+1). Block prefixes are distinct, remain inside the target selected on stopping, and can be completed to an injective enumeration. If a prediction lies in the earlier target at a boundary, its common points with later targets have all been seen; hence it misses those later targets. Avoiding the first stopping branch therefore yields the stated i*−1 boundary errors. The introduction's weaker i*−2 wording can be aligned without fixing the main issue.

The allegedly late round fails the required asymptotic test. For i≥2,

`T_i = G(n,i)+n^i+1 = n G(n,i)+n+1 ≤ (n+2)G(n,i) ≤ (n+2)max{i,m_i}`.

For i=1, T_1=n+1≤(n+2)max{1,0}. Thus all these rounds are themselves within O(max{i,m_i}) with an allowed class-dependent constant. As i grows, T_i/m_i tends to n, not infinity. This checks the paper's max term and its m_1=0 edge, not just the large-index formula.

Taking n large after an algorithm's hidden constant changes the class. It cannot establish the printed order “one class, then every algorithm with its class-dependent constant.” A possible weaker quantifier repair would prescribe a convergence constant C before selecting a sufficiently large-base family; preserving the headline order instead needs a new justified construction or argument. Neither is established by the arithmetic identity. The source theorem's truth remains unresolved, independently of the substantive formalization gap.

## Validation boundary and remaining work

Both sides' positive algorithms are semantic exact selectors with arbitrary membership and exact real weights. The paper states no explicit oracle implementation, computable maximizer or running-time theorem; the Lean interface's classical choice supplies none. The examples above use effective languages, so the C01/C02 source issues are not artifacts of that semantic generalization. No probability/distribution, stability or sampling premise is involved in these scoped claims.

All nine frozen source-inventory/Stage 1/Stage 2 artifacts were hash-verified and preserved. Previous visual source checks remain valid; the relevant source statements and four decisive native interfaces were reread after explanations. The earlier native-census gap search is reused with its stated limits; no raw proofs or new repository-global absence claim was introduced. This is a statement adjudication, not a Lean proof audit or a certification of all source proofs.

Retain the qualified/corrected C01–C03 statements and explicit clock conventions. Keep C04 coverage none/open and its endpoint diagnostic-only; resolve its quantifiers and obtain a corrected proof before formalizing the headline lower bound. No unrequested edits were made. Stop for coordinator freeze.
