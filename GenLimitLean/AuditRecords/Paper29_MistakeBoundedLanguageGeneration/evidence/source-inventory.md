# P29 independent source inventory — source-only phase

Edition: Kleinberg, Peale, Reingold, *Mistake-Bounded Language Generation*, arXiv:2605.10809v1. The margin gives 11 May 2026; the title page gives May 12, 2026. Only this edition was used. PDF pages and printed pages coincide, 1–22. The pinned original PDF was independently hashed as `c79335d8c0fec7e3960c141c034a34144e4928d118f27311c8d661f81ba61365`; visual checks use the annotation-removed derivative, separately hashed in the run record.

## Standing conventions

Section 3 (pp.3–4) fixes a countably infinite universe and infinite languages. Infinite classes have a fixed enumeration L1,L2,.... At round t=1,2,... the generator outputs before the adversary, using x1,...,x(t−1). Its output must avoid that finite adversarial prefix; avoiding its own earlier outputs is unnecessary. Adversary outputs are distinct and all belong to the eventual target. Exhaustive target coverage is not assumed. There is no correctness feedback beyond the adversary's examples.

Definition 3 takes the supremum over all such streams of the sum of errors of G on prefixes of lengths s=0,1,.... This is the same sequence of decisions as algorithm rounds t=s+1. Definitions 1–2 require correctness for all t at or above a cutoff, target-dependent or class-wide respectively. The later phrase “last-mistake time” refers to the last erroneous round. Remark 1 expressly permits a shift of at most one when move order is changed; it does not erase exact boundary issues.

The algorithms make semantic exact choices. Finite active prefixes do not by themselves provide procedures for membership, intersection nonemptiness, or maximizing a score over an infinite universe. The paper supplies no such representation/oracle/complexity model. All four guarantees are worst-case, without an expectation or probability qualifier. Appendix B was also read: it models a prefix s as an LfD context, with reward 1[y∈Li∖s], explaining how freshness and absent feedback fit the reduction.

## C01 — weighted countable mistake bound

Claim ID: `claim:kpr26:countable-weighted-mistake-bound`. Theorem 4.1 and Algorithm 1, p.5; restatement, Lemma A.1 and proof, pp.15–16. Supporting conventions are pp.3–4.

For a fixed enumerated infinite class, take nonnegative priors w0(i), total mass at most a finite W, and nondecreasing f:N→N. Let d_i=f⁻¹(i) be the largest round before the first f(t)≥i, with 0 when already active at the initial round and infinity when never reached. Algorithm 1 promises, for every target index and every realized distinct stream,

`total errors ≤ d_i + floor(log2(W/w0(i)))`.

The same generator is used for every target. At round t it maximizes the sum of weights of languages containing the candidate, considering i≤f(t) and only unseen candidates. After xt is observed it eliminates languages missing xt, keeps weights when both outputs belong, and doubles weights when xt belongs but the prediction does not. At the end of a round newly admitted languages get their prior only if consistent with the whole observed prefix.

The potential W_t sums weights through f(t+1), including newly initialized weights. Active weight cannot increase, because the chosen prediction has at least the weighted support of the unseen xt. Adding new prior mass keeps W_t≤W. After the target first appears at d_i+1, each error doubles its weight, yielding at most floor(log2(W/w0(i))) further errors, in addition to at most d_i earlier ones.

Source qualifications: zero priors are permitted in the stated hypotheses, but division/logarithm at zero is not defined; a finite meaningful bound needs positive target prior. A finite entry delay is also necessary for a finite conclusion. The initial active weights are understood to be the supplied w0 although no separate initialization loop is shown. Source pp.17–22 give related LfD context; no extra computational assumptions are supplied there.

Visual checks: pp.3,4,5,15,16 in `results/visual-checks/page_<p>.png`.

## C02 — simultaneous finite-class guarantees

Claim ID: `claim:kpr26:finite-class-joint-bound`. Definition 4 and Theorem 5.1, p.6; Algorithm 2, Theorem 5.2 and the hybrid proof, p.7. Example 1 on p.2 is relevant to timing.

Cdim(L) is the largest finite cardinality of an intersection of a subcollection of L. For each finite class, Theorem 5.1 asserts one uniformly generating algorithm with both guarantees, for every realized target and stream:

1. Total errors ≤ min{floor(log2|L|), Cdim(L)}.
2. Last erroneous round ≤ Cdim(L).

Use Algorithm 1 with N=|L|, all priors 1 and f(t)=N. It gives floor(log2 N) errors. Algorithm 2 requires choosing an unseen point in the intersection of all prefix-consistent languages whenever this set is nonempty. All consistent weighted languages have positive weight and all inconsistent ones have zero weight, so any maximizing prediction must lie in that common intersection when it is available. The same generator therefore satisfies Algorithm 2's critical rule. The paper invokes its stated Cdim time guarantee and bounds count by last-error time to obtain the minimum. The subsequent lower bound, pp.7–9, concerns worst classes of cardinality N, not per-class optimality.

Source ambiguities: under the paper's generator-first, round-1 convention, Example 1 says an intersection of size n can force an error at n+1; Definition 4 gives Cdim=n for that two-language example. Theorems 5.1/5.2 nevertheless state the bound n. The disjoint case n=0 also conflicts with the zero-error minimum. This source timing issue is retained, not silently repaired. The maximum defining Cdim has no stated empty-set value when no subcollection has a finite intersection. The proof uses any nonempty unseen common intersection; the preliminary p.6 discussion of infinite intersections is not the full algorithmic condition.

Visual checks: pp.2,4,6,7.

## C03 — logarithmic non-uniform mistake bound

Claim ID: `claim:kpr26:logarithmic-nonuniform-bound`. Instantiation on p.9; Theorem 6.1 and proof on p.10; Theorem 4.1 and Appendix A also apply.

For every fixed enumeration of a countably infinite class, one instance of Algorithm 1 uses w0(i)=1/i², f(t)=2ᵗ, and W=π²/6. For every i≥1 its mistake supremum satisfies

`M_non-unif(G,i) ≤ 3 log2 i + log2(π²/6) = O(log i)`.

The entry delay is at most floor(log2 i), while log2(W/w0(i))=log2(π²/6)+2log2 i. Substitution into C01 proves the displayed bound. This is a guarantee on total errors; no common target-dependent last-error round across all realized streams is supplied. Finite errors on each stream do give eventual correctness separately on that stream.

Source qualifications: d_i is only bounded by floor(log2 i), not equal to it at powers of two under the strict f(t)<i definition. The proof's final simplification displays equality after dropping the floor; inequality suffices for the stated result. The explicit additive constant is part of the all-index claim, even though O(log i) is asymptotic.

Visual checks: pp.5,9,10,16.

## C04 — mistake/convergence tradeoff

Claim ID: `claim:kpr26:mistake-convergence-tradeoff`. Definition 5 on p.9; comparison Algorithm 3 and Lemmas 6.2–6.3 on pp.10–11; Theorem 6.4 on p.11 and proof on p.12.

The displayed definition of m(Li) maximizes the finite size of Li intersected with a subcollection of earlier languages. The theorem asserts an existential single fixed enumerated infinite class such that every generator whose last-error time is O(max{i,m(Li)}) on all targets has `M_non-unif(G,i)≥i−1` for every i≥2. Streams witnessing this may depend on i. The positive comparison is Modified-Greedy: it scans the first t languages and keeps prefix-consistent intersections whenever an unseen point remains. Its stated time bound is max{i−1,m(Li)+1} and count bound is the minimum of that quantity and 2(i−1).

The hard family is on N×N. Fix an “arbitrarily large” n and put in Li its complete infinite i-th row plus the first nᵏ points of each earlier row k<i. The proof computes m(Li)=Σ(j=1,...,i−1)nʲ and m(L1)=0. The intersection of all languages from i onward has size m(Li)+nⁱ.

For a chosen i*≥2, list row blocks successively. At boundary `t_i=1+Σ(j=1,...,i−1)nʲ`, just before point (i,1), inspect the generator. If its prediction misses L(i−1), switch to enumerating the rest of that language, creating an error at `m(L(i−1))+n^(i−1)+1`. Otherwise its unseen point in L(i−1) lies in no later language, because those common finite points are exhausted. At i=i*, switch to enumerating the rest of L(i*). If the first branch never executes, boundaries 2 through i* supply i*−1 errors. The final stream remains distinct and realized.

Source ambiguities: the proof fixes n before using ω(m(Li)), but for fixed n>1 the displayed ratio tends to n as i grows. Taking n large instead raises the dependence of the hidden O constant on n and the quantifier order for the theorem's single fixed class; neither is specified or resolved in the text. Its opening proof paragraph says i*−2 errors, whereas the theorem, explicit boundary count and closing paragraph say i*−1. Definition 5's prose says size of a subcollection, but the displayed formula measures intersection size. The proof gives m(L1)=0 without a general empty-maximum convention. Last-error time and the inclusive convergence cutoff should remain distinguished.

Visual checks: pp.4,9,10,11,12.

Source inventory only. No Lean, first-stage reconstruction, owner assessments, prior audits or human reviews were accessed. Stop here for coordinator freeze before comparison.
