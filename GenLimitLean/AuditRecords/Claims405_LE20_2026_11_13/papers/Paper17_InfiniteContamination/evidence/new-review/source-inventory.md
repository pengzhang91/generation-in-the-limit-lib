# P17 C03 independent source inventory

Scope: only slot C03, `claim:mvyz25:claim-6-17` (Claim 6.17). Other original claims are outside this comparison. This inventory records source assertions and their standing context before any Stage1 output or Lean interface was opened in this Stage2 run. It makes no correspondence judgment.

Inventory frozen at UTC: 2026-11-14T00:11:38.640928+00:00

## Pinned source and access boundary

Paper: Anay Mehrotra, Grigoris Velegkas, Xifan Yu, Felix Zhou, *Language Generation with Infinite Contamination*, arXiv:2511.07417v1, 10 November 2025. The first-page title, authors, version banner, and date were visually checked. All 71 PDF pages of the pinned base-page extraction were read, including appendices; material outside C03 was read for context only and was not audited as another claim.

Original PDF SHA256: `e1ef3e6d24cc382782446f24cb4377b885034812d3d678cf8d9789a703f5e0a9`.

Annotation-free review derivative SHA256: `d564c55fc8337eb84b49c686ad105db7ce58cd39a8a2aba72c03981011917efb`.

Base-page text SHA256: `bf022a8a8e8bb774cc48ebc95b4a13c12e8ff1a3324108da264c10123a8d0472`.

The manifest identifies the original file as annotated. Only base-page source content was used; annotation payloads were not read. The derivative is not claimed byte-identical to the original or to the publisher comparison PDF. Printed page p corresponds to one-based PDF page p+3 after the front matter. Relevant formulas and printed page numbers were visually checked on PDF pages 18, 24, 46, 47, 48 (printed pp.15, 21, 43, 44, 45). The opaque JPEG renders of pages 47-48 resolved the initially unusable transparent PNG rendering.

## Source unit C03-S1: eventual canonical-rank cutoff

Location: Claim 6.17, Section 6.2.1, printed p.45 / PDF page 48. The claim is inside the proof of Theorem 6.15, following Algorithm 8 on printed p.44 / PDF page 47.

Fix a countable collection of infinite languages, its target K, a particular input enumeration x_1,x_2,... (possibly contaminated), and a set-based generator meeting the assumptions below. Let ell_1,ell_2,... list K in increasing canonical order. Run the element-based construction in Algorithm 8 using the same input, the same set-generator outputs A_n, its finite subcollections L_n, and known density parameter rho. In the nontrivial branch the proof explicitly assumes rho>0 (rho belongs to [0,1] in the surrounding setup).

Then there is a finite natural n_star, dependent on this fixed instance, such that for every n>=n_star, the actual output w_n lies among the first

`B(n) = ceil(2*n*(1 + 2^(-k(n)))/rho)`

elements of K: `w_n in {ell_1,...,ell_B(n)}`. In one-based rank language this says both w_n belongs to K and its rank is <=B(n). The existential threshold precedes the universal time quantifier. No uniform threshold over target languages, generators, enumerations, or rho is asserted. The claim concerns this particular Algorithm 8 output and its selected k(n), not an arbitrary unnamed sequence.

## Standing source assumptions needed for C03

- Section 3.1, printed p.15 / PDF18: languages are infinite subsets of a countable universe; for density the universe is identified with positive natural numbers with their increasing canonical order. A language's canonical enumeration is the restriction of that order. An enumeration lists each included element exactly once; the normal model excludes input repetitions. Appendix A, printed p.63 / PDF66, separately discusses adapting algorithms to repetition.
- Definitions 3-5, printed p.16 / PDF19: an element generator sees the observed history and must avoid all input elements seen so far and all of its previous outputs. A set generator outputs a set disjoint from the observed input. Eventual generation requires eventual membership in the actual target. The input may be contaminated in Theorem 6.15, with no additional numerical noise-rate/omission-rate/bounded-displacement restriction imposed on this claim beyond the assumptions on the supplied set generator.
- Theorem 6.15 and Algorithm 8 setup, printed pp.43-44 / PDF46-47: for every round n the set generator computes an infinite A_n and a finite subcollection L_n of the given collection, with A_n contained in the intersection of L_n minus the first n inputs. The target K belongs to L_n eventually. The set generator generates in the limit, and `mu_low(A_n,K)>=rho` eventually. The same A_n/L_n and eventual assertions apply to the same fixed enumeration. A common threshold N_3 can be chosen for target inclusion and density.
- Definition 1, printed p.15 / PDF18: `mu_low(A,L)` is the liminf, over m, of `|A intersect first_m(L)|/m`. This is deterministic relative density, with the denominator the rank-prefix size m. It is not density in the input order or a probability/loss assumption.
- Section 3.7, printed p.21 / PDF24: the generator may query the known collection, including membership, density and a density-rate oracle, but may not query the unknown target as target or the future input. Algorithm 8 explicitly knows rho and obtains a density-approximation threshold for each of finitely many candidate languages. This is an oracle-level construction; no runtime complexity bound or membership-only implementation is asserted here.

## Algorithm 8 data and dependencies

For each n>=1:

1. Form S_n={x_1,...,x_n} and W_(n-1)={w_1,...,w_(n-1)}. Compute (A_n,L_n) from the set generator on the observed input.
2. Choose the smallest positive integer m_n for which, for every L in L_n and every m>=m_n, `|A_n intersect first_m(L)|/m >= mu_low(A_n,L)/(1+2^(-n))`. The condition is simultaneous over the finite L_n. For n>1 replace m_n by max(m_n,m_(n-1)+1), so that the maintained sequence is strictly increasing.
3. If `m_1/(1+2^(-1)) <= 2*n/rho`, take k(n) to be the maximum k in {1,...,n} satisfying `m_k/(1+2^(-k)) <= 2*n/rho`; otherwise set k(n)=1. This fallback affects early times; the source argument uses a sufficiently late threshold.
4. Output the least element, in the common canonical universe order, of `A_(k(n)) minus (S_n union W_(n-1))`. Infinite A_(k(n)) makes a fresh output available. The same recursively produced output sequence is used in W_(n-1).

The source explanation of C03 uses the eventual K-in-L and rho-density hypotheses at the selected historical stage k(n), the rate inequality for m>=m_(k(n)), and the k(n) inequality to make B(n) a valid such m. It obtains at least 2*n candidates in the first B(n) elements of K. At most 2*n-1 elements are excluded by the n inputs and n-1 prior outputs, so the least remaining A_(k(n)) element is within that K-prefix. This explanation is read as source interpretive context, not certified as a formal proof audit.

## Source boundaries and questions retained for comparison

- The rho=0 case is explicitly separated as trivial for Theorem 6.15 before the proof of C03. The displayed rank bound divides by rho, so C03's nontrivial algorithmic cutoff is inventoried for rho>0; no literal zero-denominator extension is inferred.
- The printed Claim 6.17 is a prefix-membership assertion. A bare rank upper bound will require checking that the rank representation cannot make outsiders satisfy it trivially.
- The source uses 1-based rounds and target ranks. Any 0-based Lean representation will need an explicit offset check for both n and rank.
- The claim does not itself promise element-density rho/2, uniform sample complexity, arbitrary computational effectiveness, or all of Theorem 6.15. Those are outside C03's single-slot comparison.
- No suspected substantive source error affecting the C03 statement was identified in this source-only inventory. The proof writes mu(A_n,K) once where the surrounding definition and inequalities use mu_low; this is interpreted from immediate source context and is not silently changed into another density notion.

## Isolation declaration

Before saving this inventory, this Stage2 reviewer accessed only the assigned Stage2 prompt and one-slot index; the P17 source manifest, original/derivative PDF bytes for hashing, the full base-page extraction and its page-index bytes for hashing; the PDF skill; and temporary render files generated from the annotation-free derivative. No Stage1 result, Lean code, theorem name, theorem type, proof value, owner file, registry, old report, stage3-context, or human ledger was opened in this Stage2 run. Stage1's own prior-exposure provenance will be inspected only after this inventory is frozen.
