# P00A Stage 2 independent source inventory

This inventory was composed and saved before any Stage 1 report, Lean interface, or native census was opened. Scope: all eight original slots C01-C08; statements and named procedure interfaces, not proof certification or a complete construction-correctness audit. All eight are new source-specific review scope. No earlier approval is assumed.

## Edition, evidence and ordering

Dana Angluin, *Inductive Inference of Formal Languages from Positive Data*, Information and Control 45(2) (1980), printed pp. 117-135, DOI 10.1016/S0019-9958(80)90285-5. Received June 29, 1979; revised January 29, 1980 (printed 134 / PDF 18). The preliminary STOC 1979 version is mentioned on printed 117 but is not supplied or substituted. Only the packaged journal edition is scoped.

The original inventory has no expected PDF SHA256. Bibliographic identity was visually checked on PDF page 1, and all 19 pages are present. This establishes the packaged edition identity with that explicit qualification; it does not establish equality with a missing historical hash.

- Packaged source.pdf: SHA256 `5d9903aa5e0b86a8e4ec1f344539bce328ce69d546561937ee68da338d79721c` (bytes hashed only; annotation payloads never read).
- Reviewed annotation-free review-base-pages.pdf: SHA256 `52853b5d44876fd84f6ceb585d5cef43fa3eae7cdfcac6b6812baa886cb866cf`.
- Complete page-marked-text.txt: SHA256 `67e8243230c5a9cfb36230dfb6e0f53b6523e2ab58e409df0ba61ebd89a7e04e`.
- page-index.json: SHA256 `6c03fc5b9ef7c509ad1d82b2e8ede1419f0735933bf76211ad388c86d019e9e5` (hashed as retrieval metadata; its contents were not needed).
- Source README: SHA256 `ba2575d13ee9961509b69b1584acdafc7db124e0e7742f68e3a748cafef1dccf`.
- SOURCE_MANIFEST.json: SHA256 `b044abb93e52a4158c4cd3e10fc9d4ed4142469e6da4a88e4e62d0d75f514d48`.
- Stage 2 PROMPT.md: SHA256 `c19584fc8895ad9208a686614365c7244ae3dee42df9b28b98c68ddad1fa28dc`.
- stage2/claim-index.json: SHA256 `52bfbf3781906bd2d2df101d6bb9f659182538d8c6eb9479ea259f3b121850f9`; used solely for scope and locators, not as a claim interpretation.

Actual order: PROMPT; failed attempt to open P00A/claim-index.json (nonexistent); restricted filename search within P00A (no excluded contents read); source README and manifest; correct stage2/claim-index.json and PDF skill; entire page-marked text, with overlapping chunk rereads because the initial output was truncated; annotation-free PDF rendering and visual inspection. Thus the source metadata was opened before the corrected index path, an administrative ordering deviation only; no Stage 1/Lean access occurred. Source-phase clock observations: 2026-11-13T23:44:35Z and 2026-11-13T23:46:54Z. CoreGraphics rendered all 19 pages to /tmp/p00a-stage2-pages, and every page was visually inspected, in the order 1,5,7,8; 3,4,6,9; 11,12,13,14; 15,16,17,18; 2,10,19. Poppler was unavailable; Swift invocation failed before PDF access; the first ctypes attempt lacked Pillow and failed before PDF access; the final CoreGraphics/ImageIO renderer succeeded (one generic CoreGraphics PDF diagnostic). No annotations were used.

## Standing source conventions

Printed 119-120 / PDF 3-4: fixed finite alphabet Sigma; words are Sigma-star; languages are arbitrary subsets. The indexed family L1,L2,... has every language nonempty and a **single effective procedure** for membership (i,w) -> 0/1. This is uniform recursion in the family index, not pointwise decidability.

A positive presentation is any infinite word sequence whose range is exactly the target language. Repetition is allowed, order is arbitrary, and the presentation need not be effective. No pause token or negative example is built into a presentation. An inference machine is a deterministic Turing machine with separate request and guess events; it may request several examples without a guess or make several guesses between requests. Its guess sequence may be null, finite, or infinite. Convergence to j means an infinite sequence eventually constantly j, or a nonempty finite sequence with last term j. Inferring a family means one effective machine works for all family indices and all presentations; the limiting correct index may depend on the presentation and need only denote the same language, not the target's original index. There is no distribution, probability, loss function, sample-complexity rate, or running-time bound in these claims.

Printed 120-121 / PDF 4-5: a finite tell-tale T for Li satisfies T subset Li and, for every j, T subset Lj implies Lj is not a proper subset of Li. It need not distinguish Li from all other languages and need not be nonempty. Equivalent relative formulation: T subset Lj and Lj subset Li imply Li subset Lj. Condition 1 requires one effective enumerator given i whose range is some such finite Ti; it need not halt or announce completion. Condition 2 (printed 123 / PDF 7) drops only effective enumeration: for each i some finite tell-tale exists. Condition 1' (printed 129 / PDF 13) instead requires one effective procedure which outputs all of Ti and halts. Finiteness of an enumerable range does not give Condition 1'.

Condition 3 (printed 123 / PDF 7): for each nonempty finite sample S, only finitely many **distinct languages** of the family contain S. Duplicate indices do not count separately; this is extensional finite thickness, not finite compatible indices. Condition 4 (printed 124 / PDF 8): one effective inclusion decision function h(i,j) for Li subset Lj. Conditions 1 and 4 depend on indexing; Conditions 2 and 3 depend only on the set of denoted languages.

Printed 131 / PDF 15: consistency requires every guess on a valid presentation to contain every sample read so far. Responsiveness requires a guess between any two request events. Conservativeness requires that whenever an earlier index guess i and a later different guess j occur, Li fails to contain some sample read before the later event. These are operational properties of the same machine. Printed 132 / PDF 16: i is descriptive of S iff S subset Li and no compatible family language is a proper subset of Li; it is a minimal compatible language, not necessarily a least one. Condition 5 supplies a **partial recursive function** f on finite sets, defined and descriptive on every nonempty finite S which has any descriptive index; outside this domain it need not halt or satisfy a property. Under finite thickness, every nonempty compatible finite sample has a descriptive index.

## Independent scoped claims and procedures

### C01 — Theorem 2

Printed 127-129 / PDF 11-13, Section 6. There exists one indexed family of nonempty uniformly recursive languages satisfying Condition 2 but with **no effective inference machine** identifying it from all positive presentations. Quantifiers: exists family F; (forall i exists finite Ti forall j tell-tale condition) and not exists effective M forall targets forall presentations correct convergence. It does not say there is no arbitrary semantic learner.

The source construction is staged on prime powers, first canceling one machine with live/terminating/terminated sets, then combining all effective machines using a computable pairing function and the ith prime. Definitions include a mutable finite sample, bound b, current latest guess, even/odd exponent markers, and suppression of a guess with the wrong outer paired index. Named construction-interface comparison must distinguish this from merely restating a non-effective diagonal axiom. Complete verification of the simulation and diagonal construction is outside this stage.

### C02 — Theorem 5

Printed 133 / PDF 17, with definitions on printed 131-132 / PDF 15-16. For every indexed family of nonempty uniformly recursive languages satisfying Conditions 3 and 5, there exists **one effective inference machine** that identifies it and is simultaneously consistent, responsive and conservative. Condition 3 counts languages; Condition 5 is effective and partial, defined on all nonempty finitely sampled descriptive domains.

The named staged procedure starts with no guess; after each new sample form Sn. If the current index remains consistent with Sn, keep it; otherwise compute f(Sn), output it, and continue. Divergence of f prevents the next stage; hypotheses guarantee termination on valid family presentations. The same f and the same resulting M witness all four conclusions. No uniform runtime bound is claimed. Printed 134 / PDF 18 notes the hypotheses are sufficient, not necessary (Example 4).

### C03 — Theorem 4

Printed 131-132 / PDF 15-16, Section 7. There exists an indexed family of nonempty uniformly recursive languages which is effectively inferrable, but no effective inference machine both identifies it and is conservative on it. The source does not require the excluded conservative machine also to be consistent or responsive. The same family is noted to satisfy Condition 3 on printed 132.

Its named diagonal family contains an infinite prime-power language and finite initial-sample languages per enumerated machine. Finite members are determined by bounded simulation up to the first guess of a distinguished index and augmented with the least prime. The family is combined by pairing. Its tell-tale enumerator emits complete finite members; for the infinite member it first emits two prime powers, then simulates the indexed machine and, if the distinguished guess occurs, emits a not-yet-read power. Effective identification is part of the theorem; a conditional bundle postulating the desired family is not by itself the source existence assertion.

### C04 — Theorem 1

Printed 121-122 / PDF 5-6 (Section 3; page 123 begins corollaries). For every indexed family of nonempty uniformly recursive languages: there exists an effective inference machine identifying it iff Condition 1 holds. Left quantifiers: exists effective M forall i forall positive presentation sigma of Li exists j with Lj=Li and M[sigma] converging to j. Right quantifiers: exists one effective enumerator E forall i its enumerated range Ti is finite, lies in Li, and is a tell-tale against every family member. The witness j may vary with sigma; the single enumerator works uniformly in i. Neither a bare semantic equivalence nor a logical equivalence between already supplied realization assumptions states the full effective result.

Forward learner interface (printed 121): at stage n read one sample, consider least g<=n with Sn subset Lg and Tg enumerated in the first n computation steps subset Sn; output g if found, otherwise issue no guess. Thus stage bounds, enumeration prefixes, least-index choice, and optional guesses matter. Reverse enumeration interface (printed 122): start with a positive sample from Li; dovetail finite Li-extensions looking for a change in the last guess, enlarge the tell-tale only when such an extension is found, and append the next canonical Li sample. Full proof correctness is excluded, but the effective nature and specified interfaces remain in scope.

### C05 — Corollary 2

Printed 123-124 / PDF 7-8, Section 4; consistent/responsive strengthening in printed 131 / PDF 15 Remark. Every indexed family of nonempty uniformly recursive languages with Condition 3 is effectively inferrable. No effective bound/enumeration of all compatible indices or languages is assumed. Infinite duplicate index sets are permitted. The source builds a uniformly enumerable finite tell-tale by adding progressively larger finite initial segments of Li whenever a compatible competing finite approximation is a proper subset of the target approximation. It starts from the least member of Li. This is a procedure enumeration, without a halting/completion certificate; the proof uses only extensional finite thickness for finiteness. The later Remark allows the identifying machine to be chosen both consistent and responsive.

### C06 — Theorem 3

Printed 129-130 / PDF 13-14, Section 6. There exists an indexed family of nonempty uniformly recursive languages which is effectively inferrable but fails Condition 1'. This separates enumerable finite tell-tales from uniformly halting complete tell-tale output, not from mere set-theoretic finite tell-tales.

Named family: for the ith machine's diagonal halting time f(i), with infinity for nonhalting, R(2i-1) is all positive powers of the ith prime, and R(2i) is the initial segment through exponent f(i). The uniform membership test uses bounded simulation for n-1 steps. The inference procedure uses the prime component of the sample and guesses the even member while consistent with it, otherwise the odd member. The reduction computes the complete odd member tell-tale and tests inclusion in the even member, which would decide diagonal nonhalting. Algorithm-definition correspondence does not certify this reduction proof.

### C07 — Corollary 1

Printed 123 / PDF 7, Section 4; standing conventions printed 119-120 / PDF 3-4. Every effectively inferrable indexed family of recursive languages satisfies Condition 2. Although its sentence omits the word nonempty, Section 4 explicitly fixes a family of nonempty recursive languages immediately above the conditions. Its conclusion is deliberately non-effective: for each index there exists a finite tell-tale. The proof cites Theorem 1 plus forgetting the enumerator. It does not claim a uniformly halting finite output procedure or exact recovery of the target's given index.

### C08 — Corollary 3

Printed 124-125 / PDF 8-9, Section 4; definitions Condition 2 printed 123 and Condition 4 printed 124; consistent/responsive strengthening printed 131 / PDF 15. A family of nonempty uniformly recursive languages satisfying Conditions 2 and 4 is effectively inferrable. Decidable inclusion is a single effective procedure in the pair of indices. A family of arbitrary Decidable propositions is not sufficient evidence of this uniform algorithm.

Named enumerator starts with an empty target sample; searches for compatible j with Lj a proper subset of Li (using the inclusion decider); if found, chooses the least finite approximation witnessing the proper difference, adds the corresponding target initial segment and repeats. It is an enumerable finite output range, not necessarily halting. The source then applies Theorem 1. The Remark permits one identifying machine also consistent and responsive.

## Supporting context and suspected source questions

All examples and remarks were read as context. Example 1 (printed 125) pattern languages and Example 3 (printed 126) concatenation/Kleene-plus languages illustrate finite thickness; Example 2 violates Condition 2; Example 4 has effective tell-tales and decidable inclusion but not finite thickness. These examples are not additional original claim slots. No external Angluin 1979 text was supplied or used.

The heading defining Condition 4 is visibly printed **COROLLARY 4**, although its content is a definition, followed immediately by Corollary 3. Retain the printed label and refer to its explicit Condition 4 content; do not silently repair it or infer an extra corollary claim.

Potential boundary questions for Stage 3, not adjudicated source errors: the R(2i) display on printed 130 omits an explicit positive-exponent lower bound, supplied by surrounding positive-power prose; machine step-count conventions must preserve nonemptiness if diagonal halting is immediate. In the Theorem 4 tell-tale procedure on printed 132, the least unread prime power may be the baseline prime if the distinguished guess precedes any sample request; the proof later asserts the chosen power is outside every finite member, all of which were augmented by that baseline prime. Ask whether a conventional normalization or a larger unread exponent is intended. This is a source construction boundary question, not a conclusion that the theorem is false or Lean is wrong.

No Lean-based interpretation, comparison, developer explanation, owner material, old audit report, registry/PaperMap assessment, human ledger, or other paper package was consulted before saving this file.

Inventory saved at UTC: 2026-11-13T23:48:39.201971+00:00
