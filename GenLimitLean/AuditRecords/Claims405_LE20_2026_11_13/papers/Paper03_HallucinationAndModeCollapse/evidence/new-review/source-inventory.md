# Independent source inventory: P03 C04 / C14 / C16

Inventory recorded: 2026-11-14T00:03:15.459444+00:00. This is the source-only inventory saved before opening any Stage 1 output, Lean interface, native census, developer explanation, owner/registry file, stage3-context or old audit. Only the three original claim slots named below are assessed. Other source material was read solely for their context.

## Identity and reading record

Pinned paper: Alkis Kalavasis, Anay Mehrotra and Grigoris Velegkas, *On the Limits of Language Generation: Trade-Offs Between Hallucination and Mode Collapse*, arXiv:2411.09642v3, version date 2025-10-14. The full 98-page supplied page-marked extraction was read, including introduction, model, definitions, remarks, proof interpretation, references and appendices. One-based PDF pages 4--98 carry printed pages 1--95 (offset +3). The scoped appendix pages are printed 91--93 / PDF 94--96.

Original PDF SHA-256: `097bda3ceeab7ddb244595b2817c8766f540b508abfe24a2ca8eaa0feecf3439` (recomputed, matching claim index and manifest). Annotation-free derivative SHA-256: `d353196a94c10cc53d15aaf910a4b81d88009aa20fcfce159ecd7ddacae15b91`. Full extraction SHA-256: `00a81d3e4d941da583fdc7aeba767ebe1221b22b1636c6ebada235315448beef`. The derivative is a documented source preparation aid, not a different publisher edition. Annotation payloads were excluded. PDF 94--96 were rendered with pypdf plus macOS sips (white background added for readability) and visually inspected; the visual inspection confirms the issues below are printed text, not merely extraction defects.

## Source-global assumptions relevant to these slots

The domain X is countably infinite, identified when useful with natural numbers or finite strings. The family is an indexed countable list L1,L2,..., potentially with duplicate languages. Section 2, printed 20--21 / PDF 23--24, grants membership queries uniformly in a language index and string. A positive enumeration of K lists only elements of K and eventually every element of K, with repetitions allowed. Definition 10, printed 21 / PDF 24, defines identification as eventual stabilization to a fixed correct index, not merely eventual extensional correctness with changing duplicate indices. Definition 11 / Theorem 2.2, printed 22--23 / PDF 25--26, explain finite tell-tales and the characterization of identifiable families. A tell-tale T_i is a finite subset of Li such that no strict sublanguage in the family contains T_i. The source definition additionally refers to an oracle enumerating these sets.

A randomized generator is a Turing-machine sampler with a support of possible positive-probability outputs; a generating algorithm maps finite samples to such machines. Definition 12, printed 23 / PDF 26, requires eventual unseen outputs in K minus the finite sample; its randomized form requires nonempty support contained in that unseen set. Generation is principally meaningful for infinite target languages (printed 2 / PDF 5), although Definition 12 separately mentions the exhausted finite-target exception. Exact breadth together with consistency is eventual equality of support with K minus the seen sample; Remark 2, printed 29 / PDF 32, permits an interchangeable seen-sample variant. No statistical distributions, losses or convergence rates are claimed in Appendix B: these are adversarial-enumeration limit statements.

## C04 — claim:kmv25:explicit-mop-undecidability

Locator: Appendix A, printed 91 / PDF 94, Proposition A.1 and the entire preceding machine description; MOP Definitions 5--6 at printed 5 / PDF 8 and printed 28 / PDF 31.

Source units:

1. A static generating algorithm G1=G2=... uses the same input-free randomized machine at every sample size; the source does not condition this machine on the observed training set.
2. Its random tape has symbols {0,1,2}; it reads until the first 2, obtaining a finite binary prefix r. A branch marker b is set to 1 when r parses as an encoding <M>w of a Turing machine and input (possibly empty).
3. The printed step 3 tests `r = 1`, executes M on w and, when it halts, returns the string <M>w1. Otherwise it returns 0. Divergence is possible if a valid encoded machine does not halt; no total or almost-sure termination guarantee is stated or established here.
4. Proposition A.1 says support membership for this explicit machine is undecidable. The interpretive proof asserts that M halts on w iff the tagged output <M>w1 belongs to the support, giving the intended halting reduction.

Quantifiers and witness dependency: one explicit static machine is fixed; a purported decider must correctly answer membership for all strings for that machine. The reduction takes arbitrary M,w to the encoded tagged string. There is no uniform sample-size issue because the machine is static, no learning-rate assertion and no language-family hypothesis.

Source questions, preserved without repair: (i) the visual page really tests r=1 after defining b, rather than b=1; literal execution is inconsistent with the reduction. (ii) The probability law on ternary tapes and the parsing/encoding conventions are unstated; the reduction needs positive probability for each finite encoded prefix and injective distinguishable tagged encodings. (iii) The machine may have positive probability of divergence, so its output law is potentially a subprobability law; this is in tension with earlier language describing generators as distributions/samplers. These need adjudication, not a silent correction or an automatic Lean-bug label.

## C16 — claim:kmv25:subset-oracle-identification-without-telltales

Locator: Appendix B.1, printed 91--93 / PDF 94--96, Theorem B.1, algorithm box, all explanation and final proof continuation. Supporting source: Definition 19 / Section 5.2.3 at printed 55--56 / PDF 58--59; lowest-index post-processing Lemma 5.4 at printed 41--42 / PDF 44--45.

Source units:

1. For any fixed identifiable indexed countable family L and a correct subset oracle S(i,j) deciding Li subset Lj, there exists one algorithm A which, for every target K in L and every positive enumeration of K, eventually identifies K. Membership access from Section 2 remains available. The algorithm takes neither K's tell-tale nor any other tell-tale as input; tell-tales may be used nonconstructively in its correctness argument.
2. On step t, restrict to indices 1..t consistent with the seen sample. A candidate i is critical if its language is a subset of every earlier consistent candidate. Select the largest critical index, with a fallback if the version space is empty. This is an oracle algorithm, with finitely many language-membership/subset tests per round.
3. The raw last-critical output eventually denotes K; duplicate indices for K may continue changing infinitely often. The source explicitly adds Lemma 5.4 post-processing to stabilize to a fixed correct index and thereby meet Definition 10. The post-processing compares projections on the first t domain elements and takes the least matching index bounded by the raw output.
4. The proof uses a finite time after which K is critical, then the existence of a finite tell-tale of K to eliminate all strict sublanguage critical candidates once that tell-tale is observed. The algorithm need not know the tell-tale or the stabilization time.

Boundary/strength notes: natural-number indexing in a formal representation may harmlessly shift 1-based to 0-based indices. A bare arbitrary semantic function with eventual correctness is weaker evidence than an implementable oracle procedure. A claim of plain computability would require decidable/effective oracles; arbitrary S cannot be inferred computable. No rate is claimed. The fallback in the printed identification box outputs a random element of X rather than an index; this is a source typing issue confined to finitely many pre-target-index rounds and should be recorded as a question, not silently repaired.

## C14 — claim:kmv25:subset-oracle-best-of-both-worlds-generation

Locator: Appendix B.2, printed 93 / PDF 96, Corollary B.2, introductory paragraph and footnote 20; supporting Theorem B.1 and source-global generation definitions above.

Source units:

1. For every fixed indexed countable family L and correct subset oracle S, there exists one generating algorithm G such that for all K in L and all positive enumerations, G eventually has nonempty support contained in K minus the seen finite sample (consistent generation in the limit).
2. The same G, whenever that fixed family L is identifiable, eventually generates consistently with breadth: its support equals K minus the seen sample (or the corresponding seen-sample variant of Remark 2). This is a same-witness best-of-both-worlds guarantee, not two unrelated existential witnesses selected according to whether L is identifiable.
3. G receives no tell-tale oracle or target tell-tale. It uses the last-critical-language selection from B.1; output is an unseen sample from that selected language. Unlike the identification algorithm it does not need lowest-index post-processing (footnote 20).

Quantifiers: for each L,S choose G, before quantifying over K and its enumeration; the breadth condition is an implication on that same G under identifiability of L. All-candidate-language infinitude is the natural standing condition ensuring a nonempty unseen sample at every step; the source's finite-target exception must not be lost if a claim is read as covering finite families of finite languages. There are no rates or training distributions here.

Source interpretation question: Section 5.2.3 specifies output of the *first* unseen string, a deterministic singleton-support output, and B.2 says this is precisely that algorithm while asserting breadth on infinite K. A deterministic singleton at each stage cannot have exact support K minus a finite seen set when K is infinite. The phrase 'an unseen sample from the language' must mean a full-support randomized sampler or a richer output notion to obtain the stated breadth. Proposition 6.5 (printed 61 / PDF 64) does describe a full-support sampler via rejection sampling, but B.2 does not explicitly replace the first-unseen output by that sampler. Keep algorithm-definition correspondence distinct from the corollary's intended support-level statement and defer the ambiguity to adjudication.

## Scope and freeze discipline

Only C04, C14 and C16 have source claim dossiers in this inventory. Supporting definitions and source proof interpretations above do not create additional audited claim slots. No source issue has been classified as a Lean error. This inventory is frozen independently; later Lean comparison must not rewrite it in light of Stage 1. A separate freeze record stores the inventory byte hash and save time.
