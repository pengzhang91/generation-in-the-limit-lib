# Human audit records

This is the authoritative ledger for completed human paper-to-Lean audits.
It also indexes the ChatGPT Pro statement-faithfulness checks that still await
human review. Both are separate from Lean's kernel checks in
[AUDIT.md](../../AUDIT.md).

## Definition scope of human theorem audits

On **12 November 2026**, Peng Zhang clarified that **Level 1 human review
includes the definitions of the terms used in every already human-audited
theorem**, not only P09 Theorems 3.3 and 3.7. This dated scope clarification
applies throughout the completed-human-audit records, including the Level 1
statement component of higher-level reviews. It is attributed to Peng Zhang;
the original reviewers, dates, theorem scopes, source editions, and reviewed
checkpoints remain unchanged.

Included are the mathematical definitions needed to interpret the hypotheses
and conclusions, recursively where needed: objects and representations,
presentation and access models, validity/freshness, generation and
identification notions, noise and density conventions, and the relevant
combinatorial predicates. A definition's meaning is within Level 1; a
construction's correctness, supporting theorem proof, or proof-step
correspondence is not thereby reviewed.

The following term families illustrate the scope of the recorded reviews;
the individual records and manifests remain authoritative about exact
statements, versions, qualifications, and applicability:

| Human-audited development | Statement-relevant definitions included |
|---|---|
| P00 | Texts, naming, and arbitrary-text semantic identification in the historical reviewed scope; current applicability remains `needs-review`. |
| P00A | Semantic identification and finite tell-tales (`ConditionTwo`); no automatic review of the effective source characterization. |
| P01 | Indexed language families, infinite-language conventions, finite histories and oracle access, generation/freshness, and the robust-prompt model in the named audited results. |
| P02 | Limit, uniform, and nonuniform generation; closure witnesses/dimension and class-cover predicates used in the six named reviewed results. |
| P03 | Identification/generation rates, distributions and support, breadth/error events, tell-tales, and the computable-support interface used in Theorems 3.1--3.3. |
| P04 | Nonuniform and exhaustive generation, adaptive membership-query dialogues, feedback strategies, and GF dimension within the named audited results. |
| P05 | Exact breadth, approximate breadth, raw stability, and tell-tales used in the three audited semantic statements; infinite coverage remains excluded. |
| P06 | Occurrence-noise budgets, target-covering noisy presentations, qualitative noisy-closure finiteness, generation predicates, and covers used in the four reviewed Section 3 statements. |
| P07 | Exact presentations, the fixed semantic selector, eventual index validity, and infinitely-often target-language equality in Theorem 2.1. |
| P08 | Detection, finite candidate-set query trees, stable-index identification, and complete exactly labeled domain enumerations in Theorems 2.1 and 2.3. |
| P09 | Groups/partitions, discrete randomized generators, distinct-sample group proportions, supremum distance, consistency, fixed-scale uniform/nonuniform generation, bounded group-closure witnesses, and nondecreasing covers in Theorems 3.3 and 3.7. |
| P10 | The reviewed presentation and autonomous-output conventions, generation notions, infinitude/uncountability, and EUC in overview Theorems 3.1--3.3. |
| P21 | Metric neighborhoods/covers, scales and UUS, metric generation, scale-closure witnesses, doubling/Lipschitz conditions, and concrete example objects in the reviewed v2 Overview. |
| P39 | The indexed infinite-family model, exact/partial presentations, generator-first output, density, recursive criticality and finite-intersection closure used in the two reviewed v2 density statements; historical scopes retain their separate statuses. |

This clarification is not a new human audit of every paper or every numbered
definition. LLM-only audits do not acquire human status. A shared Lean
definition reviewed in one paper does not automatically certify its
correspondence to another source edition or another paper's definition.
Definitions used only in unreviewed theorems or proof internals remain outside
scope. Existing exclusions for semantic-only results, one direction/clause,
computability, and corrected or disputed source statements still apply.

The fingerprint manifests already guard the relevant definition meanings.
Their new scope-clarification metadata does not alter anchors, reviewed
checkpoints, or status: historical `needs-review` scopes are not renewed.

Numbered definition cards in the registry receive scoped human references
only where this meaning can be mapped to the reviewed theorem scope and
source version. A grouped card may be only partly human-reviewed; for
example, P09's fixed-alpha and nonuniform notions are included, but its
all-scale uniform and limit-generation notions are not. Formalization
coverage and source assessments remain separate from human-audit coverage.

## Completed human audits

Each record in this table was performed by the named human auditor and is
complete only at its stated level.

| Development | Audit level | Auditor | Recorded | Release |
|---|---|---|---|---|
| #01 Language Generation — semantic path | Level 3: theorem, construction, and proof correspondence | Peng Zhang | 17 July 2026; narrow re-audit 20 July 2026 | `v0.3.0`; current revision `unreleased` |
| #01 Language Generation — round-dependent Section 4 semantic path | Level 2: theorem specification and semantic construction; proof correspondence excluded | Peng Zhang | 18 October 2026 | checkpoint `c8af96a` |
| #01 Language Generation — Theorems 2.1 and 2.2 | Level 1: theorem specifications and defining interfaces | Shuangping Li | 25 September 2026 | checkpoint `d5227a2` |
| #01 Language Generation — Theorem 7.1 | Level 1: theorem statement and statement-relevant definitions | Peng Zhang | reported 8 November 2026; completion date not separately specified | checkpoint `6062058` |
| #02 Learning Theory — Proposition 2.1 and ordinary Section 2--3 main theorems | Named-result human correspondence audit; no aggregate P02 level assigned | Peng Zhang | 12 August 2026 | checkpoint `d40205b` |
| #02 Learning Theory — finite-history migration for the six named Section 2--3 results | Level 1: statement and definition applicability; construction and proof correspondence excluded | Peng Zhang | 18 October 2026 | working tree based on `c8af96a`; file hashes below |
| #02 Learning Theory — Theorem 3.3 | Level 1: theorem specification | Shuangping Li | 25 September 2026 | checkpoint `14b4deb` |
| #02 Learning Theory — Theorem 3.5 | Level 1: theorem specification | Shuangping Li | 25 September 2026 | checkpoint `04dffd2` |
| #02 Learning Theory — Theorem 3.10 | Level 1: theorem specification | Shuangping Li | 25 September 2026 | checkpoint `6462d25` |
| #03 Limits of Language Generation — Theorems 3.1--3.3 | Level 1: theorem statements and statement-relevant definitions | Peng Zhang | reported 2 November 2026; completion date not separately specified | checkpoint `82c0869` |
| #04 Exploring Facets — overview Theorems 1--4 | Named-result human correspondence audit; no aggregate P04 level assigned | Peng Zhang | 14 August 2026 | `unreleased` working tree based on `87423ff` |
| #04 Exploring Facets — overview Theorems 1, 3, and 4 | Level 1: statement and definition applicability renewed after the finite-history extraction | Peng Zhang | 19 October 2026 | checkpoint `fb37e6b` |
| #04 Exploring Facets — detailed Theorem 7 and overview Theorem 2 | Level 1: statement and adaptive membership-query definition applicability; proof correspondence excluded | Peng Zhang | 21 October 2026 | checkpoint `fb37e6b` |
| #04 Exploring Facets — overview Theorem 5 | Level 1: theorem statement and feedback/GF-dimension definitions; construction and proof correspondence excluded | Peng Zhang | 21 October 2026 | checkpoint `fb37e6b` |
| #05 Hallucinations, Breadth, and Stability — three semantic statements | Level 1: Theorem 3.3, Theorem 3.8 sufficiency, and Theorem 3.15 approximate clause; statements and relevant definitions | Peng Zhang | reported 12 November 2026; completion date not separately specified | non-P38 working tree based on `6062058`; file hashes in the scoped manifest |
| #06 Noisy Examples — Section 3 theorem specifications | Level 1: Theorems 3.1, 3.3, 3.9, and 3.10 | Peng Zhang | 13 August 2026 | checkpoint `a66d3d0` |
| #06 Noisy Examples — Section 3 theorem specifications | Level 1: Theorems 3.1, 3.3, 3.9, and 3.10 | Shuangping Li | 26 September 2026 | checkpoint `b03d957` |
| #07 Density Measures — Theorem 2.1 | Level 1: theorem statement and relevant definitions; public and canonical presentations | Peng Zhang | reported 12 November 2026; completion date not separately specified | current non-P38 working tree based on `6062058`; file hashes in the scoped manifest |
| #08 Hallucination Detection — Theorems 2.1 and 2.3 | Level 1: theorem statements and relevant definitions; public and canonical presentations | Peng Zhang | reported 12 November 2026; completion date not separately specified | current non-P38 working tree based on `6062058`; file hashes in the scoped manifest |
| #09 Representative Language Generation — Theorems 3.3 and 3.7 | Level 1: theorem statements and relevant definitions | Peng Zhang | reported 12 November 2026; completion date not separately specified | checkpoint `132a458` on `work/non-p38` |
| Paper10 Union-Closedness — Section 3 overview theorem specifications | Level 1: Theorems 3.1--3.3; Theorems 4.1, 4.3, and 4.4 are noted as their detailed presentations | Peng Zhang | 13 August 2026 | `unreleased` |
| Paper10 Union-Closedness — overview Theorems 3.1--3.3 | Level 1: theorem specifications | Shuangping Li | 25 September 2026 | checkpoint `d5227a2` |
| #12 Noise, Loss, and Feedback — all eight Overview theorems | Level 1: Theorems 1.1--1.8 and all statement-relevant definitions | Peng Zhang | reported 12 November 2026; completion date not separately specified | non-P38 working tree based on `132a458`; scoped source hashes |
| #13 Pareto-optimal Non-uniform Generation — Overview Theorems 1, 4, 5, 6, and 8 | Level 1: five statements and all statement-relevant definitions; Theorem 9 endgame excluded | Peng Zhang | reported 13 November 2026; completion date not separately specified | non-P38 checkpoint `9efdb94` |
| #14 List Language Identification — Overview Theorems 1 and 2 | Level 1: both statements and all statement-relevant definitions | Peng Zhang | reported 13 November 2026; completion date not separately specified | non-P38 checkpoint `9efdb94` |
| #15 Partial Enumeration — all Overview Theorems 1.5, 1.7, 1.8, and 1.9 | Level 1: four statements and all statement-relevant definitions | Peng Zhang | reported 13 November 2026; completion date not separately specified | non-P38 checkpoint `d294766` |
| #17 Infinite Contamination — all nine Overview theorems | Level 1: Theorems 5.1, 5.4, 6.1, 6.4, 6.5, 6.11, 6.14, 6.18, and 7.8 and all statement-relevant definitions | Peng Zhang | reported 13 November 2026; completion date not separately specified | non-P38 working tree based on `d294766`; scoped source hashes |
| #19 Effect of Noise — all four Overview theorems | Level 1: Theorems 2.16--2.19 and all statement-relevant definitions | Peng Zhang | reported 13 November 2026; completion date not separately specified | non-P38 working tree based on `d294766`; scoped source hashes |
| #21 On Generation in Metric Spaces — arXiv v2 Overview | Level 1: all 20 Overview theorem statements and statement-relevant definitions | Peng Zhang | reported 1 November 2026; completion date not separately specified | checkpoint `7bdc137` |
| #22 Language Generation with Replay — Theorems 4.1, 5.1, 6.1, 6.6, and 7.3 | Level 1: theorem statements and statement-relevant definitions; Theorem 7.1 excluded | Shuangping Li | 12 November 2026 | checkpoint `6062058` |
| #23 Banach Density, Topology, and Geometry — arXiv v2 Overview Claims 3.3, 3.5, 3.6, 4.4, 4.11 (repaired), 4.18, 4.20, and 7.1 | Level 1: the eight Overview claim statements and statement-relevant definitions; Theorems 4.1, 4.5, 5.1, 5.5, 5.8, and 5.9 are not formalized | Shuangping Li | 13 November 2026 | checkpoint `6062058` |
| #27 Language Generation with Feedback: Queries and Mistakes — Theorems 3.1--3.4, Corollaries 3.6--3.8, and partial Theorems 3.9--3.10 | Level 1: twelve Overview statements and statement-relevant definitions; `theorem_3_9_of_selfLocking`, Appendix Theorems A.10--A.11, and the element-to-set direction of Theorem 3.9 excluded | Shuangping Li | 13 November 2026 | checkpoint `a19851f` |
| #28 Contrastive Identification and Generation in the Limit — arXiv v1 Overview | Level 1: all 19 Overview statements and statement-relevant definitions | Shuangping Li | 13 November 2026 | checkpoint `c828be2` |
| #29 Mistake-Bounded Language Generation — Theorems 4.1, 5.1, and 6.1, Lemmas 6.2--6.3 | Level 1: seven Overview statements and statement-relevant definitions; `theorem_6_4_proof_diagnostic` excluded | Shuangping Li | 13 November 2026 | checkpoint `c828be2` |
| #30 Time-Sensitive Language Generation — Theorem 4 / Appendix Theorem 12 | Level 1: the four totalized-GCG Overview statements and statement-relevant definitions; the other six Overview declarations excluded | Shuangping Li | 13 November 2026 | checkpoint `c828be2` |
| #31 On Language Generation in the Limit with Bounded Memory — arXiv v1 Overview | Level 1: all 13 Overview statements and statement-relevant definitions; Theorems 4.1 and 4.10 in their order-robust form | Shuangping Li | 13 November 2026 | checkpoint `c828be2` |
| #32 Generating in the Limit with Infinitely Many Hallucinations — arXiv v1 Overview | Level 1: ten Overview statements and statement-relevant definitions; the Theorem 3.5 endgame, certificate wrappers, and Lemma D.1 diagnostic excluded | Shuangping Li | 13 November 2026 | checkpoint `c828be2` |
| #39 Dense Generation — arXiv v2 Theorems 3.15 and B.3 | Level 1: the two Overview density statements and statement-relevant definitions; Theorem 3.15 achievability only | Peng Zhang | reported 7 November 2026; completion date not separately specified | checkpoint `3f0aa55` |
| #39 Dense Generation — exact presentation (earlier supplied manuscript) | Black-box input/output specification | Peng Zhang | 16 July 2026 | `v0.3.0` |
| #39 Dense Generation — patient-scope machine (earlier supplied manuscript) | State-machine construction and manuscript correspondence | Peng Zhang | 19 July 2026 | `unreleased` |
| #39 Dense Generation — criticality and focus (earlier supplied manuscript) | Definition-level manuscript correspondence | Peng Zhang | 19 July 2026 | `unreleased` |
| #39 Dense Generation — exact-presentation main result (earlier supplied manuscript) | End-to-end algorithm-to-main-theorem correspondence | Peng Zhang | 19 July 2026 | checkpoint `374e24f` |
| #39 Dense Generation — partial enumeration, manuscript Lemma 3.16 and Theorem 3.17 (arXiv v1 Lemma 3.18 and Theorem 3.19) | Level 2: transformation and main-theorem correspondence against the earlier supplied manuscript | Peng Zhang | 19 July 2026 | `unreleased` |
| #0 Language Identification — arbitrary-text semantic theory | Level 2: shared Core prerequisites and arbitrary-text theory | Peng Zhang | 2 August 2026 | `unreleased` |
| #0A Inductive Inference from Positive Data — semantic characterization | Level 1: semantic Theorem 1 | Peng Zhang | 10 August 2026 | `unreleased` |

## Applicability after later revisions

This table records maintenance impact assessments, not new human reviews and
not extensions of the original audit scopes. `Carried forward` means that the
audited mathematical interface remains applicable at the named checkpoint;
new declarations outside that interface remain unaudited.

The machine-checked applicability layer under
[`Fingerprints/`](Fingerprints/) conservatively detects changes to selected
audited theorem types and semantic definition bodies.  A mismatch marks the
scope `needs-review`; it does not rewrite the immutable audit evidence or
decide whether the revised code remains faithful to the paper.  Every scope
listed in the completed-human-audit table now has a declaration manifest.
Only scopes whose current applicability is established are marked `current`;
the others retain an explicit `needs-review` candidate.  Theorem proof-body
and proof-correspondence applicability remains manual.

| Prior human audit | Current checkpoint | Status | Impact assessment |
|---|---|---|---|
| #01 Section 4 semantic path, Level 3 | reviewed baseline `f624971`; later shared selector extraction | `needs-review` for the historical Level 3 scope | The 18 October Level 2 record reviews the current specification and construction, including shared selectors, but explicitly excludes proof correspondence and does not renew the historical Level 3 scope. The historical fingerprints are preserved. |
| #01 round-dependent Section 4 semantic path, Level 2 | reviewed and fingerprinted `c8af96a` | Current; machine-guarded at statement and construction level | The semantic theorem specification and construction, including greatest-critical-index selection, least-fresh-element selection, and the empty-candidate fallback, were reviewed. Theorem proof bodies and proof-step correspondence remain outside this review. |
| #01 Theorems 2.1 and 2.2, Level 1 | reviewed `d5227a2`; fingerprints `b03d957` | Current; machine-guarded at statement level | The finite-query and fixed-sample specifications, defining oracle interfaces, and explicit universe-coding transports were reviewed. |
| #01 Theorem 7.1, Level 1 | reviewed checkpoint `6062058` | Current; statement and definition fingerprints | Peng Zhang reports completion for the public robust-prompt theorem and its canonical string statement. The exact-presentation model, robustness quantifiers, explicit universe coding, prefix extension, eventual target membership, and freshness are included. Construction and proof correspondence and separately strengthened or transported results are outside this scope. |
| #02 named Section 2--3 results | reviewed working tree based on `c8af96a`, 18 October 2026 | Current; machine-guarded at statement and definition level | Peng Zhang confirmed that the finite-history interface migration preserves the definitions and statements of Proposition 2.1 and Theorems 2.4, 2.5, 3.3, 3.5, and 3.10. Construction and proof correspondence were not reviewed; no aggregate P02 level is assigned. |
| #02 Theorem 3.3, Level 1 | fingerprint baseline `14b4deb` | Current; machine-guarded at statement level | The statement and relevant definitions were reviewed, retaining the explicit nonempty-universe convention. |
| #02 Theorem 3.5, Level 1 | fingerprint baseline `04dffd2` | Current; machine-guarded at statement level | The statement and relevant definitions were reviewed, retaining the explicit nonempty-universe convention. |
| #02 Theorem 3.10, Level 1 | fingerprint baseline `6462d25` | Current; machine-guarded at statement level | The statement and relevant definitions were reviewed, retaining the explicit nonempty-universe convention. |
| #03 Theorems 3.1--3.3, Level 1 | reviewed checkpoint `82c0869` | Current; statement and definition fingerprints | Peng Zhang reports Level 1 completion for the three `Results/Overview.lean` statements and their defining interfaces. Construction and proof correspondence, the separate `Results.Additional` result, and other P03 results are outside this scope. |
| #0A semantic characterization, Level 1 | fingerprint baseline `f624971` | Carried forward; machine-guarded at statement level | The audited `SemanticallyInferrable C ↔ ConditionTwo C` statement and its statement-relevant definitions are unchanged. Its proof now delegates a finite eventuality helper to shared Support infrastructure. CI guards the statement and its semantic dependencies, but not the proof body. Effective Theorem 1 and Corollaries 1--3, including the new Corollary 2 and 3 proofs, remain outside this human-audit scope. |
| #04 overview Theorems 1--4 and detailed Theorem 7, Level 1 | reviewed and fingerprinted `fb37e6b` | Current; machine-guarded at statement and definition level | The 19 October review of Theorems 1, 3, and 4 and the 21 October review of detailed Theorem 7 / overview Theorem 2 renew the combined scope. The shared dialogue definitions are included; proof correspondence and the Theorem 7 proof repair are excluded. |
| #04 overview Theorems 1, 3, and 4, Level 1 | reviewed and fingerprinted `fb37e6b` | Current; machine-guarded at statement and definition level | Peng Zhang completed the narrow needs-review checks for these three specifications and their defining interfaces, including the shared finite-history operator. Construction and proof correspondence remain outside scope. |
| #04 overview Theorem 5, Level 1 | reviewed and fingerprinted `fb37e6b` | Current; machine-guarded at statement and definition level | Peng Zhang reviewed the feedback characterization statement, alternating strategy model, truthful exact presentations, uniform distinct-sample threshold, and finite GF dimension on 21 October 2026. This completes the Level 1 overview Theorems 1--5 scope; construction and proof correspondence remain outside scope. |
| #05 three semantic statements, Level 1 | non-P38 working tree based on `6062058`; scoped file hashes and fingerprints | Current; statement and definition fingerprints | Peng Zhang reports Level 1 completion for `theorem_3_3_semantic`, `theorem_3_8_sufficiency_semantic`, and `theorem_3_15_approximate_semantic`. Theorem 3.8 necessity, the exact clause of Theorem 3.15, constructions, proofs, and other P05 results are outside scope. |
| #06 Section 3 theorem specifications, Level 1 | reviewed `b03d957`; fingerprints `0894d0f` | Current; machine-guarded at statement level | The 26 September review renews the four qualified statements and relevant definitions, including shared occurrence-noise predicates, coverage requirements, and explicit universe assumptions. |
| #07 Theorem 2.1, Level 1 | current non-P38 working tree based on `6062058`; file hashes and compiled fingerprints | Current; statement and definition fingerprints | Peng Zhang reports Level 1 completion for the public and canonical `theorem_2_1` statement: eventual index validity and infinitely-often target-language equality for the fixed semantic selector. Other P07 results, density conclusions, construction correspondence, and proof correspondence are excluded. |
| #08 Theorems 2.1 and 2.3, Level 1 | current non-P38 working tree based on `6062058`; file hashes and compiled fingerprints | Current; statement and definition fingerprints | Peng Zhang reports Level 1 completion for detection/identification equivalence and detection from complete, exactly labeled domain enumerations. Other P08 results and construction/proof correspondence are excluded. |
| #09 Theorems 3.3 and 3.7, Level 1 | reviewed checkpoint `132a458`; source hashes and compiled fingerprints | Current; statement and definition fingerprints | Peng Zhang reports Level 1 completion for the group-closure characterization and the stronger nonuniform cover characterization. Existing semantic and source-definition qualifications remain explicit. Constructions, proofs, and other P09 results are excluded. |
| Paper10 overview Theorems 3.1--3.3, Level 1 | fingerprint baseline `d5227a2` | Current; machine-guarded at statement level | The 25 September review renews the overview specifications and relevant definitions, including the finite-history interface and recorded presentation, autonomous-schedule, and EUC conventions. |
| #12 all Overview theorems and their definitions, Level 1 | non-P38 working tree based on `132a458`; scoped file hashes and compiled fingerprints | Current; statement and definition fingerprints | Peng Zhang reports review of all eight current Overview statements and their recursive defining interfaces. Theorem 1.7 covers the strict witness; the separate general finite-feedback equivalence, algorithms, and proofs are not independently reviewed. |
| #13 Overview Theorems 1, 4, 5, 6, and 8, Level 1 | reviewed checkpoint `9efdb94`; source hashes and compiled fingerprints | Current; statement and definition fingerprints | Peng Zhang reports review of the five current Overview statements and their recursive defining interfaces, retaining the distinct-history semantic scope and Procedure-2 repair. Theorem 9 endgame, the representative branch, construction correspondence, and proofs are excluded. |
| #14 Overview Theorems 1 and 2 and their definitions, Level 1 | reviewed checkpoint `9efdb94`; source hashes and compiled fingerprints | Current; statement and definition fingerprints | Peng Zhang reports review of both current Overview statements and their recursive defining interfaces, retaining presentability, behavioral list correctness, the zero-width extension, and relative-Angluin layer conventions. Constructions, proofs, and the statistical branch are excluded. |
| #15 all Overview theorems and their definitions, Level 1 | reviewed checkpoint `d294766`; source hashes and compiled fingerprints | Current; statement and definition fingerprints | Peng Zhang reports review of Theorems 1.5, 1.7, 1.8, and 1.9 and their recursive defining interfaces, retaining the finite-scope witness, raw-index stuttering Algorithm-1, and full-text TD conventions. Other Supporting results, density claims, partial-text topology, constructions, and proofs are excluded. |
| #17 all Overview theorems and their definitions, Level 1 | working tree based on `d294766`; exact source hashes and compiled fingerprints | Current; statement and definition fingerprints | Peng Zhang reports all nine current Overview statements and their recursive definitions, including the canonical-order Theorem 6.18 interface. Semantic/indexing, parameter-range, source-repair, and grouped-card limitations remain explicit; other Supporting results, construction and proof correspondence are excluded. |
| #19 all Overview theorems and their definitions, Level 1 | working tree based on `d294766`; exact source hashes and compiled fingerprints | Current; statement and definition fingerprints | All four current public statements and recursive definitions. Semantic, injective-presentation, threshold-dependency and existential-packaging qualifications retained; construction and proof review excluded. |
| #21 arXiv v2 Overview, Level 1 | reviewed checkpoint `7bdc137` | Current; statement and definition fingerprints | Peng Zhang reports Level 1 completion for all 20 theorems in `Results/Overview.lean`, including the two auxiliary lemmas. Proof-body and construction correspondence are outside this Level 1 record. |
| #22 Theorems 4.1, 5.1, 6.1, 6.6, and 7.3, Level 1 | reviewed checkpoint `6062058` | Current; statement and definition fingerprints | Shuangping Li reviewed the six `Results/Overview.lean` statements for these theorems and their defining interfaces. Theorem 7.1, construction and proof correspondence, and other P22 results are outside this scope. |
| #23 arXiv v2 Overview Claims, Level 1 | reviewed checkpoint `6062058` | Current; statement and definition fingerprints | Shuangping Li reviewed the eight `Results/Overview.lean` aliases for Claims 3.3, 3.5, 3.6, 4.4, 4.11 (repaired form), 4.18, 4.20, and 7.1 and their defining interfaces. The unformalized headline Theorems 4.1, 4.5, 5.1, 5.5, 5.8, and 5.9, construction and proof correspondence, and other P23 results are outside this scope. |
| #27 ICML 2026 Section 3 results, Level 1 | reviewed checkpoint `a19851f` | Current; statement and definition fingerprints | Shuangping Li reviewed twelve `Results/Overview.lean` statements: Theorems 3.1--3.4, Corollaries 3.6--3.8, the set-to-element direction of Theorem 3.9, the Appendix Lemma A.8 counterexample, and Theorem 3.10 components A.9, A.12, and A.13, with their defining interfaces. `theorem_3_9_of_selfLocking`, Appendix Theorems A.10--A.11, construction and proof correspondence, and other P27 results are outside this scope. |
| #28 arXiv v1 Overview, Level 1 | reviewed checkpoint `c828be2` | Current; statement and definition fingerprints | Shuangping Li reviewed all 19 `Results/Overview.lean` aliases and their defining interfaces. Theorem 4.3 is reviewed in its coverage form, Theorem 4.7 as (i) iff (iii), and Theorem 5.13 only through its strictness witnesses. Construction and proof correspondence and results outside the Overview are outside this scope. |
| #29 arXiv v1 Theorems 4.1, 5.1, 6.1 and Lemmas 6.2--6.3, Level 1 | reviewed checkpoint `c828be2` | Current; statement and definition fingerprints | Shuangping Li reviewed seven `Results/Overview.lean` statements and their defining interfaces, including the corrected `Cdim + 1` form of Theorem 5.1. `theorem_6_4_proof_diagnostic`, Theorem 6.4, construction and proof correspondence, and other P29 statements are outside this scope. |
| #30 arXiv v2 Theorem 4 and Appendix Theorem 12, Level 1 | reviewed checkpoint `c828be2` | Current; statement and definition fingerprints | Shuangping Li reviewed the four totalized-GCG `Results/Overview.lean` statements and their defining interfaces, with Lean's stricter `id` deadline recorded. Theorems 1--3, the endgame, turn-taking, and rate-core declarations, construction and proof correspondence, and other P30 statements are outside this scope. |
| #31 arXiv v1 Overview, Level 1 | reviewed checkpoint `c828be2` | Current; statement and definition fingerprints | Shuangping Li reviewed all 13 `Results/Overview.lean` aliases and their defining interfaces. Theorems 4.1 and 4.10 are order-robust minimax statements, which imply the source's lower bounds but not its fixed-order upper bounds. Construction and proof correspondence and results outside the Overview are outside this scope. |
| #32 arXiv v1 Overview, Level 1 | reviewed checkpoint `c828be2` | Current; statement and definition fingerprints | Shuangping Li reviewed ten `Results/Overview.lean` statements and their defining interfaces. The Theorem 3.5 endgame, the Lemma 4.5 and Theorems 4.8--4.9 certificate wrappers, the finite-guess Lemma D.1 diagnostic, construction and proof correspondence, and other P32 statements are outside this scope. |
| #39 arXiv v2 Theorems 3.15 and B.3, Level 1 | reviewed checkpoint `3f0aa55` | Current; statement and definition fingerprints | Peng Zhang reports Level 1 completion for the two Overview density statements and their defining interfaces, including the shared Core density specialization. This separate review does not renew the four historical P39 audit scopes. |
| #0 arbitrary-text semantic theory | current-tree candidate at `f624971` | `needs-review` | The audit predates the numbered-path migration, and its tell-tale predicate later became a compatibility abbreviation to the shared finite-tell-tale API. The current declarations appear preserved, but the ledger's migration-aware narrow review remains outstanding. |
| #39 recursive criticality and focus | current-tree candidate at `f624971` | `needs-review` | The definitions appear preserved across the numbered-path migration; a migration-aware narrow review remains outstanding. |
| #39 patient-scope machine | current-tree candidate at `f624971` | `needs-review` | The state-machine declarations appear preserved across the numbered-path migration; a migration-aware narrow review remains outstanding. |
| #39 exact-presentation conclusion | current-tree candidate at `f624971` | `needs-review` | The ledger already records that the shared-density/API cleanup changed the paper-facing density wrapper. A narrow human re-audit is explicitly pending. |
| #39 partial enumeration | current-tree candidate at `f624971` | `needs-review` | The paper-facing transformation and result declarations appear preserved across migration, but a migration-aware narrow review remains outstanding. |

## ChatGPT Pro checks awaiting human audit

At the maintainer's direction, ChatGPT Pro performed the six source-pinned,
two-stage checks below. These records were contributed as preliminary review
evidence; they do not assign a human audit level.

| Development | Check scope | Checker | Recorded | Human status |
|---|---|---|---|---|
| [#01 added Language Generation paths](../Paper01_LanguageGeneration/) | Observed-set interface and both finite-query Theorem 2.1 paths, compared with the NeurIPS proceedings and arXiv v1 | ChatGPT Pro | 2 August 2026 | Partial: current NeurIPS Theorems 2.1 and 2.2 interfaces have a Level 1 review; the observed-set and historical arXiv-v1 scopes remain outside that review. |
| [#02 Learning Theory](../Paper02_LearningTheory/) | Ordinary and prompted generation, sample-complexity interfaces, hierarchy results, Appendix C, and the Theorem 4.1 combinatorial boundary, compared with arXiv v5 | ChatGPT Pro | 2 August 2026 | Partial human audit complete for Proposition 2.1 and Theorems 2.4, 2.5, 3.3, 3.5, and 3.10; all other P02 scope remains pending |
| [#06 Noisy Examples](../Paper06_NoisyExamples/) | Every paper-owned qualitative statement, exposed assumptions and source repairs, and quantitative exclusions, compared with arXiv v2 | ChatGPT Pro | 2 August 2026 | Partial human audit complete at Level 1 for Section 3 Theorems 3.1, 3.3, 3.9, and 3.10; all other #06 scope remains pending |
| [#08 Hallucination Detection](../Paper08_HallucinationDetection/) | Detection/identification reductions, tell-tale and negative-example results, Appendix results, Example 1, and oracle/effectivity boundaries, compared with arXiv v2 | ChatGPT Pro | 2 August 2026 | Partial human audit complete at Level 1 for Theorems 2.1 and 2.3 and their relevant definitions; all other #08 scope remains pending |
| [#28 Contrastive Generation](../Paper28_ContrastiveGeneration/) | Deterministic statements, hierarchy and robustness coverage, and the Theorem 6.6 witness interface, compared with the arXiv-v1 pre-repair baseline | ChatGPT Pro | 2 August 2026 | Partial: Level 1 review of the 19 Overview statements completed 13 November 2026 (see the #28 section below); the named-witness repair is kernel-checked separately |
| [#31 Bounded Memory](../Paper31_BoundedMemory/) | Deterministic statements, universe/order/output/indexing boundaries, and Appendix Lemma A.3, compared with the arXiv-v1 pre-repair baseline | ChatGPT Pro | 2 August 2026 | Partial: Level 1 review of the 13 Overview statements completed 13 November 2026 (see the #31 section below); the Lemma A.3 wrapper repair is kernel-checked separately |

The same method was used for each record:

| Checked item | ChatGPT Pro-assisted method |
|---|---|
| Stage 1: code-only reconstruction | Reconstruct the mathematical interface from Lean declaration signatures and statement-relevant definition bodies while withholding the paper and excluding comments, theorem proof bodies, and tactic scripts as mathematical evidence. |
| Stage 2: source comparison | Compare that reconstruction with the checksum-pinned author source and verify its title, authors, version, and readability. |
| Statement fidelity | Check mathematical objects and types, binder and quantifier order, hypotheses, conclusions, representation and indexing choices, presentation/access/output interfaces, and whether the Lean statement is equivalent, stronger, weaker, conditional, or vacuous at an edge case. |
| Coverage and assembly | Inventory the paper's numbered claims, match them to Lean declarations, identify omitted claims, and check whether advertised witnesses or theorem chains are exposed by statement-level interfaces. |
| Findings and provenance | Record source errors, formalization gaps, boundary qualifications, exact source and Lean snapshot hashes, and any later repair as a separately tracked change. |

These checks did **not** audit theorem proof-body correctness, establish
proof-step correspondence, rerun Lean, certify the papers' mathematics, or
constitute a human audit. Lean compilation and logical-dependency checks are
recorded separately in [AUDIT.md](../../AUDIT.md). The immutable evidence and
machine-readable provenance are under [`AuditRecords/`](../). A future human
reviewer can add a dated level, scope, and code anchors to the completed table
above without rewriting these preliminary records.

## Numbered-path migration

The code anchors below preserve the filesystem paths and SHA-256 values that
existed when each human review was performed. The current source tree uses the
numbered paper paths shown here:

| Audited snapshot path | Current path |
|---|---|
| `GenLimit/Gold/` | [`GenLimit/Paper00_LanguageIdentification/`](../../GenLimit/Paper00_LanguageIdentification/) |
| `GenLimit/Angluin/` | [`GenLimit/Paper00A_PositiveDataInference/`](../../GenLimit/Paper00A_PositiveDataInference/) |
| `GenLimit/KM/` | [`GenLimit/Paper01_LanguageGeneration/`](../../GenLimit/Paper01_LanguageGeneration/) |
| `GenLimit/DenseGeneration/` | [`GenLimit/Paper39_DenseGeneration/`](../../GenLimit/Paper39_DenseGeneration/) |

The organizational move also rewrote imports and documentation comments, so
some current files no longer have the audited byte hash even when their
declarations and proofs are otherwise unchanged. This ledger does not treat
that mechanical migration as a human re-audit.

## #01 Language Generation: semantic construction and proof correspondence

For a fixed family `O`, the #01 declaration
`KM.Semantic.generator O stream` does not receive the
hidden target index `z`. If `stream` exactly presents `O.language z`, the main
theorem says that every sufficiently late output belongs to the target and is
absent from `sample stream t`.

| Checked item | Audited meaning |
|---|---|
| Model | `OracleFamily` is an indexed family of infinite languages, and `Presents` means exact positive-data presentation. |
| Criticality | `Critical` is KM criticality; critical languages form the required inclusion chain and the target is eventually critical. |
| Construction | At round `t`, `focus` selects the greatest critical index below `t`, and `fresh` selects the least focused-language element outside `sample stream t`. |
| Uniformity | The generator depends on `O`, `stream`, and `t`, not on `z`. |
| Conclusion | Eventual target membership and freshness from the first `t` stream observations; generator outputs need not be mutually distinct. |
| Access model | Round `t` uses the current observation prefix, but whole-language inclusion makes this semantic construction noncomputable from the membership oracle. |

This Level 3 audit covers the round-dependent Section 4 construction,
especially (4.2)--(4.6), with `t` explicit. It does not certify a literal
finite-set-only realization of the interface stated in (4.1).

At checkpoint `f302337`, this Level 3 record remains applicable to that exact
semantic scope. The later observed-set and finite-query paths, Theorem 2.2,
and the Theorems 2.1/2.2 universe transports are kernel checked but have not
received a human paper-to-Lean correspondence audit.

At fingerprint baseline `f624971`, the audited P01 semantic files and the
statement-relevant portions of the shared model remain unchanged from that
maintenance checkpoint.  CI now checks their normalized declaration
fingerprints; this automates change detection for statement and construction
applicability, not a new human review or proof-correspondence judgment.

On 20 July 2026, Peng Zhang performed a narrow human re-audit against the #01
Language Generation NeurIPS 2024 proceedings version after the semantic-file cleanup. The
paper-facing definitions, main theorem statement, and proof steps were
unchanged: the existing proof body was moved directly into
`kleinbergMullainathan_main`, the duplicate `eventual_correctness` alias was
removed, and the Section 4 boundary was documented.

The audited-snapshot code anchors are:

| Code anchor | SHA-256 |
|---|---|
| `GenLimit/KM/Critical.lean` | `61b1c01977eaa69adaa63e56ccf8a0dac9c3554035a99d6d325ea2affeeb2e60` |
| `GenLimit/KM/Semantic.lean` | `3f603dff375c9f3cc5ee0bca80271e8dd36b775f3f661d2fa56cf8e5923aefaa` |

The shared model is in [`GenLimit/Core/Basic.lean`](../../GenLimit/Core/Basic.lean).
This audit does not require a literal tactic-by-tactic or line-by-line identity
between the Lean proof and the prose. It does cover the theorem statement,
semantic construction, intermediate mathematical steps, and proof
correspondence at Level 3. It does not cover the observed-set interface or
either finite-query development (the NeurIPS proceedings endpoint machine and
the arXiv-v1 whole-prefix machine).

## #01 Language Generation: round-dependent semantic construction, Level 2

On 18 October 2026, Peng Zhang reported completion of a Level 2 human
paper-to-Lean audit at checkpoint
`c8af96afa1a1b50d141ab80751e73900a02b5beb`. The comparison source was the
NeurIPS 2024 proceedings version of Kleinberg--Mullainathan, *Language
Generation in the Limit*, with PDF SHA-256
`4b29159d3d11506fa8f92f38e4dfe234f209a730f786de7ef6c577f7e34b0745`.
The review covers the Section 2 model and the round-dependent Section 4
semantic specification and construction, especially (4.2)--(4.6), over `ℕ`.

The reviewer confirmed both the theorem specification (assumptions, inputs,
outputs, and conclusion) and the semantic construction against the paper.
The reviewed construction includes the critical-candidate definition, the
greatest critical index in the finite scope, the least element outside the
observed sample, and the arbitrary fallback when the candidate set is empty.
It includes the delegation of `focus` and `fresh` to the shared
`greatestCandidateWithFallback` and `leastFreshFromInfinite` definitions.

The scope retains these explicit boundaries:

- `Presents` requires an exact positive presentation and permits repetitions;
  `sample stream t` contains observations at positions strictly below `t`.
- The generator takes the round `t` explicitly and does not receive the hidden
  target index. This review covers the round-dependent construction, rather
  than a literal finite-set-only interpretation of (4.1).
- The construction is semantic and noncomputable from pointwise membership
  queries alone. Its conclusion is eventual target membership and freshness
  relative to the observed sample; its own outputs may repeat.
- Theorem proof bodies, intermediate proof-step correspondence, and the
  Appendix A.2 proofs were not reviewed. The observed-set implementation,
  finite-query machine, Theorem 2.2, universe transports, quantitative bounds,
  and Theorem 7.1 are outside this Level 2 scope.

This is a separate completed Level 2 record. It does not renew or replace the
historical Level 3 audit, whose current applicability remains `needs-review`.
The [Level 2 fingerprint manifest](Fingerprints/P01_SemanticLevel2.json)
guards the reviewed theorem type and defining construction bodies, including
the shared selector bodies; it does not track theorem proof bodies.

The following file hashes pin the reviewed source snapshot. They identify
files containing the reviewed definitions and theorem specifications, not an
audit of the proof bodies or every declaration in those files.

| Code anchor | SHA-256 |
|---|---|
| `GenLimit/Core/Basic.lean` | `d3defc57c979dbc75764899c92945b3d4d622c67ae2752a39bcb24f256637f26` |
| `GenLimit/Core/OracleFamily.lean` | `f850a016f37d6e4eb31e01030edc1d1e9f9574fc64c57c71a749713213ea7636` |
| `GenLimit/Core/TargetStability.lean` | `a9a6d0939b0d91fc5f7027dc88efc1139522fc5166e3869aec664f1a5d93b692` |
| `GenLimit/Paper01_LanguageGeneration/Critical.lean` | `ec91014338cadfd05d3c503824b485de64cacaeba5effb7f6957c6f643e497ce` |
| `GenLimit/Support/LeastCandidate.lean` | `4956574428ed9737912dc5d042cf40b14414129f60d0e2ea56cd82fdfa1295b6` |
| `GenLimit/Support/Fresh.lean` | `cb931ef005dcbaa95b1f5f134997b0e6a0bf0cbd5fca0bfbb9934da0184c423e` |
| `GenLimit/Paper01_LanguageGeneration/Semantic.lean` | `500d393b72ef3a7b30184dbff85495ba0ca0a1d808aae66f75bcef7f178869af` |

## #01 Language Generation: Theorems 2.1 and 2.2 specifications

On 25 September 2026, Shuangping Li completed a Level 1 review of Theorems
2.1 and 2.2 against the [NeurIPS 2024 proceedings](https://proceedings.neurips.cc/paper_files/paper/2024/hash/7988e9b3876ad689e921ce05d711442f-Abstract-Conference.html)
at Lean checkpoint `d5227a2af277f5448a4afa95e2e8044f3625fb35`, with
Codex-assisted statement translations.

The review covers the finite-query and fixed-sample specifications, relevant
oracle and presentation definitions, and explicit universe-coding transports.
Construction and proof correspondence, quantitative complexity, the observed-set
path, and Theorem 7.1 are excluded. The [scoped fingerprint record](Fingerprints/P01_MainTheorems2_1And2_2Level1.json)
is current; the historical Section 4 Level 3 scope remains `needs-review`.

## #01 Language Generation: Theorem 7.1 specification

On 8 November 2026, Peng Zhang reported completion of a Level 1 human
paper-to-Lean audit of NeurIPS 2024 Theorem 7.1 at checkpoint
`60620581aa210daec6fa7d3aa65d7f9fdb565b8c`. The actual completion date was
not separately specified. The reviewed declarations are
`GenLimit.KM.Results.theorem_7_1` in `Results/Overview.lean` and its canonical
statement `GenLimit.KM.Prompted.theorem_7_1` in `Prompted/Strings.lean`.

The comparison source is the supplied local NeurIPS 2024 proceedings PDF,
`papers/P01_LanguageGeneration.pdf`, with SHA-256
`e8a94a9c8d7509edbed5e9b7731d96f1da44b1d4558a0149fa3f9e873bc7f752`.
The source statement is on printed page 10, with robustness defined on page 9
and the supporting algorithm in Appendix A.5, pages 14--15. This hash pins
the locally reviewed PDF snapshot; the earlier P01 audits retain their own
source hashes.

The Level 1 scope includes the theorem statement and its statement-relevant
definitions: a countably indexed family of infinite languages of finite
strings, exact positive presentations allowing repetitions, the supplied
`List A ≃ ℕ` coding and membership-oracle interface, and robustness requiring
arbitrarily long continuations in every candidate language. The continuation
may depend on the candidate and the length bound. The reviewed conclusion
is eventual target membership and freshness relative to the observed sample,
with every sufficiently late output extending the current robust prompt;
prompts may change at every round.

The [scoped fingerprint record](Fingerprints/P01_Theorem7_1Level1.json)
guards the two theorem types and their recursive project-local defining
dependencies. Defining bodies and proof-certificate types are tracked only
to preserve the meaning of the statement; this does not constitute a Level 2
construction audit or Level 3 proof-correspondence audit.

The separate uniform-threshold strengthening, classical countable-alphabet
wrapper, arbitrary-string-universe transports, and empty-prompt corollary
are not independently human-reviewed by this record. Query bounds,
complexity, and runtime implementation claims are also excluded. The prior
Theorems 2.1/2.2 Level 1, semantic Level 2, and historical semantic Level 3
records retain their original scopes and applicability statuses.

## #02 Learning Theory: Proposition 2.1 and ordinary Section 2--3 main theorems

On 12 August 2026, Peng Zhang reported completion of a human paper-to-Lean
audit of Proposition 2.1, Theorems 2.4 and 2.5, and all results explicitly
labelled as theorems in ordinary Section 3 of Li--Raman--Tewari,
*Generation through the Lens of Learning Theory*. The Section 3 theorems are
Theorems 3.3, 3.5, and 3.10. The comparison source was
[`arXiv:2410.13714v5`](https://arxiv.org/abs/2410.13714v5), and the audited
Lean checkpoint was
`d40205b723b809b70e12a091631e0527a09e5c07`. The pinned source PDF has
SHA-256 `acaf59abdb4542173cb20dd05e874f7fa5b505bf7b2c5c561529d5e387502482`.

This ledger records the named-result audit as complete. It deliberately does
not infer one undifferentiated audit level for the rest of P02.

| Paper result | Lean declaration | Audited correspondence boundary |
|---|---|---|
| Proposition 2.1 | `GenLimit.LiRamanTewari.proposition_2_1` | Both hierarchy implications are strict on one existentially quantified countably infinite example type. The infinite-domain qualification repairs the false literal reading for arbitrary finite countable domains, and the concrete tagged `BlockUniverse` witness is hidden inside the proof. |
| Theorem 2.4 | `GenLimit.LiRamanTewari.theorem_2_4` | Every countable UUS class is generatable in the limit; the Lean wrapper factors through the stronger nonuniform conclusion of Corollary 3.6. |
| Theorem 2.5 | `GenLimit.LiRamanTewari.theorem_2_5` | Every finite UUS class is uniformly generatable; the Lean wrapper reuses the finite-class closure bound and Theorem 3.3. |
| Theorem 3.3 | `GenLimit.LiRamanTewari.uniform_generatability_iff_finite_closure_dimension` | Under the paper's UUS hypothesis, uniform generatability is equivalent to finite closure dimension. |
| Theorem 3.5 | `GenLimit.LiRamanTewari.nonuniform_generatability_iff_nondecreasing_finite_closure_cover` | Under UUS, nonuniform generatability is equivalent to admitting a nondecreasing cover whose components have finite closure dimension. |
| Theorem 3.10 | `GenLimit.LiRamanTewari.finite_closure_dimension_cover_implies_generatable_in_limit` | A finite cover by classes of finite closure dimension suffices for generation in the limit. |

This completed scope does **not** independently certify the Section 3 lemmas
or corollaries used by those theorem proofs: Lemmas 3.1, 3.2, 3.4, 3.7, 3.8,
3.9, and 3.12, Corollary 3.6, or the unnumbered corollary represented by
`finite_cone_cover_generatable_in_limit`. Nor does it cover Theorems 2.2 or
2.3, Section 4, prompted Section 5, Appendix C, literal PAC/online models,
computability, membership-oracle implementations, or efficiency claims.
Those results remain available for separate human audit even where Lean's
kernel already checks their proofs.

The audited revision anchors below pin the named declarations and the two
strictness witnesses used by Proposition 2.1. A file anchor does not extend
the audit to every other declaration in that file.

| Code anchor | SHA-256 |
|---|---|
| `GenLimit/Paper02_LearningTheory.lean` | `df59d4c282dad5aabea020bb0770d3ec3d0e08eaa5cee52f8d5c85bf394a8326` |
| `GenLimit/Paper02_LearningTheory/Hierarchy.lean` | `7d2e3e003bd34bdd62f78f07ff2061db4d895322dd903e5043f395b23a05cb5b` |
| `GenLimit/Paper02_LearningTheory/Closure.lean` | `3de98d002562da528c0a68a58ecb63fa8c54ca5e329b4c5dd996d6dfe5c812d3` |
| `GenLimit/Paper02_LearningTheory/NonuniformCharacterization.lean` | `08a3f35c99915b2e03f850db02f43a3673a0ff9aefc57d43ce73d1bd015bedef` |
| `GenLimit/Paper02_LearningTheory/GenerationInLimitCharacterization.lean` | `28b092ca31f4404b6dcab7b62e0205e9f5098ef98bcc0f35282b798de1067625` |
| `GenLimit/Paper02_LearningTheory/EarlierSectionThreeExamples.lean` | `ce26852b74ee9bb332108e60ce8383183b7f1557278f92075a84b5c3ab3d0e0b` |
| `GenLimit/Paper02_LearningTheory/LimitVsNonuniformSeparation.lean` | `6642d8a461a22e093c28d5ca426614c9eda71a68cc8a62e93ad38ebdbd1e1f4f` |

## #02 Learning Theory: finite-history statement and definition applicability review

On 18 October 2026, Peng Zhang reported completion of the narrow human
statement-and-definition review for Proposition 2.1 and Theorems 2.4, 2.5,
3.3, 3.5, and 3.10. This is a Level 1 review of those named specifications
and their defining interfaces, not an aggregate audit level for P02. The
comparison source remains *Generation through the Lens of Learning Theory*,
arXiv:2410.13714v5, with the pinned PDF SHA-256
`acaf59abdb4542173cb20dd05e874f7fa5b505bf7b2c5c561529d5e387502482`.

The reviewed working tree is based on checkpoint
`c8af96afa1a1b50d141ab80751e73900a02b5beb`. The mathematical code in the
reviewed files matches that commit. `Core/VersionSpace.lean` additionally has
two local documentation annotations identifying Section 2.1; its working-tree
hash, rather than its committed byte hash, is recorded below.

The reviewer confirmed the following:

- Expanding `Generator alpha := FiniteHistoryOperator alpha alpha` preserves
  the original type `forall t, (Fin t -> alpha) -> alpha`. The generator
  receives an ordered finite history, including repetitions, while `sample`
  records distinct observations. `output` supplies only positions below `t`
  and does not supply the hidden target or future observations.
- One generator serves the entire class. Uniform generation has one shared
  distinct-sample threshold; nonuniform generation permits a target-dependent
  threshold independent of the stream; limit generation permits a threshold
  depending on both target and exact presentation. The `StreamIn` and
  `Presents` requirements and exact distinct-sample-count triggers retain the
  paper's intended distinction.
- `CorrectAt` requires target membership and freshness relative to the
  observed sample, without requiring mutually distinct generator outputs.
- The version space, common core, optional closure's empty-version-space
  case, finite closure dimension including its zero convention, increasing
  covers, and finite covers retain their reviewed mathematical meanings.
- The six result signatures retain their explicit qualifications:
  Proposition 2.1 uses one existentially quantified countably infinite
  example type; the other five use the stated nonempty countable-universe
  conventions and UUS assumptions. Theorem 2.4 requires a countable class and
  Theorem 2.5 a finite class; the three Section 3 results do not
  add a countability assumption on the whole language class.

This review renews the definition and statement applicability of the earlier
named-result record after the finite-history migration. It does not review
algorithmic constructions, theorem proof bodies, intermediate proof-step
correspondence, supporting Section 3 lemmas or corollaries, quantitative
sample-complexity bounds, Theorems 2.2--2.3, Section 4, prompted Section 5,
Appendix C, or computability and efficiency claims. The two strictness-witness
type anchors retained from the earlier manifest are historical statement
guards, not a new construction or proof audit of those witnesses.

The [named-result fingerprint manifest](Fingerprints/P02_NamedSection2And3Results.json)
is now `current` for this statement-and-definition scope. It explicitly
guards the shared `FiniteHistoryOperator` body, optional closure definitions,
and public theorem specifications in addition to the retained anchors. The
dated August and September human records and immutable AI evidence are
preserved.

| Reviewed code anchor | Working-tree SHA-256 |
|---|---|
| `GenLimit/Core/GenericGeneration.lean` | `a92d4e3f0101d187a45b46e3c6921fea54f9bd8cd5435ed28241de3fe318dd92` |
| `GenLimit/Core/ClassGeneration.lean` | `2e661a66f115c9fb9f9a7316d599d878a9ca54315f8bc711a768f941f8d7b382` |
| `GenLimit/Core/VersionSpace.lean` | `366be41fb4edb62bfa78013a2663a1de44c8c36074c49799d13e943902f19dbf` |
| `GenLimit/Core/ClosureDimension.lean` | `dd6f250e0a41e576d6059b46118897602baee44093ec0d4dff0acb737076b752` |
| `GenLimit/Core/ClassCovers.lean` | `f952c8877e93e902f027e41109e449071a5f9c73d726d8c65488ffd14f93d166` |
| `GenLimit/Paper02_LearningTheory/Definitions.lean` | `2b971ac1a13ae87b3b242628a5accf6aa667f728815cd4ece3722e362ccb784e` |
| `GenLimit/Paper02_LearningTheory/Hierarchy.lean` | `7d2e3e003bd34bdd62f78f07ff2061db4d895322dd903e5043f395b23a05cb5b` |
| `GenLimit/Paper02_LearningTheory/Results/Overview.lean` | `78929cf0578b4e25eeb152fd12764870da29324fe8530bcdc78da98b42869631` |

The 8 November 2026 background-facade reorganization moves the unchanged
`Results.theorem_2_4` and `Results.theorem_2_5` types from `Results/Overview.lean`
to `Results/Background.lean`. The fingerprint exporter imports that facade
explicitly. Canonical declarations and reviewed baselines remain unchanged;
this layout change neither renews proof correspondence nor extends human
review to the new background wrappers for Theorems 2.2 and 2.3.

## #02 Learning Theory: Theorem 3.3 specification and finite-history interface

On 25 September 2026, Shuangping Li completed a Level 1 review of Theorem 3.3
against [arXiv:2410.13714v5](https://arxiv.org/html/2410.13714v5) at Lean
checkpoint `14b4debc380de5b874e28a79f0bd15c9cab84744`, with Codex-assisted
statement translations.

The review covers the theorem specification and statement-relevant
definitions, including the shared finite-history interface, with the explicit
nonempty-universe convention. Construction and proof correspondence, the
quantitative corollary, and other P02 results are excluded.

The [scoped fingerprint record](Fingerprints/P02_Theorem3_3Level1.json) is
current. The separate 18 October statement-and-definition review also renews
the broader named-result manifest without extending construction or proof
coverage.

## #02 Learning Theory: Theorem 3.5 specification

On 25 September 2026, Shuangping Li completed a Level 1 review of Theorem 3.5
against [arXiv:2410.13714v5](https://arxiv.org/html/2410.13714v5) at Lean
checkpoint `04dffd222333994d57c963871175e53b56452bf1`, with Codex-assisted
statement translations.

The review covers the theorem specification and statement-relevant
definitions, with the explicit nonempty-universe convention. Construction
and proof correspondence, Lemmas 3.7--3.8, Corollary 3.6, and other P02
results are excluded.

The [scoped fingerprint record](Fingerprints/P02_Theorem3_5Level1.json) is
current. The separate 18 October statement-and-definition review also renews
the broader named-result manifest without extending construction or proof
coverage.

## #02 Learning Theory: Theorem 3.10 specification

On 25 September 2026, Shuangping Li completed a Level 1 review of Theorem 3.10
against [arXiv:2410.13714v5](https://arxiv.org/html/2410.13714v5) at Lean
checkpoint `6462d256c5f4a99d46d73d95b7f8d3a86bf94645`, with Codex-assisted
statement translations.

The review covers the theorem specification and statement-relevant
definitions, including exact presentations and the finite cover, with the
explicit nonempty-universe convention. Construction and proof correspondence,
Corollary 3.11, and other P02 results are excluded.

The [scoped fingerprint record](Fingerprints/P02_Theorem3_10Level1.json) is
current. The separate 18 October statement-and-definition review also renews
the broader named-result manifest without extending construction or proof
coverage.

## #03 Limits of Language Generation: Theorems 3.1--3.3, Level 1

On 2 November 2026, Peng Zhang reported completion of a Level 1 human audit
of P03 Theorems 3.1, 3.2, and 3.3. This is the reporting date; the actual
completion date was not separately specified. The reviewed checkpoint is
`82c086930f040d8a8e82e2cb62a26c2d3045997f`.

The comparison source is *On the Limits of Language Generation: Trade-Offs
Between Hallucination and Mode Collapse*, arXiv:2411.09642v3 (14 October
2025), with pinned PDF SHA-256
`097bda3ceeab7ddb244595b2817c8766f540b508abfe24a2ca8eaa0feecf3439`.
The [paper map](../../PaperMaps/Paper03_HallucinationAndModeCollapse.md)
records the source qualifications and formalization boundaries.

The reviewed statements are in
[`Results/Overview.lean`](../../GenLimit/Paper03_HallucinationAndModeCollapse/Results/Overview.lean),
with prefix `GenLimit.HallucinationModeCollapse.Results`:

| Paper item | Reviewed declaration | Statement scope |
|---|---|---|
| Theorem 3.1 | `theorem_3_1` | Identification-rate dichotomy, Angluin characterization, and randomized exponential lower bound. |
| Theorem 3.2 | `theorem_3_2` | Exponential fresh-generation upper and lower bounds, with the stated infinitude, oracle, nontriviality, and computability conditions. |
| Theorem 3.3 | `theorem_3_3` | Statistical breadth separation and generation rates, with the stated pointwise MOP, oracle, sampling, and computability conditions. |

Level 1 includes the definitions that give these statements their meaning:
indexed language families, positive presentations and IID distributions,
randomized learners, identification and generation losses, rate predicates,
Angluin's condition, nontriviality, and the oracle, support-membership,
sampler, and computation interfaces used in the three statements.

The [fingerprint manifest](Fingerprints/P03_Theorems3_1To3_3_Level1.json)
guards these statement types and their project-local defining dependencies.
Supporting proof-certificate types preserve the meaning of definitions;
they are not separate human audit claims. Construction and proof-step
correspondence (Levels 2 and 3), a separate audit of the stronger result in
`Results/Additional.lean`, and all other P03 statements are outside this
record. Capturing fingerprints is a mechanical maintenance step.

## #04 Exploring Facets: overview Theorems 1--4

On 14 August 2026, Peng Zhang reported completion of a human paper-to-Lean
audit of overview Theorems 1--4 of Charikar--Pabbaraju, *Exploring Facets of
Language Generation in the Limit*.  The comparison source was the supplied
`papers/P04_ExploringFacetsOfLanguageGeneration.pdf`, corresponding to
arXiv:2411.15364v2, with SHA-256
`cea686c86617749044c31e89fd212b29a32ad91a88c088326b30f7991b785381`.
The audited working tree was based on
`87423ff7f77437af2c63d525a5cbc36095b3f8b8`; the file hashes below pin the
subsequent uncommitted paper-facing infinitude-signature cleanup that was also
present when this record was entered.

This is an additive dated record.  It does not overwrite or supersede any
earlier human or AI-assisted audit record.  Because no aggregate audit level
was supplied, the ledger records completion of the four named theorem
correspondence checks without inferring construction-level or proof-body
coverage.

| Paper result | Lean declaration | Audited correspondence boundary |
|---|---|---|
| Theorem 1 | `GenLimit.CharikarPabbaraju.Results.theorem_1` | Every countably indexed collection of infinite languages over a countable infinite example type is non-uniformly generatable. The paper's standing infinitude assumption is explicit as `UUS (Set.range C)`. |
| Theorem 2 | `GenLimit.CharikarPabbaraju.Results.theorem_2` | The overview membership-query lower bound is exposed through detailed Theorem 7: no single computable deterministic membership-query algorithm satisfies the non-uniform guarantee for every genuine pair of distinct infinite languages over `ℕ`. |
| Theorem 3 | `GenLimit.CharikarPabbaraju.Results.theorem_3` | There exists a countable `UUS` class of regular languages over the literal finite alphabet `Bool` that is not exhaustively generatable. Lean makes the paper's standing infinitude assumption explicit in the existential witness. |
| Theorem 4 | `GenLimit.CharikarPabbaraju.Results.theorem_4` | For a countably indexed `UUS` family over a countable universe, exhaustive generatability is equivalent to Weak Angluin's Condition with Existence. The Lean headline is semantic; its sufficient direction is implemented at the paper's strong-oracle layer. |

This named-result record does **not** claim a human audit of the proofs of
Theorems 1--4, detailed Theorems 6--8, the completion-driven repair of the
printed Theorem 7 proof, Claims or Propositions in Sections 5--7, Examples 9
and 10, the randomized corollary, computability implementations, or oracle
complexity.  Those remain separate audit scopes even where Lean's kernel
already checks the corresponding declarations.

The audited-revision code anchors are:

| Code anchor | SHA-256 |
|---|---|
| `GenLimit/Paper04_ExploringFacetsOfLanguageGeneration/Results/Overview.lean` | `41098064c4ce4d71faf6c115e851d5a9c2ec99cf4b0e9e3dbd29549f945b652b` |
| `GenLimit/Paper04_ExploringFacetsOfLanguageGeneration/Definitions.lean` | `c568ac33381693d8519d1cc1006fa0d1fea8f92f3b1825e756cf8056d59661ce` |
| `GenLimit/Paper04_ExploringFacetsOfLanguageGeneration/MembershipQueryLowerBoundStatement.lean` | `ce2d8157f9da4e043a0247770603dfd4f679456c697a63caacb1550f39897a65` |
| `GenLimit/Paper04_ExploringFacetsOfLanguageGeneration/RegularRayEncoding.lean` | `ccb2a0030d5154db5ac92f47f6395527119028713f4c1b0e3e522181d809817a` |
| `GenLimit/Paper04_ExploringFacetsOfLanguageGeneration/Exhaustive.lean` | `10eefe41f91ee7ba3bb2b5d8b07c140efcdd9aea33509f09429a5e492c70af87` |
| `GenLimit/Paper04_ExploringFacetsOfLanguageGeneration/ExhaustiveCharacterization.lean` | `0a8484c28a45f23270306b98503e00ed4841a0ea3bb965dfb14715cc543cb0c5` |

## #04 Exploring Facets: overview Theorems 1, 3, and 4, Level 1 renewal

On 19 October 2026, Peng Zhang confirmed completion of the narrow human
needs-review checks for overview Theorems 1, 3, and 4. This is a Level 1
review of the named theorem specifications and their statement-relevant
definitions following the shared finite-history extraction. The reviewed
Lean checkpoint is `fb37e6b978f56eb0bcd7b6425ed4e13b1dd9e456`. The comparison
source remains the supplied arXiv:2411.15364v2 PDF, with SHA-256
`cea686c86617749044c31e89fd212b29a32ad91a88c088326b30f7991b785381`.

The completed scope covers the nonuniform-generation specification of
Theorem 1, the countable class of infinite regular languages over `Bool`
in Theorem 3, and the semantic exhaustive-generation/Weak Angluin's Condition
with Existence equivalence in Theorem 4. The defining interfaces include
`Generator alpha := FiniteHistoryOperator alpha alpha` and
`ExhaustiveAlgorithm alpha := FiniteHistoryOperator alpha (Nat -> alpha)`;
expanding these aliases preserves the finite-history algorithm types.

The [scoped fingerprint manifest](Fingerprints/P04_OverviewTheorems1_3_4Level1.json)
is `current` for these three statements and their defining interfaces.
At this review date, the combined Theorems 1--4 candidate remained separate;
the 21 October record below subsequently renews that combined scope.
This 19 October renewal does not cover the adaptive membership-query model,
algorithmic constructions, theorem proof bodies, intermediate proof-step
correspondence, oracle implementations, or complexity. No aggregate P04
audit level is assigned.

## #04 Exploring Facets: detailed Theorem 7 and overview Theorem 2, Level 1 renewal

On 21 October 2026, Peng Zhang confirmed completion of the human audit of
detailed Theorem 7, which supplies overview Theorem 2. Continuing the current
Level 1 review scope, this records statement and statement-relevant definition
correspondence after the shared adaptive membership-query dialogue extraction.
The reviewed mathematical code matches checkpoint
`fb37e6b978f56eb0bcd7b6425ed4e13b1dd9e456`. The source edition remains the
supplied arXiv:2411.15364v2 PDF, historically pinned with SHA-256
`cea686c86617749044c31e89fd212b29a32ad91a88c088326b30f7991b785381`.

The local review copy was saved with additional annotations on 21 October
and now has SHA-256
`4ead3a271d5ed818e755fa2a817ef14db8a7de60ca3c464f792c189db0d0633e`.
The exact pinned PDF remains its first 449,890 bytes. All 31 pages have
identical extracted text and decoded page content streams in the pinned and
annotated copies; the source edition and mathematical text are unchanged.

The scope covers `Results.theorem_7`, `TheoremSevenStatement`, and
`Results.theorem_2`, together with the shared dialogue algorithm, adaptive
query-trace, completed-round, execution, and output predicates and their P04
two-language oracle instantiation. The statement requires one computable
deterministic algorithm to work for every pair of distinct infinite languages,
with finite-query termination at every round and target-dependent
distinct-sample thresholds independent of the exact presentation.

The reviewed interface uses a total next-action function. It represents a
nonterminating round by unbounded querying; no simulation theorem for
arbitrary partial oracle machines is certified by this record. Theorem proof
bodies, intermediate proof-step correspondence, the completion-driven repair
of the printed Theorem 7 proof, oracle implementations, and complexity remain
outside this Level 1 scope.

Together with the 19 October review of Theorems 1, 3, and 4, this renews the
[combined fingerprint manifest](Fingerprints/P04_OverviewTheorems1To4.json)
to `current`. The former candidate's provenance is retained in the manifest;
the dated August and October records are preserved. This does not assign an
aggregate P04 audit level or extend human coverage to overview Theorem 5.

## #04 Exploring Facets: overview Theorem 5, Level 1

On 21 October 2026, Peng Zhang confirmed completion of the Level 1 human
audit of overview Theorem 5, covering its statement and relevant definitions.
The reviewed mathematical code matches checkpoint
`fb37e6b978f56eb0bcd7b6425ed4e13b1dd9e456`. The comparison source is the
supplied arXiv:2411.15364v2 PDF, historically pinned with SHA-256
`cea686c86617749044c31e89fd212b29a32ad91a88c088326b30f7991b785381`.
The annotated review copy and its verified relationship to that pinned PDF
are recorded in the [Theorem 5 fingerprint manifest](Fingerprints/P04_Theorem5Level1.json).

The scope covers `Results.theorem_5` in
[`Results/Overview.lean`](../../GenLimit/Paper04_ExploringFacetsOfLanguageGeneration/Results/Overview.lean)
and its defining interfaces in
[`Feedback.lean`](../../GenLimit/Paper04_ExploringFacetsOfLanguageGeneration/Feedback.lean):
the alternating generator and adversary strategies, their interaction, exact
positive presentations and truthful target-membership answers, distinct
samples through the current round, the uniform generation guarantee,
consistent-language intersection, and finite GF dimension. One generator and
one distinct-sample threshold must work for every target and consistent
adversary. The statement retains the infinite-language assumption through
`UUS C` and a countable universe, while permitting an arbitrary language
class without assuming the class itself is countable.

The manifest is `current` for this statement and these definitions. Together
with the earlier reviews, all five P04 overview theorem specifications now
have current Level 1 human coverage. Generator constructions, theorem proof
bodies, intermediate proof correspondence, separate Section 7 result
statements, computability, and complexity remain outside this review. This
does not assign an aggregate audit level to the whole P04 development.

## #05 Hallucinations, Breadth, and Stability: three semantic statements, Level 1

On 12 November 2026, Peng Zhang reported completion of a **Level 1** human
paper-to-Lean audit of the following three declarations and their relevant
definitions, explicitly selecting the `work/non-p38` workspace. This is the
reporting date; the actual completion date was not separately specified.
The reviewed working tree is based on
`60620581aa210daec6fa7d3aa65d7f9fdb565b8c` and contains unrelated uncommitted work.
The [scoped fingerprint manifest](Fingerprints/P05_SemanticTheorems3_3_3_8_3_15_Level1.json) pins the reviewed
source-file hashes and compiled statement/definition fingerprints; the HEAD
reference alone does not assert that the whole working tree was clean.

The source is *On Characterizations for Language Generation: Interplay of
Hallucinations, Breadth, and Stability*, arXiv:2412.18530v2 (3 July 2025),
using the local `papers/P05_HallucinationsBreadthAndStability.pdf` supplied
in the sibling `language generation lean` workspace, with SHA-256
`66751922ee4a3b7f8edbfdf0eb85085c4d7cca55a520446e76023796266b760c`.
That PDF was read without modifying the sibling workspace; all audit-record
changes are in non-P38. Theorems 3.3, 3.8, and 3.15 are on printed pages
9, 11, and 12. Relevant definitions are in Sections 2 and 3. The source
snapshot is recorded independently of earlier LLM-audit PDF hashes.

The reviewed declarations are in
[`Results/Overview.lean`](../../GenLimit/Paper05_HallucinationsBreadthAndStability/Results/Overview.lean),
with prefix `GenLimit.BreadthCharacterizations.Results`:

| Source item | Reviewed declaration | Reviewed statement scope |
|---|---|---|
| Theorem 3.3 | `theorem_3_3_semantic` | Semantic exact-breadth generatability iff Angluin's condition, for an indexed family of infinite languages over a nonempty countable universe. |
| Theorem 3.8, sufficiency only | `theorem_3_8_sufficiency_semantic` | Weak Angluin's condition implies semantic approximate-breadth generatability, for an indexed family of infinite languages over a countable universe. |
| Theorem 3.15, approximate clause only | `theorem_3_15_approximate_semantic` | Existence of a stable approximate-breadth support generator iff Angluin's condition, for an indexed family of infinite languages over `Nat`. |

The Level 1 scope includes the definitions determining these statements:
indexed language families; complete positive presentations allowing repeated
observations; ordered finite histories and their observed samples;
support-valued generators; exact breadth as support `K \ S_t`;
approximate breadth as support contained in `K` with finite omission;
stability as eventual exact constancy of the raw support; and the strong
and weak finite tell-tale conditions. Approximate breadth does not require
removal of the observed sample.

This record covers the named semantic interfaces, without asserting Turing
computability, executable oracle access, sampling distributions, or rates.
Theorem 3.8's necessity direction, arbitrary-countable-universe transport of
Theorem 3.15, its exact-breadth clause, the separately named whole-target
correction, literal-specification countertheorems, and all other P05 results
are outside this review. Source-conflict findings retain their separate
pending human-review status. Construction correspondence (Level 2) and proof
correspondence (Level 3) are excluded. Capturing fingerprints records the
user's completed review; it is not an additional human review by Codex.

## #06 Noisy Examples: Section 3 theorem specifications

On 13 August 2026, Peng Zhang reported completion of a Level 1 human audit of
Section 3 Theorems 3.1, 3.3, 3.9, and 3.10 of Raman--Raman,
*Generation from Noisy Examples*.  The comparison source was the supplied
`papers/P06_NoisyExamples.pdf`, with SHA-256
`1e2401c4641714a2b2c62c477152551a20f9e68ed7a7d17cb501d020a14b1c99`,
and the audited Lean checkpoint was
`a66d3d0`.

This human record is independent of, and does not replace, the earlier
checksum-pinned ChatGPT Pro statement-faithfulness record in
[`AuditRecords/Paper06_NoisyExamples`](../Paper06_NoisyExamples/).

At Level 1, the human audit checks the assumptions, mathematical objects,
quantifier structure, and conclusions of the four theorem statements.  It
does not claim a human check of their constructions or proof steps.

| Paper result | Lean declaration | Audited specification |
|---|---|---|
| Theorem 3.1 | `GenLimit.NoisyExamples.theorem_3_1` | Under UUS, uniform noise-independent generatability is equivalent to infinitude of the class-wide common intersection. Lean exposes the proof's implicit infinite ambient-universe assumption. |
| Theorem 3.3 | `GenLimit.NoisyExamples.theorem_3_3` | Under UUS, uniform noise-dependent generatability is equivalent to finite noisy closure dimension at every fixed noise level. Lean requires a nonempty example type so a generator can be total. |
| Theorem 3.9 | `GenLimit.NoisyExamples.theorem_3_9` | Ordinary noiseless non-uniform generatability implies noisy generatability in the limit. |
| Theorem 3.10 | `GenLimit.NoisyExamples.theorem_3_10` | A finite cover by uniformly noise-independent generatable classes implies noisy generatability in the limit. Lean exposes the proof's implicit infinite ambient-universe assumption. |

This Level 1 record does **not** cover Definition 3.2, Corollaries 3.4 and
3.7, Lemmas 3.5, 3.6, and 3.8, Algorithm 1, proof-body correspondence,
Appendices A--G, the numerical noisy closure dimension `NC_n`, quantitative
sample complexity, computability, membership-oracle access, or efficiency.
Those remain separate human-audit items even though their current Lean scope
is kernel checked.  In particular, this record does not supersede the broader
AI-assisted audit of every paper-owned qualitative statement.

The audited-revision code anchors are:

| Code anchor | SHA-256 |
|---|---|
| `GenLimit/Paper06_NoisyExamples/UniformIndependent.lean` | `b87b552e3d16664c59c48d09a46d2bcf9ff15231d7a33dfb0036274bd09c8d02` |
| `GenLimit/Paper06_NoisyExamples/NoisyClosure.lean` | `0a4483d7bc1f75180dfc403a14f1c20ec65fba565e41878f4c76ca0bc93dea9c` |
| `GenLimit/Paper06_NoisyExamples/NoiselessRobustification.lean` | `693668f9901754ed65360fa99ab04cfa6b9e8218c24fc4f87ff9b767d8f68667` |
| `GenLimit/Paper06_NoisyExamples/FiniteUnionLimit.lean` | `efa673d181e200bc7899e1e9e1eb51da0efe5137e97cd1fe32fb8c959a1d2d45` |

## #06 Noisy Examples: renewed Section 3 specifications

On 26 September 2026, Shuangping Li completed a Level 1 review of Theorems
3.1, 3.3, 3.9, and 3.10 against [arXiv:2501.04179v2](https://arxiv.org/html/2501.04179v2)
at Lean checkpoint `b03d9575f16edf0c5ea3bc10ff245ad4ad51f912`, with
Codex-assisted statement translations.

The review covers the qualitative specifications and relevant definitions,
retaining occurrence-counted noise, coverage requirements, and explicit
universe assumptions. Construction and proof correspondence, Algorithm 1,
quantitative bounds, and other P06 results are excluded.
The [scoped fingerprint record](Fingerprints/P06_Section3TheoremsLevel1.json)
is current.

## #07 Density Measures: Theorem 2.1, Level 1

On 12 November 2026, Peng Zhang reported completion of a **Level 1** human
paper-to-Lean audit of P07 `theorem_2_1`, explicitly selecting the current
`work/non-p38` tree. This is the reporting date; the completion date was not
separately specified. The working tree is based on
`60620581aa210daec6fa7d3aa65d7f9fdb565b8c` and includes uncommitted changes, including
the current explicit Overview wrapper. The
[scoped fingerprint manifest](Fingerprints/P07_Theorem2_1Level1.json) records the exact
source-file hashes and compiled statement/definition fingerprints; the HEAD
alone does not identify the dirty working-tree snapshot.

The source is Jon Kleinberg and Fan Wei, *Density Measures for Language
Generation*, arXiv:2504.14370v1. The supplied local
`papers/P07_DensityMeasuresForLanguageGeneration.pdf` in the sibling
`language generation lean` workspace has SHA-256
`c17f179bf152196adb8dac7ed88d5001aa0a34554eb37af95578c03bee8afe69`.
Theorem 2.1 is on printed page 8 (PDF page 10); Section 2.1 defines the model
on printed pages 6--7, and footnote 3 on page 8 explains the first-occurrence
convention. The earlier source-comparison PDF hash in the registry and
PaperMap is retained as separate provenance. The supplied PDF was read only;
all audit-record changes are in non-P38.

This is one reviewed theorem, with two presentations:

- Public: `GenLimit.KleinbergWei.DensityMeasures.Results.theorem_2_1` in
  [`Results/Overview.lean`](../../GenLimit/Paper07_DensityMeasuresForLanguageGeneration/Results/Overview.lean).
- Canonical: `GenLimit.KleinbergWei.DensityMeasures.theorem_2_1` in
  [`InfinitelyOften.lean`](../../GenLimit/Paper07_DensityMeasuresForLanguageGeneration/InfinitelyOften.lean).

Their normalized statement types agree. For a `Nat`-indexed language family
`C`, an exact presentation `Presents stream (C z)`, and `FirstOccurrence C z`,
the fixed semantic selector `guessIndex C stream` satisfies both:

1. Eventually every guessed language is contained in the target:
   `IndexValidInLimit C stream z`.
2. At arbitrarily late rounds, the guessed language equals the target:
   `forall t, exists r, t <= r and AccurateAt C stream z r`.

Level 1 includes the indexed-family and exact-presentation definitions,
consistency and finite samples, the first-occurrence convention, validity,
accuracy, and the definitions fixing which selector the statement concerns.
Repeated observations and duplicate family languages are allowed; accuracy
means equality of languages, not necessarily equality of their indices.
The target's first occurrence is an analysis convention, not an input to the
selector. The paper assumes infinite languages globally; this Lean index
statement is more general and does not require that assumption. On the
paper's infinite-language instances it gives the stated index guarantee.
No element-output freshness or density conclusion is asserted by this record.

The selector uses the corrected strict-critical predicate comparing only
with earlier consistent indices. The existing source qualifications remain
recorded in the PaperMap. Fingerprinting selector definitions and supporting
proof-certificate types guards statement meaning; it does not constitute a
Level 2 algorithm-construction comparison or a Level 3 audit of proof bodies,
Claim 3.2's proof repair, or intermediate proof correspondence. Computability,
query/runtime bounds, Corollary 2.2, Theorem 2.4, all density theorems, other
P07 results, and P39's distinct patient-scope algorithm are outside this
review. Earlier LLM audit evidence remains unchanged.

## #08 Hallucination Detection: Theorems 2.1 and 2.3, Level 1

On 12 November 2026, Peng Zhang reported completion of a **Level 1** human
paper-to-Lean audit of P08 `theorem_2_1` and `theorem_2_3` in the current
`work/non-p38` tree. This is the reporting date; the completion date was not
separately specified. The working tree is based on `60620581aa210daec6fa7d3aa65d7f9fdb565b8c`
and includes the uncommitted explicit Overview statements. The
[scoped fingerprint manifest](Fingerprints/P08_Theorems2_1And2_3Level1.json) records
the exact reviewed source-file hashes and compiled statement/definition
fingerprints; the HEAD alone does not identify the working-tree snapshot.

The source is Karbasi, Montasser, Sous, and Velegkas, *(Im)possibility of
Automated Hallucination Detection in Large Language Models*,
arXiv:2504.17004v2. The supplied local
`papers/P08_HallucinationDetection.pdf` in the sibling `language generation lean`
workspace has SHA-256 `a83673838f6bca53fa73a229be814899badad31f87016de5573f96c698a7ec7f`.
Theorem 2.1 is on page 7 and Theorem 2.3 on page 8; the positive-example game
and Definition 1 are on page 5, Definition 2 and its complete labeled-domain
convention on pages 7--8, and Definition 3 on page 19. The historical AI-audit
PDF hash remains unchanged as separate provenance. The supplied PDF was
read only; all audit-record changes are in non-P38.

The two reviewed mathematical statements each have a public and canonical
presentation with the same normalized type:

| Result | Public declaration | Canonical declaration |
|---|---|---|
| Theorem 2.1 | `GenLimit.HallucinationDetection.Results.theorem_2_1` | `GenLimit.HallucinationDetection.theorem_2_1` |
| Theorem 2.3 | `GenLimit.HallucinationDetection.Results.theorem_2_3` | `GenLimit.HallucinationDetection.theorem_2_3` |

The public declarations are in
[`Results/Overview.lean`](../../GenLimit/Paper08_HallucinationDetection/Results/Overview.lean);
the canonical statements are in
[`Reductions.lean`](../../GenLimit/Paper08_HallucinationDetection/Reductions.lean)
and [`NegativeExamples.lean`](../../GenLimit/Paper08_HallucinationDetection/NegativeExamples.lean).

- **Theorem 2.1:** for a nonempty countable type and a `Nat`-indexed family,
  `HallucinationDetectable C` is equivalent to `IdentifiableInLimit C`.
  Detection must eventually give the correct answer to `G ⊆ C z` for every
  exact positive presentation and every candidate set `G`. Identification
  means eventual stabilization to one fixed index denoting the target.
  Repetitions in the presentation and duplicate languages in the family are
  allowed; finite languages are allowed. Empty targets have no positive
  presentation in this no-pause model, so that conditional obligation is
  vacuous. The explicit nonempty-domain specialization is retained.
- **Theorem 2.3:** `DetectableWithNegativeExamples C` holds for every indexed
  family. `IsLabeledEnumeration` requires every domain point to appear at a
  finite position and every Boolean label to equal its true target-membership
  label. A negative example certifies nonmembership in the target, not in `G`.
  The assumption is a complete, correctly labeled domain enumeration, not a
  finite or incomplete collection of negative examples. Lean needs no
  countability/nonemptiness typeclass here because correctness is conditional
  on such an enumeration; unpresentable-domain cases are vacuous.

Both detector interfaces see only finite histories and build finite adaptive
membership-query trees for the fixed candidate set `G`. They do not receive
unrestricted access to its full characteristic function. One detector works
for all targets, presentations, and candidate sets for the given family;
the eventual threshold may depend on those inputs. Semantic, potentially
noncomputable learners and family access remain the documented model.

This records the user's completed statement/definition review. The recursive
definition bodies, finite query-tree constructors, and evaluation machinery
are fingerprinted to preserve the statements' meaning. This is not a Level 2
comparison of Algorithms 1--2 or `negativeExampleDetector`, nor a Level 3
proof audit. Separate reduction lemmas, Corollary 2.2, Appendix results,
Example 1's source error and repair, computational guarantees, query-cost
bounds, probabilistic carry-over, and other P08 claims remain outside this
human audit. Existing immutable LLM evidence is unchanged.

## #09 Representative Language Generation: Theorems 3.3 and 3.7, Level 1

On 12 November 2026, Peng Zhang reported completion of a **Level 1** human
audit of P09 Theorems 3.3 and 3.7 and their relevant definitions in
`work/non-p38`. This is the reporting date; the actual completion date was
not separately specified. At the maintainer's request, the existing P09
changes were first committed as `132a458f9238c1f397c19b7909f5b77013306189`. The reviewed
mathematical source files are exactly those of this commit; adding this
record does not change the theorem statements or their proofs.

The comparison source is Peale, Raman, and Reingold, *Representative Language
Generation*, final ICML 2025 proceedings version, PMLR 267. The supplied
`papers/P09_RepresentativeLanguageGeneration.pdf` in the sibling
`language generation lean` workspace has SHA-256
`647dff8492c32479171e6acb4751a17a084407a39e502ec7ce6dfeebf9a6e61d`,
matching the registry's pinned source. Theorem 3.3 is on page 6, Theorem 3.7
on page 7, and the relevant model and definitions on pages 3--5.

The reviewed public statements are in
[`Results/Overview.lean`](../../GenLimit/Paper09_RepresentativeLanguageGeneration/Results/Overview.lean):

| Result | Reviewed declaration | Statement scope |
|---|---|---|
| Theorem 3.3 | `GenLimit.RepresentativeGeneration.Published.theorem_3_3` | For a nonempty countable domain, a UUS class, a countable partition, and positive tolerance, representative uniform generatability is equivalent to bounded group-closure witness cardinalities. |
| Theorem 3.7 | `GenLimit.RepresentativeGeneration.Published.theorem_3_7` | Representative nonuniform generatability is equivalent to a nondecreasing cover by classes uniformly generatable at each positive tolerance; the cover may depend on the tolerance. |

The record retains the current statement qualifications:

- Theorem 3.3 uses `HasFiniteGroupClosureDimension`, the bounded-witness
  formulation. It does not assert an exact numerical dimension or an optimal
  sample-complexity formula. The explicit nonempty domain, supremum group
  distance, and positive-history convention remain part of the interface.
  Existing LLM findings about the literal scalar definition's zero/infinity
  conventions remain separately recorded; this human record does not turn
  those source-error findings into an independent human certification.
- Theorem 3.7 deliberately exposes a stronger statement than the paper:
  countability of the domain, UUS, and the partition assumptions are absent.
  Its natural-number-indexed groups may overlap or fail to cover the domain.
  Under the paper's assumptions it specializes to the published theorem;
  there is no single cover required to work for every tolerance.
- Representation compares the output distribution with the proportions among
  distinct observations at every positive history length. Consistency means
  probability one on unseen target elements at every subsequent time once
  the distinct-sample threshold is reached. Uniform and nonuniform streams
  need only remain inside the target, rather than enumerate it completely.
  A uniform threshold precedes all targets and streams; a nonuniform
  threshold may depend on the target but precedes its stream.

The [scoped fingerprint manifest](Fingerprints/P09_Theorems3_3And3_7Level1.json) pins
the two theorem types, their recursive project-local defining dependencies,
and source-file hashes. Dependency fingerprinting preserves statement meaning;
it does not add separate human reviews of every supporting declaration.

This records the maintainer's reported statement/definition review. Algorithm
constructions, the threshold-selection proof repair, theorem proof bodies and
proof-step correspondence, effective sampling, computability and complexity,
other numbered results, source-error counterexamples, and corrected Lemma 4.8
and Theorem 4.4 are outside this Level 1 scope. Existing source assessments,
formalization coverage, and immutable LLM evidence are not upgraded.

## Paper10 Union-Closedness: overview theorem specifications

On 13 August 2026, Peng Zhang reported completion of a Level 1 human audit of
overview Theorems 3.1, 3.2, and 3.3 of Hanneke--Karbasi--Mehrotra--Velegkas,
*On Union-Closedness of Language Generation*.  The comparison source was
arXiv:2506.18642v1.

This dated human record is independent of, and does not supersede or duplicate,
the earlier AI-assisted source comparison documented in the
[Paper10 map](../../PaperMaps/Paper10_UnionClosednessOfLanguageGeneration.md).

At Level 1, the human audit checks the assumptions, objects, presentation
semantics, cardinality and generation conclusions of overview Theorems
3.1--3.3.  Theorems 4.1, 4.3, and 4.4 are noted as the source's detailed
presentations of those results, but this record does not claim a separate
human check of the detailed constructions, proof steps, or cross-section
consistency.

| Overview result | Detailed presentation | Lean declaration | Audited specification |
|---|---|---|---|
| Theorem 3.1 | Theorem 4.1 | `theorem_3_1` | Two uncountable non-uniformly generatable classes have a union that is not generatable in the limit under the source's duplicate-free presentation convention. |
| Theorem 3.2 | Theorem 4.3 | `theorem_3_2` | The source orders the countable non-uniform class first and the uncountable uniform class second, and says that neither requires adversary-provided elements. |
| Theorem 3.3 | Theorem 4.4 | `theorem_3_3` | There exists an uncountable non-uniformly generatable class without EUC. |

Separately, the Codex-assisted Lean formalization reported that the class
displayed in Theorem 4.4 is countable and therefore cannot instantiate the
uncountable class required by Theorem 3.3.  Lean uses the first uncountable
class from Theorem 4.1 as `theorem_3_3_witness` and proves directly that it
fails EUC.  This is an AI-assisted formalization finding recorded for
provenance.

This Level 1 record does **not** certify the alternating-recursion proofs,
sweep-generator implementations, cardinality proofs, the proof body of the
common-core calculation, Proposition A.1, randomized Proposition A.2,
Appendix A.2, Remark A.3, computability, or complexity.  Those remain separate
human-audit items even though the checked Lean revision is kernel-verified.

## Paper10 Union-Closedness: renewed overview specifications

On 25 September 2026, Shuangping Li completed a Level 1 review of overview
Theorems 3.1--3.3 against [arXiv:2506.18642v1](https://arxiv.org/html/2506.18642v1)
at Lean checkpoint `d5227a2af277f5448a4afa95e2e8044f3625fb35`, with
Codex-assisted statement translations.

The review covers the specifications and relevant definitions, retaining the
duplicate-free presentation convention, autonomous-schedule interpretation,
infinite-language witnesses, and Theorem 3.3's uncountable-witness qualification.
Construction and proof correspondence and other P10 results are excluded.
The [scoped fingerprint record](Fingerprints/P10_OverviewTheorems3_1To3_3.json)
is current.

## #12 Noise, Loss, and Feedback: all Overview theorems and their definitions, Level 1

On 12 November 2026, Peng Zhang reported completion of a **Level 1** human
audit of every theorem in P12 `Results/Overview.lean`, together with all
definitions used in those statements, in `work/non-p38`. This is the reporting
date; the actual completion date was not separately specified. The reviewed
version is the current working tree based on
`132a458f9238c1f397c19b7909f5b77013306189`, including the uncommitted P12
Overview changes. It is pinned by the source-file hashes in the
[fingerprint manifest](Fingerprints/P12_OverviewTheorems1_1To1_8Level1.json),
not by the base commit alone.

The comparison source is Bai, Panigrahi, and Zhang, *Language Generation in
the Limit: Noise, Loss, and Feedback*, arXiv:2507.15319v2 (5 February 2026).
The supplied `papers/P12_NoiseLossAndFeedback.pdf` in the sibling
`language generation lean` workspace has SHA-256
`04dd3d133ba2b4e9272527e524e1a0a46c37701e1f44b3b13dd8793a83a9cc4c`. This locally resaved PDF has
different bytes from the registry's pinned official PDF
(`ef6dc568b5815b6fe052c5dd52bef89d01a1d7d4eed86e946c368305078c42e5`), but
all 23 extracted page texts match exactly. Both source identities and the
page-text comparison hash are recorded in the manifest. The overview
statements appear on PDF pages 2--3; relevant definitions are in Sections 2,
4, 5, and 6.

All eight reviewed declarations are in
[`Results/Overview.lean`](../../GenLimit/Paper12_NoiseLossAndFeedback/Results/Overview.lean),
under `GenLimit.NoiseLossFeedback.Results`:

| Result | Declaration | Reviewed statement scope |
|---|---|---|
| Theorem 1.1 | `theorem_1_1` | Two classes have the stated nonuniform/uniform generation guarantees with and without samples, but their union is not generatable in the repetition-free sample model. |
| Theorem 1.2 | `theorem_1_2` | Uniform and nonuniform noisy generation are respectively equivalent to uniform and nonuniform generation without samples, for a UUS class over the canonical universe. |
| Theorem 1.3 | `theorem_1_3` | Generation without samples is equivalent to a nondecreasing cover by classes with infinite common intersections. |
| Theorem 1.4 | `theorem_1_4` | The same uniform or nonuniform generator remains correct under arbitrary infinite omissions. |
| Theorem 1.5 | `theorem_1_5` | For each finite budget, one UUS class simultaneously realizes both adjacent omission and adjacent noise separations. |
| Theorem 1.6 | `theorem_1_6` | One class is generatable for every known finite noise bound, with a generator allowed to depend on the bound, but not under an unknown finite amount of noise. |
| Theorem 1.7 | `theorem_1_7` | One class is generatable with a membership query on every round, but not without feedback or with any fixed finite total query budget. |
| Theorem 1.8 | `theorem_1_8` | Every explicitly indexed countable language family over the naturals is nonuniformly identifiable with truthful membership feedback; equality is of languages, not necessarily their indices. |

The Level 1 review explicitly includes **all mathematical definitions used
to interpret these theorem statements**, recursively through their hypotheses
and conclusions and shared project-local definitions:

- languages, language classes, indexed families, and the standing
  infinite-language (`UUS`) convention;
- finite-history generators, repetition-free exact positive enumerations,
  observed input sets, freshness, and uniform/nonuniform/limit quantifiers
  (Definitions 2.1--2.4);
- noisy enumeration and the three noisy-generation predicates
  (Definitions 2.8--2.11), with finitely many distinct extraneous input values;
- injective autonomous generators and uniform/nonuniform generation without
  samples (Definitions 4.1--4.3), and the increasing infinite-core cover;
- infinite omissions and same-generator preservation interfaces
  (Definitions 4.8--4.10), plus bounded finite omissions
  (Definitions 4.13--4.14);
- known finite noise bounds and eventual generation under those bounds
  (Definitions 5.1--5.2);
- mandatory-query feedback and eventual fresh generation
  (Definitions 6.1--6.2), optional-query finite budgets
  (Definitions 6.5--6.6), truthful response execution, and compatible histories;
- feedback identification and target-dependent, presentation-independent
  stabilization (Definitions 6.8--6.9).

The finite feedback budget is uniform over compatible executions and bounds
the total number of queries. Unrestricted feedback makes one query on every
round. All these feedback models continue to receive positive examples.
Noise bounds count bad input values; they do not bound generator mistakes.
No-sample generators have distinct outputs, whereas ordinary freshness is
relative to observed inputs. Theorem 1.1's positive no-sample clauses already
force its witness languages to be infinite.

The scope is the current eight Lean Overview statements and their defining
interfaces. In particular, `Results.theorem_1_7` states the strict separation
witness; the separate general `finiteFeedback_iff_noFeedback` theorem is not
independently reviewed by this record. Theorem 1.8 retains its indexed-family
interface. Existing universe assumptions, semantic qualifications, source
assessments, and proof-repair notes remain in force.

This is the maintainer's reported Level 1 review. It does not certify Level 2
algorithm/construction correspondence, Level 3 proof correspondence, source
proof repairs or counterexamples, effectiveness, runtime, other numbered
theorem statements, or other papers reusing the definitions. Definitions
2.12--2.13 (projection), Definition 5.3 (nonuniform known-noise generation),
and Definitions 5.5--5.6 (maps/isomorphism) are not added merely because they
share a registry card with reviewed definitions. References on mixed cards
cover only the explicitly listed definition endpoints, not their detailed
theorems, algorithms, or proofs. The earlier LLM audit remains separate.

## #13 Pareto-optimal Non-uniform Generation: Overview Theorems 1, 4, 5, 6, and 8, Level 1

On 13 November 2026, Peng Zhang reported completion of a **Level 1** human
audit of all P13 `Results/Overview.lean` theorems except
`theorem_9_representative_endgame`, together with all definitions involved
in the reviewed statements. This is the reporting date; the actual completion
date was not separately specified.

The reviewed non-P38 checkpoint is `9efdb9479980994db77c8443792c74c3302f541c`.
With the user's authorization, the existing P13 Overview comment clarifying
Procedure 2's initialization repair was committed first. That single-file
commit changes no theorem statement or proof. All mathematical source files
covered by the [fingerprint manifest](Fingerprints/P13_OverviewTheorems1_4_5_6_8Level1.json)
match this checkpoint; the human-audit metadata is recorded afterward.

The comparison source is Charikar and Pabbaraju, *Pareto-optimal Non-uniform
Language Generation*, arXiv:2510.02795v1 (3 October 2025). The supplied
`papers/P13_ParetoOptimalNonuniformGeneration.pdf` in the sibling
`language generation lean` workspace has SHA-256
`a9cab95147e30a6dcf652cb56ffa81c7d8b8a3e36de8a8a600601818bb28fcd3`, matching the registry's
pinned source. The separate archived arXiv download has the same extracted
text on all 24 pages; the later PMLR edition is not the review target.

The five reviewed declarations are in
[`Results/Overview.lean`](../../GenLimit/Paper13_ParetoOptimalNonuniformGeneration/Results/Overview.lean),
under `GenLimit.ParetoGeneration.Results`:

| Result | Declaration | Reviewed statement scope |
|---|---|---|
| Theorem 1 | `theorem_1` | For each requested finite prefix, one globally valid generator realizes a positive time vector matching the canonical Procedure-1 vector on that prefix and Pareto-optimal there. |
| Theorem 4 | `theorem_4` | Every monotone unbounded scheduler gives the displayed positive time vector: the maximum of scheduler-entry time and canonical complexity plus one. |
| Theorem 5 | `theorem_5` | Finite canonical-complexity sublevels suffice for a generator realizing the entire canonical positive Pareto-optimal vector. |
| Theorem 6 | `theorem_6` | The concrete noisy scheduler based on corrected Procedure 2 realizes the displayed positive noisy time vector, with empty witnesses and zero complexity when no candidate exists. |
| Theorem 8 | `theorem_8` | Finite noisy-complexity sublevels make the corrected canonical noisy vector realizable and Pareto-optimal. |

The review explicitly includes **all definitions needed to interpret the five
theorem statements**, recursively through their hypotheses, conclusions, and
named concrete functions. This includes:

- indexed language families, finite-history generators, injective observations,
  distinct sample sets, input-relative freshness, positive generation-time
  vectors, and standard/noisy realizability;
- `ParetoOptimal`, coordinate improvement/worsening, `MatchesPrefix`, and
  `PrefixParetoOptimal`;
- finite indexed intersections, candidate and score predicates, the canonical
  Procedure-1 stages, canonical complexity, insertion order, and its zero-score
  convention;
- monotone unbounded schedulers, scheduler-entry time, finite sublevels,
  the displayed maximum time vectors, greedy scans, and the concrete
  `schedulerGenerator` and `noisySchedulerGenerator` definitions;
- noisy exceptions, `NoiseContainedAt`, language/noise coordinates,
  the corrected Procedure-2 candidate/sample/witness definitions, canonical
  noisy complexity, noisy realizable vectors, and `variantCanonicalTime`;
- recursively used shared mathematical definitions, including finite-history
  operators, sequence samples, the finite negative part, and fresh selection.

These definitions are reviewed as part of the meaning of the theorem
statements. Their presence does not separately certify the construction
correctness of Procedures 1--2 or the correspondence of their proofs.

The recorded review retains the current qualifications:

- The source is arXiv:2510.02795v1. This does not automatically review the
  later ALT 2026/PMLR edition or its additional oracle-cost discussion.
- The public Lean statements quantify over arbitrary indexed sets on an
  infinite ambient type. They do not explicitly require every indexed set to
  be infinite; the paper's global infinite-language convention supplies the
  intended source instances.
- The guarantees use injective finite histories, whose length is the number
  of distinct observations. The paper permits repeated observations and
  measures time by distinct inputs, but an arbitrary repeated-history adapter
  is not part of this reviewed theorem surface.
- The noisy interface uses a fixed family of language/noise coordinates and
  counts distinct exceptions in those injective histories. The source's
  `(noise level, language index)` pairs are represented by flattened coordinates
  with repeated language copies and a coordinate-wise noise function. This
  does not certify a separate repeated-input/occurrence-noise adapter.
- Theorems 6 and 8 use the corrected empty-witness/zero-score Procedure-2
  definitions. Their statement and definition review does not independently
  certify the source-error diagnostic or its counterexample proof.
- Generation time is a sample threshold. The functions are classical semantic
  objects; no machine implementation, effective oracle program, or runtime
  bound is included.

The user explicitly excludes `theorem_9_representative_endgame`. Theorem 7,
representative distribution/group-scarcity definitions and Procedure 3,
other numbered results, supporting-lemma correspondence, and all Level 2
construction or Level 3 proof correspondence remain outside this review.
Supporting proof-certificate types are fingerprinted only to preserve the
meaning of the selected definitions. Shared definitions do not confer human
audit credit on other papers. Existing source assessments and formalization
coverage are unchanged; earlier LLM evidence remains separate.

## #14 List Language Identification: Overview Theorems 1 and 2, Level 1

On 13 November 2026, Peng Zhang reported completion of a **Level 1** human
audit of P14 `Results/Overview.lean` Theorems 1 and 2 and all definitions
involved in those statements. The user explicitly corrected the initial
paper label from P13 to P14. This is the reporting date; the actual completion
date was not separately specified.

The reviewed `work/non-p38` checkpoint is `9efdb9479980994db77c8443792c74c3302f541c`.
All five mathematical source files covered by the
[fingerprint manifest](Fingerprints/P14_OverviewTheorems1And2Level1.json) match
this commit. Existing unrelated working-tree changes are not part of this
record; no P14 mathematical source was changed to add it.

The comparison source is Charikar, Pabbaraju, and Tewari,
*A Characterization of List Language Identification in the Limit*,
arXiv:2511.04103v1 (submitted 6 November 2025; title page dated 7 November).
The reviewed local `papers/P14_ListLanguageIdentification.pdf` in the sibling
`language generation lean` workspace has SHA-256
`ec1b3a62c0399e032a20cef01b07abdece54e858bb45c1f18f9ebaeb22e1b8f9`.
Its arXiv-v1 metadata and all 30 pages of extracted text agree with the
archived v1 audit text after removing page markers and whitespace. The local
Quartz-resaved PDF is not byte-identical to the registry's pinned PDF hash
`fdc00078c5ca6f2794005d608ebae5c46a7b5f012e5a200891e10cfd1f4a32d4`;
both identities are retained in the manifest without changing the source edition.

The two declarations are in
[`Results/Overview.lean`](../../GenLimit/Paper14_ListLanguageIdentification/Results/Overview.lean),
under `GenLimit.ListIdentification.Results`:

| Result | Declaration | Reviewed statement scope |
|---|---|---|
| Theorem 1 | `theorem_1` | For a presentable indexed family, semantic `k`-list identifiability is equivalent to the recursive `k`-Angluin condition. |
| Theorem 2 | `theorem_2` | For the same interface, semantic `k`-list identifiability is equivalent to a cover by `k` relative-Angluin subcollections. |

The review includes **all definitions needed to interpret both theorem
statements**, recursively through their hypotheses and conclusions:

- shared `Language`, `LanguageFamily`, `Stream`, `Presents`, and
  `FiniteHistoryOperator` definitions;
- `ListIdentifier`, `listOutput`, `TargetInGuess`, `IdentifiesFrom`,
  `ListIdentifies`, and `ListIdentifiable` (source Definitions 1--2);
- `Psi` and `KAngluinCondition`, including finite tell-tales, strict
  sublanguages, the depth-zero convention, and the recursive successor
  clause (source Section 4, equations (4)--(6));
- `IsRelativeTellTale`, `RelativeConditionTwo`, `CoversAllIndices`, and
  `HasAngluinStratification` (the relative Angluin and union-of-layers
  interface used by Theorem 2).

The manifest guards the two theorem types and all 18 recursively used
project-local definitions, including the generated `Psi.match_1` helper:
38 type/value anchors across five source files. Definitions are reviewed for
their mathematical meaning; this is not a Level 2 construction or Level 3
proof-correspondence audit.

The review retains the existing correspondence qualifications:

- The source assumes a countable universe and nonempty languages, which may
  be finite or infinite. Lean uses an arbitrary type with decidable equality
  and explicitly requires an exact positive presentation of each indexed
  language. This supplies the needed countability/nonemptiness at the
  language level without imposing a global infinite-language hypothesis.
- `Presents stream L` means `Set.range stream = L`: every input is in the
  target and every target element eventually appears. Repetitions are
  permitted. Lean's zero-based finite-prefix convention does not change
  the eventual guarantee.
- Output is a fixed-width `Fin k -> Nat` tuple of family indices. At each
  sufficiently late time, some slot denotes a language extensionally equal
  to the target. The successful slot/index may vary; neither whole-list
  stabilization nor eventual stabilization to one index is required.
- The source takes `k >= 1`; Lean also defines the zero-width case. For a
  presentable indexed family, both sides of either equivalence are false
  at zero. The tell-tale size is only required to be finite, not bounded
  by `k`.
- Theorem 2 is exposed as a cover by exactly `k` sets of family indices,
  each satisfying Angluin's condition relative to that layer. This retains
  the existing qualification connecting relative Angluin layers with
  ordinary identifiability under presentability. Layers need not be
  disjoint and may be empty or repeated; duplicate indices for equal
  languages are allowed.
- These are classical semantic existence statements, matching the source's
  unrestricted list-valued-function model. No effective computation,
  extracted program, runtime bound, or restricted-oracle guarantee is added.

Detailed Theorems 6 and 7 are not separately credited as human-audited
statements merely because their proofs establish these Overview results.
Algorithm 1, the lower-bound/locking argument, the peeling construction,
all proof bodies, statistical Theorem 3, and the remaining probabilistic/rate
results are outside this Level 1 scope. Shared definitions do not grant
human audit credit to other papers. Existing source assessments and
formalization coverage remain unchanged, and earlier LLM evidence is separate.
P14 has no standalone definition claim cards; this definition review is
recorded with the two theorem cards, ledger, and fingerprint manifest.

## #15 Partial Enumeration: all Overview Theorems 1.5, 1.7, 1.8, and 1.9, Level 1

On 13 November 2026, Peng Zhang reported completion of a **Level 1** human
audit of **all theorems declared in P15 `Results/Overview.lean`** and all
definitions involved in those statements. These are Theorems 1.5, 1.7, 1.8,
and 1.9. This is the reporting date; the actual completion date was not
separately specified.

At the user's authorization, the existing P15 Overview/Supporting
reorganization and its PaperMap update were committed first as
`d294766f6749c23ae5a11e866fb7916175d2927f` on `work/non-p38`.
The four public statements delegate to existing canonical proofs. The
targeted P15 Overview build and one full Lean build passed before the commit.
All mathematical files covered by the
[fingerprint manifest](Fingerprints/P15_OverviewTheorems1_5_1_7_1_8_1_9Level1.json)
match this checkpoint. Audit metadata was added afterward.

The comparison source is Kleinberg and Wei, *Language Generation and
Identification From Partial Enumeration: Tight Density Bounds and
Topological Characterizations*, **arXiv:2511.05295v1**, submitted 7 November
2025 (the PDF title page is dated 10 November 2025). The local
`papers/P15_PartialEnumeration.pdf` in the sibling `language generation lean`
workspace has SHA-256
`a33b59725302753cefee10d33d93c9c7b0f7215b1f4858abc8fce532234c5d7b`,
matching the registry-pinned source. All 46 extracted pages agree with the
archived v1 text after removing page markers and whitespace.

The four public declarations are in
[`Results/Overview.lean`](../../GenLimit/Paper15_PartialEnumeration/Results/Overview.lean),
under `GenLimit.KleinbergWei.PartialEnumeration.Results`:

| Result | Public declaration | Equivalent canonical endpoint | Reviewed statement scope |
|---|---|---|---|
| Theorem 1.5 | `theorem_1_5` | `theorem_2_1` | The fixed semantic finite-scope generator eventually outputs target members fresh from the observed history, on every exact presentation of an infinite target subset. |
| Theorem 1.7 | `theorem_1_7` | `theorem_1_7` | The fixed finite-scope semi-index has an infinite denoted intersection at every round and an eventually target-contained intersection. |
| Theorem 1.8 | `theorem_1_8` | `theorem_1_8` | The concrete raw-index Algorithm-1 run gives semi-index generation and contains the whole enumerated subset at arbitrarily late rounds. |
| Theorem 1.9 | `theorem_1_9` | `FullTopology.theorem_4_9_fullText` | For a class of nonempty natural-number languages, causal language-valued full-text identification is equivalent to countability and the full-enumeration TD property. |

The four public/canonical pairs have identical normalized statement-type
fingerprints. The registry's Theorem 4.9 card records the same source result
as Overview Theorem 1.9; it is counted once.

The review includes **all definitions needed to interpret all four Overview
theorems**, recursively through their hypotheses, conclusions, and named
functions. This includes:

- indexed natural-number languages, streams, exact positive presentations,
  observed sample sets, finite-history learners, target validity, and
  input-relative freshness;
- `GeneratesFromPartialEnumeration`, `FreshGeneratesInLimit`, consistency,
  finite prefix intersections, admissible scopes, `selectedScope`,
  `selectedIntersection`, `freshOutput`, and the shared fresh-selection body;
- finite semi-indices and `intersectionOf`, `selectedIndices`,
  `SemiIndexGenerates`, and `SemiIndexTraceGenerates`;
- the named `algorithmOneIndices`/`algorithmOneChosen` recursion, consistency
  chain states, the identified-intersection state, Rule-2 candidate/maximality
  predicates, and the totalized reset selection that determine the meaning
  of Theorem 1.8's fixed witness;
- `IdentifiableOnFullTexts`, the shared language-valued
  `ExtensionallyIdentifiable`/`ExtensionalIdentifies` interface, causal
  finite-history learners, ordered prefixes, and eventual stabilization;
- `FullTopology.Point`, `basicOpen`, `FullOpen`, `TDPoint`, and `TDSpace`:
  finite positive evidence and open neighborhoods separating a language
  from its proper class sublanguages.

The manifest guards 57 declarations with 100 type/value anchors, including
43 defining bodies, the four Overview types, their four equivalent canonical
types, generated helpers, and supporting proof-certificate types. Seventeen
source files are hashed, including the `Results.Supporting` import facade.
Guarding a proof-certificate type does not review its proof; guarding a named
function for statement meaning does not separately certify that its
construction follows the paper's algorithm.

The recorded review retains the current correspondence boundaries:

- The generation statements use a countably indexed family of infinite
  languages over `Nat`, with `Presents stream E`, `E.Infinite`, and
  `E` contained in the target. The observed infinite subset need not be a
  member of the family. Exact positive presentations allow repetitions;
  eventual correctness is quantified over every such compatible stream.
- Theorems 1.5 and 1.7 expose fixed semantic finite-scope witnesses. Their
  definitions are part of this Level 1 scope, but no round-for-round
  identity with the source's displayed three-case algorithm is asserted.
- Theorem 1.8 uses the documented uncompressed raw-index realization of
  Algorithm 1. Eliminated indices can introduce stuttering rounds, and the
  early zero-reset case is totalized at the first positive scope. The review
  retains these conventions without claiming exact compressed-trace
  correspondence. Its containment guarantee is infinitely often, not
  eventually at every round.
- Theorem 1.9, restated as source Theorem 4.9, uses arbitrary set-classes of
  nonempty `Nat` languages, permitting finite languages as well. The source's
  standing infinite-language model supplies such instances. The learner
  returns a language as a function of its finite ordered input history;
  countability is a conclusion, not hidden in an indexed representation.
  Correctness means eventual equality to the target on every exact full text.
- `TDSpace` is expressed using full-open neighborhoods isolating a language
  from its proper sublanguages, the equivalent pointwise form of the source's
  closed punctured-singleton-closure condition. The existing proper-sublanguage
  interpretation of the source's malformed tell-tale display is retained;
  the source-error diagnostic and its proof are not separately human-audited.
- The formalization is classical and semantic. These records make no new
  computability, restricted-oracle, runtime, or query-complexity claim.

Only the four theorems declared in the current `Results/Overview.lean` are
included. Importing `Results.Supporting` does not include its other endpoints
in this review. In particular, the conditional density endpoints for
Theorems 3.1 and 3.5 / main Theorem 1.6, Corollaries 4.10--4.11 (including the
partial-text counterexample), and the unformalized partial-enumeration
topology Theorems 1.10--1.11 / 4.12--4.13 remain outside scope. Level 2
construction correspondence, Level 3 proof correspondence, and other
supporting-lemma/source-error proofs are not reviewed by this record.

The canonical source-numbered endpoints listed above represent the same four
reviewed statements, not additional human-reviewed claims. Other papers using
the shared definitions receive no automatic human credit. P15 has no separate
definition claim cards; definition review is recorded with these four theorem
cards, this ledger, and the manifest. Existing source assessments and partial
formalization coverage remain unchanged; earlier LLM evidence is separate.

## #17 Infinite Contamination: all Overview theorems and their definitions, Level 1

On 13 November 2026, Peng Zhang reported completion of a **Level 1** human
audit of **all nine theorems declared in P17 `Results/Overview.lean`** and
**all definitions involved in those statements**. This is the reporting
date; the actual completion date was not separately specified.

The reviewed version is the **current non-P38 working tree based on
`d294766f6749c23ae5a11e866fb7916175d2927f`**, including its uncommitted P17
Overview/Supporting organization, `CanonicalExpansion.lean`, the current
`ElementDensity.lean` transfer, and shared `Core/CanonicalDensity.lean`.
It is not identified by the base commit alone. The
[fingerprint manifest](Fingerprints/P17_AllOverviewTheoremsLevel1.json)
pins the exact reviewed file bytes and semantic anchors. No commit or push
was requested for this record.

The source is Mehrotra, Velegkas, Yu, and Zhou, *Language Generation with
Infinite Contamination*, **arXiv:2511.07417v1 (10 November 2025)**.
The local `papers/P17_InfiniteContamination.pdf` in the sibling
`language generation lean` workspace has SHA-256
`e1ef3e6d24cc382782446f24cb4377b885034812d3d678cf8d9789a703f5e0a9`, matching the registry-pinned artifact.
Its base-page text agrees with the 71-page official v1 PDF (SHA-256
`6a791bc54891ba447fbf391db9f84927dbe20231a310cfee821760f7aafa9760`)
on all normalized pages. Annotation payloads are not source mathematical
evidence; the differing PDF byte hashes are retained, not equated.

The public declarations are in
[`Results/Overview.lean`](../../GenLimit/Paper17_InfiniteContamination/Results/Overview.lean)
under `GenLimit.InfiniteContamination.Results`:

| Result | Public declaration | Reviewed statement scope |
|---|---|---|
| Theorem 5.1 | `theorem_5_1` | Existence of an element generator for every indexed infinite-language family, under vanishing noise and arbitrary omissions. |
| Theorem 5.4 | `theorem_5_4` | Constant-noise generation is equivalent to the finite-subcollection condition, for an explicitly enumerated infinite-language class and 0 < c < 1. |
| Theorem 6.1 | `theorem_6_1` | The named finite-expansion Algorithm-5 generator eventually produces infinite fresh valid sets and attains set-based upper density at least 1 - c. |
| Theorem 6.4 | `theorem_6_4` | The explicit two-language witness rules out any upper-density guarantee strictly above 1 - c, for 0 < c < 1. |
| Theorem 6.5 | `theorem_6_5` | Infinite-set generation with lower density under finite contamination is equivalent to the pairwise finite-difference density condition. |
| Theorem 6.11 | `theorem_6_11` | The vanishing-noise set-density characterization for explicitly indexed infinite languages and supplied target orders. |
| Theorem 6.14 | `theorem_6_14` | The constant-noise set-density characterization on 0 < c < 1 and positive rho; the source c = 1 endpoint is outside the statement. |
| Theorem 6.18 | `theorem_6_18` | The conditional finite-expansion transfer for element-density guarantees, using internally constructed canonical natural-number orders and internally proved finite-change density invariance. |
| Theorem 7.8 | `theorem_7_8` | The named Algorithm-9 set generator is eventually fresh and valid and each sufficiently late output set has lower density at least (1 - epsilon) / M under vanishing noise and bounded displacement. |

The Level 1 scope includes all definitions needed to interpret these nine
statements, recursively through hypotheses, conclusions, and named functions:

- languages, indexed families, `OracleFamily`, streams, finite histories,
  sample sets, exact presentations, element/set generators, and output sets;
- element freshness from both observed inputs and earlier generated elements,
  set freshness from observed inputs, eventual validity, and the global
  every-history requirement in `IsInfiniteSetGenerator`;
- occurrence noise counts/rates, finite/vanishing/eventually constant noise,
  finite/arbitrary omissions, `OmissionsAtMost`, and the combined presentation
  predicates, including the relevant injectivity requirements;
- ordered languages, canonical enumerations, spatial lower/upper density,
  set-based time liminf/limsup density, and the language of element outputs;
- finite subcollection intersections and the generation/dense-set conditions;
- finite-expansion coding and languages, `finiteExpansionOracleFamily`,
  `canonicalFamilyOrders`, and the shared canonical natural-order interfaces;
- the Algorithm-5 and Algorithm-9 named generator definitions and their
  recursively used consistency, priority, prefix, cutoff, threshold, and
  finite-sample deletion definitions; the explicit floor-increment witness
  used in Theorem 6.4;
- canonical rank, bounded displacement, and the density parameters appearing
  in Theorem 7.8.

The manifest guards **138 declarations**, including **106 definition bodies**,
using **244 type/value anchors** and hashes of **25 source files**. The nine
canonical endpoint types are guarded alongside the nine public types as
equivalent presentations of the same reviewed statements. Eight pairs have
identical normalized type hashes; Theorem 6.18 uses the definitionally equal
`GenLimit.Presents`/`GenLimit.Generic.Presents` aliases, checked by Lean while
retaining both distinct hashes. Supporting
proof-certificate types and generated helpers occur only as semantic guards;
their proofs are not reviewed. Algorithm definitions are included for
statement meaning, without separate Level 2 construction correspondence.

The recorded scope retains these qualifications:

- Countable language collections are supplied by explicit natural-number
  enumerations, with every member infinite. The development is classical and
  semantic; no ordinary computability, restricted-oracle implementation,
  runtime, or query-complexity certification follows from this review.
- The relevant noise/omission enumerations are injective. The exact `Presents`
  premise in Theorem 6.18 permits repetitions, while its finite-contamination
  conclusion has the stated injective-enumeration convention. Rates count
  observed positions; omission density concerns elements ever observed.
- Set-based upper/lower density uses time limsup/liminf of the spatial lower
  density of each output set. Theorem 6.1's upper-density guarantee differs
  from Theorem 7.8's bound on every sufficiently late output set. Supplied
  `OrderedLanguage` values and carrier equalities remain explicit.
- Theorems 5.4, 6.4, and 6.14 retain their stated parameter restrictions.
  Theorem 6.14 does not cover c = 1. This record does not certify the separate
  source-error explanation for that endpoint, nor assert it mathematically
  impossible. The definitions and the displayed restricted statement are
  the reviewed interface.
- Theorem 6.18 is the current canonical-order transfer: the old external
  measure-compatibility assumption has been removed by the formalization,
  and canonical orders/finite-change invariance are provided internally.
  Its premise still supplies a generator with the specified vanilla
  guarantees for every finite expansion. This review does not turn it into
  an unconditional numerical-density corollary or review the supporting
  canonical-order construction proofs.
- Algorithm 9 deletes the observed finite sample from the output set for
  freshness. The named definitions are reviewed as part of the statement;
  exact step-by-step correspondence with paper pseudocode and the proof of
  density preservation are not separately certified.

Only the nine theorems declared in the current `Results/Overview.lean` are
included. Importing `Results.Supporting` does not extend human review to its
Theorem 6.15, Corollary 6.16, Proposition 7.4, Lemma 7.5, or other supporting
results. Numerical Corollary 6.20, Theorem 6.21, the other Section 7 bounds,
Appendix B results, and source-error diagnostic proofs remain outside scope.
Grouped claim cards receive credit only for their reviewed component: e.g.
Theorem 6.5 does not independently certify Lemma 6.9, and reviewing the
Definition-11 term used by Theorem 7.8 does not audit Proposition 7.4/Lemma 7.5.
No Level 2 construction review, Level 3 proof correspondence, cross-paper
review, or renewal of historical `needs-review` scopes is inferred. Existing
formalization coverage, source assessments, and LLM audit evidence remain
separate and unchanged.

## #19 Effect of Noise: all Overview theorems and their definitions, Level 1

On 13 November 2026, Peng Zhang reported completion of a **Level 1 human
audit of all four P19 Overview theorems (2.16--2.19) and all definitions
involved in their statements**. This is the reporting date; the actual
completion date was not separately specified.

The record applies to the **current non-P38 working tree based on
`d294766f6749c23ae5a11e866fb7916175d2927f`**, with exact reviewed bytes pinned by
the [fingerprint manifest](Fingerprints/P19_AllOverviewTheoremsLevel1.json). It is not an assertion that
the whole working tree equals the base commit. No commit or push is included.

The source is Li and Zhang, *Characterizing the Effect of Noise in Language
Generation in the Limit*, **arXiv:2601.21237v2 (1 June 2026)**. The supplied
17-page local `papers/P19_EffectOfNoise.pdf` in the sibling workspace has
SHA-256 `e02e71896533933188b7c405c57a06698221af6ba598ed1d90b841b675ae804b`, matching the registered artifact.
Its 17 normalized base-page texts match the official versioned PDF with
SHA-256 `91a94905872920a960e6686cc5f13c18911c718f25f02507ab42fda54aa9a9cd`.
The different PDF bytes remain distinguished; annotation payloads are not
source mathematical evidence.

The reviewed public declarations are in
[`Results/Overview.lean`](../../GenLimit/Paper19_EffectOfNoise/Results/Overview.lean),
under `GenLimit.QuantifyingNoise.Results`:

| Source result | Public declaration | Reviewed statement scope |
|---|---|---|
| Theorem 2.16 | `theorem_2_16` | For infinite-language classes over a countable nonempty universe, every positive finite noise level is equivalent to level one, for both uniform and nonuniform generation. |
| Theorem 2.17 | `theorem_2_17` | Existence of a class on the literal source universe Nat × Nat that is uniformly generatable without noise but not nonuniformly generatable with one noisy value. |
| Theorem 2.18 | `theorem_2_18` | Finite level-one noisy-closure dimension, uniform generation at every positive finite level, and one noise-dependent uniform generator are equivalent; a noiseless/noisy separating class on Nat × Nat is also asserted. |
| Theorem 2.19 | `theorem_2_19` | A monotone countable exhaustion by classes of finite level-one noisy-closure dimension, nonuniform generation at every positive finite level, and one noise-dependent nonuniform generator are equivalent; a separating class on Nat × Nat is also asserted. |

The review includes all recursively statement-relevant project definitions:
languages and arbitrary language classes, streams and finite-history generators,
`AllLanguagesInfinite`, injective target-covering enumerations with finitely many
distinct outside values, sample sets and inclusive observation/output timing,
`CorrectAt`, fixed-noise uniform/nonuniform predicates, their noise-dependent
versions, noisy consistency and common-core/closure, finite noisy-closure
witnesses and dimension, monotone countable finite-dimension exhaustions,
and the `PaperColumnPoint = Nat × Nat` universe.

The exact fingerprint manifest guards **38 declarations** (the four public
theorem types and **34 definition bodies**) with **72 type/value anchors**,
and pins **10 source files**. Standard Lean/Mathlib foundations are the external
dependency boundary; this is not a review of their implementation or proofs.

The recorded Level 1 scope retains the following conventions and limits:

- Presentations are injective, cover every target element, and have at most
  the specified number of distinct outside values. Repeated streams and
  omission/noise models from other papers are not substituted.
- At paper time t, the generator sees the inclusive prefix x0,...,xt.
  Correctness means target membership and freshness from that sample;
  freshness from the generator's own earlier outputs is not required here.
- A uniform threshold is chosen before target and presentation. A nonuniform
  threshold may depend on the target but precedes the presentation. A
  noise-dependent generator is chosen once before every natural noise level,
  including zero; only its convergence bounds depend on that level.
- The arbitrary input class is not assumed countable. The explicit
  `[Countable α]` and `[Nonempty α]` concern its universe. Theorem 2.19's
  countable exhaustion does not assert each layer or the whole class countable.
- The generic equivalences assume `AllLanguagesInfinite C`. The displayed
  existential separation clauses of 2.17--2.19 do not separately conjoin
  `AllLanguagesInfinite` for their witness. This record covers the actual
  public statements and definitions, without silently strengthening their
  displayed existential types or granting a separate review to native witness
  facts merely because their proofs are used.
- This is a semantic/classical formalization. No extracted executable,
  ordinary-computability, oracle-query or runtime guarantee is certified.
  In particular, the rejected-iteration Algorithm 1 construction used by
  the proof of 2.17 does not receive an independent Level 2 review here.

Only the four theorems declared in the current `Results/Overview.lean` are
covered. Other supporting lemmas, construction/proof bodies, source-error
diagnostics, other source editions, and independent P06 or other-paper claims
are not newly audited. Reviewing shared definitions does not renew unrelated
historical `needs-review` scopes. Formalization/source assessments and LLM
evidence remain separate and unchanged.

## #21 On Generation in Metric Spaces: arXiv v2, Level 1

On 1 November 2026, Peng Zhang reported completion of a Level 1 human audit
of **all theorems in P21's `Results/Overview.lean`**, and explicitly identified
that file as the reviewed scope. This is the reporting date; the actual audit
completion date was not separately specified. The reviewed source checkpoint is
`7bdc13736355fe247f1b17020625bb60f8056afa`.

The comparison source is *On Generation in Metric Spaces*,
arXiv:2602.07710v2, with original unannotated PDF SHA-256
`b4e14e33fce18aa5d970a49d4886a647d9de888e8de29fab12ff8cda0afacfbc`.
The [paper map](../../PaperMaps/Paper21_GenerationInMetricSpaces.md) records
representation choices, generalized interfaces, and source-proof adaptations.

The Level 1 scope comprises 20 source-facing statements in
[`Results/Overview.lean`](../../GenLimit/Paper21_GenerationInMetricSpaces/Results/Overview.lean):

- Theorems 3.1, 3.3, 3.5, 4.1, 4.2, 4.4, 4.6, 4.7, and 4.10;
- Corollaries 3.2, 3.4, and 4.3;
- Proposition D.1;
- Examples 4.5, 4.8, 4.9, 4.11, and B.3;
- Lemmas C.1 and C.2.

Statement applicability includes the definitions that give these statements
their meaning: the finite-history generator and presentation interfaces,
closed neighborhoods, ambient and internal covers, scale-closure witnesses,
UUS, the three generation predicates, doubling and Lipschitz domination,
and the concrete sets, metrics, and displayed generator occurring in the
example statements. The conditional-generation and threshold-reachability
conventions documented by the facade remain explicit.

The [Level 1 fingerprint manifest](Fingerprints/P21_V2OverviewLevel1.json)
guards the 20 statement types and their project-local defining dependencies.
Supporting proof-certificate types are guarded only to preserve the meaning
of definitions; this is not a separate human audit of every dependency.
Theorem proof bodies and proof-step correspondence, construction-level
verification as a separate Level 2 audit, executable implementations,
computability and complexity, and source items absent from the Overview
(including standalone Lemma 2.1 and the orthogonal covering estimate) are
outside the recorded scope. This record documents the user's completed
human audit; creating fingerprints is a mechanical maintenance step.

## #22 Language Generation with Replay: Theorems 4.1, 5.1, 6.1, 6.6, and 7.3, Level 1

On 12 November 2026, Shuangping Li completed a Level 1 review of the P22
Overview statements of Theorems 4.1, 5.1, 6.1, 6.6, and 7.3 against
arXiv:2603.11784v2 (pinned PDF SHA-256
`336e313632cd6f63da3965bfcb18fe3c40be3d6556433f654054c6249e19f325`) at Lean
checkpoint `60620581aa210daec6fa7d3aa65d7f9fdb565b8c`, with AI-assisted
statement translations.

The reviewed declarations are in
[`Results/Overview.lean`](../../GenLimit/Paper22_LanguageGenerationWithReplay/Results/Overview.lean),
under `GenLimit.Replay.Results`:

| Paper item | Reviewed declaration | Statement scope |
|---|---|---|
| Theorem 4.1 | `theorem_4_1` | Uniform generation and uniform generation with replay are equivalent at every positive threshold `d`; no UUS assumption is needed. At `d = 0` the replay predicate is vacuous, so `0 < d` is required. |
| Theorem 5.1 | `theorem_5_1` | The explicit class `nonuniformHardClass` on `Sum ℕ ℕ`, standing for the source's nonzero integers, separates non-uniform generation from non-uniform generation with replay. The Lean class also contains `cutoffLanguage 0`, which does not affect the separation. |
| Theorem 6.1 | `theorem_6_1` | Every indexed family of infinite languages with a Boolean membership oracle over a countable domain is generatable in the limit with replay. |
| Theorem 6.1, membership-query form | `theorem_6_1_finite_query` | On the normalized `ℕ` universe, one carried-cutoff Witness Protection generator succeeds for every oracle family, and each round is determined by a valid finite answered-query cache. No Mathlib `Computable` claim is made. |
| Theorem 6.6 | `theorem_6_6` | Some uncountable UUS class on `Sum ℤ ℕ` is generatable in the limit but not with replay. |
| Theorem 7.3 | `theorem_7_3` | Some four-member family of infinite subsets of `ℤ` is not properly generatable in the limit with replay. |

Level 1 includes the definitions that give these statements their meaning:
the finite-history generator, stream, sample, and correctness interfaces, UUS,
the ordinary and replay generation predicates, replay sequences and
enumerations, proper generation, indexed oracle families, and the Witness
Protection state, run, and finite-query-trace definitions named by the
membership-query form of Theorem 6.1.

Theorem 7.1 is excluded. `Theorem71Statement` is a fair rendering of the
source statement, but it is not proved. The premise of
`theorem_7_1_of_algorithm3`, `Algorithm3UniversalConstructionStatement`,
holds vacuously whenever `Theorem71Statement` does, so the two are logically
equivalent and the reduction is not evidence for Theorem 7.1. The
[fingerprint manifest](Fingerprints/P22_V2OverviewLevel1.json) guards the six
reviewed statement types and their recursive project-local defining
dependencies. Construction and proof correspondence, Theorem 7.1 and its
diagnostic, and other P22 statements are outside this record.

## #23 Banach Density, Topology, and Geometry: arXiv v2 Overview Claims, Level 1

On 13 November 2026, Shuangping Li completed a Level 1 review of the eight P23
Overview claim statements against arXiv:2604.02385v2 (pinned PDF SHA-256
`c884ae86bdb9510c752b26cd5962ea94fb548885672b3cb0d24a2c2ab31cad3d`) at Lean
checkpoint `60620581aa210daec6fa7d3aa65d7f9fdb565b8c`, with AI-assisted
statement translations. The P23 module and its shared
`Support/KleinbergWei` topology are unchanged between that checkpoint and
the fingerprint baseline `43a61da`.

The reviewed declarations are aliases in
[`Results/Overview.lean`](../../GenLimit/Paper23_BanachDensityTopologyAndGeometry/Results/Overview.lean),
under `GenLimit.KleinbergWei.Banach.Results`:

| Paper item | Reviewed declaration | Statement scope |
|---|---|---|
| Definitions 3.1--3.2 and Claim 3.3 | `claim_3_3` | For window bounds `g ≤ f` (nondecreasing, values in `ℕ ∪ {∞}`, all at least `1`), the lower `f`-window density of any set is at most its lower `g`-window density. Densities are valued in `ℝ≥0∞`; window starts satisfy `m ≥ 1`. |
| Claim 3.5 | `claim_3_5` | Lower Banach density equals the infimum of the lower window densities over all window bounds. Attainment by the constant-`⊤` bound is the separate library lemma `lowerWindowDensity_top`. |
| Perfect-tower definition and Claim 3.6 | `claim_3_6` | A member of the collection is a limit point of the containment topology exactly when it is the terminal language of an infinite perfect tower. The supplied enumeration only excludes the empty terminal language, where both sides fail; the collection need not be countable. |
| Claim 4.4 and Appendix Claim 7.1 | `claim_4_4`, `claim_7_1` | For nondecreasing `f : ℕ → ℕ`, niceness is equivalent to unboundedness. Lean's zero-based niceness allows `T = 0` and window length `0`; the paper-literal variant (`T > 0`, `k_i ≥ 1`) is equivalent for nondecreasing `f`. |
| Claim 4.11, repaired | `claim_4_11_repaired` | In a collection of finite Cantor--Bendixson rank, a sequence of proper subsets of `K` that eventually contains every element of `K` eventually has rank strictly below the rank of `K`. The printed claim omits `J_j ≠ K` and is false for the constant sequence; ranks are finite only. |
| Claim 4.18 | `claim_4_18` | The cardinality bound `|C| ≤ r` on prefix-LCA change indices, in any meet-semilattice with a strictly monotone natural depth bounded by `r` at the first vertex. The ancestor-chain part is the separate lemma `claim_4_18_monotone_ancestral_chain`. |
| Claim 4.20 | `claim_4_20` | Under Mathlib's rooted-tree classes (`SemilatticeInf`, `PredOrder`, `IsPredArchimedean`), some adjacent pair of any sequence of at least two vertices has the overall LCA. |

Level 1 includes the definitions that give these statements their meaning:
the window count, ratio, minimum, and lower window and Banach densities;
window bounds; the containment topology, basic neighborhoods, limit points,
and finite Cantor--Bendixson derivatives and ranks; perfect and convergent
proper towers; niceness and unboundedness; and the prefix-LCA and
change-index definitions.

Theorems 4.1, 4.5, 5.1, 5.5, 5.8, and 5.9 and their corollaries are not
formalized and have no Overview declaration, so they are outside this record.
Audit probes compiled during the review, outside the library, confirm that Claim 3.6 holds without the
enumeration hypothesis, that the paper-literal niceness notion is equivalent
to the Lean notion for nondecreasing `f`, and that Claim 4.20 applies to every
Mathlib `RootedTree`; all eight declarations use only `propext`,
`Classical.choice`, and `Quot.sound`. The
[fingerprint manifest](Fingerprints/P23_V2OverviewLevel1.json) guards the
eight reviewed statement types and their recursive project-local defining
dependencies. Construction and proof correspondence and other P23 statements
are outside this record.

## #27 Language Generation with Feedback: Section 3 results, Level 1

On 13 November 2026, Shuangping Li completed a Level 1 review of twelve P27
Overview statements against the ICML 2026 OpenReview PDF `jvfXyIcQ8a`
(pinned SHA-256
`e3467ab76be2eae001490a43e461865d2c704633e2656bd05ff2eb477b4b1319`) at Lean
checkpoint `a19851f908fe806a616767988f93016c1768ef48`, with AI-assisted statement translations. The P27 module
is unchanged since `a04b759`.

The reviewed declarations are in
[`Results/Overview.lean`](../../GenLimit/Paper27_FeedbackQueriesAndMistakes/Results/Overview.lean),
under `GenLimit.FeedbackQueries.Results`:

| Paper item | Reviewed declaration | Statement scope |
|---|---|---|
| Theorem 3.1 | `theorem_3_1` | Over a countable infinite universe, a class of infinite languages is generatable by an element-valued generator with truthful mistake feedback exactly when it has a countable inner cover. |
| Theorem 3.2 | `theorem_3_2` | Set- and element-valued mistake-feedback generation are equivalent. The set-valued feedback bit judges the first output element in one fixed injection of the universe into `ℕ`, a specialization of the source's arbitrary canonical order. |
| Theorem 3.3 | `theorem_3_3` | Some class over `ℕ` is generatable with one membership query per round by an element-valued generator but by no set-valued generator. The witness is outside Level 1. |
| Theorem 3.4 | `theorem_3_4` | Set-valued generation with one membership query per round is equivalent to having a countable inner cover. |
| Corollary 3.6 | `corollary_3_6` | Countable unions preserve element-valued mistake-feedback generation and set-valued query-feedback generation. |
| Corollary 3.7 | `corollary_3_7` | Both models remain generatable with zero examples. As in the source, the zero-example success condition is only `z_n ∈ K`; under this literal reading the mistake-feedback half holds for every class of nonempty languages, so its content lies in the query half. |
| Corollary 3.8 | `corollary_3_8` | Eventually correct mistake and query feedback are both characterized by countable inner covers. Lean requires success on every sample stream, not only enumerations of the target, which strengthens the sufficiency direction; the source's necessity direction follows from Theorems 3.1 and 3.4. |
| Theorem 3.9, set-to-element | `theorem_3_9_set_to_element` | Without feedback, set-valued generation in the limit implies element-valued generation in the limit. |
| Appendix Lemma A.8 | `theorem_3_9_appendix_A_8_gap` | A fresh generator for a one-language class succeeds on every presentation, yet one presentation has no self-locking prefix. This faithfully refutes Lemma A.8 as stated. |
| Theorem 3.10, A.9 | `theorem_3_10_finiteInnerCover_sufficient` | A finite inner cover suffices for no-feedback generation in the limit. |
| Theorem 3.10, A.12 | `theorem_3_10_countableInnerCover_example` | Some generatable class of infinite languages over `ℕ` has a countable inner cover. |
| Theorem 3.10, A.13 | `theorem_3_10_noFiniteInnerCover_example` | Some generatable class of infinite languages over `ℕ × ℕ` has no finite inner cover. |

Level 1 includes the definitions that give these statements their meaning:
countable and finite inner covers; the element- and set-valued mistake and
query interaction models and their feedback runs; the canonical-order first
element; the zero-example and eventually correct models; the no-feedback
element and set generation predicates; and the self-locking and freshness
definitions named by the Lemma A.8 counterexample.

`theorem_3_9_of_selfLocking` is excluded. Its premise asks every successful
generator, after freshening, to self-lock along every presentation, which is
Lemma A.8 itself. That premise already fails for the one-language class of the
Lemma A.8 counterexample, so the conditional theorem is not evidence for the
element-to-set direction of Theorem 3.9. That direction and Appendix Theorems
A.10 and A.11, whose source proofs use it, remain unformalized. The
[fingerprint manifest](Fingerprints/P27_ICMLSection3Level1.json) guards the
twelve reviewed statement types and their recursive project-local defining
dependencies, except one private proof-only existence lemma that cannot be
named by the exporter. Construction and proof correspondence and other P27
statements are outside this record.

## #28 Contrastive Identification and Generation: arXiv v1 Overview, Level 1

On 13 November 2026, Shuangping Li completed a Level 1 review of all 19 P28 Overview
aliases (15 distinct statements) against arXiv:2605.06211v1 (pinned SHA-256
`40af9564b2066c0c47840aaf66b28caf12e5848b1673153cfcd4c92d0de5bf2a`) at Lean
checkpoint `c828be2`, with AI-assisted statement translations. The reviewed
declarations are aliases in
[`Results/Overview.lean`](../../GenLimit/Paper28_ContrastiveGeneration/Results/Overview.lean),
under `GenLimit.ContrastiveGeneration.Results`:

| Paper item | Reviewed declaration | Statement scope |
|---|---|---|
| Definition 4.1 and Proposition 4.2 | `proposition_4_2` | Non-eliminability is equivalent to common-crossing coverage, for any nonempty countable target. |
| Theorem 4.3 | `theorem_4_3` | Coverage form of the four-region criterion; with Proposition 4.2 it gives the source equivalence. The N1--N3 regime list is not formalized. |
| Definition 4.5 and Theorem 4.7 | `theorem_4_7` | (i) iff (iii): contrastive identifiability equals text identifiability plus the overlapping-cover condition on incomparable pairs. |
| Theorem 5.4 | `theorem_5_4` | Uniform contrastive generation iff finite closure dimension. |
| Theorem 5.4, quantitative | `theorem_5_4_quantitative` | Threshold `d + 1` works iff the dimension is at most `d`. |
| Theorem 5.4, sharpness | `theorem_5_4_sharp_sample_complexity` | Dimension exactly `d` makes `d + 1` the least positive threshold. Positivity is needed: the source's necessity claim fails at `d = 0` (audit probe). |
| Theorem 5.5 | `theorem_5_5` | Non-uniform generation iff an increasing chain of finite-dimension classes. |
| Proposition 5.8 | `proposition_5_8` | Infinite safe cores suffice for contrastive generation. |
| Definition 5.10 and Proposition 5.11 | `proposition_5_11` | An eventual core suffices, without the source's countability or infinitude assumptions. |
| Proposition 5.12 | `proposition_5_12` | A shared presentation with finite intersection obstructs generation; the certificates are the source hypotheses. |
| Theorem 5.13, witness | `theorem_5_13_punctured_witness` | The punctured class is contrastively generatable but neither text- nor contrastively identifiable. |
| Theorem 5.13, witness | `theorem_5_13_disjoint_witness` | The disjoint class is text-identifiable and text-generatable but not contrastively generatable. |
| Theorem 5.14 | `theorem_5_14_punctured_witness` | Same statement as the Theorem 5.13 punctured witness: CtrGen is not contained in TxtId. |
| Theorem 5.14 | `theorem_5_14_disjoint_witness` | Same statement as the Theorem 5.13 disjoint witness: TxtId is not contained in CtrGen. |
| Definition 6.2 and Proposition 6.3 | `proposition_6_3_defect_infimum` | The fewest forced wrong-cut violations equal the defect number. |
| Proposition 6.3 | `proposition_6_3_zero_defect` | Non-eliminability iff zero defect. |
| Definition 6.4 and Theorem 6.5 | `theorem_6_5` | The co-singleton family is not 1-corrupted text identifiable. |
| Theorem 6.6 | `theorem_6_6` | One identifier recovers the co-singleton family under every finite contrastive corruption budget (existential form). |
| Theorem 6.8 | `theorem_6_8` | For every `k >= 1`, k-corrupted contrastive and text identification are incomparable, with explicit witnesses. |

Level 1 includes the definitions that give these statements their meaning:
oriented edges and crossing, valid and corrupted presentations, the
identifier and generator interfaces, edge-induced closure, hollow sets and
closure dimension, safe and eventual cores, shared presentations, the defect
number, and the witness families. Lean learners see oriented pairs; an audit
probe shows that re-orienting canonically gives an orientation-blind identifier,
so this adds no power. Example 5.9 as printed is incorrect (the appendix
repairs it) and is not formalized. The
[fingerprint manifest](Fingerprints/P28_V1OverviewLevel1.json) guards the
reviewed statement types and their recursive project-local defining
dependencies. The full Theorem 5.13 diamond, construction and proof
correspondence, and results outside the Overview are outside this record.

## #29 Mistake-Bounded Language Generation: Theorems 4.1, 5.1, and 6.1 and Lemmas 6.2--6.3, Level 1

On 13 November 2026, Shuangping Li completed a Level 1 review of seven P29 Overview
statements against arXiv:2605.10809v1 (pinned SHA-256
`c79335d8c0fec7e3960c141c034a34144e4928d118f27311c8d661f81ba61365`) at Lean
checkpoint `c828be2`, with AI-assisted statement translations. The reviewed
declarations are in
[`Results/Overview.lean`](../../GenLimit/Paper29_MistakeBoundedLanguageGeneration/Results/Overview.lean),
under `GenLimit.MistakeBounded.Results`. Every statement concerns the concrete
Lean algorithms on injective streams inside the target, which is the source's
unique-element model (Remark 1):

| Paper item | Reviewed declaration | Statement scope |
|---|---|---|
| Theorem 4.1 | `theorem_4_1` | Algorithm 1 makes at most `activation + B` mistakes whenever `W < 2^(B+1) w0(target)`; the least such `B` is the source's floor of `log2(W/w0)`. The guard `w0(target) > 0` excludes only the case where the source bound is undefined. |
| Theorem 5.1, corrected | `theorem_5_1` | On a finite class with closure dimension at most `d`: at most `min(floor(log2 N), d + 1)` mistakes and no mistake from round `d + 1` on. The printed `Cdim` version is false under the source's generator-first order. |
| Theorem 5.1, diagnostic | `theorem_5_1_order_diagnostic` | Two disjoint infinite languages have closure dimension 0, yet every first output misses one of them. |
| Theorem 6.1 | `theorem_6_1` | The doubling-schedule, `1/i^2`-prior Algorithm 1 has the exact integer logarithmic bound from the source proof. |
| Theorem 6.1, displayed bound | `theorem_6_1_displayed_bound` | Every prefix has at most `3 log2 i + log2(pi^2/6)` mistakes. |
| Lemma 6.2 | `lemma_6_2` | Modified-Greedy makes at most `min(2(i-1), max(i-1, m+1))` mistakes. |
| Lemma 6.3 | `lemma_6_3` | Modified-Greedy makes no mistake from round `max(i-1, m+1)` on. |

Level 1 includes the definitions that give these statements their meaning:
mistake traces, total-mistake and last-mistake predicates, the concrete
Algorithm 1 runs (weights, activation, weighted argmax), Modified-Greedy, the
closure dimension and non-uniform complexity. Audit probes show that the
algorithms' outputs depend only on past observations, so fixed streams also
cover adaptive adversaries. `theorem_6_4_proof_diagnostic` is excluded: it is
an arithmetic identity used to document a gap in the source proof of Theorem
6.4, not a source statement. The
[fingerprint manifest](Fingerprints/P29_V1OverviewLevel1.json) guards the
seven reviewed statement types and their recursive project-local defining
dependencies. Construction and proof correspondence and other P29 statements
are outside this record.

## #30 Time-Sensitive Language Generation: Theorem 4 and Appendix Theorem 12, Level 1

On 13 November 2026, Shuangping Li completed a Level 1 review of the four P30 Overview
statements for Theorem 4 / Appendix Theorem 12 against arXiv:2605.11302v2
(pinned SHA-256
`c66e7e8848a3931c0f03023769ef70a78785b2eaec15e0f1724e625f8392416a`) at Lean
checkpoint `c828be2`, with AI-assisted statement translations. The reviewed
declarations are in
[`Results/Overview.lean`](../../GenLimit/Paper30_TimeSensitiveLanguageGeneration/Results/Overview.lean),
under `GenLimit.TimeSensitive.Results`:

| Paper item | Reviewed declaration | Statement scope |
|---|---|---|
| Theorem 4 | `theorem_4_totalized_gcg` | The repaired GCG is eventually consistent with timely upper density at least `1/2` on every exact presentation, and exactly `1/2` on a concrete adaptive presentation. |
| Appendix Theorem 12 | `theorem_12_totalized_gcg` | The same statement, as the appendix restatement. |
| Theorem 4, lower half | `theorem_4_totalized_gcg_lower` | Eventual consistency and timely upper density at least `1/2` on a given exact presentation. |
| Appendix Theorem 12, lower half | `theorem_12_totalized_gcg_lower` | The same lower half, as the appendix restatement. |

Lean's `id` deadline requires the target element of zero-based rank `j` among the first `j` outputs, one step stricter than the source's identity deadline `D(i) = i`; the `>= 1/2` half is therefore stronger than the source's, while the `= 1/2` presentation is proved only at the stricter deadline. The GCG is the library's repaired construction, not the printed
Algorithm 2, whose queue defect the paper map documents.

Six Overview declarations are excluded. `theorem_4_density_endgame` and
`theorem_12_density_endgame` assume density reaches every threshold below `1/2`
infinitely often, which is equivalent to their conclusion;
`theorem_4_totalized_gcg_eq_of_turnTaking` assumes a certificate equivalent to
half of its conclusion; `appendix_D_rate_core` is satisfied by the zero rate and
omits positivity, `r(i) = o(i)`, and superlinearity; and
`theorems_1_2_pathwise_counting_core` and `lemma_2_density_endgame` are correct
proof steps rather than source statements. Theorems 1--3 are therefore not
covered. The [fingerprint manifest](Fingerprints/P30_V2Theorem4Level1.json)
guards the four reviewed statements and their recursive project-local defining
dependencies. Construction and proof correspondence are outside this record.

## #31 Bounded Memory: arXiv v1 Overview, Level 1

On 13 November 2026, Shuangping Li completed a Level 1 review of all 13 P31 Overview
aliases against arXiv:2605.30324v1 (pinned SHA-256
`6c446edfa4f8ebc2978d144d213e88f61f29d06922721b016ba89faf64470049`) at Lean
checkpoint `c828be2`, with AI-assisted statement translations. The reviewed
declarations are aliases in
[`Results/Overview.lean`](../../GenLimit/Paper31_BoundedMemory/Results/Overview.lean),
under `GenLimit.BoundedMemory.Results`:

| Paper item | Reviewed declaration | Statement scope |
|---|---|---|
| Theorem 1.1 | `theorem_1_1` | Every countable collection of infinite subsets of `ℕ` has one memoryless set generator that succeeds on every finitely repeating enumeration; an audit probe extends this to any countable infinite universe. |
| Theorem 3.1 | `theorem_3_1` | Characterization of memoryless set generation under arbitrary repetitions, in the source's equivalent form. |
| Theorem 3.2 | `theorem_3_2` | Set output is necessary: separations for element output and index output. |
| Theorem 4.1 | `theorem_4_1_order_robust` | The order-robust memoryless minimax upper density equals `1/C(k-1, floor((k-1)/2))`. The adversary chooses the target's density order after the generator, unlike the source's fixed canonical order, so the equality implies the source's lower bound and the fixed-order upper bound is not part of the reviewed statement. |
| Theorem 4.2 | `theorem_4_2_order_robust` | For each `k >= 3`, some family admits no positive lower-density guarantee for memoryless generators. |
| Theorem 4.10 | `theorem_4_10_order_robust` | Window-`W` generators have the same order-robust minimax value as memoryless ones. The adversary chooses the target's density order after the generator, unlike the source's fixed canonical order, so the equality implies the source's lower bound and the fixed-order upper bound is not part of the reviewed statement. |
| Theorem 4.15 | `theorem_4_15_order_robust` | Lower bound for `b`-buffer generators, valid for every ordering of the target. |
| Proposition 5.1 | `proposition_5_1` | Three languages defeat exact incremental identification, already on finitely repeating enumerations. |
| Theorem 5.2 | `theorem_5_2` | Every nonempty finite collection is approximately incrementally identifiable after re-indexing; an audit probe removes the re-indexing for distinct languages. |
| Theorem A.1 | `theorem_A_1` | Exact index generation fails for three languages. |
| Proposition A.2 | `proposition_A_2` | The triangle obstruction to index generation. |
| Theorem A.4 | `theorem_A_4_semantic` | Coding compilation over `ℕ`: an eventually almost-contained full-history learner yields a previous-output generator; an audit probe shows the premise is satisfiable. |
| Theorem A.5 | `theorem_A_5_nat_semantic` | Every nonempty finite family of infinite subsets of `ℕ` has a previous-output generator that eventually outputs unseen target elements. |

Level 1 includes the definitions that give these statements their meaning:
memoryless, window, and buffer generators, finitely repeating enumerations,
ordered languages and densities, the minimax values, incremental learners, and
almost containment. Several statements are stated over `ℕ` only or are stronger
than the source (finitely repeating enumerations). The
[fingerprint manifest](Fingerprints/P31_V1OverviewLevel1.json) guards the 13
reviewed statement types and their recursive project-local defining
dependencies. The source's fixed-order upper bounds in Theorems 4.1 and 4.10,
construction and proof correspondence, and results outside the Overview are
outside this record.

## #32 Infinitely Many Hallucinations: arXiv v1 Overview, Level 1

On 13 November 2026, Shuangping Li completed a Level 1 review of ten P32 Overview
statements against arXiv:2606.28354v1 (pinned SHA-256
`67aefbbc734d010380daf4da5d2f19ceed51592e8f9004c322fefc0e43359975`) at Lean
checkpoint `c828be2`, with AI-assisted statement translations. The reviewed
declarations are aliases in
[`Results/Overview.lean`](../../GenLimit/Paper32_InfinitelyManyHallucinations/Results/Overview.lean),
under `GenLimit.InfinitelyManyHallucinations.Results`:

| Paper item | Reviewed declaration | Statement scope |
|---|---|---|
| Theorem 2.1 | `theorem_2_1` | For an infinite `f`-bounded guess, the best lower precision over `f`-bounded target exhaustions equals the guess's lower membership precision; the infinite guess is the source's standing assumption. |
| Lemma 2.2 | `lemma_2_2` | For a fixed target exhaustion, the best exhaustion-level lower recall equals the lower coverage ratio. |
| Proposition 2.4 | `proposition_2_4_single_step` | Tail-precision attainment, single-step form. |
| Proposition 2.4 | `proposition_2_4_constant_step` | Tail-precision attainment, constant-step form. |
| Proposition 3.3 | `proposition_3_3` | Eventually valid new strings iff eventual tail precision 1, using the `|G \ T| < ∞` reading the source states after Definition 3.2. |
| Lemma 4.7 | `lemma_4_7` | A guess containing every unrevealed target string has lower recall at least one minus the adversary's upper recall. |
| Theorem 4.3 | `theorem_4_3` | Without novelty, some generator achieves recall 1 and precision 1 against every infinite `f`-bounded adversary inside `L`. As in the source, the generator is chosen after the target, so the literal statement is weak; the library's witness does not depend on the target, and an audit probe proves the uniform form. |
| Appendix theorem (generation without novelty) | `appendix_valid_generation_without_novelty` | Copying the adversary gives recall at least the adversary's recall, with precision and tail precision 1; the tightness clause is not formalized. |
| Appendix lemma after Definition 4.2 | `gamma_admissible_exploration_exists` | For every `γ < 1` there is an exploration set with count at most `(1 - γ) m`. |
| Lemma D.1 | `appendix_lemma_D_1_of_limit_infinite` | For an infinite guess, lower tail precision 1 implies precision 1. |

Level 1 includes the definitions that give these statements their meaning:
exhaustions and `f`-boundedness, lower membership precision, tail precision,
recall, generated exhaustions, and exploration sets. Five Overview declarations
are excluded: `theorem_3_5_fixed_pod_endgame` (its premise is equivalent to its
conclusion), the three `..._of_trace_certificate` wrappers for Lemma 4.5 and
Theorems 4.8--4.9 (their certificates carry most of the conclusion and require
a valid first output), and `tail_precision_one_finite_guess_counterexample`,
whose finite guess violates the source's standing infinite-guess assumption, so
it does not refute Lemma D.1 as stated. The
[fingerprint manifest](Fingerprints/P32_V1OverviewLevel1.json) guards the ten
reviewed statement types and their recursive project-local defining
dependencies. Construction and proof correspondence are outside this record.

## #39 Dense Generation: arXiv v2 Theorems 3.15 and B.3, Level 1

On 7 November 2026, Peng Zhang reported completion of a Level 1 human audit
of P39 Theorems 3.15 and B.3. This is the reporting date; the actual completion
date was not separately specified. The reviewed code checkpoint is
`3f0aa554d8e713095983504e27f371afb8206be8`.

The comparison source is *Dense Language Generation Made Simple:
Deterministic, Randomized, and Multi-Order Algorithms*, arXiv:2608.01320v2,
with pinned PDF SHA-256
`8dfc7ada39b62bb79d380331deeb4377035ec35d26b8334c2c6c6a91cb711b08`.

The reviewed declarations are in
[`Results/Overview.lean`](../../GenLimit/Paper39_DenseGeneration/Results/Overview.lean),
under `GenLimit.DenseGeneration.Results`:

| Paper item | Reviewed declaration | Statement scope |
|---|---|---|
| Theorem 3.15, achievability | `theorem_3_15` | The concrete patient-scope run has target-relative lower density at least `1/2` for every exact presentation of an indexed infinite target. |
| Theorem B.3 | `theorem_B_3` | If an infinite presented subset `E` of the target has relative lower density `α`, patient-scope on the filtered finite-intersection closure has target-relative lower density at least `α / 2`. |

Level 1 includes the definitions determining these statements' meaning:
indexed infinite language families, exact positive presentations,
generator-first target elements, the concrete patient-scope output and
finite-intersection closure interfaces, and the operational density quantities.
The reviewed density definition uses Core's ordered lower density with the
target's increasing enumeration; it includes the explicit infinitude argument
introduced by the shared-density refactor.

The [Level 1 fingerprint manifest](Fingerprints/P39_V2Theorems3_15AndB_3_Level1.json)
guards the two statement types and their recursive project-local defining
dependencies. Supporting proof-certificate types are tracked to preserve the
meaning of definitions, not as separate audited results. Capturing these
fingerprints is a mechanical maintenance step recording the user's review.

The separate optimality upper bound in Theorem 3.15, other P39 statements
(including joint validity/novelty variants), construction correspondence
(Level 2), proof-step correspondence and theorem proof bodies (Level 3),
executability, and complexity are outside this record. The four historical
P39 fingerprint manifests retain their original baselines and `needs-review`
status; this Level 1 review does not renew their broader or distinct scopes.

## #39 Dense Generation: arXiv v2 migration on 5 November 2026

On 5 November 2026, the active facade was updated to the supplied
arXiv:2608.01320v2 PDF (SHA-256
`8dfc7ada39b62bb79d380331deeb4377035ec35d26b8334c2c6c6a91cb711b08`).
V2 restores the earlier recursive-criticality interface. At that migration,
the facade exposed Lemma 3.12, Fact 3.13, Lemma 3.14, Theorem 3.15, and
Appendix B numbering, while retaining the canonical machine, density proofs,
and earlier numbered aliases. Subsequent cleanup narrowed the facade to the
two main theorems and removed the earlier library aliases.
New proofs expose the critical-chain update properties, both Fact 3.13
clauses, and Example B.1's zero-density conclusion.

This is an engineering/source-comparison record, **not a human audit**.
The historical records below and all four historical P39 fingerprint baselines
keep their original source, checkpoint, and `needs-review` status. No v2 human
correspondence level was assigned by that migration. The separate 7 November
Level 1 review is recorded above. The
[P39 PaperMap](../../PaperMaps/Paper39_DenseGeneration.md) records edition
correspondence and coverage.

The fingerprint checker still reports the three construction-value differences
for `highestCritical`, `highestSurvivor`, and `lowestConsistentInScope` against
the old candidate baseline. These selectors were changed by the earlier
shared-selector refactor `98d59c4`; `Patient/Machine.lean` is byte-identical
between this update and checkpoint `e5949e6`. The v2 migration does not
re-baseline those warnings or resolve the pending human construction review.

## #39 Dense Generation: exact-presentation black-box specification

For a fixed family `O`, `PatientMachine.output O stream` does not receive the
hidden target index `z`. For every stream exactly presenting `O.language z`,
the joint theorem gives eventual target validity, novelty, and target-relative
lower density at least `1 / 2`.

| Checked item | Audited meaning |
|---|---|
| Inputs | `OracleFamily` is an indexed family of infinite languages; `Presents stream (O.language z)` means that the stream presents exactly the target. |
| Uniformity | The generator depends on `O` and the observed stream, not on `z`. |
| Validity | Every sufficiently late output belongs to `O.language z`. |
| Novelty | Every sufficiently late output differs from all stream values through that round and from all earlier generator outputs. |
| Density | The numerator counts target elements below `n` first announced by the generator; the denominator is `|O.language z ∩ Finset.range n|`, not `n`. |
| Strength | The result proves achievability of target-relative lower density at least `1 / 2`. |

At the audited snapshot, the code anchors were
`GenLimit/DenseGeneration/Patient/Machine.lean` and
`GenLimit/DenseGeneration/Patient/Main.lean`,
with `Presents` and `OracleFamily` in `GenLimit.Core`. This audit does not
certify manuscript-algorithm correspondence, paper-to-Lean proof
correspondence, finite-query executability, computational complexity, or the
separate upper bound needed for optimality. The current machine is semantic
and noncomputable because recursive criticality compares whole infinite
languages. The separate construction audit below now covers the machine's
manuscript correspondence, and the definition audit below covers recursive
criticality and focus, at their respective stated levels.

## #39 Dense Generation: patient-scope machine construction

The construction in the audited-snapshot file
`GenLimit/DenseGeneration/Patient/Machine.lean` was
checked directly against the Dense Generation manuscript. The result is
**PASS** at the state-machine construction and manuscript-correspondence
level.

| Checked item | Audited correspondence |
|---|---|
| Indexing and time | Positive paper values and one-based language indices are translated to `ℕ`; paper round `T ≥ 1` is Lean output round `T - 1`, while the post-round state is `run O stream T`. |
| State and initialization | The exclusive scope bound, focus-change count, consecutive-focus age, focus index, output history, last output, and move label have the intended roles; the initial scope and `tau` are `1`, while the initial focus and age are `0`. |
| Stable branch | The machine tests the previous `2 ^ tau` completed focus rounds, expands the scope by one, recomputes the highest critical focus after the current observation, and increments `tau` exactly when the focus changes. |
| Backtracking | The three manuscript cases are represented by the highest surviving critical index, the lowest consistent index in the old scope, and the globally lowest consistent index when the old scope is empty of consistent candidates. The exclusive Lean scope `i + 1` matches the one-based paper scope ending at the selected language. |
| Output and history | Each round receives `stream t`, decides using the sample through that announcement, selects the least focused-language value absent from both parties' prior announcements, updates `age` and `used`, and records the output in the post-round state. |
| Totalization and access model | Extra fallbacks make the Lean definitions total on arbitrary histories but are unreachable on an exact presentation. The construction is semantic and noncomputable because it uses whole-language consistency, criticality, and inclusion. |

The audited code anchor has SHA-256
`ca4ad447ccaeeb9ce9304c555b525a32d8a2f491c0372d3b5b9f32f0898f6b73`.
This record does not yet cover `MachineInvariant.lean`, downstream validity or
charging arguments, the rest of the `Patient` directory, or a line-by-line
audit of every helper-theorem proof in `Machine.lean`.

## #39 Dense Generation: recursive criticality and focus definitions

The definitions `RecursiveCritical` and `IsFocus` in
the audited-snapshot file `GenLimit/DenseGeneration/Critical.lean` were checked directly against
Definitions 3.2, 3.5, and 3.6 of the Dense Generation manuscript. The result
is **PASS** at the definition and manuscript-correspondence level.

| Checked item | Audited correspondence |
|---|---|
| Recursive criticality | Index zero is critical exactly when it is consistent. An index `n + 1` is critical exactly when it is consistent and its language is contained in every earlier recursively critical language. |
| Focus | `IsFocus C stream t s f` says that `f < s`, that `f` is recursively critical, and that every recursively critical `j < s` satisfies `j ≤ f`; hence `f` is the highest-indexed critical language in scope. |
| Indexing | The manuscript's one-based language indices are translated to zero-based Lean indices, and a Lean scope bound `s` contains exactly the indices `< s`. |
| Audit boundary | Only the two paper-facing definitions were audited. The lemmas and proofs in `Critical.lean`, including eventual target criticality and focus containment, are verified by Lean but were not checked against the manuscript proof steps. |

The audited `Critical.lean` code anchor has SHA-256
`a4ca152c7dccca987999b5fc68dc04541be79bd209fdbaabaaf7bf4f87e77d9f`.

## #39 Dense Generation: exact-presentation end-to-end conclusion

Taken together, the exact-presentation input/output audit, the recursive
criticality and focus definition audit, and the patient-scope machine audit
constitute an **end-to-end algorithm-to-main-theorem correspondence audit**
for Theorem 3.14. Human review identifies the manuscript algorithm with the
Lean state machine and the manuscript claim with the Lean theorem statement;
Lean's kernel verifies that this machine satisfies that statement.

This establishes the main exact-presentation algorithmic claim without
certifying the manuscript's intermediate lemmas, its proof steps, or a
line-by-line correspondence between the manuscript proof and the Lean proof.
It also does not add finite-query, complexity, optimality, randomized, or
partial-enumeration claims. The audited `Patient/Main.lean` code anchor at
checkpoint `374e24f` has SHA-256
`d2998e711536b5cea618b32fb7e09c22dceab244e3ce7355e2d9e90906ffb2d3`.

The later shared-density and API cleanup changed the paper-facing density
wrapper, made an internal certificate bridge private, and removed a redundant
derived theorem. At that later checkpoint, the file hash was
`cd4b763251a6f77e36522cbc7203b0abbfdbea12cc9e9f4fa8bc9a689ba7a91a`;
a narrow human re-audit of the exact-presentation wrapper remains pending.

## #39 Dense Generation: partial enumeration, Lemma 3.16 and Theorem 3.17

The finite-intersection transformation, the paper-facing statements of Lemma
3.16 and Theorem 3.17, and their operational density definitions were checked
directly against Section 3.3 of the Dense Generation manuscript. The result is
**PASS at Level 2** for these two results.

| Checked item | Audited correspondence |
|---|---|
| Inputs | The stream exactly presents an infinite language `E`, with `E ⊆ O.language z`; `O.language z` is the unknown true target `K`. |
| Closure transformation | The definitions in `Partial/Closure.lean` encode nonempty finite intersections by positive binary codes, retain exactly the infinite intersections, order retained codes increasingly, and expose the resulting indexed family as `closure O`. |
| Reused algorithm | The formal construction is the already-audited patient-scope machine run as `PatientMachine.output (closure O) stream`; the machine itself is unchanged. |
| Uniformity | The generator receives `O` and the observed stream, but not `E` or the hidden target index `z`. |
| Lemma 3.16 | `lemma_3_16_generation` gives eventual membership in `O.language z`, freshness from the observed stream through the current round, and non-repetition of generator outputs. |
| Density metric | `relativeLowerDensity A K` is the liminf of ambient-prefix counts `|A ∩ [0,n)| / |K ∩ [0,n)|`. The output metric explicitly counts generator-first elements that belong to `K`. |
| Theorem 3.17 | If `E` has relative lower density `α` in `K`, the concrete transformed run has target-relative lower density at least `α / 2`. |
| Access model | Retaining only infinite intersections and reindexing them is semantic and noncomputable; the audited result does not claim a finite-query implementation. |

Human review identifies the manuscript's transformed algorithm with the Lean
construction and its claims with the Lean theorem statements. Lean's kernel
verifies that this construction satisfies those statements. The audit reuses
the existing patient-machine record whose SHA-256 is
`ca4ad447ccaeeb9ce9304c555b525a32d8a2f491c0372d3b5b9f32f0898f6b73`.
The audited Lean code checkpoint is `22f04f7`.

The new audited code anchors have SHA-256 values:

| Code anchor | SHA-256 |
|---|---|
| `GenLimit/DenseGeneration/Partial/Closure.lean` | `6cc7c705b49d03d8966ad64902305c93528d102ce4e5dd0b281708312737e671` |
| `GenLimit/DenseGeneration/Abstract/TargetDensity.lean` | `fcad41b14bad213f8014da6d99fdba04ed28df27fe37bf1b0873594700f37358` |
| `GenLimit/DenseGeneration/Partial/Validity.lean` | `45709d6ec5cb32c42a1faad66a52154143164a6fa1f18af25d4351113c1f8e4c` |
| `GenLimit/DenseGeneration/Partial/Main.lean` | `9754880a47f8e18c248bf28e27bec16b050ee78e9399625bbee9cc6781e5c868` |

After the original audit checkpoint, the internal certificate bridge in
`Partial/Main.lean` was made private and its explanatory comment was
clarified. The audited paper-facing definitions and theorem statements were
unchanged.

The audited manuscript copy has SHA-256
`1a9a81a7aa02719f5cfe852746f3db853d47d42f699e8f62cc78f451ef7cb23e`.

This record does not cover Example 3.15, intermediate proof-step
correspondence, the proof bodies in `Partial/Critical`, `Partial/Certificate`,
`Partial/Trace`, or the counting and liminf modules. It also does not cover
finite-query executability, complexity, the Kleinberg--Wei algorithm, or the
optimality upper bound.

## #0 Language Identification: arbitrary-text semantic theory

On 2 August 2026, Peng Zhang reported completion of a human audit at Level 2
for the #0 Language Identification arbitrary-text semantic path. The new shared Core files had
also been read as the prerequisite layer. The audited scope is the concrete
semantic theory of identification from arbitrary exact positive text.

| Checked file or layer | Audited role |
|---|---|
| `GenLimit/Core/Text.lean` | Ordered finite prefixes of a stream and their finite-set view. |
| `GenLimit/Core/Identification.lean` | Generic learners, eventual syntactic stabilization, and identification in the limit. |
| `GenLimit/Gold/Text/Model.lean` | #0 text naming relations and the target-, class-, and semantic-identification interfaces. |
| `GenLimit/Gold/Text/Consistency.lean` | Equivalence between positive compatibility of a finite history and consistency of the corresponding stream prefix. |
| `GenLimit/Gold/Text/Finite.lean` | The observed-elements learner and the semantic convergence content of Theorem I.6 for all finite languages. |
| `GenLimit/Gold/Text/Locking.lean` | The semantic locking-sequence lemma used as supporting machinery; it is not presented as a numbered theorem in the paper. |
| `GenLimit/Gold/Text/Superfinite.lean` | The paper's Section 8 arbitrary-text semantic obstruction: all finite languages are identifiable, but no proper superclass is. |

The audit therefore covers the definitions and proof chain leading from the
finite-language learner through locking and finite tell-tales to
`superfinite_not_semanticallyIdentifiable` and
`finiteLanguages_maximal_semanticallyIdentifiable`.  It verifies the intended
semantic reading: even a possibly noncomputable learner cannot identify, from
every arbitrary positive text, a class containing every finite language and
at least one infinite language.

This record does not cover the audited-snapshot `GenLimit/Gold/Abstract/` path, Theorem 7.1,
`Abstract/TextSpecialization.lean`, `Text/Enumeration.lean`,
`GenLimit/Gold/Informant/`,
or the bridge files.  It also does not certify effective tester or generator
indices, recursive or primitive-recursive counterexample texts, or Gold's
Theorems I.8 and I.9.  Under the current `ℕ → ℕ` stream model, the empty
language has no exact text, so its identification condition is vacuous.

The audited code anchors have SHA-256 values:

| Code anchor | SHA-256 |
|---|---|
| `GenLimit/Core/Text.lean` | `0d09cf30062fc02b8b77214e987009eebc4ebf6aa77fc5e3df5bdaa9ff993a21` |
| `GenLimit/Core/Identification.lean` | `b4629c10265a70a52c5955b50b723c33d186c0ea66500c7f91ffa3b7f6bd96e8` |
| `GenLimit/Gold/Text/Model.lean` | `2e05362eea4ec3d44de34f89dd6e183f0b3ba76f75a0294c5282bf9d7b52274f` |
| `GenLimit/Gold/Text/Consistency.lean` | `f00718c664cd1b1bd1f00164c96625c36965325caa1ec74915db52fb5e608626` |
| `GenLimit/Gold/Text/Finite.lean` | `97427cb75441a51ec9b74f9d47398dc1ddcb3294d06d829ffa3145691bad4619` |
| `GenLimit/Gold/Text/Locking.lean` | `972eb4e2719228190e59262fb6ce974912584a56c3c219ab4edc33875c827010` |
| `GenLimit/Gold/Text/Superfinite.lean` | `b8cc3d36129cb62d2b3ed6916f5926081bcf7345a3f6c3e6a73b427a99b7f842` |

## #0A Inductive Inference from Positive Data: semantic characterization

On 10 August 2026, Peng Zhang reported completion of a Level 1 human audit of
Angluin's semantic analogue of Theorem 1. The audited Lean theorem is
`GenLimit.Angluin.semanticallyInferrable_iff_conditionTwo`:

```lean
SemanticallyInferrable C ↔ ConditionTwo C
```

The result identifies semantic positive-data inferrability with the existence
of a finite tell-tale for every indexed language.

## Re-audit condition

The two `v0.3.0` records apply to that release. Every later record applies to
the exact audited-snapshot hashes stated above. The numbered-path migration
changes the bytes of files whose imports or documentation comments were
rewritten, so this ledger preserves the earlier human conclusions as
historical records without claiming that the current numbered files retain
those hashes. A migration-aware human re-audit is required before extending a
record to a changed current anchor or making a stronger correspondence claim.
