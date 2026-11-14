# P22 — informed adjudication

**C05 remains a substantive formalization gap.** The documentation openly acknowledges the missing Algorithm 3 construction; it does not complete the unconditional source lower bound. The other claims retain faithful correspondence, with explicit model/representation qualifications for C02 and C03. No genuine translation mismatch or justified source correction is established.

This is the **same source-informed Stage 2 reviewer**, continuing after the comparison freeze, not a third independent blind review. Coordinator steering reinforced the already recorded distinction between the broader false certificate demand and the actual source lemma; no new parent-supplied proof was adopted. Prior blind-stage findings remain frozen. All mathematical arguments below are **informal, not Lean-checked**. No proof certification, build, extracted execution, or human-review credit is supplied.

## Evidence and explanation inventory

Source identity and mathematical dossiers remain those of the frozen [source inventory](source-inventory.md) and [comparison](source-comparison.md): arXiv:2603.11784v2, 5 July 2026, PDF SHA-256 `336e313632cd6f63da3965bfcb18fe3c40be3d6556433f654054c6249e19f325`; supplied interface snapshot label `e56b617a39899cb9acfd94b61e19680934bf78aa1f40d8d07d8e7f1d10bee1fc`. Printed/PDF page numbers agree on the inspected pages. All nine target types were rechecked, and 84 distinct previously reviewed anchors match their frozen type hashes. Source pp. 9, 20, and 22 were visually rechecked.

The newly allowed explanations are [PaperMap](../stage3-context/PaperMap.md), SHA-256 `6067827986a1dd8d7a089be152a14bde2d1dc73112eb47a00bdab6d487bfdeb3`, and [registry](../owner/registry.json), SHA-256 `1a701351439635a3682badc1b214a43fdc2e1d07c916777a9ee9d0010ce502c6`.

| Explanation location | Assertion | Adjudication |
|---|---|---|
| PaperMap lines 17–25, 38; registry `/claims/0` | Uniform semantic result preserves positive threshold; UUS not needed | Supported by direct target/native conversion interfaces; faithful generalization. |
| PaperMap line 39; registry `/claims/1/lean_links/0/notes` | Two-copy domain preserves source support incidence | Adequate as an alternate existential witness explanation; too strong if read as literal incidence isomorphism of the whole displayed families. |
| PaperMap lines 19–25, 41–42, 67–79; registry `/claims/2` | Persistent-cutoff Nat procedure has finite oracle caches; arbitrary-countable transport is semantic | Supported at the exact finite-search/finite-query interface, with the computational limits retained below. |
| PaperMap line 43; registry `/claims/3` | Literal marker-padded class, simpler ordinary generator | Supported by fixed-class/native definitions and theorem types. |
| PaperMap line 44, lines 83–86; registry `/claims/4` | Construction open; silent-divergence diagnosis; broader obligation false | The formalization gap is confirmed. The broader refutation is not the source lemma. Silent-divergence diagnosis remains dependent on the intended computational premises. |
| PaperMap line 45; registry `/claims/5` | Exact four integer languages | Supported by named family definitions; distinguish that witness from the facade's four-index statement. |

Embedded references to other audits and kernel checks are explanatory text only. Their records/proofs were not opened and are not credited as validation here. Requested model/effort remain `gpt-6.1-sol / xhigh`; backend revision is unobservable.

## Every registered target

Names below have prefix `GenLimit.Replay`. The exact types and anchors are in the frozen Stage 2 dossiers.

| Slot | Target | Final target disposition |
|---|---|---|
| C01 | `Results.theorem_4_1` | Matches source context; faithful generalization to inhabited domains/classes. |
| C02 | `Results.theorem_5_1` | Qualified representation: equivalent existential separation, alternate witness. |
| C03 | `Results.theorem_6_1` | Qualified model: semantic arbitrary-countable-domain existence with classical transport. |
| C03 | `Results.theorem_6_1_finite_query` | Qualified model: same named Nat generator's correctness and finite oracle-cache transition specification. |
| C04 | `Results.theorem_6_6` | Matches source context, including same-class ordinary/replay properties. |
| C05 | `Theorem71Statement` | Substantive gap: a proposition definition, not an unconditional proof. |
| C05 | `Results.theorem_7_1_of_algorithm3` | Substantive gap: construction remains a premise. |
| C05 | `Results.theorem_7_1_overstrong_construction_is_false` | Qualified auxiliary counterstatement; not a refutation or repair of source Lemma 7.2. |
| C06 | `Results.theorem_7_3` | Matches source context; retain index/range-cardinality qualification. |

The six claim dispositions are respectively: matches-source-context; qualified-model-or-representation; qualified-model-or-representation; matches-source-context; substantive-formalization-gap; matches-source-context.

## C05 — separate the gap, counterstatement, and source-model question

The source Theorem 7.1 (p. 18) is unconditional. Lemma 7.2 (pp. 20, 22) says the membership function produced by Algorithm 3 is total recursive and every indexed support is infinite. The actual formal certificate instead **requires** a recursive infinite family, a stream, and an output execution at every round, plus one of the two failure patterns. These are fields to supply, not an implementation of the source construction. The PaperMap and registry correctly disclose this incompleteness.

Let U(A) denote `UniversalProperMembershipGenerator A`, C(A) denote certificate inhabitation, P denote `∀A, U(A) → C(A)`, and Q denote `¬∃A, U(A)`. The registered reduction is P→Q. The explanatory assertion that P and Q are equivalent is supported logically: Q implies P vacuously; under the declared certificate endgame, P and a universal A produce a certificate refuting that A. The narrower premise therefore cannot be treated as an already discharged or weaker result. This argument uses the exposed interfaces, not a new Lean proof.

The broader refuted demand is `∀A, Computable A → C(A)`, with no assumption that a round completes. `queryForeverAlgorithm` always asks the same membership question. A certificate cannot exist for it because the certificate demands an output every round. This is an appropriate counterexample to that **stronger certificate requirement**.

It is not a counterexample to Lemma 7.2. After one-based reindexing, let the interaction repeatedly query (1,1). In printed Algorithm 3, k grows without bound and J≥k. After the initial two columns, every column j≥3 is eventually assigned 1 for all i. Consequently this interaction's F is 0 only at the initial trap pair (2,2), and 1 elsewhere. It is jointly recursive and every row is infinite, despite no output being produced. This direct infinite-interaction argument shows precisely why the completed-execution certificate and source membership-map lemma must remain distinct. It is not a finite experiment or a theorem refutation.

The separate **silent-divergence** diagnosis needs its premises stated. If arbitrary partial programs are allowed, a program may query (1,1) once and then silently loop. The printed process can then wait before receiving an output with J=2, leaving F(i,3) unassigned. This exposes a missing case under that broad program reading. But such a program is not a total history-to-output generator in the source's earlier definition and is not a total next-action dialogue function in the Lean model. The example therefore does not establish failure under every intended reading of “computable G,” and it certainly does not refute the headline theorem.

A minimal **model clarification** would require a total next-action protocol, so an endless round issues infinitely many queries. Lean already uses such total computable action functions, but the Algorithm 3 family construction is still absent. An alternative clock/dovetailing repair for general partial programs would need proofs of recursive membership, infinite rows, target enumeration, and execution preservation; adding a clock by itself is not a certified repair. Neither proposal is implemented as a completed source correction by the supplied endpoints. The source-proof issue remains unresolved; the formalization gap is definite.

## Remaining representation and computation checks

**C02.** The source's displayed positive-N witness (p. 9) has every language containing 1. The formal family includes both the all-left language and cutoffLanguage 0, the all-right language, whose intersection is empty. A bijective incidence isomorphism preserves whether all languages have a common point. Thus the whole displayed families cannot be literally incidence-isomorphic under that source convention. The existing explanation should explicitly mention the added cutoff-zero language, as Stage 2 did; omission of unused integer zero is only part of the representation change. Both endpoints still concern existence of a countable UUS separating class, so the alternate formal witness supplies the required statement. This is a qualification of the explanation, not a source error or genuine translation mismatch.

**C03.** The semantic endpoint provides one generator for each indexed infinite family with a correct Boolean oracle on a countable domain. Its coding is classically selected. The Nat endpoint gives eventual correctness for the same named carried WP generator together with one finite answered-query cache supplying validity, agreement of the entire next state under all agreeing valid oracles, the branch formula, coverage, and bounds. Active cache cardinality is at most `t*(|updatedSure|+foundCutoff)` and inactive cardinality at most `t*|updatedSure|`; these count distinct answered queries, not elapsed time.

Locality alone never proves computability: an oracle-independent noncomputable function of the input would have an empty oracle cache. Here the exposed WP definitions supply more—explicit finite scans, Boolean membership tests, protected finite minima, and a natural-number search, with finite-cutoff existence stated separately. Given that declared existence result, the displayed search is a finite oracle-relative recipe on each round. This supports the documentation's limited operational interpretation; it is not an independently certified ordered oracle program, extracted executable, ordinary `Computable` theorem for arbitrary oracles, uniform runtime rate, or effective coding from `Countable`. The documentation's disclaimers are appropriate.

**C01, C04, C06.** The disclosed broader semantic scope in C01 does not weaken the source positive-threshold result. C04's marker formulas match exactly after reindexing, while its different ordinary-generator formula is permitted by the existential claim. In C06 the named four supports are genuinely distinct: 1 separates the two negative-side supports, −1 separates the two positive-side supports, and −3 separates each negative-side from each positive-side support. This informal check supports the concrete four-member explanation without attributing a new range-cardinality theorem to the facade. The ordinary-positive proper-generation comparison is recalled prior work, not an extra scoped theorem proved here.

## Remaining work and validation limits

The necessary formalization work is C05's recursive-family/certificate construction under a precise machine model, followed by the unconditional lower bound. Clarify that the query-forever counterstatement concerns the completed-output certificate and that the silent-divergence concern is model-dependent. A narrow documentation clarification for C02's alternate witness would make the explanation exact. No source, registry, proof, or mathematical file has been edited.

All six claims, nine targets, the two parts of Lemma 7.2, and the semantic/finite-query split were rechecked. The source's earlier minor indexing and empty-marker questions remain as recorded in Stage 2; no repair was silently assumed. All prior freezes are preserved. This stage is complete as an informed statement adjudication; C05 remains incomplete mathematically/formally, and source/proof certification remains outside the review. Stop for coordinator freeze.
