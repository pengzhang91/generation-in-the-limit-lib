# Human audit records

This is the authoritative ledger for completed human paper-to-Lean audits.
It also indexes the ChatGPT Pro statement-faithfulness checks that still await
human review. Both are separate from Lean's kernel checks in
[AUDIT.md](../../AUDIT.md).

## Completed human audits

Each record in this table was performed by the named human auditor and is
complete only at its stated level.

| Development | Audit level | Auditor | Recorded | Release |
|---|---|---|---|---|
| #01 Language Generation — semantic path | Level 3: theorem, construction, and proof correspondence | Peng Zhang | 17 July 2026; narrow re-audit 20 July 2026 | `v0.3.0`; current revision `unreleased` |
| #01 Language Generation — round-dependent Section 4 semantic path | Level 2: theorem specification and semantic construction; proof correspondence excluded | Peng Zhang | 18 October 2026 | checkpoint `c8af96a` |
| #01 Language Generation — Theorems 2.1 and 2.2 | Level 1: theorem specifications and defining interfaces | Shuangping Li | 25 September 2026 | checkpoint `d5227a2` |
| #02 Learning Theory — Proposition 2.1 and ordinary Section 2--3 main theorems | Named-result human correspondence audit; no aggregate P02 level assigned | Peng Zhang | 12 August 2026 | checkpoint `d40205b` |
| #02 Learning Theory — finite-history migration for the six named Section 2--3 results | Level 1: statement and definition applicability; construction and proof correspondence excluded | Peng Zhang | 18 October 2026 | working tree based on `c8af96a`; file hashes below |
| #02 Learning Theory — Theorem 3.3 | Level 1: theorem specification | Shuangping Li | 25 September 2026 | checkpoint `14b4deb` |
| #02 Learning Theory — Theorem 3.5 | Level 1: theorem specification | Shuangping Li | 25 September 2026 | checkpoint `04dffd2` |
| #02 Learning Theory — Theorem 3.10 | Level 1: theorem specification | Shuangping Li | 25 September 2026 | checkpoint `6462d25` |
| #04 Exploring Facets — overview Theorems 1--4 | Named-result human correspondence audit; no aggregate P04 level assigned | Peng Zhang | 14 August 2026 | `unreleased` working tree based on `87423ff` |
| #04 Exploring Facets — overview Theorems 1, 3, and 4 | Level 1: statement and definition applicability renewed after the finite-history extraction | Peng Zhang | 19 October 2026 | checkpoint `fb37e6b` |
| #04 Exploring Facets — detailed Theorem 7 and overview Theorem 2 | Level 1: statement and adaptive membership-query definition applicability; proof correspondence excluded | Peng Zhang | 21 October 2026 | checkpoint `fb37e6b` |
| #04 Exploring Facets — overview Theorem 5 | Level 1: theorem statement and feedback/GF-dimension definitions; construction and proof correspondence excluded | Peng Zhang | 21 October 2026 | checkpoint `fb37e6b` |
| #06 Noisy Examples — Section 3 theorem specifications | Level 1: Theorems 3.1, 3.3, 3.9, and 3.10 | Peng Zhang | 13 August 2026 | checkpoint `a66d3d0` |
| #06 Noisy Examples — Section 3 theorem specifications | Level 1: Theorems 3.1, 3.3, 3.9, and 3.10 | Shuangping Li | 26 September 2026 | checkpoint `b03d957` |
| Paper10 Union-Closedness — Section 3 overview theorem specifications | Level 1: Theorems 3.1--3.3; Theorems 4.1, 4.3, and 4.4 are noted as their detailed presentations | Peng Zhang | 13 August 2026 | `unreleased` |
| Paper10 Union-Closedness — overview Theorems 3.1--3.3 | Level 1: theorem specifications | Shuangping Li | 25 September 2026 | checkpoint `d5227a2` |
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
| #02 named Section 2--3 results | reviewed working tree based on `c8af96a`, 18 October 2026 | Current; machine-guarded at statement and definition level | Peng Zhang confirmed that the finite-history interface migration preserves the definitions and statements of Proposition 2.1 and Theorems 2.4, 2.5, 3.3, 3.5, and 3.10. Construction and proof correspondence were not reviewed; no aggregate P02 level is assigned. |
| #02 Theorem 3.3, Level 1 | fingerprint baseline `14b4deb` | Current; machine-guarded at statement level | The statement and relevant definitions were reviewed, retaining the explicit nonempty-universe convention. |
| #02 Theorem 3.5, Level 1 | fingerprint baseline `04dffd2` | Current; machine-guarded at statement level | The statement and relevant definitions were reviewed, retaining the explicit nonempty-universe convention. |
| #02 Theorem 3.10, Level 1 | fingerprint baseline `6462d25` | Current; machine-guarded at statement level | The statement and relevant definitions were reviewed, retaining the explicit nonempty-universe convention. |
| #0A semantic characterization, Level 1 | fingerprint baseline `f624971` | Carried forward; machine-guarded at statement level | The audited `SemanticallyInferrable C ↔ ConditionTwo C` statement and its statement-relevant definitions are unchanged. Its proof now delegates a finite eventuality helper to shared Support infrastructure. CI guards the statement and its semantic dependencies, but not the proof body. Effective Theorem 1 and Corollaries 1--3, including the new Corollary 2 and 3 proofs, remain outside this human-audit scope. |
| #04 overview Theorems 1--4 and detailed Theorem 7, Level 1 | reviewed and fingerprinted `fb37e6b` | Current; machine-guarded at statement and definition level | The 19 October review of Theorems 1, 3, and 4 and the 21 October review of detailed Theorem 7 / overview Theorem 2 renew the combined scope. The shared dialogue definitions are included; proof correspondence and the Theorem 7 proof repair are excluded. |
| #04 overview Theorems 1, 3, and 4, Level 1 | reviewed and fingerprinted `fb37e6b` | Current; machine-guarded at statement and definition level | Peng Zhang completed the narrow needs-review checks for these three specifications and their defining interfaces, including the shared finite-history operator. Construction and proof correspondence remain outside scope. |
| #04 overview Theorem 5, Level 1 | reviewed and fingerprinted `fb37e6b` | Current; machine-guarded at statement and definition level | Peng Zhang reviewed the feedback characterization statement, alternating strategy model, truthful exact presentations, uniform distinct-sample threshold, and finite GF dimension on 21 October 2026. This completes the Level 1 overview Theorems 1--5 scope; construction and proof correspondence remain outside scope. |
| #06 Section 3 theorem specifications, Level 1 | reviewed `b03d957`; fingerprints `0894d0f` | Current; machine-guarded at statement level | The 26 September review renews the four qualified statements and relevant definitions, including shared occurrence-noise predicates, coverage requirements, and explicit universe assumptions. |
| Paper10 overview Theorems 3.1--3.3, Level 1 | fingerprint baseline `d5227a2` | Current; machine-guarded at statement level | The 25 September review renews the overview specifications and relevant definitions, including the finite-history interface and recorded presentation, autonomous-schedule, and EUC conventions. |
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
| [#08 Hallucination Detection](../Paper08_HallucinationDetection/) | Detection/identification reductions, tell-tale and negative-example results, Appendix results, Example 1, and oracle/effectivity boundaries, compared with arXiv v2 | ChatGPT Pro | 2 August 2026 | Pending |
| [#28 Contrastive Generation](../Paper28_ContrastiveGeneration/) | Deterministic statements, hierarchy and robustness coverage, and the Theorem 6.6 witness interface, compared with the arXiv-v1 pre-repair baseline | ChatGPT Pro | 2 August 2026 | Pending; the named-witness repair is kernel-checked separately |
| [#31 Bounded Memory](../Paper31_BoundedMemory/) | Deterministic statements, universe/order/output/indexing boundaries, and Appendix Lemma A.3, compared with the arXiv-v1 pre-repair baseline | ChatGPT Pro | 2 August 2026 | Pending; the Lemma A.3 wrapper repair is kernel-checked separately |

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
