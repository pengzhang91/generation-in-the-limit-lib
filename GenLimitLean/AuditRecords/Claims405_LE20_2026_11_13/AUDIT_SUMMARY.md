# LLM audit: original 405-claim inventory, papers numbered ≤20

Completed for the amended scope: **29 new isolated reviews**, plus **241 reused prior claim reviews**. The reuse group contains **192 detailed claim reviews** and **49 scoped component reviews**. All **270 original claim IDs** in the selected 20 papers have an individual record. The 49 limited reviews are not upgraded to complete claim reviews, and a completed review is not a passing formalization verdict.

The user explicitly requested that already audited claims not be re-audited. Earlier reports, verdicts, source identities and code snapshots are preserved. Changes since those snapshots are applicability notes, not automatic authorization for another review.

## Scope and navigation

The inventory is the original 405-record set at `14b4deb`, not the evolving current registry. Selected papers are P00, P00A, P01–P15 and P17–P19. P16 and P20 have no records in that inventory. This batch does not claim to audit the other 135 original records.

- [All 270 claim records](claims.json) and [readable coverage table](CLAIM_COVERAGE.md).
- [Machine-readable summary](summary.json), [validation](evidence/original-batch/validation.json), and [exact reuse plan](owner/reuse-plan.json).
- [AuditRecords-format archives](papers/): one `record.json`, `README.md`, `SHA256SUMS`, and evidence directory per paper. Historical evidence copies remain byte-identical; paths inside them retain their original interpretation.

| Paper | New reviews | Reused detailed | Reused component scope |
|---|---:|---:|---:|
| P00 | 17 | 0 | 0 |
| P00A | 8 | 0 | 0 |
| P01 | 0 | 5 | 0 |
| P02 | 0 | 25 | 0 |
| P03 | 3 | 13 | 1 |
| P04 | 0 | 15 | 5 |
| P05 | 0 | 13 | 6 |
| P06 | 0 | 20 | 0 |
| P07 | 0 | 5 | 5 |
| P08 | 0 | 17 | 0 |
| P09 | 0 | 11 | 1 |
| P10 | 0 | 10 | 1 |
| P11 | 0 | 1 | 8 |
| P12 | 0 | 18 | 1 |
| P13 | 0 | 1 | 6 |
| P14 | 0 | 3 | 0 |
| P15 | 0 | 8 | 2 |
| P17 | 1 | 17 | 9 |
| P18 | 0 | 3 | 3 |
| P19 | 0 | 7 | 1 |

## New findings

- **P00, 17 claims:** the semantic results have substantial native support, while effective machine naming, restricted-text instances and several other source results remain deliberately unformalized. Theorem 7.1 has all three native components, although its bundled interface places an unnecessary countable-presentation premise on the first two clauses. The printed naming-translation direction needs a qualified correction under the partial-range program convention; empty/total-generator conventions remain explicit limits. See [P00 adjudication](papers/Paper00_LanguageIdentification/evidence/new-review/adjudication.md).
- **P00A, 8 claims:** effective Theorem 1 and Corollaries 1–3 match their core specifications with representation qualifications; Theorems 2–5 remain formalization gaps. A proposition definition for Theorem 2 does not prove it. Alternative tell-tale procedures can produce different finite sets while satisfying the same specification, so unqualified “extensionally equivalent” wording is too strong. Contextual consistency/responsiveness properties are distinct from the reviewed core statements. See [P00A adjudication](papers/Paper00A_PositiveDataInference/evidence/new-review/adjudication.md).
- **P03, 3 appendix claims:** Proposition A.1 remains unformalized; its branch-test repair and partial-output versus normalized-probability model need separate treatment. For Theorem B.1 and Corollary B.2, separately reconstructed native selector, canonicalization and breadth ingredients support the required compositions informally, but the named source-facing bridges remain unassembled. The literal first-unseen output rule needs full-support sampling to support B.2. No genuine Lean statement translation error was established. See [P03 adjudication](papers/Paper03_HallucinationAndModeCollapse/evidence/new-review/adjudication.md).
- **P17, Claim 6.17:** the numeric rank result and a separate correctness theorem concern the same generator, so target membership is available under the combined hypotheses. The development uses a justified semantic threshold variant; literal pseudocode identity and the advertised time-index correspondence require qualification. No false Lean theorem or source-error verdict is asserted for this claim. See [P17 adjudication](papers/Paper17_InfiniteContamination/evidence/new-review/adjudication.md).

New disposition counts: `formalization-gap`: 16, `matches-source-context`: 1, `mixed`: 10, `qualified-model-or-representation`: 2. Mixed findings retain their component distinctions; they are not automatically translation errors. Source mistakes, partial formalization, valid alternative constructions and interface organization are not collapsed into one error category.

The later human-review clarification for **P10 Theorem 3.3** is preserved in English alongside the immutable older LLM findings: the same concrete witness already has a separate infinitude theorem. The issue is presentation/interface assembly, not a missing mathematical fact or a translation error. The infinitude convention is global in the Preliminaries and reiterated in Remark 2.2. See [maintainer clarification](owner/maintainer-clarifications.json). This adds no new human audit credit.

## Method and applicability

New reviews used requested **gpt-6.1-sol / xhigh**: source-withheld Lean type/definition reconstruction, a different fresh context that saved its source inventory before reading Lean, and informed adjudication after the comparison froze. Adjudication continued the second reviewer; it is not a third independent blind review. Supplemental reconstructions used the original retained source-withheld contexts. All original reports remain immutable, and supplemental discovery/read-order details are disclosed. Exact backend revision and applied configuration are not independently observable.

The new mathematical input is the dirty non-P38 working-tree snapshot captured at **2026-11-13 23:09:10 UTC**, based on `d294766f6749c23ae5a11e866fb7916175d2927f`; [source manifest](owner/source-snapshot.json) pins 671 files. It is not the base commit alone. Later concurrent P18/generated-audit edits and separately authorized human-audit instrumentation are recorded as live-tree drift in validation; the frozen inputs remain intact.

Twenty primary source editions (669 pages) were prepared. Exact registered PDF hashes match where available; P00A and P05 have no original expected hash. Annotation payloads were excluded and differing publisher/annotated bytes remain distinguished. Additional P02/P06 conference PDFs were unavailable; their exact arXiv sources and prior scoped reviews were retained, without claiming a new conference-edition review. Prior edition/hash limitations are preserved per claim.

This is statement, relevant-definition, named-algorithm-interface and coverage review. It is not exhaustive theorem-proof-body checking, proof-step correspondence, full algorithm construction/runtime auditing, ordinary computability certification from arbitrary semantic functions, or human approval. A source inventory or declaration census alone does not establish correspondence.

## Validation at audit completion and later publication

- All 270 unique original IDs, stage output identities, input/output freeze hashes, and supplemental target coverage verified.
- Reuse evidence: **241 claims, 656 references, 47 unique files** checked; historical bytes preserved in the new archive mappings.
- All 671 frozen source-file hashes and supplied source PDF/text hashes checked. New record checksum manifests verified.
- Targeted selected-paper umbrella preparation passed (3,587 build jobs); four pre-existing P17 `unnecessarySimpa` linter warnings were recorded separately from failures. No repository-wide build was needed because the LLM batch changed no mathematical Lean source.
- Git HEAD and staged changes remained unchanged. At audit completion, the packages and reports were local/untracked and no staging, commit, push or mathematical source repair had occurred. The maintainer subsequently authorized publication of these result archives; full input packages remain local and untracked.

Separate user-requested human-record tasks were completed in the live non-P38 tree: **P17’s nine Overview theorems and their definitions**, and **P19’s four Overview Theorems 2.16–2.19 with 34 recursive definition bodies**. These are attributed user reports, not certifications produced by this LLM review. Their targeted builds, fingerprint and registry checks passed; metadata was uncommitted at audit completion and is included in the separate human-record publication. See the [human ledger](../Human/README.md). Original task verification logs remain in the local input package.
