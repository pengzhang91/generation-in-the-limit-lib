# P27: Language Generation with Feedback: Queries and Mistakes — LLM statement audit

All ten source-claim groups, 13 targets and 38 components were reviewed. The counterexample to Appendix Lemma A.8 satisfies the source's success and freshness premises, including its specific freshening rule. It supports a justified correction of actual-prefix self-locking, but does not refute the headline Theorem 3.9: the same example satisfies both sides of that equivalence.

The unrestricted reverse direction of Theorem 3.9 and Theorem 3.10 components A.10/A.11 remain formalization gaps. The principal feedback characterizations retain faithful semantic correspondence with explicit algorithm/model qualifications. Native three-point and vertical-row same-class witnesses were recovered. The auxiliary zero-example set-mistake guarantee and adjacent Cartesian-product remark remain unrepresented in the inspected interfaces.

A separate local Appendix A.4 phase claim has an informal bounded-negative-count repair without changing its theorem statement. Algorithm variants do not automatically inherit the source's query-nonrepetition addendum. No genuine oracle/timing translation mismatch was established. Additional mathematical checks are informal, not newly Lean-checked. The exact source PDF hash is verified; Section 3.5 locator metadata should read Section 3.4.4 for this edition.

This review covers **10 current source-claim records**, with 13 registered target declarations, against the frozen non-P38 working tree based on `ca97f2b`. The base commit alone does not identify the audited dirty tree; the [input manifest](evidence/input-manifest.json) pins its bytes.

The two independent contexts requested **gpt-6.1-sol / xhigh**. Stage 1 reconstructed Lean types and defining bodies without the paper, comments or theorem proof bodies. The source reviewer first froze an independent paper inventory, then compared it with Stage 1 and the exact Lean interface. The later adjudication continued that same source reviewer after freezing the comparison; it was not a third independent blind review. Backend revision is not exposed.

## Results and provenance

- [Source inventory](evidence/source-inventory.md)
- [Lean-only reconstruction](evidence/code-only-reconstruction.md)
- [Source comparison](evidence/source-comparison.md)
- [Adjudication](evidence/adjudication.md) and [per-claim dispositions](evidence/adjudicated-claims.json)
- [Run record](evidence/audit-run-record.json) and [archive record](record.json)

- ICML 2026 OpenReview record jvfXyIcQ8a: verified PDF SHA-256 `e3467ab76be2eae001490a43e461865d2c704633e2656bd05ff2eb477b4b1319`.

Completion is separate from a passing verdict or full formalization. Source corrections, missing formalization, interface assembly, model/representation qualifications and substantive translation discrepancies are distinguished in the reports. Algorithm interfaces and defining transitions are reviewed where relevant; proof bodies and complete implementation correctness are not certified. Existing human audit credit and historical LLM evidence are unchanged.

The selected-paper preparation build passed; no repository-wide build was run because this task changed no mathematical Lean files. Full input packages, PDFs and source-page images remain local under `audit-packages/REMAINING8_2026-11-14_ca97f2b/P27` and untracked. Results use the existing AuditRecords layout. No Git staging, commit or push occurred during the original audit run. The result archive was subsequently committed in `0d95bb73c0e5f013bce3105df831ef1c7e5c6af6`; raw input packages remain untracked.

Verify this directory with `shasum -a 256 -c SHA256SUMS`.
