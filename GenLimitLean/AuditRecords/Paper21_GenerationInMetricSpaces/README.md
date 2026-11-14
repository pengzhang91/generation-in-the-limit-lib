# P21: On Generation in Metric Spaces — LLM statement audit

All 14 scoped source-claim groups (18 registered targets) are represented: nine retain model or representation qualifications and five match the source context. No substantive formalization gap or genuine translation mismatch was established for these scoped claims.

Example 4.8 uses a documented zero-exponent witness family. It supplies the full threshold phenomenon, but literal identity with a positive-exponent reading of the source is not established. Adding g_3 to the initial observations repairs a local cover inclusion only under the zero-exponent reading; this is not an unconditional correction of the source theorem. Example 4.5 all-radius UUS follows by an informal composition of existing interfaces for the same class, so a missing facade is not a missing mathematical fact.

These are semantic statements, with real-scalar and reachability qualifications where relevant; Appendix E implementation questions lie outside the scoped targets. Informal mathematical checks were not newly Lean-checked. The exact v2 source PDF hash is verified. This audit does not supply review of the ten original P21 v1 source records.

This review covers **14 current source-claim records**, with 18 registered target declarations, against the frozen non-P38 working tree based on `ca97f2b`. The base commit alone does not identify the audited dirty tree; the [input manifest](evidence/input-manifest.json) pins its bytes.

The two independent contexts requested **gpt-6.1-sol / xhigh**. Stage 1 reconstructed Lean types and defining bodies without the paper, comments or theorem proof bodies. The source reviewer first froze an independent paper inventory, then compared it with Stage 1 and the exact Lean interface. The later adjudication continued that same source reviewer after freezing the comparison; it was not a third independent blind review. Backend revision is not exposed.

## Results and provenance

- [Source inventory](evidence/source-inventory.md)
- [Lean-only reconstruction](evidence/code-only-reconstruction.md)
- [Source comparison](evidence/source-comparison.md)
- [Adjudication](evidence/adjudication.md) and [per-claim dispositions](evidence/adjudicated-claims.json)
- [Run record](evidence/audit-run-record.json) and [archive record](record.json)

- arXiv:2602.07710v2: verified PDF SHA-256 `b4e14e33fce18aa5d970a49d4886a647d9de888e8de29fab12ff8cda0afacfbc`.

Completion is separate from a passing verdict or full formalization. Source corrections, missing formalization, interface assembly, model/representation qualifications and substantive translation discrepancies are distinguished in the reports. Algorithm interfaces and defining transitions are reviewed where relevant; proof bodies and complete implementation correctness are not certified. Existing human audit credit and historical LLM evidence are unchanged.

The selected-paper preparation build passed; no repository-wide build was run because this task changed no mathematical Lean files. Full input packages, PDFs and source-page images remain local under `audit-packages/REMAINING8_2026-11-14_ca97f2b/P21` and untracked. Results use the existing AuditRecords layout. No Git staging, commit or push occurred during the original audit run. The result archive was subsequently committed in `0d95bb73c0e5f013bce3105df831ef1c7e5c6af6`; raw input packages remain untracked.

Verify this directory with `shasum -a 256 -c SHA256SUMS`.
