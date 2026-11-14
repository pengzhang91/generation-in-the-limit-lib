# P39: Dense Language Generation Made Simple: Deterministic, Randomized, and Multi-Order Algorithms — LLM statement audit

The earlier/v2 recursive deterministic and partial-enumeration statements match their scoped semantic source claims, with explicit access and representation qualifications. No genuine Lean translation mismatch was established. Literal-v1 machine claims, deterministic optimality and randomized/multi-order extensions retain their documented formalization gaps. The registry understates the existing two-clause fact_3_13 interface; example-value documentation also needs clarification. C12 achievability is covered, while its printed theorem's missing optimality remains separately accounted for under C03. Exact-v1 PDF byte hashes and screenshot verification remain qualified.

This review covers **44 current source-claim records**, with 32 registered target declarations, against the frozen non-P38 working tree based on `ca97f2b`. The base commit alone does not identify the audited dirty tree; the [input manifest](evidence/input-manifest.json) pins its bytes.

The two independent contexts requested **gpt-6.1-sol / xhigh**. Stage 1 reconstructed Lean types and defining bodies without the paper, comments or theorem proof bodies. The source reviewer first froze an independent paper inventory, then compared it with Stage 1 and the exact Lean interface. The later adjudication continued that same source reviewer after freezing the comparison; it was not a third independent blind review. Backend revision is not exposed.

## Results and provenance

- [Source inventory](evidence/source-inventory.md)
- [Lean-only reconstruction](evidence/code-only-reconstruction.md)
- [Source comparison](evidence/source-comparison.md)
- [Adjudication](evidence/adjudication.md) and [per-claim dispositions](evidence/adjudicated-claims.json)
- [Run record](evidence/audit-run-record.json) and [archive record](record.json)

- Earlier manuscript supplied for formalization: verified PDF SHA-256 `1a9a81a7aa02719f5cfe852746f3db853d47d42f699e8f62cc78f451ef7cb23e`.
- arXiv:2608.01320v1: exact-version primary source reviewed; raw PDF byte hash **not independently verified**.
- arXiv:2608.01320v2: verified PDF SHA-256 `8dfc7ada39b62bb79d380331deeb4377035ec35d26b8334c2c6c6a91cb711b08`.

Completion is separate from a passing verdict or full formalization. Source corrections, missing formalization, interface assembly, model/representation qualifications and substantive translation discrepancies are distinguished in the reports. Algorithm interfaces and defining transitions are reviewed where relevant; proof bodies and complete implementation correctness are not certified. Existing human audit credit and historical LLM evidence are unchanged.

The selected-paper preparation build passed; no repository-wide build was run because this task changed no mathematical Lean files. Full input packages, PDFs and source-page images remain local under `audit-packages/REMAINING8_2026-11-14_ca97f2b/P39` and untracked. Results use the existing AuditRecords layout. No Git staging, commit or push was performed.

Verify this directory with `shasum -a 256 -c SHA256SUMS`.
