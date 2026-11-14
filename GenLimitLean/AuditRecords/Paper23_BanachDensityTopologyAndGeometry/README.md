# P23: Validity, Sparse Holes, and Breadth in Language Generation: Banach Density, Topology, and Geometry — LLM statement audit

Seven represented structural claim groups have no demonstrated translation error at the reviewed interfaces; Claim 4.11 implements a justified source qualification. Six headline generation, geometry and discrepancy groups remain unformalized. Separate source wording/formula and registry-scope issues are recorded. Mathematical counterexamples and repair arguments in the adjudication are informal and not Lean-checked.

This review covers **13 current source-claim records**, with 8 registered target declarations, against the frozen non-P38 working tree based on `ca97f2b`. The base commit alone does not identify the audited dirty tree; the [input manifest](evidence/input-manifest.json) pins its bytes.

The two independent contexts requested **gpt-6.1-sol / xhigh**. Stage 1 reconstructed Lean types and defining bodies without the paper, comments or theorem proof bodies. The source reviewer first froze an independent paper inventory, then compared it with Stage 1 and the exact Lean interface. The later adjudication continued that same source reviewer after freezing the comparison; it was not a third independent blind review. Backend revision is not exposed.

## Results and provenance

- [Source inventory](evidence/source-inventory.md)
- [Lean-only reconstruction](evidence/code-only-reconstruction.md)
- [Source comparison](evidence/source-comparison.md)
- [Adjudication](evidence/adjudication.md) and [per-claim dispositions](evidence/adjudicated-claims.json)
- [Run record](evidence/audit-run-record.json) and [archive record](record.json)

- arXiv:2604.02385v2: verified PDF SHA-256 `c884ae86bdb9510c752b26cd5962ea94fb548885672b3cb0d24a2c2ab31cad3d`.

Completion is separate from a passing verdict or full formalization. Source corrections, missing formalization, interface assembly, model/representation qualifications and substantive translation discrepancies are distinguished in the reports. Algorithm interfaces and defining transitions are reviewed where relevant; proof bodies and complete implementation correctness are not certified. Existing human audit credit and historical LLM evidence are unchanged.

The selected-paper preparation build passed; no repository-wide build was run because this task changed no mathematical Lean files. Full input packages, PDFs and source-page images remain local under `audit-packages/REMAINING8_2026-11-14_ca97f2b/P23` and untracked. Results use the existing AuditRecords layout. No Git staging, commit or push was performed.

Verify this directory with `shasum -a 256 -c SHA256SUMS`.
