# P32: Generating in the Limit with Infinitely Many Hallucinations — LLM statement audit

All ten source-claim groups and 18 registered targets were reviewed. The half-density/pod constructions, strict and fractional novelty algorithms, matching upper bounds and copying tightness retain formalization gaps. Existing native no-novelty exploration and copying witnesses were recovered, so those constructions are not reported as absent.

The existing claim that Appendix Lemma D.1 is refuted is not supported: Section 2.2 already assumes an infinite guess language. Lean's implication matches that global context, while the finite diagnostic lies outside it. The source-refutation labels need metadata correction, not a change to the Lean implication. Separately, an in-domain example supports a local appendix cardinality repair without changing its theorem statement.

Sparse-exploration certificates demand a zero-offset bound at every prefix, stronger than the source's r(n)+O(1) estimate; supplying the missing algorithms must address that distinction. Raw repeated proposals versus newly added increments remain a qualified modeling issue. No genuine Lean translation mismatch was established. All additional mathematical arguments are informal, not newly Lean-checked. The exact-version official PDF text and HTML were reviewed, but raw PDF SHA-256 and decisive screenshot verification remain unavailable.

This review covers **10 current source-claim records**, with 18 registered target declarations, against the frozen non-P38 working tree based on `ca97f2b`. The base commit alone does not identify the audited dirty tree; the [input manifest](evidence/input-manifest.json) pins its bytes.

The two independent contexts requested **gpt-6.1-sol / xhigh**. Stage 1 reconstructed Lean types and defining bodies without the paper, comments or theorem proof bodies. The source reviewer first froze an independent paper inventory, then compared it with Stage 1 and the exact Lean interface. The later adjudication continued that same source reviewer after freezing the comparison; it was not a third independent blind review. Backend revision is not exposed.

## Results and provenance

- [Source inventory](evidence/source-inventory.md)
- [Lean-only reconstruction](evidence/code-only-reconstruction.md)
- [Source comparison](evidence/source-comparison.md)
- [Adjudication](evidence/adjudication.md) and [per-claim dispositions](evidence/adjudicated-claims.json)
- [Run record](evidence/audit-run-record.json) and [archive record](record.json)

- arXiv:2606.28354v1: exact-version primary source reviewed; raw PDF byte hash **not independently verified**.

Completion is separate from a passing verdict or full formalization. Source corrections, missing formalization, interface assembly, model/representation qualifications and substantive translation discrepancies are distinguished in the reports. Algorithm interfaces and defining transitions are reviewed where relevant; proof bodies and complete implementation correctness are not certified. Existing human audit credit and historical LLM evidence are unchanged.

The selected-paper preparation build passed; no repository-wide build was run because this task changed no mathematical Lean files. Full input packages, PDFs and source-page images remain local under `audit-packages/REMAINING8_2026-11-14_ca97f2b/P32` and untracked. Results use the existing AuditRecords layout. No Git staging, commit or push was performed.

Verify this directory with `shasum -a 256 -c SHA256SUMS`.
