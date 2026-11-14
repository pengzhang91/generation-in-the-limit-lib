# P29: Mistake-Bounded Language Generation — LLM statement audit

All four source-claim groups and five targets were reviewed. The positive-prior and finite-activation guards clarify the meaningful finite-bound case of Theorem 4.1. Theorem 5.1's generator-first convention requires the documented +1 correction to the closure-dimension mistake and last-error bounds; a disjoint infinite-language pair already contradicts the printed zero bound. The exact displayed Theorem 6.1 bound is natively present for the same generator, beyond the sharper registered integer endpoint.

Theorem 6.4 remains a disclosed substantive formalization gap: the registered diagnostic is only arithmetic. Independently, its printed fixed-base argument does not contradict a class-dependent Big-O rate; the late rounds are still bounded by (n+2) max{i,m_i}. The source headline's truth remains unresolved, rather than refuted by this check.

No genuine translation mismatch or missing interface assembly was established. Semantic/classical access and clock conventions remain explicit. All additional mathematical checks are informal, not newly Lean-checked; no proof certification is claimed. The exact source PDF hash is verified.

This review covers **4 current source-claim records**, with 5 registered target declarations, against the frozen non-P38 working tree based on `ca97f2b`. The base commit alone does not identify the audited dirty tree; the [input manifest](evidence/input-manifest.json) pins its bytes.

The two independent contexts requested **gpt-6.1-sol / xhigh**. Stage 1 reconstructed Lean types and defining bodies without the paper, comments or theorem proof bodies. The source reviewer first froze an independent paper inventory, then compared it with Stage 1 and the exact Lean interface. The later adjudication continued that same source reviewer after freezing the comparison; it was not a third independent blind review. Backend revision is not exposed.

## Results and provenance

- [Source inventory](evidence/source-inventory.md)
- [Lean-only reconstruction](evidence/code-only-reconstruction.md)
- [Source comparison](evidence/source-comparison.md)
- [Adjudication](evidence/adjudication.md) and [per-claim dispositions](evidence/adjudicated-claims.json)
- [Run record](evidence/audit-run-record.json) and [archive record](record.json)

- arXiv:2605.10809v1: verified PDF SHA-256 `c79335d8c0fec7e3960c141c034a34144e4928d118f27311c8d661f81ba61365`.

Completion is separate from a passing verdict or full formalization. Source corrections, missing formalization, interface assembly, model/representation qualifications and substantive translation discrepancies are distinguished in the reports. Algorithm interfaces and defining transitions are reviewed where relevant; proof bodies and complete implementation correctness are not certified. Existing human audit credit and historical LLM evidence are unchanged.

The selected-paper preparation build passed; no repository-wide build was run because this task changed no mathematical Lean files. Full input packages, PDFs and source-page images remain local under `audit-packages/REMAINING8_2026-11-14_ca97f2b/P29` and untracked. Results use the existing AuditRecords layout. No Git staging, commit or push was performed.

Verify this directory with `shasum -a 256 -c SHA256SUMS`.
