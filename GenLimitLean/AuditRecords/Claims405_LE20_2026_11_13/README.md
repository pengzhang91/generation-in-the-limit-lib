# LLM audit of the original 405-claim inventory: papers numbered ≤20

This publishes the completed result archive for **270 original claims across 20 papers**: **29 new isolated reviews**, **192 reused detailed reviews**, and **49 reused component reviews**. The user requested reuse without re-auditing previously reviewed claims. Component reviews retain their limited scope; completion does not imply all-pass or complete formalization.

- [Findings and scope](AUDIT_SUMMARY.md), [claim table](CLAIM_COVERAGE.md), and [individual claim records](claims.json).
- [Per-paper AuditRecords archives](papers/) and [machine-readable summary](summary.json).
- [Frozen source identity](owner/source-snapshot.json), [reuse plan](owner/reuse-plan.json), and [P10 maintainer clarification](owner/maintainer-clarifications.json).
- [Original batch validation](evidence/original-batch/validation.json) describes checks made before publication; [publication integrity](publication-validation.json) covers these copies.

New reviews requested **gpt-6.1-sol / xhigh**, with a source-withheld Lean reconstruction and a separate source-first paper comparison. Informed adjudication continued the comparison reviewer after freezing its output. The backend revision is not exposed. The review covers statements, relevant definitions, scoped named algorithm interfaces, and missing/partial source correspondence, not full theorem proofs or complete algorithm implementations.

The audited new input was a frozen dirty non-P38 snapshot based on `d294766`, captured on 2026-11-13. Historical reviews retain their own code/source identities. Publication adds no re-audit or human certification, and does not attest every later source change. Original evidence files are byte-preserved. Their local paths and statements about then-untracked files are historical; use the published navigation above for repository links.

Only results, source hashes and provenance are distributed. Original PDFs, Lean input bundles, build caches and local `audit-packages/` remain untracked. Each paper retains the established `record.json`, `README.md`, `SHA256SUMS`, and `evidence/` layout. Verify checksum manifests from their containing directory.
