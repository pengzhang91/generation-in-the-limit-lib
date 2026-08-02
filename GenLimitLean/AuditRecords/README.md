# External audit records

This directory preserves paper-scoped external review evidence alongside the
Lean development it discusses. Each record is independently checksummed and
identifies the exact Lean snapshot and source editions used for review.

These records are neither Lean kernel certificates nor human correspondence
audits. Kernel and axiom checks live in [`../Audit.lean`](../Audit.lean) and
[`../AUDIT.md`](../AUDIT.md). Named human reviews, with their exact levels and
code anchors, live only in [`../HUMAN_AUDIT.md`](../HUMAN_AUDIT.md).

Each paper directory contains:

- `record.json`: machine-readable source, provenance, scope, and review status;
- `SHA256SUMS`: integrity checks for the evidence files;
- `README.md`: a concise paper-specific interpretation guide; and
- `evidence/`: the preserved external-review artifacts, but never source PDFs.

Run each checksum manifest from its containing directory, or rely on the CI
step that checks every `AuditRecords/**/SHA256SUMS` file.
