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

Current mirrored records cover KM, Li--Raman--Tewari, Raman--Raman,
Karbasi--Montasser--Sous--Velegkas (Paper 08), Li--Han--Jiang--Gao
(Paper 28), and Kleinberg--Mehrotra--Saberi--Velegkas (Paper 31). The Angluin
sibling used by Papers 08 and 28 has a scope map but no separate external-audit
record.

Paper 28 additionally demonstrates the audit/improvement loop. Its record
pins the pre-repair Lean tree inspected by both external stages, the repaired
private-source tree, and the exact named-witness patch. Public history keeps
the baseline import, immutable audit record, and repair as separate steps.
The repair resolves the Theorem 6.6 witness-interface finding but does not
retroactively alter the evidence or claim a human review, computable
tie-breaking rule, or effective algorithm.

Paper 31 records the same baseline--audit--repair discipline. Its immutable
evidence classified Appendix Lemma A.3 as faithful jointly but unbundled: all
four coding-cell properties were proved, but no source-facing existential
wrapper assembled them. The separately tracked public `lemma_A_3` repair only
packages those existing facts. It does not alter the evidence, claim human
review, transport the `ℕ` construction to every countable universe, or add
computability, runtime, oracle, or machine-level memory guarantees.
