# P17 — original-inventory LLM audit record

Language Generation with Infinite Contamination. This uses the existing AuditRecords v1 layout. The maintainer authorized publication of the results; the full input package remains local and untracked.

Claim records: **27**. Modes: reused-detailed-review: 17, new-isolated-review: 1, reused-scoped-component-review: 9. Completion is separate from verdict; a recorded absence/partial formalization is not a passing formalization.

See [record.json](record.json), [claim-level records](evidence/claims.json), and [prior-evidence map](evidence/prior-evidence-map.json). Reused reports are byte-preserved and retain their original source editions, snapshots and scope. They were not re-reviewed. Scoped component reviews are not upgraded to whole-claim reviews.

New work: [Lean reconstruction](evidence/new-review/code-only-reconstruction.md), [source comparison](evidence/new-review/source-comparison.md), and [adjudication](evidence/new-review/adjudication.md). The first two use separate source-withheld/source-informed contexts, requested gpt-6.1-sol/xhigh. Adjudication continues the second reviewer after freeze; it is not a third independent blind review. Supplements, where present, are separately frozen and preserve the original reports.

Paths inside copied evidence retain their original package/workspace meaning. Source PDFs and the full Lean input snapshot remain in the local original batch. The published [source manifest](../../owner/source-snapshot.json) pins the audited bytes; inputs are not redistributed here. No theorem-proof audit or human approval is implied.

Verify from this directory with `sha256sum -c SHA256SUMS`.
