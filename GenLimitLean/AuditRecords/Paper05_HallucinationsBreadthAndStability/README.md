# #05 HallucinationsBreadthAndStability — LLM statement-faithfulness record

结论：现有语义核心对应良好，但 P05 仍是部分形式化。两条 literal stability 反定理是有数学依据、预先披露的源文规格诊断，不计为未解释的 Lean 错误；它们也不能代替论文相应的正向算法、维数条件和定量保证。整个论文不评为全部通过／完整覆盖。

This directory mirrors the completed two-stage statement-faithfulness review for
*On Characterizations for Language Generation: Interplay of Hallucinations, Breadth, and Stability*, followed by its separately frozen discrepancy adjudication.
It uses the existing AuditRecords v1 layout; this conversion is not a new audit.

1. Reconstruct selected Lean statements without the paper, comments or proof bodies.
2. Compare them with the pinned author source in a different fresh context.
3. After freezing that comparison, inspect explanations and adjudicate differences.

The first two stages requested `gpt-6.1-sol` / `xhigh`.
Backend revision is not exposed. The adjudication is **not** a third independent
blind review. Its actual reviewer/context/configuration, including P03's
coordinator adjudication, remain in the preserved run records.

## Scope and evidence

- Selected target declarations: **6**. Completion does not imply all-pass or whole-paper formalization.
- Source: arXiv:2412.18530v2; PDF SHA-256 `ba5c0de2215a156ea45791e2399487aed75e08715176d57c24e6238ce4fdd7dd`. Source PDFs are not redistributed here.
- Base commit: `60620581aa210daec6fa7d3aa65d7f9fdb565b8c` on `work/non-p38`.
- Exact inputs are a **dirty working-tree byte snapshot**, not the base commit alone; [input manifest](evidence/input-manifest.json) pins them.
- [Code-only reconstruction](evidence/code-only-reconstruction.md)
- [Source comparison](evidence/source-comparison.md)
- [Discrepancy adjudication](evidence/adjudication.md)
- [Chinese audit summary](evidence/AUDIT_SUMMARY.md)
- [Completed original run record](evidence/audit-run-record.json)
- [Archive record](record.json)
- Original full QA/input package (local only, not distributed): `audit-packages/P05_2026-11-10_6062058`.

The reports and run records are byte-for-byte mirrors. Historical paths inside
them retain their original package interpretation and are not rewritten.
Original input-preparation metadata may say prepared/not-audited; the completed
run record above records the executed review. Hash discrepancies between official
and historically registered PDFs, when present, remain explicitly qualified in
source identity evidence. No historical bytes or mathematical claims are upgraded.

This is a statement/model correspondence review, not a proof-body audit or human
certification. Existing human reviews are recorded separately in the [human ledger](../Human/README.md).
No repair or new Lean verification was performed during this conversion. Original
audit packages remain local and untracked. The maintainer subsequently authorized
publishing these result archives; this publication does not revise the immutable
review evidence or its historical scope and code applicability.

Verify the archive from this directory using the same command as existing records:

```bash
sha256sum -c SHA256SUMS
```
