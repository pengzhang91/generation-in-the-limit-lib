# #03 HallucinationAndModeCollapse — LLM statement-faithfulness record

结论（加入差异裁决后）：P03 的核心语义数学与已明示的 oracle 构造总体对应良好。Theorem 3.6 属于有依据的源文修正；无限目标假设符合论文上下文；计算模型对应则保留已说明的条件和源文解释问题。13 个目标声明均已覆盖，但不能把整个 Overview 标为无条件逐字等价／全部通过。完成状态与数学 verdict 分开，也不表示新增证明或人类认证。

This directory mirrors the completed two-stage statement-faithfulness review for
*On the Limits of Language Generation: Trade-Offs Between Hallucination and Mode Collapse*, followed by its separately frozen discrepancy adjudication.
It uses the existing AuditRecords v1 layout; this conversion is not a new audit.

1. Reconstruct selected Lean statements without the paper, comments or proof bodies.
2. Compare them with the pinned author source in a different fresh context.
3. After freezing that comparison, inspect explanations and adjudicate differences.

The first two stages requested `gpt-6.1-sol` / `xhigh`.
Backend revision is not exposed. The adjudication is **not** a third independent
blind review. Its actual reviewer/context/configuration, including P03's
coordinator adjudication, remain in the preserved run records.

## Scope and evidence

- Selected target declarations: **13**. Completion does not imply all-pass or whole-paper formalization.
- Source: arXiv:2411.09642v3; PDF SHA-256 `097bda3ceeab7ddb244595b2817c8766f540b508abfe24a2ca8eaa0feecf3439`. Source PDFs are not redistributed here.
- Base commit: `60620581aa210daec6fa7d3aa65d7f9fdb565b8c` on `work/non-p38`.
- Exact inputs are a **dirty working-tree byte snapshot**, not the base commit alone; [input manifest](evidence/input-manifest.json) pins them.
- [Code-only reconstruction](evidence/code-only-reconstruction.md)
- [Source comparison](evidence/source-comparison.md)
- [Discrepancy adjudication](evidence/adjudication.md)
- [Chinese audit summary](evidence/AUDIT_SUMMARY.md)
- [Completed original run record](evidence/audit-run-record.json)
- [Archive record](record.json)
- Original full QA/input package (local only, not distributed): `audit-packages/P03_Overview_2026-11-09_6062058`.

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
