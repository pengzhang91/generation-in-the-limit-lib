# #15 PartialEnumeration — LLM statement-faithfulness record

结论：partial generation、有限交集假设的生成及 full-text 识别／分离有实质 native 支持；α/3、α/2 密度结果仍是条件性组件，缺少完整运行与证书组装。论文 partial topology 的定义与 Theorem 4.12 存在实质冲突，Lean 尚未形式化该部分。本次裁决也撤回了一项第二阶段的错误判断：按观察数量对齐后，没有所谓 current-input freshness 缺口。

This directory mirrors the completed two-stage statement-faithfulness review for
*Language Generation and Identification From Partial Enumeration: Tight Density Bounds and Topological Characterizations*, followed by its separately frozen discrepancy adjudication.
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
- Source: arXiv:2511.05295v1; PDF SHA-256 `a33b59725302753cefee10d33d93c9c7b0f7215b1f4858abc8fce532234c5d7b`. Source PDFs are not redistributed here.
- Base commit: `60620581aa210daec6fa7d3aa65d7f9fdb565b8c` on `work/non-p38`.
- Exact inputs are a **dirty working-tree byte snapshot**, not the base commit alone; [input manifest](evidence/input-manifest.json) pins them.
- [Code-only reconstruction](evidence/code-only-reconstruction.md)
- [Source comparison](evidence/source-comparison.md)
- [Discrepancy adjudication](evidence/adjudication.md)
- [Chinese audit summary](evidence/AUDIT_SUMMARY.md)
- [Completed original run record](evidence/audit-run-record.json)
- [Archive record](record.json)
- Original full QA/input package (local only, not distributed): `audit-packages/P15_2026-11-10_6062058`.

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
