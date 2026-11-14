# #07 DensityMeasuresForLanguageGeneration — LLM statement-faithfulness record

结论：index generation 正结果和 perfect-tower／limit-point 等价对应良好；其余目标主要是中间或条件性数学。尚无完整的无条件 1/8 element-density 算法、finite-rank 密度定理、index-breadth iff 或 truth-index 最优性证明。既有说明中的两项推断需要收窄：pair map 单射不推出 capacity two；早期 rank-two ancestry 反例不满足 late A_acc 证明所需的关键前提。

This directory mirrors the completed two-stage statement-faithfulness review for
*Density Measures for Language Generation*, followed by its separately frozen discrepancy adjudication.
It uses the existing AuditRecords v1 layout; this conversion is not a new audit.

1. Reconstruct selected Lean statements without the paper, comments or proof bodies.
2. Compare them with the pinned author source in a different fresh context.
3. After freezing that comparison, inspect explanations and adjudicate differences.

The first two stages requested `gpt-6.1-sol` / `xhigh`.
Backend revision is not exposed. The adjudication is **not** a third independent
blind review. Its actual reviewer/context/configuration, including P03's
coordinator adjudication, remain in the preserved run records.

## Scope and evidence

- Selected target declarations: **9**. Completion does not imply all-pass or whole-paper formalization.
- Source: arXiv:2504.14370v1; PDF SHA-256 `3a1f56b09c05e7ed84a37544f53d84393f0bb968ad013e5bbd110ff14c0a5038`. Source PDFs are not redistributed here.
- Base commit: `60620581aa210daec6fa7d3aa65d7f9fdb565b8c` on `work/non-p38`.
- Exact inputs are a **dirty working-tree byte snapshot**, not the base commit alone; [input manifest](evidence/input-manifest.json) pins them.
- [Code-only reconstruction](evidence/code-only-reconstruction.md)
- [Source comparison](evidence/source-comparison.md)
- [Discrepancy adjudication](evidence/adjudication.md)
- [Chinese audit summary](evidence/AUDIT_SUMMARY.md)
- [Completed original run record](evidence/audit-run-record.json)
- [Archive record](record.json)
- Original full QA/input package (local only, not distributed): `audit-packages/P07_2026-11-10_6062058`.

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
