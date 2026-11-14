# #11 LearningAlgorithmsInTheLimit — LLM statement-faithfulness record

结论：具体有限程序 TM／TBO 学习器有实质构造，Corollary 15 的具体有效接口特例应获完整信用；其余时间类、转导、不可计算下界及 MSM 结果主要是已披露的条件性核心。Lemma 9／25 在论文允许的部分函数、仅正观察语义下有反例；Lean 的共同输入源／完整 Option 正确性版本成立，但不能不加限定地登记为原引理的完整形式化。

This directory mirrors the completed two-stage statement-faithfulness review for
*Learning Algorithms in the Limit*, followed by its separately frozen discrepancy adjudication.
It uses the existing AuditRecords v1 layout; this conversion is not a new audit.

1. Reconstruct selected Lean statements without the paper, comments or proof bodies.
2. Compare them with the pinned author source in a different fresh context.
3. After freezing that comparison, inspect explanations and adjudicate differences.

The first two stages requested `gpt-6.1-sol` / `xhigh`.
Backend revision is not exposed. The adjudication is **not** a third independent
blind review. Its actual reviewer/context/configuration, including P03's
coordinator adjudication, remain in the preserved run records.

## Scope and evidence

- Selected target declarations: **16**. Completion does not imply all-pass or whole-paper formalization.
- Source: COLT 2025 proceedings, PMLR 291; PDF SHA-256 `83aef91acf3b06c6dbbe6432fa5c1084cc7396c206684a5ebf0d4f62c0e61d57`. Source PDFs are not redistributed here.
- Base commit: `60620581aa210daec6fa7d3aa65d7f9fdb565b8c` on `work/non-p38`.
- Exact inputs are a **dirty working-tree byte snapshot**, not the base commit alone; [input manifest](evidence/input-manifest.json) pins them.
- [Code-only reconstruction](evidence/code-only-reconstruction.md)
- [Source comparison](evidence/source-comparison.md)
- [Discrepancy adjudication](evidence/adjudication.md)
- [Chinese audit summary](evidence/AUDIT_SUMMARY.md)
- [Completed original run record](evidence/audit-run-record.json)
- [Archive record](record.json)
- Original full QA/input package (local only, not distributed): `audit-packages/P11_2026-11-10_6062058`.

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
