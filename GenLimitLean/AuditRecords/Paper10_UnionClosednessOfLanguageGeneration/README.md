# #10 UnionClosednessOfLanguageGeneration — LLM statement-faithfulness record

结论：主要确定性数学结果在 native 命名见证和无限性声明的组合下对应良好；抽象 `theorem_3_3` 入口存在真实的规格弱化，不能由注释自动补齐。随机化、部分识别及具体附录例子仍未覆盖。源文中的符号和证明措辞修正有依据，不计为未解释的 Lean 错误。

This directory mirrors the completed two-stage statement-faithfulness review for
*On Union-Closedness of Language Generation*, followed by its separately frozen discrepancy adjudication.
It uses the existing AuditRecords v1 layout; this conversion is not a new audit.

1. Reconstruct selected Lean statements without the paper, comments or proof bodies.
2. Compare them with the pinned author source in a different fresh context.
3. After freezing that comparison, inspect explanations and adjudicate differences.

The first two stages requested `gpt-6.1-sol` / `xhigh`.
Backend revision is not exposed. The adjudication is **not** a third independent
blind review. Its actual reviewer/context/configuration, including P03's
coordinator adjudication, remain in the preserved run records.

## Scope and evidence

- Selected target declarations: **10**. Completion does not imply all-pass or whole-paper formalization.
- Source: arXiv:2506.18642v1; PDF SHA-256 `9e788a45543e67a80ab81880efe848da9b7ba1ed464bb696e2f462178dc5f089`. Source PDFs are not redistributed here.
- Base commit: `60620581aa210daec6fa7d3aa65d7f9fdb565b8c` on `work/non-p38`.
- Exact inputs are a **dirty working-tree byte snapshot**, not the base commit alone; [input manifest](evidence/input-manifest.json) pins them.
- [Code-only reconstruction](evidence/code-only-reconstruction.md)
- [Source comparison](evidence/source-comparison.md)
- [Discrepancy adjudication](evidence/adjudication.md)
- [Chinese audit summary](evidence/AUDIT_SUMMARY.md)
- [Completed original run record](evidence/audit-run-record.json)
- [Archive record](record.json)
- Original full QA/input package (local only, not distributed): `audit-packages/P10_2026-11-10_6062058`.

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

## Later maintainer clarification after human review

For Theorem 3.3, infinitude is not an unproved missing condition: the same concrete witness has the required infinitude property proved separately below the theorem. This is a writing/interface-assembly issue; the property should be included in the statement of `theorem_3_3`. The paper states infinitude globally in the Preliminaries and again in Remark 2.2, rather than repeating it in the theorem. This clarification preserves the older report without classifying the issue as a Lean translation error. See the [recorded clarification](../Claims405_LE20_2026_11_13/owner/maintainer-clarifications.json).
