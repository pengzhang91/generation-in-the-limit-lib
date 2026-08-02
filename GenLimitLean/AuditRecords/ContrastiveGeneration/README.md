# Li--Han--Jiang--Gao external statement-audit record

This directory preserves the two-stage AI-assisted statement-faithfulness
review for Paper 28, Li--Han--Jiang--Gao's *Contrastive Identification and
Generation in the Limit*:

1. reconstruct the mathematics from Lean signatures and
   statement-relevant definitions without seeing the paper;
2. compare that reconstruction with the pinned arXiv-v1 author PDF.

The immutable review inspected repository commit
`dfcd13534f9d51642a9f88904268e95454c88f7f`. Its verdict is that the central
deterministic, information-theoretic results are substantially faithful, but
the clean hierarchy, the general robustness claim, and constructive/effective
claims are not completely represented.

The comparison also found a statement-interface gap around Theorem 6.6: the
audited theorem type asserted that some budget-independent identifier exists,
but did not name `absenceCountIdentifier` as its witness. A later private-source
repair adds that named theorem without changing the mathematical assumptions.
This record pins both source states and the repair diff, but does **not** claim
that the repair has already been applied in this initial public import. That
follow-up belongs in its own public commit.

See the [Paper 28 map](../../PaperMaps/ContrastiveGeneration.md) for the
statement correspondence and limitations. The development is kernel checked,
but no named human correspondence level has been assigned; human review is
tracked separately in [`../../HUMAN_AUDIT.md`](../../HUMAN_AUDIT.md).

Verify the byte-for-byte evidence mirrors from this directory with:

```bash
sha256sum -c SHA256SUMS
```
