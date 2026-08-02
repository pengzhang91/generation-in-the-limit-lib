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
This record pins both source states and the repair diff. The initial public
audit import preserved the inspected baseline; the repair was then applied in
the separately tracked follow-up commit `6a1904dd5bc33a47b310adc753d0a35ad9df80cf`.
It resolves the named-witness interface gap without establishing computable
tie-breaking, oracle-free execution, or a runtime bound.

See the [Paper 28 map](../../PaperMaps/ContrastiveGeneration.md) for the
statement correspondence and limitations. The development is kernel checked,
but no named human correspondence level has been assigned; human review is
tracked separately in [`../../HUMAN_AUDIT.md`](../../HUMAN_AUDIT.md).

Verify the byte-for-byte evidence mirrors from this directory with:

```bash
sha256sum -c SHA256SUMS
```
