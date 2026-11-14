# #28 Contrastive Generation — ChatGPT Pro statement-faithfulness record

This directory preserves the two-stage statement-faithfulness check performed
with ChatGPT Pro at the maintainer's direction for #28 Contrastive Generation,
Li--Han--Jiang--Gao's *Contrastive Identification and Generation in the
Limit*:

1. reconstruct the mathematics from Lean signatures and
   statement-relevant definitions without seeing the paper;
2. compare that reconstruction with the pinned arXiv-v1 author PDF.

The checksum-pinned evidence remains byte-for-byte unchanged and therefore
retains the module labels from the audited snapshot. Current source paths use
`GenLimit.Paper28_ContrastiveGeneration`; declaration namespaces remain
stable.

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

See the [#28 map](../../PaperMaps/Paper28_ContrastiveGeneration.md) for the
statement correspondence and limitations. Shuangping Li completed Level 1
review of all 19 Overview statements and their statement-relevant definitions
on 13 November 2026 at `c828be2`. The full Theorem 5.13 inclusion diamond,
construction and proof correspondence, and results outside the Overview are
excluded. See the [human ledger](../Human/README.md) and
[applicability manifest](../Human/Fingerprints/P28_V1OverviewLevel1.json).
The historical `audit.humanCorrespondence` field retains its original status;
this later human review does not rewrite the LLM evidence.

Verify the byte-for-byte evidence mirrors from this directory with:

```bash
sha256sum -c SHA256SUMS
```
