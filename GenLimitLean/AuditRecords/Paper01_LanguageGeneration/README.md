# #01 Language Generation — ChatGPT Pro statement-faithfulness record

This record mirrors the two-stage statement-faithfulness check performed with
ChatGPT Pro at the maintainer's direction for #01 Language Generation,
Kleinberg--Mullainathan's *Language Generation in the Limit*:

1. reconstruct the mathematical claims from declaration signatures and
   statement-relevant definitions without seeing the paper;
2. compare that reconstruction with pinned NeurIPS 2024 and arXiv-v1 PDFs.

The checksum-pinned evidence remains byte-for-byte unchanged and therefore
retains the module labels from the audited snapshot. Current source paths use
`GenLimit.Paper01_LanguageGeneration`; declaration namespaces remain stable.

The comparison supports the four Theorem 2.1 paths now exposed by
`GenLimit.KM`, while also identifying material exclusions: finite-family
Theorem 2.2, prompted generation, arbitrary-countable-universe transport, and
pairwise distinctness of generated outputs.

The existing Level 3 human audit covers only `GenLimit.KM.Semantic`. It does
not extend to the observed-set interface or either finite-query machine. See
[`../Human/README.md`](../Human/README.md) for the named human record and
[`../../PaperMaps/Paper01_LanguageGeneration.md`](../../PaperMaps/Paper01_LanguageGeneration.md) for the complete correspondence
map.

Verify the mirrored evidence from this directory with:

```bash
sha256sum -c SHA256SUMS
```
