# KM external statement-audit record

This record mirrors the two-stage AI-assisted review for Paper 01,
Kleinberg--Mullainathan's *Language Generation in the Limit*:

1. reconstruct the mathematical claims from declaration signatures and
   statement-relevant definitions without seeing the paper;
2. compare that reconstruction with pinned NeurIPS 2024 and arXiv-v1 PDFs.

The comparison supports the four Theorem 2.1 paths now exposed by
`GenLimit.KM`, while also identifying material exclusions: finite-family
Theorem 2.2, prompted generation, arbitrary-countable-universe transport, and
pairwise distinctness of generated outputs.

The existing Level 3 human audit covers only `GenLimit.KM.Semantic`. It does
not extend to the observed-set interface or either finite-query machine. See
[`../../HUMAN_AUDIT.md`](../../HUMAN_AUDIT.md) for the named human record and
[`../../PaperMaps/KM.md`](../../PaperMaps/KM.md) for the complete correspondence
map.

Verify the mirrored evidence from this directory with:

```bash
sha256sum -c SHA256SUMS
```
