# #06 Noisy Examples — ChatGPT Pro statement-faithfulness record

This record mirrors the two-stage statement-faithfulness check performed with
ChatGPT Pro at the maintainer's direction for #06 Noisy Examples,
Ananth Raman and Vinod Raman's *Generation from Noisy Examples*:

1. reconstruct the mathematical claims from Lean declaration signatures and
   statement-relevant definitions without seeing the paper;
2. compare that reconstruction with the pinned arXiv-v2 author PDF.

The checksum-pinned evidence remains byte-for-byte unchanged and therefore
retains the module labels from the audited snapshot. Current source paths use
`GenLimit.Paper06_NoisyExamples`; declaration namespaces remain stable.

The review finds a substantially faithful qualitative formalization with
explicit repairs. Every paper-owned numbered mathematical result has a Lean
counterpart, while assumptions needed for empty, finite, or nonempty ambient
universes are exposed. The record also identifies the quantitative material
that is not formalized: the numerical noisy-closure complexity `NC_n`, the
`Theta(NC_n)` sample-complexity statement, and the proof-level bound
`NC_n(H_i) < i`.

The development is kernel-checked, but no named human correspondence level has
been assigned. See [`../../PaperMaps/Paper06_NoisyExamples.md`](../../PaperMaps/Paper06_NoisyExamples.md)
for the detailed scope and [`../Human/README.md`](../Human/README.md) for
the separate human-audit ledger.

Verify the mirrored evidence from this directory with:

```bash
sha256sum -c SHA256SUMS
```
