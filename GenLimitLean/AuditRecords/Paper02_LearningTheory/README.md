# #02 Learning Theory — ChatGPT Pro statement-faithfulness record

This record mirrors the two-stage statement-faithfulness check performed with
ChatGPT Pro at the maintainer's direction for #02 Learning Theory,
Li--Raman--Tewari's *Generation through the Lens of Learning Theory*:

1. reconstruct the mathematical claims from Lean declaration signatures and
   statement-relevant definitions without seeing the paper;
2. compare that reconstruction with the pinned arXiv-v5 author PDF.

The checksum-pinned evidence remains byte-for-byte unchanged and therefore
retains the module labels from the audited snapshot. Current source paths use
`GenLimit.Paper02_LearningTheory`; declaration namespaces remain stable.

The review finds the ordinary and prompted generation theory substantially
faithful. It also records two important boundaries: the six Theorem 4.1
constructions are formalized only at the VC/Littlestone combinatorial layer,
not as literal PAC/online-learning models, and Lean refutes the paper's false
arbitrary-stream EUC equivalence while proving Theorems C.2 and C.4 from the
printed Definition C.1.

The development is kernel-checked, but no named human correspondence level has
been assigned. See [`../../PaperMaps/Paper02_LearningTheory.md`](../../PaperMaps/Paper02_LearningTheory.md)
for the detailed scope and [`../Human/README.md`](../Human/README.md) for
the separate human-audit ledger.

Verify the mirrored evidence from this directory with:

```bash
sha256sum -c SHA256SUMS
```
