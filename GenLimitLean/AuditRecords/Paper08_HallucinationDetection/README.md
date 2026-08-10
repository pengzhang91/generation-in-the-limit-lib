# #08 Hallucination Detection — ChatGPT Pro statement-faithfulness record

This record mirrors the two-stage statement-faithfulness check performed with
ChatGPT Pro at the maintainer's direction for #08 Hallucination Detection,
Karbasi--Montasser--Sous--Velegkas's *`(Im)possibility of Automated
Hallucination Detection in Large Language Models`*:

1. reconstruct the mathematical claims from Lean declaration signatures and
   statement-relevant definitions without seeing the paper;
2. compare that reconstruction with the pinned arXiv-v2 author PDF.

The checksum-pinned evidence remains byte-for-byte unchanged and therefore
retains the module labels from the audited snapshot. Current source paths use
`GenLimit.Paper08_HallucinationDetection`; declaration namespaces remain
stable.

The review finds the central semantic equivalence between hallucination
detection and identification in the limit substantially faithful. It also
records the exact limits of that conclusion: the result is noncomputable and
oracle-level, `ConditionTwo` supplies finite tell-tales only existentially,
and the negative-example theorem is substantive only when a complete labeled
enumeration exists. Most importantly, Lean corrects the paper's false claim
after Example 1: the multiples family does satisfy the finite tell-tale
condition and is therefore detectable.

The Angluin support modules are a separately documented sibling development;
the audit compared their interfaces only as dependencies of #08. The
development is kernel-checked, but no named human correspondence level has
been assigned. See
[`../../PaperMaps/Paper08_HallucinationDetection.md`](../../PaperMaps/Paper08_HallucinationDetection.md),
[`../../PaperMaps/Angluin.md`](../../PaperMaps/Angluin.md), and the separate
[`../Human/README.md`](../Human/README.md) human-audit ledger.

Verify the mirrored evidence from this directory with:

```bash
sha256sum -c SHA256SUMS
```
