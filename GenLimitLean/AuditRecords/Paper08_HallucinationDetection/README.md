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

The later #0A integration changes the shared identifier representation from
finite tuples to ordered lists and routes tell-tale necessity through the
audited Gold result. It consequently retires the #08-local auxiliary adapter
and locking interface D33--D42 from the audited snapshot; no numbered #08
claim is removed. The immutable evidence continues to describe the exact
pre-refactor audit input.

The review finds the central semantic equivalence between hallucination
detection and identification in the limit substantially faithful. It also
records the exact limits of that conclusion: the result is noncomputable and
oracle-level, `ConditionTwo` supplies finite tell-tales only existentially,
and the negative-example theorem is substantive only when a complete labeled
enumeration exists. Most importantly, Lean corrects the paper's false claim
after Example 1: the multiples family does satisfy the finite tell-tale
condition and is therefore detectable.

The #0A Angluin modules are a separately documented sibling development; the
audit compared their interfaces only as dependencies of #08. Their semantic
Theorem 1 characterization has a separate Level 1 human audit. See
[`../../PaperMaps/Paper08_HallucinationDetection.md`](../../PaperMaps/Paper08_HallucinationDetection.md),
[`../../PaperMaps/Paper00A_PositiveDataInference.md`](../../PaperMaps/Paper00A_PositiveDataInference.md), and the separate
[`../Human/README.md`](../Human/README.md) human-audit ledger.

Verify the mirrored evidence from this directory with:

```bash
sha256sum -c SHA256SUMS
```
