# Karbasi--Montasser--Sous--Velegkas external statement-audit record

This record mirrors the two-stage AI-assisted review for Paper 08,
Karbasi--Montasser--Sous--Velegkas's *`(Im)possibility of Automated
Hallucination Detection in Large Language Models`*:

1. reconstruct the mathematical claims from Lean declaration signatures and
   statement-relevant definitions without seeing the paper;
2. compare that reconstruction with the pinned arXiv-v2 author PDF.

The review finds the central semantic equivalence between hallucination
detection and identification in the limit substantially faithful. It also
records the exact limits of that conclusion: the result is noncomputable and
oracle-level, `ConditionTwo` supplies finite tell-tales only existentially,
and the negative-example theorem is substantive only when a complete labeled
enumeration exists. Most importantly, Lean corrects the paper's false claim
after Example 1: the multiples family does satisfy the finite tell-tale
condition and is therefore detectable.

The Angluin support modules are a separately documented sibling development;
the audit compared their interfaces only as dependencies of Paper 08. The
development is kernel-checked, but no named human correspondence level has
been assigned. See
[`../../PaperMaps/HallucinationDetection.md`](../../PaperMaps/HallucinationDetection.md),
[`../../PaperMaps/Angluin.md`](../../PaperMaps/Angluin.md), and the separate
[`../../HUMAN_AUDIT.md`](../../HUMAN_AUDIT.md) human-audit ledger.

Verify the mirrored evidence from this directory with:

```bash
sha256sum -c SHA256SUMS
```
