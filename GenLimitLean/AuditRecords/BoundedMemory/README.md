# Kleinberg--Mehrotra--Saberi--Velegkas external statement-audit record

This directory preserves the two-stage AI-assisted statement-faithfulness
review for Paper 31, Kleinberg--Mehrotra--Saberi--Velegkas's *On Language
Generation in the Limit with Bounded Memory*:

1. reconstruct the mathematics from Lean signatures and statement-relevant
   definitions without seeing the paper;
2. compare that reconstruction with the pinned arXiv-v1 author PDF.

The immutable review inspected repository commit
`dfcd13534f9d51642a9f88904268e95454c88f7f`. Its verdict is **mostly faithful
with qualifications**: the principal deterministic semantic results are
present, but the `ℕ` specialization, target-specific density orders,
set-output infinitude interface, and equal-range relabeling in Theorem 5.2
prevent a fully literal correspondence.

The comparison also found that the audited baseline had all four substantive
components of Appendix Lemma A.3, but no single source-facing existential
wrapper. A later private-source repair adds `lemma_A_3` without changing the
mathematical assumptions, oracle access, or effectivity level. This record pins
both source states and the repair diff. The initial public audit import at
`71265c18e05f7650660dec4d117a5b03b645e7f0` preserved the inspected baseline;
the repair is now applied in a separately tracked follow-up. It resolves the
missing paper-facing wrapper without adding a generic countable-universe
transport, effective code allocation, runtime bound, oracle model, or
machine-level memory claim.

The original ChatGPT conversation is preserved at the
[external audit conversation](https://chatgpt.com/g/g-p-6a6bc5b59d48819186b418c17390f24b-auto-research/c/6a6e3fc9-17a4-83ea-9dd6-60aea04ed032).
See the [Paper 31 map](../../PaperMaps/BoundedMemory.md) for the detailed
statement correspondence and limitations. The development is kernel checked,
but no named human correspondence level has been assigned; human review is
tracked separately in [`../../HUMAN_AUDIT.md`](../../HUMAN_AUDIT.md).

Verify the byte-for-byte evidence mirrors from this directory with:

```bash
sha256sum -c SHA256SUMS
```
