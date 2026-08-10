# #31 Bounded Memory — ChatGPT Pro statement-faithfulness record

This directory preserves the two-stage statement-faithfulness check performed
with ChatGPT Pro at the maintainer's direction for #31 Bounded Memory,
Kleinberg--Mehrotra--Saberi--Velegkas's *On Language Generation in the Limit
with Bounded Memory*:

1. reconstruct the mathematics from Lean signatures and statement-relevant
   definitions without seeing the paper;
2. compare that reconstruction with the pinned arXiv-v1 author PDF.

The checksum-pinned evidence remains byte-for-byte unchanged and therefore
retains the module labels from the audited snapshot. Current source paths use
`GenLimit.Paper31_BoundedMemory`; declaration namespaces remain stable.

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

The checksum-pinned evidence files in this directory are the public record of
the ChatGPT Pro check. See the [#31 map](../../PaperMaps/Paper31_BoundedMemory.md)
for the detailed statement correspondence and limitations. The development is
kernel checked, but no named human correspondence level has been assigned;
human review is tracked separately in
[`../Human/README.md`](../Human/README.md).

Verify the byte-for-byte evidence mirrors from this directory with:

```bash
sha256sum -c SHA256SUMS
```
