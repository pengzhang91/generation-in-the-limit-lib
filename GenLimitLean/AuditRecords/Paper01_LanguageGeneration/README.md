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

At the audited snapshot, the comparison supported four Theorem 2.1 paths and
identified material exclusions: finite-family Theorem 2.2, prompted
generation, arbitrary-countable-universe transport, and pairwise distinctness
of generated outputs.

## Post-audit developments

Commit `f302337` adds the native fixed-sample membership-query formalization
of NeurIPS Theorem 2.2, including its infinite pairwise-distinct output
sequence, explicit-equivalence transport, and classical countable-universe
wrapper. The current tree also has the corresponding countable-universe
transport for Theorem 2.1. These later declarations are kernel and
axiom-allowlist checked. They are not retroactively covered by the original
ChatGPT Pro evidence or the historical semantic Level 3 audit; later scoped
Level 1 reviews are recorded below.

Commits `b740500` and `8e0a19d` are compatibility-preserving refactors after
that audit. The first moves the proof of natural-number antitone stabilization
to a paper-independent Support module while retaining the original P01 theorem
and statement. The second adds a shared finite-sample oracle-consistency
predicate, reuses it in the finite-family filter, and factors the existing
finite-query consistency bridge through it. The public P01 definitions and
main theorem statements used downstream remain available with their original
names. These refactors passed the repository build and axiom audit, but they do
not extend the scope of the checksum-pinned or human paper-correspondence
records.

Robust-prompt Theorem 7.1 is now formalized, with public endpoint
`GenLimit.KM.Results.theorem_7_1` and canonical endpoint
`GenLimit.KM.Prompted.theorem_7_1`. Peng Zhang reported Level 1 review of those
two statements and their relevant definitions on 8 November 2026 at
`6062058`. The separately strengthened and transported results are outside
that human review. Shuangping Li's 25 September 2026 Level 1 review covers
Theorems 2.1 and 2.2 and their defining interfaces, including the explicit
universe-coding transports recorded in the human ledger.

The informal strengthening that the countable-family Theorem 2.1 machines can
avoid repeating their own outputs remains outside the formalization;
Theorem 2.2's separate pairwise-distinct conclusion is complete. Current
coverage is maintained in the paper map linked below.

The historical Level 3 human audit covers only `GenLimit.KM.Semantic`. It was
carried forward through `f302337`, but later shared-selector changes leave
that Level 3 scope `needs-review`. It does not extend to the observed-set
interface, finite-query machine, Theorem 2.2 or universe transports; the
separate Level 1 reviews do not certify their proof correspondence. See
[`../Human/README.md`](../Human/README.md) for the named human record and
[`../../PaperMaps/Paper01_LanguageGeneration.md`](../../PaperMaps/Paper01_LanguageGeneration.md) for the complete correspondence
map.

On 18 October 2026, Peng Zhang completed a separate Level 2 review of the
round-dependent Section 4 semantic specification and construction at
`c8af96a`, including the shared greatest-candidate and least-fresh selectors.
Theorem proof bodies and proof-step correspondence were explicitly excluded.
This current Level 2 record does not renew the historical Level 3 scope,
which remains `needs-review`. See the human ledger and
[`../Human/Fingerprints/P01_SemanticLevel2.json`](../Human/Fingerprints/P01_SemanticLevel2.json)
for the scoped record and reviewed fingerprints. The checksum-pinned
ChatGPT Pro evidence remains unchanged.

Verify the mirrored evidence from this directory with:

```bash
sha256sum -c SHA256SUMS
```
