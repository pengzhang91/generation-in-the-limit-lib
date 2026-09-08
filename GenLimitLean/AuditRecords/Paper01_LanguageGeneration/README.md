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
axiom-allowlist checked, but they are not retroactively covered by the
checksum-pinned ChatGPT Pro evidence or by the existing human audit.

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

The remaining unformalized NeurIPS main result is robust-prompt Theorem 7.1.
The informal strengthening that the countable-family Theorem 2.1 machines can
avoid repeating their own outputs also remains outside the formalization;
Theorem 2.2's separate pairwise-distinct conclusion is complete. Current
coverage is maintained in the paper map linked below.

The existing Level 3 human audit covers only `GenLimit.KM.Semantic`. It is
carried forward through `f302337` because the audited `Critical` and `Semantic`
definitions, theorem statements, and proofs were unchanged. It does not
extend to the observed-set interface, the finite-query machine, Theorem 2.2,
or either theorem's universe transports. See
[`../Human/README.md`](../Human/README.md) for the named human record and
[`../../PaperMaps/Paper01_LanguageGeneration.md`](../../PaperMaps/Paper01_LanguageGeneration.md) for the complete correspondence
map.

Verify the mirrored evidence from this directory with:

```bash
sha256sum -c SHA256SUMS
```
