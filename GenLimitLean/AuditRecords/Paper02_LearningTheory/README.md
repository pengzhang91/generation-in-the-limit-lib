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
The later P02-local refactor and the Gold/Angluin/KM bridge modules are not
retroactively included in that evidence bundle; their current kernel and
axiom status is tracked by `Audit.lean` and the paper map.

The review finds the ordinary and prompted generation theory substantially
faithful. It also records two important boundaries: the six Theorem 4.1
constructions are formalized only at the VC/Littlestone combinatorial layer,
not as literal PAC/online-learning models, and Lean refutes the paper's false
arbitrary-stream EUC equivalence while proving Theorems C.2 and C.4 from the
printed Definition C.1. The later bridge diagnostic additionally refutes the
printed arbitrary-class wording of Theorem 2.3 and proves its corrected
countable form; this postdates and does not alter the immutable evidence.

The development is kernel-checked. A scope-limited human audit is now recorded
for Proposition 2.1 and Theorems 2.4, 2.5, 3.3, 3.5, and 3.10; no aggregate
human correspondence level has been assigned to P02 as a whole. See
[`../../PaperMaps/Paper02_LearningTheory.md`](../../PaperMaps/Paper02_LearningTheory.md)
for the theorem correspondence and current scope boundaries, and
[`../Human/README.md`](../Human/README.md) for the separate human-audit ledger.

The current paper map is intentionally revision-aware. In particular, it
records the later identification bridges, the corrected countable Theorem
2.3 and its arbitrary-class counterexample, the Lemma 3.4 singleton-closure
repair, and the principal currently known scope boundaries. Statements
in the immutable evidence that identification is absent remain historically
correct for its pinned snapshot but are superseded as descriptions of the
current tree. The evidence itself must not be edited retroactively.

Verify the mirrored evidence from this directory with:

```bash
sha256sum -c SHA256SUMS
```
