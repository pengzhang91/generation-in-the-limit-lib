# Audit records

This directory is the authoritative home for paper-to-Lean audit evidence:

- [`Human/README.md`](Human/README.md) records completed human audits, their
  exact levels and code anchors, and the queue of checks awaiting human review.
- The numbered paper directories preserve source-pinned ChatGPT Pro
  statement-faithfulness checks and machine-readable provenance.

At the maintainer's direction, ChatGPT Pro performed the paper-scoped checks
preserved here. Each record is independently checksummed and identifies the
exact Lean snapshot and source editions used for review.

The checks used the same two-stage method:

1. reconstruct the mathematical interface from Lean declaration signatures
   and statement-relevant definition bodies while withholding the paper and
   excluding comments, theorem proof bodies, and tactic scripts as
   mathematical evidence;
2. compare that reconstruction with the pinned author source, checking objects
   and types, binder and quantifier order, hypotheses and conclusions,
   representation and indexing, presentation/access/output interfaces,
   theorem coverage and witness-link assembly, strength or weakening, vacuity
   and edge cases, and omitted claims.

These records are neither Lean kernel certificates nor human correspondence
audits. ChatGPT Pro did not audit theorem proof-body correctness, establish
proof-step correspondence, rerun Lean, or certify the papers' mathematics. Kernel and
axiom checks live in [`../Audit.lean`](../Audit.lean) and
[`../AUDIT.md`](../AUDIT.md). Named human reviews, with their exact levels and
code anchors, live in [`Human/README.md`](Human/README.md), which also
provides a uniform index of these pending checks.

Each paper directory contains:

- `record.json`: machine-readable source, provenance, scope, and review status;
- `SHA256SUMS`: integrity checks for the evidence files;
- `README.md`: a concise paper-specific interpretation guide; and
- `evidence/`: the preserved external-review artifacts, but never source PDFs.

Run each checksum manifest from its containing directory, or rely on the CI
step that checks every `AuditRecords/**/SHA256SUMS` file.

Current mirrored ChatGPT Pro records cover
[`#01 Language Generation`](Paper01_LanguageGeneration/),
[`#02 Learning Theory`](Paper02_LearningTheory/),
[`#06 Noisy Examples`](Paper06_NoisyExamples/),
[`#08 Hallucination Detection`](Paper08_HallucinationDetection/),
[`#28 Contrastive Generation`](Paper28_ContrastiveGeneration/), and
[`#31 Bounded Memory`](Paper31_BoundedMemory/). The adjacent classical
development [`#0A Inductive Inference from Positive Data`](../PaperMaps/Paper00A_PositiveDataInference.md),
used by #08 and #28, has a Level 1 human audit recorded in the
[`Human`](Human/) ledger but no separate mirrored ChatGPT Pro record.

#28 Contrastive Generation additionally demonstrates the audit/improvement loop. Its record
pins the pre-repair Lean tree inspected by both external stages, the repaired
private-source tree, and the exact named-witness patch. Public history keeps
the baseline import, immutable audit record, and repair as separate steps.
The repair resolves the Theorem 6.6 witness-interface finding but does not
retroactively alter the evidence or claim a human review, computable
tie-breaking rule, or effective algorithm.

#31 Bounded Memory records the same baseline--audit--repair discipline. Its immutable
evidence classified Appendix Lemma A.3 as faithful jointly but unbundled: all
four coding-cell properties were proved, but no source-facing existential
wrapper assembled them. The separately tracked public `lemma_A_3` repair only
packages those existing facts. It does not alter the evidence, claim human
review, transport the `ℕ` construction to every countable universe, or add
computability, runtime, oracle, or machine-level memory guarantees.
