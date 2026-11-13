# Human-audit applicability fingerprints

These manifests detect when a declaration covered by a completed human audit
may no longer have the reviewed statement or semantic construction.  They are
a maintenance layer over the immutable evidence records; they are not new
paper-to-Lean audits.

`AuditFingerprintExport.lean` reads the current compiled Lean environment and
exports normalized declaration expressions.  The checker computes SHA-256
fingerprints and compares them with the tracked manifests:

```text
python3 scripts/check_audit_fingerprints.py
```

Run this command from the repository root.

The normalization removes expression metadata and local binder names.  A
theorem anchor records only its type.  A semantic definition anchor records
both its type and value.  This means that a proof-only theorem refactor does
not change statement applicability, while a changed theorem statement or
selected definition body is detected.

## Status workflow

- `current`: all exported anchors must match the reviewed baseline.  A
  mismatch fails CI and is reported as `NEEDS-REVIEW`.
- `needs-review`: the mismatch has been explicitly acknowledged with a
  nonempty `review_note`.  CI reports a warning but permits unrelated work to
  continue; the old baseline remains unchanged.

When declaration fingerprints were not captured at the historical audit
checkpoint, a current-tree candidate may be recorded with
`candidate_baseline: true`.  Such a manifest must remain `needs-review`; the
checker rejects any attempt to mark it `current`.  After the narrow human
review, remove the candidate marker, replace `candidate_captured_at` with a
reviewed `baseline_captured_at`, record the new human checkpoint, and set the
status to `current`.

Do not replace a reviewed fingerprint merely to make CI pass.  After a human
reviews the affected scope, use

```text
python3 scripts/check_audit_fingerprints.py --dump AUDIT_ID
```

to display the current hashes, record the new reviewed checkpoint, and return
the manifest to `current`.  The command only prints data and never rewrites a
baseline automatically.

## Guarded scopes

Each manifest contains its exact `applicability_scope` and
`not_automatically_tracked` boundary.  The current status summary is:

| Paper | Human-audit scope | Status |
|---|---|---|
| P0 | arbitrary-text semantic theory | `needs-review`: numbered-path and tell-tale migration candidate |
| P0A | semantic characterization | `current` |
| P01 | historical round-dependent semantic Level 3 scope | `needs-review`: proof correspondence not renewed |
| P01 | round-dependent semantic specification and construction | `current`: Level 2, 18 October 2026 |
| P01 | Theorems 2.1 and 2.2 specifications and defining interfaces | `current`: Level 1, 25 September 2026 |
| P02 | Proposition 2.1 and named Section 2--3 results | `current`: statement and definition applicability, 18 October 2026; construction and proofs excluded |
| P02 | Theorem 3.3 specification | `current`: Level 1, 25 September 2026 |
| P02 | Theorem 3.5 specification | `current`: Level 1, 25 September 2026 |
| P02 | Theorem 3.10 specification | `current`: Level 1, 25 September 2026 |
| P03 | Theorems 3.1--3.3 statements and defining interfaces | `current`: Level 1 reported 2 November 2026, checkpoint `82c0869` |
| P04 | overview Theorems 1--4 and detailed Theorem 7 | `current`: combined Level 1 statement and definition renewal, 21 October 2026 |
| P04 | overview Theorems 1, 3, and 4 | `current`: Level 1 statement and definition renewal, 19 October 2026 |
| P04 | overview Theorem 5 | `current`: Level 1 statement and feedback/GF-dimension definitions, 21 October 2026 |
| P06 | Section 3 Theorems 3.1, 3.3, 3.9, and 3.10 | `current`: Level 1, 26 September 2026 |
| P10 | overview Theorems 3.1--3.3 | `current`: Level 1, 25 September 2026 |
| P21 | arXiv v2: all 20 Overview theorem statements and their defining interfaces | `current`: Level 1 reported 1 November 2026, checkpoint `7bdc137` |
| P22 | arXiv v2 Theorems 4.1, 5.1, 6.1 (both forms), 6.6, and 7.3 statements and defining interfaces; Theorem 7.1 excluded | `current`: Level 1, 12 November 2026, checkpoint `6062058` |
| P23 | arXiv v2 Overview Claims 3.3, 3.5, 3.6, 4.4, 4.11 (repaired), 4.18, 4.20, and 7.1 statements and defining interfaces | `current`: Level 1, 13 November 2026, checkpoint `6062058` |
| P27 | ICML 2026 Theorems 3.1--3.4, Corollaries 3.6--3.8, Theorem 3.9 set-to-element, the Lemma A.8 counterexample, and Theorem 3.10 components A.9, A.12, and A.13 statements and defining interfaces | `current`: Level 1, 13 November 2026, checkpoint `a19851f` |
| P28 | arXiv v1: all 19 Overview statements and defining interfaces | `current`: Level 1, 13 November 2026, checkpoint `c828be2` |
| P29 | arXiv v1 Theorems 4.1, 5.1 (corrected), and 6.1 and Lemmas 6.2--6.3 statements and defining interfaces | `current`: Level 1, 13 November 2026, checkpoint `c828be2` |
| P30 | arXiv v2 Theorem 4 / Appendix Theorem 12 (four totalized-GCG statements, stricter `id` deadline) and defining interfaces | `current`: Level 1, 13 November 2026, checkpoint `c828be2` |
| P31 | arXiv v1: all 13 Overview statements (Theorems 4.1 and 4.10 order-robust) and defining interfaces | `current`: Level 1, 13 November 2026, checkpoint `c828be2` |
| P32 | arXiv v1: ten Overview statements and defining interfaces | `current`: Level 1, 13 November 2026, checkpoint `c828be2` |
| P39 | arXiv v2 Theorems 3.15 (achievability) and B.3 statements and defining interfaces | `current`: Level 1 reported 7 November 2026, checkpoint `3f0aa55` |
| P39 | historical criticality/focus, patient machine, exact main result, and partial enumeration | `needs-review`: migration candidates; the exact-main wrapper also has a recorded API change |

The new P39 Level 1 manifest guards only the two v2 Overview statements and
their defining dependencies. It includes the Core ordered-density
specialization in increasing target order, but does not renew any of the four
historical P39 audit scopes or certify construction/proof correspondence.

The P22 Level 1 manifest guards six Overview statements and their defining
dependencies. It does not guard `theorem_7_1_of_algorithm3` or the Theorem 7.1
diagnostic, which are outside the reviewed scope.

The P23 Level 1 manifest guards the eight Overview claim aliases and their
defining dependencies. The unformalized headline Theorems 4.1, 4.5, 5.1, 5.5,
5.8, and 5.9 have no Overview declarations and are outside the reviewed scope.

The P27 Level 1 manifest guards twelve Overview statements and their defining
dependencies. It does not guard `theorem_3_9_of_selfLocking`, whose premise
fails even for a one-language class, or the private existence lemma used by
`sourceFirst`.

The P28 Level 1 manifest guards all 19 Overview aliases and their defining
dependencies. The full Theorem 5.13 inclusion diamond is not an Overview
statement and is outside the reviewed scope.

The P29 Level 1 manifest guards seven Overview statements and their defining
dependencies. It does not guard `theorem_6_4_proof_diagnostic`, which is not a
source statement.

The P30 Level 1 manifest guards the four totalized-GCG Overview statements and
their defining dependencies. It does not guard the density-endgame,
turn-taking, rate-core, counting-core, or Lemma 2 endgame declarations.

The P31 Level 1 manifest guards all 13 Overview aliases and their defining
dependencies. The source's fixed-order upper bounds for Theorems 4.1 and 4.10
are not Overview statements and are outside the reviewed scope.

The P32 Level 1 manifest guards ten Overview statements and their defining
dependencies. It does not guard the Theorem 3.5 endgame, the certificate
wrappers for Lemma 4.5 and Theorems 4.8--4.9, or the finite-guess Lemma D.1
diagnostic.

The historical P01 semantic manifest protects statement and construction
dimensions but not proof bodies and remains `needs-review`. The 18 October
Level 2 manifest separately protects the current specification and construction,
including the shared greatest-candidate and least-fresh selector bodies. It
does not renew historical proof correspondence. The separate P01
Level 1 manifest covers Theorems 2.1 and 2.2 and their explicit-coding interfaces;
it does not renew the historical construction/proof scope or cover the
observed-set path. The P02 named-result manifest was renewed on 18 October
for definition and statement applicability after the finite-history migration;
it does not certify construction or proof correspondence. The P04 Theorems
1, 3, and 4 manifest separately renews statement and definition applicability
on 19 October. The 21 October review of detailed Theorem 7 / overview Theorem 2
also renews the shared adaptive membership-query definitions, completing the
combined Level 1 scope. Construction/proof correspondence and the Theorem 7
proof repair remain outside both statement-level scopes.
The separate 21 October Theorem 5 manifest guards the feedback game and
GF-dimension definitions, completing current Level 1 coverage of overview
Theorems 1--5 without extending it to constructions or proofs.
P0A protects only the semantic
characterization statement and its meaning, not the effective theorem or
Corollaries 1--3.  The other exclusions are recorded directly in their
manifests.
