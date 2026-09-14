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
| P01 | round-dependent semantic construction | `current` |
| P02 | Proposition 2.1 and named Section 2--3 results | `current` |
| P04 | overview Theorems 1--4 | `needs-review`: shared dialogue extraction candidate |
| P06 | Section 3 Theorems 3.1, 3.3, 3.9, and 3.10 | `needs-review`: Core contamination migration candidate |
| P10 | overview Theorems 3.1--3.3 | `current` |
| P39 | criticality/focus, patient machine, exact main result, and partial enumeration | `needs-review`: migration candidates; the exact-main wrapper also has a recorded API change |

The P01 manifest protects statement and construction dimensions but not proof
bodies.  Its observed-set, finite-query, Theorem 2.2, and universe-transport
paths remain outside the human audit.  P0A protects only the semantic
characterization statement and its meaning, not the effective theorem or
Corollaries 1--3.  The other exclusions are recorded directly in their
manifests.
